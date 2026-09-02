#!/usr/bin/env python3
"""Extract the exported statement surface of the _CoqProject tree.

One stdout line per exported declaration, sorted:

    file|section.path|kind|name|ctxhash|statement

statement is the declaration sentence with comments stripped and
whitespace normalized; for Definition/Fixpoint/Instance it is cut at
the first top-level `:=` (bodies are not surface). ctxhash is a
sha1 over the enclosing sections' Variable/Hypothesis/Context
sentences, because section discharge changes a statement with zero
text change. `Local` declarations and `Let`s are non-exported: they
are printed only under --local. HB.* generated names are out of this
extractor's reach (accepted risk, see the P2 spec's gate contract).

Usage:
    statement_surface.py [--rev COMMIT] [--local]

With --rev, files are read from that git revision (via `git show`),
so the before-surface of any wave is regenerated on demand and no
snapshot is stored.
"""
import hashlib
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from strip_comments import strip

KINDS = {"Definition", "Lemma", "Theorem", "Corollary", "Record",
         "Fixpoint", "Instance", "Axiom", "Notation"}
BODY_CUT = {"Definition", "Fixpoint", "Instance"}
CTX = {"Variable", "Variables", "Hypothesis", "Hypotheses", "Context"}
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def sentences(text):
    """Split comment-stripped, whitespace-normalized Rocq source into
    sentences: a `.` followed by a space or EOF ends one, unless it is
    the second dot of `..` or sits inside a string literal."""
    out, cur, in_str = [], [], False
    n = len(text)
    for i, c in enumerate(text):
        cur.append(c)
        if c == '"':
            in_str = not in_str
        elif c == "." and not in_str:
            nxt = text[i + 1] if i + 1 < n else " "
            prev = text[i - 1] if i else " "
            if nxt == " " and prev != ".":
                out.append("".join(cur).strip())
                cur = []
    tail = "".join(cur).strip()
    if tail:
        out.append(tail)
    return out


def cut_body(s):
    """Truncate before the first top-level `:=` (outside all brackets
    and strings): the type is surface, the body is not."""
    depth, in_str = 0, False
    for i in range(len(s) - 1):
        c = s[i]
        if in_str:
            in_str = c != '"'
            continue
        if c == '"':
            in_str = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and s[i + 1] == "=" and depth == 0:
            return s[:i].rstrip()
    return s


def parse_file(fname, text, exported, local_out):
    stack = []  # [(section_name, [ctx sentences])]
    for s in sentences(strip(text)):
        while s.startswith("#["):
            j = s.find("]")
            if j < 0:
                break
            s = s[j + 1:].lstrip()
        toks = s.split(" ", 2)
        if not toks or not toks[0]:
            continue
        head = toks[0]
        if head in ("Section", "Module"):
            if len(toks) > 1:
                stack.append((toks[1].rstrip("."), []))
            continue
        if head in ("End", "End."):
            if stack:
                stack.pop()
            continue
        is_local = False
        if head in ("Local", "Global"):
            is_local = head == "Local"
            s = s[len(head):].lstrip()
            toks = s.split(" ", 2)
            head = toks[0] if toks and toks[0] else ""
        if head in CTX:
            if stack:
                stack[-1][1].append(s)
            continue
        if head not in KINDS:
            continue
        rest = s[len(head):].lstrip()
        if head == "Notation":
            m = re.match(r'"((?:[^"\\]|\\.)*)"', rest)
            name = m.group(1) if m else rest.split(" ", 1)[0]
        else:
            m = NAME_RE.match(rest)
            if not m:
                continue
            name = m.group(0)
        stmt = cut_body(s) if head in BODY_CUT else s
        secpath = ".".join(n for n, _ in stack)
        ctx = " | ".join(c for _, cl in stack for c in cl)
        ctxhash = hashlib.sha1(ctx.encode()).hexdigest()[:12]
        line = f"{fname}|{secpath}|{head}|{name}|{ctxhash}|{stmt}"
        (local_out if is_local else exported).append(line)


def read_source(fname, rev):
    if rev:
        r = subprocess.run(["git", "show", f"{rev}:{fname}"],
                           capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None
    p = Path(fname)
    return p.read_text(encoding="utf-8") if p.exists() else None


def main():
    rev = None
    want_local = False
    args = sys.argv[1:]
    while args:
        a = args.pop(0)
        if a == "--rev":
            rev = args.pop(0)
        elif a == "--local":
            want_local = True
        else:
            sys.exit(f"unknown arg {a}")
    cp = read_source("_CoqProject", rev)
    if cp is None:
        sys.exit("cannot read _CoqProject")
    files = [l.strip() for l in cp.splitlines()
             if l.strip().endswith(".v") and not l.strip().startswith("-")]
    exported, local_out = [], []
    for f in files:
        src = read_source(f, rev)
        if src is None:
            print(f"MISSING|{f}", file=sys.stderr)
            continue
        parse_file(f, src, exported, local_out)
    for line in sorted(local_out if want_local else exported):
        print(line)


if __name__ == "__main__":
    main()
