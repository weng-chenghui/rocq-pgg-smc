#!/usr/bin/env python3
"""Checks that the PublishedRow -> Published rename (layers A-E) changed
identifiers only.

For every tracked .v file outside notes/: the committed text at BASE with the
map of rename_map.tsv applied to every identifier token must equal the working
copy, (1) as a stream of code tokens with comments removed, and (2) as a stream
of comment words with the box delimiters and the layout removed.  Then scans
the working copy for an old name left behind, for a line over 80 bytes that
BASE did not have, for a box line that does not end in a space before its
closing delimiter, and for the project's barred words in changed lines.

usage: check_rename.py [BASE]      (run from anywhere; BASE defaults to HEAD)
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = subprocess.check_output(
    ["git", "-C", HERE, "rev-parse", "--show-toplevel"]).decode().strip()
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
BARRED = re.compile(
    r"\b(apex|gate|gates|gated|gating|posit|posits|posited|positing)\b"
    r"|\bL[0-9]", re.I)

MAP = {}
for line in open(os.path.join(HERE, "rename_map.tsv")):
    old, new = line.rstrip("\n").split("\t")[:2]
    MAP[old] = new
# Tokens that occur in comments only and name the renamed lemma family.
COMMENT_ONLY = {"_rowE": "_pathE", "rowE": "pathE",
                "AnalysisPathRows": "AnalysisPaths"}


def split(text):
    """(code, comments) with the other part blanked."""
    code, com, depth, i = [], [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
            com.append(" ")
            if i < len(text) and text[i] == "*" and not text.startswith("*)", i):
                i += 1
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            code.append(" ")
            com.append(" ")
        else:
            (com if depth else code).append(text[i])
            (code if depth else com).append(
                "\n" if text[i] == "\n" else " ")
            i += 1
    return "".join(code), "".join(com)


def ren(text, table):
    return IDENT.sub(lambda m: table.get(m.group(0), m.group(0)), text)


def first_diff(a, b, label):
    for k, (x, y) in enumerate(zip(a, b)):
        if x != y:
            print(f"   {label}: first difference at token {k}")
            print("   expected:", " ".join(a[max(0, k - 6):k + 8]))
            print("   found   :", " ".join(b[max(0, k - 6):k + 8]))
            return
    print(f"   {label}: lengths differ, {len(a)} against {len(b)}")


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else "HEAD"
    files = subprocess.check_output(
        ["git", "-C", REPO, "ls-tree", "-r", "--name-only", base]
    ).decode().split("\n")
    files = [f for f in files if f.endswith(".v") and not f.startswith("notes/")]
    both = dict(MAP)
    both.update(COMMENT_ONLY)
    ok, changed = True, 0
    for f in files:
        old = subprocess.run(["git", "-C", REPO, "show", f"{base}:{f}"],
                             capture_output=True, text=True, check=True).stdout
        path = os.path.join(REPO, f)
        if not os.path.exists(path):
            print(f"MISSING {f}")
            ok = False
            continue
        new = open(path, encoding="utf-8").read()
        if old == new:
            leftovers = [w for w in IDENT.findall(new) if w in MAP]
            if leftovers:
                ok = False
                print(f"UNTOUCHED BUT HOLDS OLD NAMES {f}: {sorted(set(leftovers))}")
            continue
        changed += 1
        oc, om = split(old)
        nc, nm = split(new)
        a, b = ren(oc, MAP).split(), nc.split()
        c, d = ren(om, both).split(), nm.split()
        good = a == b and c == d
        ok &= good
        print(f"{'SAME' if good else 'DIFF'}  {f}  (code {len(a)}/{len(b)}, "
              f"comment words {len(c)}/{len(d)})")
        if a != b:
            first_diff(a, b, "code")
        if c != d:
            first_diff(c, d, "comments")
        old_long = {ren(l, both) for l in old.splitlines()
                    if len(l.encode()) > 80}
        old_lines = set(old.splitlines())
        for n, line in enumerate(new.splitlines(), 1):
            if len(line.encode()) > 80 and line not in old_long:
                ok = False
                print(f"   LONG {f}:{n} ({len(line.encode())} bytes)")
            if line.startswith("(*") and line.endswith("*)") \
                    and not set(line) <= set("(*)") \
                    and not line.startswith("(**") \
                    and len(line.encode()) >= 78 and not line.endswith(" *)"):
                ok = False
                print(f"   BOX {f}:{n}: no space before the closing delimiter")
            if line not in old_lines and BARRED.search(line):
                ok = False
                print(f"   BARRED {f}:{n}: {line.strip()}")
            for w in IDENT.findall(line):
                if w in both:
                    ok = False
                    print(f"   LEFTOVER {f}:{n}: {w}")
    print(f"{changed} files changed")
    print("ALL OK" if ok else "PROBLEMS")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
