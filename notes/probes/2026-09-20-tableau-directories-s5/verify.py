#!/usr/bin/env python3
"""Check that the six staged phase files are pure moves of s5_rows.v.

Checks, in order:

  1. name sets.  Every declaration of instances/s5/s5_rows.v appears in
     exactly one staged file, and the staged files declare nothing else
     besides the seven the plan adds by name.
  2. token identity.  For each moved declaration, the comment-stripped token
     stream of the staged text equals production's, statement and proof.
  3. docstring word identity.  The (** ... *) block attached to a moved
     declaration has the same word sequence in both.
  4. recorded failures.  Each Fail is compiled un-Failed against production
     and against the staged text, and the two error messages are compared.
     A Fail whose subject no longer resolves would otherwise pass silently.
  5. line length, box column, banned vocabulary.

Usage: python3 verify.py
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PROD = os.path.join(ROOT, "instances", "s5", "s5_rows.v")
STAGED_DIR = os.path.join(HERE, "staged", "instances", "s5", "tableau")
PHASES = ["algebraic", "executable", "observed", "sampled",
          "analysis_bridged", "checks"]
STAGED = [os.path.join(STAGED_DIR, "s5_tableau_%s.v" % p) for p in PHASES]

LOCK = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
        "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")
SCRATCH = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
           "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad")

NEW_NAMES = {"s5_algebraic", "s5_dealt_executable", "s5_supplied_executable",
             "s5_dealt_splitE", "s5_supplied_splitE", "s5_rand_sampled",
             "s5_row_rand_splitE"}

BANNED = [r"\bapex\b", r"\bgat(e|es|ed|ing)\b", r"\bposit(|s|ed|ing)\b",
          r"\bL1\b", r"\bindisting\.", r"\bindist\b", r"\bIND\b"]

FAILED = []


def fail(msg):
    FAILED.append(msg)
    print("FAIL " + msg)


def strip_comments(text):
    """Remove (* ... *) comments, nesting-aware, keeping string literals."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            out.append(" ")
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


DECL_RE = re.compile(
    r"^(Fail\s+|Local\s+|Global\s+)*"
    r"(Definition|Lemma|Theorem|Corollary|Fact|Remark|Example|Check)\b")


def items(text):
    """Split comment-stripped source into (kind, name, body) items."""
    lines = text.splitlines()
    starts = [i for i, l in enumerate(lines) if DECL_RE.match(l)]
    res = []
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        body = "\n".join(lines[i:j]).strip()
        head = lines[i]
        m = re.match(r"^(?:Fail\s+)?(?:Local\s+|Global\s+)?"
                     r"(Definition|Lemma|Theorem|Corollary|Fact|Remark|"
                     r"Example|Check)\s+([A-Za-z0-9_']+)", head)
        if m:
            kind, name = m.group(1), m.group(2)
        else:
            kind, name = "Check", "<anonymous Check>"
        if head.startswith("Fail"):
            kind = "Fail " + kind
        res.append((kind, name, body))
    return res


def toks(s):
    return re.findall(r"[A-Za-z0-9_'\.]+|[^\sA-Za-z0-9_'\.]", s)


def docstrings(path):
    """Map declaration name -> the words of the (** ... *) block above it."""
    raw = open(path).read()
    res = {}
    for m in re.finditer(r"\(\*\*(?!\*)(.*?)\*\)\s*\n"
                         r"((?:Fail\s+)?(?:Definition|Lemma|Theorem|Corollary|"
                         r"Fact|Remark|Example)\s+([A-Za-z0-9_']+))",
                         raw, re.S):
        res[m.group(3)] = m.group(1).split()
    return res


def main():
    prod_items = items(strip_comments(open(PROD).read()))
    prod = {}
    for kind, name, body in prod_items:
        key = (kind, name)
        if key in prod:
            fail("duplicate in production: %s %s" % key)
        prod[key] = body
    print("production items: %d" % len(prod_items))

    staged = {}
    where = {}
    for path in STAGED:
        for kind, name, body in items(strip_comments(open(path).read())):
            key = (kind, name)
            if key in staged:
                fail("declared twice in the staged files: %s %s (%s and %s)"
                     % (kind, name, where[key], os.path.basename(path)))
            staged[key] = body
            where[key] = os.path.basename(path)

    # 1. name sets
    lost = set(prod) - set(staged)
    extra = set(staged) - set(prod)
    for k in sorted(lost):
        fail("lost: %s %s" % k)
    for k in sorted(extra):
        if k[1] not in NEW_NAMES:
            fail("unexpected new declaration: %s %s in %s"
                 % (k[0], k[1], where[k]))
    print("moved %d, new %d, lost %d"
          % (len(set(prod) & set(staged)), len(extra), len(lost)))

    # 2. token identity
    bad = 0
    for k in sorted(set(prod) & set(staged)):
        if toks(prod[k]) != toks(staged[k]):
            bad += 1
            fail("token stream differs: %s %s (in %s)" % (k[0], k[1], where[k]))
            a, b = toks(prod[k]), toks(staged[k])
            for i, (x, y) in enumerate(zip(a, b)):
                if x != y:
                    print("      first at token %d: prod %r staged %r"
                          % (i, x, y))
                    break
            else:
                print("      lengths %d vs %d" % (len(a), len(b)))
    print("token identity: %d of %d moved declarations identical"
          % (len(set(prod) & set(staged)) - bad, len(set(prod) & set(staged))))

    # 3. docstring word identity
    pd = docstrings(PROD)
    sd = {}
    for path in STAGED:
        sd.update(docstrings(path))
    nd = 0
    for name, words in sorted(pd.items()):
        if name not in sd:
            fail("docstring lost for %s" % name)
        elif sd[name] != words:
            fail("docstring words differ for %s" % name)
        else:
            nd += 1
    print("docstrings: %d of %d word-identical" % (nd, len(pd)))

    # 5. scans
    for path in STAGED:
        base = os.path.basename(path)
        for i, line in enumerate(open(path, "rb").read().split(b"\n"), 1):
            if len(line) > 80:
                fail("%s:%d line is %d bytes" % (base, i, len(line)))
        for i, line in enumerate(open(path).read().splitlines(), 1):
            if line.startswith("(*") and line.rstrip().endswith("*)"):
                r = line.rstrip()
                if set(r[2:-2]) != {"*"} and r.endswith("**)"):
                    fail("%s:%d box line ends in a stray asterisk: %s"
                         % (base, i, r[-20:]))
                if len(r) != 80:
                    fail("%s:%d box line is %d columns, not 80"
                         % (base, i, len(line.rstrip())))
            for pat in BANNED:
                if re.search(pat, line, re.I):
                    fail("%s:%d banned vocabulary %s: %s"
                         % (base, i, pat, line.strip()))
        if "indistinguishability" in open(path).read().lower():
            pass
    print("scans done")

    # 4. recorded failures
    check_fails()

    print()
    if FAILED:
        print("%d CHECK(S) FAILED" % len(FAILED))
        return 1
    print("ALL CHECKS PASSED")
    return 0


UNFAILED = {
    "s5_dealt_rand":
        "Definition s5_dealt_rand : Tableau Sampled :=\n"
        "  s5_dealt sample s5_rand_family.\n",
    "s5_F_k5":
        "Definition s5_F_k5 : s5_F = MkFunctionality id 5 := erefl.\n",
}

def preamble(path):
    """The import and settings block of a file: from its first From line up to
    the banner that opens its first section."""
    lines = open(path).read().splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("From "))
    j = next(k for k in range(i, len(lines)) if lines[k].startswith("(****"))
    return "\n".join(lines[i:j]) + "\n\n"


def read_flags():
    flags = []
    for raw in open(os.path.join(HERE, "_CoqProject")):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-arg "):
            flags += [p for p in line.split() if p != "-arg"]
        elif line.startswith("-R ") or line.startswith("-Q "):
            flags += line.split()
    return flags


def error_of(flags, head, body, tag):
    path = os.path.join(SCRATCH, "unfail_%s.v" % tag)
    with open(path, "w") as f:
        f.write(head + body)
    p = subprocess.run([LOCK, "600", "8000", "rocq", "compile"] + flags
                       + ["-R", SCRATCH, "unfail_probe", path],
                       cwd=HERE, capture_output=True, text=True)
    txt = p.stdout + p.stderr
    m = re.search(r"^Error:.*", txt, re.S | re.M)
    return m.group(0).strip() if m else "<NO ERROR: the term was accepted>"


def check_fails():
    """Compile each recorded Fail un-Failed, in the context its own file
    gives it, on both sides, and compare the rejections."""
    flags = read_flags()
    # Production: s5_rows.v's own preamble, plus a Require of the module the
    # Fail sits in.  Staged: the checks file's own preamble, which already
    # requires the phase chain.
    prod_head = preamble(PROD) + "From pgg_smc Require Import s5_rows.\n\n"
    staged_head = preamble(STAGED[-1])
    for name, body in sorted(UNFAILED.items()):
        a = error_of(flags, prod_head, body, name + "_prod")
        b = error_of(flags, staged_head, body, name + "_staged")
        if a.startswith("<NO ERROR"):
            fail("Fail %s: production accepts the un-Failed term" % name)
        for side, msg in (("production", a), ("staged", b)):
            if "was not found in the current environment" in msg:
                fail("Fail %s: on the %s side the subject does not resolve, "
                     "so the recorded Fail passes for the wrong reason: %s"
                     % (name, side, msg.splitlines()[0]))
        if a != b:
            fail("Fail %s: error messages differ" % name)
            print("   prod   : " + a[:400].replace("\n", "\n            "))
            print("   staged : " + b[:400].replace("\n", "\n            "))
        else:
            print("Fail %s: same rejection: %s"
                  % (name, a.splitlines()[0][:110]))


if __name__ == "__main__":
    sys.exit(main())
