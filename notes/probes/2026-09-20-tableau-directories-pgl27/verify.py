#!/usr/bin/env python3
"""Check that the six staged phase files plus the reduced proximity file are
pure moves of instances/pgl27/pgl27_rows.v and
instances/pgl27/pgl27_proximity.v.

Checks, in order:

  1. name sets.  Every declaration of the two production files appears in
     exactly one staged file, and the staged files declare nothing else
     besides the eight the plan adds by name.
  2. token identity.  For each moved declaration, the comment-stripped token
     stream of the staged text equals production's, statement and proof.
  3. docstring word identity.  The (** ... *) block attached to a moved
     declaration has the same word sequence in both, except for the one
     intended difference listed and printed below.
  4. the cut.  The five declarations that stay are in the reduced proximity
     file and in no phase file.
  5. line length, box column, banned vocabulary, and the innermost scope.
  6. recorded failures.  Each Fail is compiled un-Failed in the preamble of
     the file it sits in, on both sides, and the two error messages are
     compared.  A Fail whose subject no longer resolves would otherwise pass
     silently.

Usage: python3 verify.py
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PROD_ROWS = os.path.join(ROOT, "instances", "pgl27", "pgl27_rows.v")
PROD_PROX = os.path.join(ROOT, "instances", "pgl27", "pgl27_proximity.v")
STAGED_INST = os.path.join(HERE, "staged", "instances", "pgl27")
STAGED_DIR = os.path.join(STAGED_INST, "tableau")
PHASES = ["algebraic", "executable", "observed", "sampled",
          "analysis_bridged", "checks"]
STAGED_PHASE = [os.path.join(STAGED_DIR, "pgl27_tableau_%s.v" % p)
                for p in PHASES]
STAGED_PROX = os.path.join(STAGED_INST, "pgl27_proximity.v")
STAGED = STAGED_PHASE + [STAGED_PROX]

LOCK = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
        "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")
SCRATCH = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
           "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad")
STAGED_R = "staged/instances/pgl27"

NEW_NAMES = {"pgl27_algebraic_start",
             "pgl27_dealt_executable",
             "pgl27_dealt_executable_paramsE",
             "pgl27_dealt_executableE",
             "pgl27_exact_sampled",
             "pgl27_prior_exact_sampled",
             "pgl27_row_exact_sampledE",
             "pgl27_row_word_sampledE",
             "pgl27_row_prior_exact_sampledE"}

# The declarations that are distance mathematics and stay in
# instances/pgl27/pgl27_proximity.v.
STAYING = {("Lemma", "pgl27_static_obsE"),
           ("Lemma", "pgl27_static_obs_funE"),
           ("Definition", "pgl27_word_secret"),
           ("Lemma", "pgl27_word_proximity_close"),
           ("Fact", "pgl27_pow2_40_ge1"),
           ("Fact", "pgl27_pow2_40_gt0"),
           ("Lemma", "pgl27_word_uniform_ideal_close_false")}

# The one intended docstring difference.  The sentence cited the file the
# lemma is moving out of; after the move that lemma and the row it is about
# are in one file, so the citation would point at the reader's own file.
INTENDED_DOCSTRING_DIFF = {
    "pgl27_word_proximity_cert": (
        "'and the distance above' becomes 'and the distance "
        "pgl27_word_proximity_close of pgl27_proximity.v': the distance is "
        "no longer above the certificate but in the file this one requires"),
    "pgl27_row_word_proximity_rowE": (
        "'as pgl27_row_word_rowE of pgl27_rows.v says' becomes 'as "
        "pgl27_row_word_rowE says': the retired file name is gone and the "
        "lemma now sits in the same file as the one it cites"),
    "pgl27_word_proximity_cert_uniform_ideal": (
        "'pgl27_word_uniform_ideal_close_false above' becomes "
        "'pgl27_word_uniform_ideal_close_false of pgl27_proximity.v': the "
        "refutation stays in the reduced file and this recorded rejection "
        "moves to the checks file"),
}

# The one intended token difference.  verify.py slices a declaration by the
# lines up to the next declaration, so production's slice for this recorded
# rejection absorbs the three lines that open the section around
# pgl27_word_uniform_ideal_close_false.  Those three lines stay with that
# lemma in the reduced proximity file; the rejection itself is unchanged.
INTENDED_TOKEN_DIFF = {}

BANNED = [r"\bapex\b", r"\bgat(e|es|ed|ing)\b", r"\bposit(|s|ed|ing)\b",
          r"\bL1\b", r"\bindisting\.", r"\bindist\b", r"\bIND\b"]

FAILED = []


def fail(msg):
    FAILED.append(msg)
    print("FAIL " + msg)


def strip_comments(text):
    """Remove (* ... *) comments, nesting-aware."""
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


SCAFFOLD_RE = re.compile(
    r"^(Section|End|Variable|Variables|Let|Hypothesis|Context)\b")


def drop_scaffold(body):
    """A declaration's slice runs to the next declaration, so it absorbs any
    section scaffolding written between the two.  Those lines are compared
    separately, by scaffolding(), and left out of the token stream."""
    return "\n".join(l for l in body.splitlines()
                     if not SCAFFOLD_RE.match(l))


def scaffolding(path):
    return [l.rstrip() for l in open(path).read().splitlines()
            if SCAFFOLD_RE.match(l)]


def toks(s):
    return re.findall(r"[A-Za-z0-9_'\.]+|[^\sA-Za-z0-9_'\.]", s)


def docstrings(path):
    """Map declaration name -> the words of the (** ... *) block above it."""
    raw = open(path).read()
    res = {}
    # The block must hold no comment close of its own, so that a docstring
    # over a Local Notation is not swallowed into the next declaration's.
    # The pilot's regex crossed them; S5 has no Local Notation and PGL(2,7)
    # has two.
    for m in re.finditer(r"\(\*\*(?!\*)((?:(?!\*\)).)*?)\*\)\s*\n"
                         r"((?:Fail\s+)?(?:Definition|Lemma|Theorem|Corollary|"
                         r"Fact|Remark|Example)\s+([A-Za-z0-9_']+))",
                         raw, re.S):
        res[m.group(3)] = m.group(1).split()
    return res


def main():
    prod = {}
    origin = {}
    for path in (PROD_ROWS, PROD_PROX):
        for kind, name, body in items(strip_comments(open(path).read())):
            key = (kind, name)
            if key in prod:
                fail("duplicate in production: %s %s" % key)
            prod[key] = body
            origin[key] = os.path.basename(path)
    print("production items: %d (%s + %s)"
          % (len(prod),
             len([k for k in origin if origin[k] == "pgl27_rows.v"]),
             len([k for k in origin
                  if origin[k] == "pgl27_proximity.v"])))

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
    print("moved or stayed %d, new %d, lost %d"
          % (len(set(prod) & set(staged)), len(extra), len(lost)))

    # 2. token identity
    bad = 0
    intended = 0
    for k in sorted(set(prod) & set(staged)):
        if toks(drop_scaffold(prod[k])) != toks(drop_scaffold(staged[k])):
            if k[1] in INTENDED_TOKEN_DIFF:
                intended += 1
                print("token stream differs BY DESIGN: %s %s\n      %s"
                      % (k[0], k[1], INTENDED_TOKEN_DIFF[k[1]]))
                continue
            bad += 1
            fail("token stream differs: %s %s (in %s)" % (k[0], k[1], where[k]))
            a = toks(drop_scaffold(prod[k]))
            b = toks(drop_scaffold(staged[k]))
            for i, (x, y) in enumerate(zip(a, b)):
                if x != y:
                    print("      first at token %d: prod %r staged %r"
                          % (i, x, y))
                    break
            else:
                print("      lengths %d vs %d" % (len(a), len(b)))
    n_shared = len(set(prod) & set(staged))
    print("token identity: %d of %d declarations identical, "
          "%d intended difference(s)" % (n_shared - bad - intended, n_shared,
                                         intended))

    # 3. docstring word identity
    pd = {}
    for path in (PROD_ROWS, PROD_PROX):
        pd.update(docstrings(path))
    sd = {}
    for path in STAGED:
        sd.update(docstrings(path))
    nd = 0
    for name, words in sorted(pd.items()):
        if name not in sd:
            fail("docstring lost for %s" % name)
        elif sd[name] != words:
            if name in INTENDED_DOCSTRING_DIFF:
                print("docstring differs BY DESIGN: %s\n      %s"
                      % (name, INTENDED_DOCSTRING_DIFF[name]))
                a, b = words, sd[name]
                for i, (x, y) in enumerate(zip(a, b)):
                    if x != y:
                        print("      first at word %d: prod %r staged %r"
                              % (i, x, y))
                        break
            else:
                fail("docstring words differ for %s" % name)
        else:
            nd += 1
    print("docstrings: %d of %d word-identical, %d intended difference(s)"
          % (nd, len(pd), len(INTENDED_DOCSTRING_DIFF)))

    # 4. the cut
    for k in sorted(STAYING):
        if k not in staged:
            fail("a staying declaration is nowhere: %s %s" % k)
        elif where[k] != "pgl27_proximity.v":
            fail("a staying declaration moved into a phase file: %s %s in %s"
                 % (k[0], k[1], where[k]))
    in_prox = {k for k in staged if where[k] == "pgl27_proximity.v"}
    if in_prox != STAYING:
        fail("the reduced proximity file holds %s, expected %s"
             % (sorted(in_prox), sorted(STAYING)))
    else:
        print("the cut: %d declarations stay in pgl27_proximity.v, "
              "%d move" % (len(STAYING), len(prod) - len(STAYING)))

    # 4b. section scaffolding
    a = scaffolding(PROD_PROX)
    b = scaffolding(STAGED_PROX)
    if a != b:
        fail("the section scaffolding of the reduced proximity file "
             "differs: %s against %s" % (a, b))
    else:
        print("section scaffolding of pgl27_proximity.v: %d line(s), "
              "unchanged" % len(a))
    for path in STAGED_PHASE:
        extra = scaffolding(path)
        if extra:
            fail("%s holds section scaffolding: %s"
                 % (os.path.basename(path), extra))

    # 5. scans
    for path in STAGED:
        base = os.path.basename(path)
        for i, line in enumerate(open(path, "rb").read().split(b"\n"), 1):
            if len(line) > 80:
                fail("%s:%d line is %d bytes" % (base, i, len(line)))
        for i, line in enumerate(open(path).read().splitlines(), 1):
            r = line.rstrip()
            # A box line: opens a comment with (* and closes it on the same
            # line.  A one-line (** ... *) docstring is not a box line.
            if r.startswith("(*") and not r.startswith("(**") \
               and r.endswith("*)"):
                if set(r[2:-2]) != {"*"} and r.endswith("**)"):
                    fail("%s:%d box line ends in a stray asterisk: %s"
                         % (base, i, r[-20:]))
                # PSL(2,11) audit F11: a content line whose text abuts *)
                # passes a width check and reads wrong.
                if set(r[2:-2]) != {"*"} and not r.endswith(" *)"):
                    fail("%s:%d box content line has no space before *): %s"
                         % (base, i, r[-24:]))
                if len(r) != 80:
                    fail("%s:%d box line is %d columns, not 80"
                         % (base, i, len(r)))
            for pat in BANNED:
                if re.search(pat, line, re.I):
                    fail("%s:%d banned vocabulary %s: %s"
                         % (base, i, pat, line.strip()))
    lasts = {}
    for path in STAGED_PHASE:
        opens = [l.strip() for l in open(path).read().splitlines()
                 if l.startswith("Local Open Scope")]
        assert opens, os.path.basename(path)
        lasts[os.path.basename(path)] = opens[-1]
    if len(set(lasts.values())) != 1:
        fail("the innermost Local Open Scope differs across the phase files: %s"
             % lasts)
    else:
        print("innermost scope, all six phase files: %s"
              % sorted(set(lasts.values()))[0])
    prod_rows_last = [l.strip() for l in open(PROD_ROWS).read().splitlines()
                      if l.startswith("Local Open Scope")][-1]
    prod_prox_last = [l.strip() for l in open(PROD_PROX).read().splitlines()
                      if l.startswith("Local Open Scope")][-1]
    print("innermost scope, production pgl27_rows.v: %s" % prod_rows_last)
    print("innermost scope, production pgl27_proximity.v: %s"
          % prod_prox_last)
    if prod_prox_last != sorted(set(lasts.values()))[0]:
        print("RE-SCOPED BY DESIGN: the declarations moved out of "
              "pgl27_proximity.v are read under the phase files' block. "
              "fidelity.v and baseline.v print the type of each of them "
              "under one scope block and the two outputs are diffed, so a "
              "numeral or a notation that resolved differently would print "
              "differently there.")
    if prod_rows_last != prod_prox_last:
        print("RE-SCOPED THE OTHER WAY BY DESIGN: pgl27_static_obsE and "
              "pgl27_static_obs_funE move from pgl27_rows.v into the reduced "
              "pgl27_proximity.v, so they are read under that file's block "
              "instead. fidelity.v and baseline.v print their types under "
              "one block and the two outputs are diffed.")
    prox_last = [l.strip() for l in open(STAGED_PROX).read().splitlines()
                 if l.startswith("Local Open Scope")][-1]
    if prox_last != prod_prox_last:
        fail("the reduced proximity file changed its innermost scope: %s"
             % prox_last)
    print("scans done")

    # 6. recorded failures
    check_fails()

    print()
    if FAILED:
        print("%d CHECK(S) FAILED" % len(FAILED))
        return 1
    print("ALL CHECKS PASSED")
    return 0


# Each recorded Fail, written without the Fail, with the production file it
# sits in and the staged file it sits in.  The bodies are read out of the
# production sources, so this table cannot drift from them.
CHECKS = os.path.join(STAGED_DIR, "pgl27_tableau_checks.v")


def _unfailed():
    res = {}
    for path, mod in ((PROD_ROWS, "pgl27_rows"),
                      (PROD_PROX, "pgl27_proximity")):
        for kind, name, body in items(strip_comments(open(path).read())):
            if not kind.startswith("Fail"):
                continue
            body = body.split(chr(10) + "Section ")[0].rstrip()
            assert body.startswith("Fail "), name
            res[name] = (path, mod, CHECKS, body[5:].rstrip() + chr(10))
    return res


UNFAILED = _unfailed()


def preamble(path):
    """The import and settings block of a file: from its first From line up to
    the banner that opens its first section."""
    lines = open(path).read().splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("From "))
    j = next(k for k in range(i, len(lines)) if lines[k].startswith("(****"))
    return "\n".join(lines[i:j]) + "\n\n"


def read_flags(with_staged):
    flags = []
    for raw in open(os.path.join(HERE, "_CoqProject")):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-arg "):
            flags += [p for p in line.split() if p != "-arg"]
        elif line.startswith("-R ") or line.startswith("-Q "):
            parts = line.split()
            if not with_staged and parts[1] == STAGED_R:
                continue
            flags += parts
    return flags


def error_of(with_staged, head, body, tag):
    path = os.path.join(SCRATCH, "unfail_%s.v" % tag)
    with open(path, "w") as f:
        f.write(head + body)
    p = subprocess.run([LOCK, "900", "12000", "rocq", "compile"]
                       + read_flags(with_staged)
                       + ["-R", SCRATCH, "unfail_probe", path],
                       cwd=HERE, capture_output=True, text=True)
    txt = p.stdout + p.stderr
    m = re.search(r"^Error:.*", txt, re.S | re.M)
    return m.group(0).strip() if m else "<NO ERROR: the term was accepted>"


def check_fails():
    """Compile each recorded Fail un-Failed, in the context its own file
    gives it, on both sides, and compare the rejections."""
    for name in sorted(UNFAILED):
        prod_path, prod_mod, staged_path, body = UNFAILED[name]
        prod_head = (preamble(prod_path)
                     + "From pgg_smc Require Import %s.\n\n" % prod_mod)
        staged_head = preamble(staged_path)
        if staged_path == STAGED_PROX:
            staged_head += ("From pgg_smc Require Import "
                            "pgl27_word_proximity.\n\n")
        a = error_of(False, prod_head, body, name + "_prod")
        b = error_of(True, staged_head, body, name + "_staged")
        if a.startswith("<NO ERROR"):
            fail("Fail %s: production accepts the un-Failed term" % name)
        for side, msg in (("production", a), ("staged", b)):
            if "was not found in the current environment" in msg:
                fail("Fail %s: on the %s side the subject does not resolve, "
                     "so the recorded Fail passes for the wrong reason: %s"
                     % (name, side, msg.splitlines()[0]))
        if a != b:
            fail("Fail %s: error messages differ" % name)
            print("   prod   : " + a[:500].replace("\n", "\n            "))
            print("   staged : " + b[:500].replace("\n", "\n            "))
        else:
            print("Fail %s: same rejection: %s"
                  % (name, a.splitlines()[0][:110]))


if __name__ == "__main__":
    sys.exit(main())
