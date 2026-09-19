#!/usr/bin/env python3
"""Prove that landing 3's staged text is its source text plus the listed edits.

Four checks.

  (1) WHOLE-FILE TOKENS for the five files that already exist in production:
      instances/pgl27/pgl27_exec.v, instances/pgl27/pgl27_models.v,
      instances/pgl27/pgl27_analysis.v, manifest/pgg_analysis_manifest.v and
      manifest/pgg_analysis_client.v.  Comments removed, whitespace
      normalized, a unified diff of the token streams against production.
      Every hunk must be one of the listed additions.

  (2) PER-DECLARATION TOKENS.  Each landed declaration is looked up by name in
      the probe file that declares it and its token stream compared.  Two
      substitutions are applied to the staged stream before the comparison and
      printed: the R7 rename of pow2_40_ge1 and pow2_40_gt0, and nothing else.
      A declaration whose tokens differ is printed in full, and the three
      that are meant to differ are named in EXPECTED below and printed with
      their reason.

  (3) COMMENT WORDS of every landed declaration, staged against the probe's,
      as a unified word diff.

  (4) SCANS over the staged tree: retired names, lines over 80 bytes, the
      barred words, any abbreviation of "indistinguishability", and the word
      "ceiling".

The script only prints; it makes no judgement.  STATUS.md records which hunks
are expected.
"""

import difflib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PROBE = os.path.join(REPO, "notes/probes/2026-09-19-tableau-extensions")

WHOLE = [
    ("staged/instances/pgl27/pgl27_exec.v",
     os.path.join(REPO, "instances/pgl27/pgl27_exec.v")),
    ("staged/instances/pgl27/pgl27_models.v",
     os.path.join(REPO, "instances/pgl27/pgl27_models.v")),
    ("staged/instances/pgl27/pgl27_analysis.v",
     os.path.join(REPO, "instances/pgl27/pgl27_analysis.v")),
    ("staged/manifest/pgg_analysis_manifest.v",
     os.path.join(REPO, "manifest/pgg_analysis_manifest.v")),
    ("staged/manifest/pgg_analysis_client.v",
     os.path.join(REPO, "manifest/pgg_analysis_client.v")),
]

# staged file -> the probe files its landed declarations come from
NEW = [
    ("staged/instances/pgl27/pgl27_proximity.v",
     ["p5_pgl27_prior_ideal.v", "p5_pgl27_word_proximity.v",
      "p5_mutations.v"]),
]

# declarations that land inside a file production already has, and the probe
# file each comes from
ADDED = [
    ("staged/instances/pgl27/pgl27_exec.v",
     {"pgl27_prior_sample": "p5_pgl27_prior_ideal.v"}),
    ("staged/instances/pgl27/pgl27_models.v",
     {"pgl27_prior_exact_family": "p5_pgl27_prior_ideal.v"}),
]

# staged name -> the name the probe declares it under (R7).  The staged token
# stream has the staged name rewritten to the probe's before the comparison,
# so a declaration reported token-identical is identical modulo this name.
RENAMED = {"pgl27_pow2_40_ge1": "pow2_40_ge1",
           "pgl27_pow2_40_gt0": "pow2_40_gt0"}

# the declarations whose token stream is meant to differ from the probe's,
# and why.  Every other declaration must come out token-identical.
EXPECTED = {
    "var_dist_fdist1_uniform":
        "the four-branch first [...] replaced by the branch that fires",
    "pgl27_cross_model_proximity":
        "its subject respelled inline, pgl27_exact_sampled not being in the"
        " tree",
    "pgl27_row_prior_exact_rowE":
        "stated at the manifest row pgl27_row_prior_exact, which did not"
        " exist when the probe was written",
}

DECL = re.compile(
    r"^(?:Fail\s+)?(Lemma|Definition|Theorem|Fact|Corollary)\s+([A-Za-z_][\w']*)",
    re.M)

# Block boundaries: a declaration ends where the next declaration OR the next
# section-structure sentence begins, so that a Section header following the
# last lemma of a file is not counted as part of that lemma.
CUT = re.compile(
    r"^(?:Fail\s+)?(?:Lemma|Definition|Theorem|Fact|Corollary|Section|End"
    r"|Variables?|Hypothesis|Check|Arguments|Notation|Local|Print|Timeout)\b",
    re.M)

RETIRED = ["SpectralDecay", "SpectralCert", r"_indist\b",
           "RepricePayload", "idealproximity_ceiling"]
BARRED = [r"\bapex\b", r"\bgate[sd]?\b", r"\bgating\b",
          r"\bposit(s|ed|ing)?\b", r"\bL1\b", r"\bceiling\b"]
ABBREV = re.compile(r"indist(?!inguishab)", re.I)

LANDED = [
    "staged/instances/pgl27/pgl27_exec.v",
    "staged/instances/pgl27/pgl27_models.v",
    "staged/instances/pgl27/pgl27_analysis.v",
    "staged/manifest/pgg_analysis_manifest.v",
    "staged/manifest/pgg_analysis_client.v",
    "staged/instances/pgl27/pgl27_proximity.v",
]


def split_comments(text):
    """Return (code, comments) with Rocq's nested (* *) handled."""
    code, comments = [], []
    depth, i, n = 0, 0, len(text)
    buf = []
    while i < n:
        if text.startswith("(*", i):
            if depth == 0:
                buf = []
            depth += 1
            i += 2
            continue
        if depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                comments.append("".join(buf))
            continue
        if depth:
            buf.append(text[i])
        else:
            code.append(text[i])
        i += 1
    return "".join(code), comments


def tokens(code):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|\d+|\S", code)


def report(name, a, b, kind):
    d = list(difflib.unified_diff(a, b, "source", "staged", n=1, lineterm=""))
    hunks = sum(1 for l in d if l.startswith("@@"))
    changed = sum(1 for l in d
                  if l[:1] in "+-" and not l.startswith(("+++", "---")))
    print("--- %s : %s : %d hunk(s), %d changed token(s)/word(s)"
          % (name, kind, hunks, changed))
    for l in d:
        print("   " + l)
    return hunks


def blocks(path):
    """name -> (code tokens, preceding comment words) for every declaration."""
    raw = open(path).read()
    code, _ = split_comments(raw)
    out = {}
    cuts = [m.start() for m in CUT.finditer(code)] + [len(code)]
    for m in DECL.finditer(code):
        end = next(c for c in cuts if c > m.start())
        out[m.group(2)] = tokens(code[m.start():end])
    docs = {}
    for m in DECL.finditer(raw):
        head = raw[:m.start()]
        j = head.rfind("(**")
        k = head.rfind("*)")
        docs[m.group(2)] = (head[j + 3:k].split()
                            if j != -1 and k > j else [])
    return out, docs


def compare(nm, pnm, st, sd, pt, pd, where):
    # the R7 rename is undone everywhere, in a declaration's own name and in
    # every reference to the two renamed facts inside another proof.  The
    # tokenizer keeps a trailing sentence dot inside the identifier token, so
    # the lookup strips it and puts it back.
    def ren(t):
        base = t.rstrip(".")
        return RENAMED.get(base, base) + t[len(base):]
    stoks = [ren(t) for t in st[nm]]
    ok = pt[pnm] == stoks
    if not ok:
        if nm in EXPECTED:
            print("   EXPECTED DIFFERENCE in %s: %s" % (nm, EXPECTED[nm]))
        report("%s (from %s)" % (nm, where), pt[pnm], stoks, "code tokens")
    if pd[pnm] != sd[nm]:
        report("%s (from %s)" % (nm, where), pd[pnm], sd[nm], "comment words")
    return ok


def main():
    print("=" * 78)
    print("(1) WHOLE-FILE TOKEN DIFFS AGAINST PRODUCTION")
    print("=" * 78)
    for rel, src in WHOLE:
        s_code, _ = split_comments(open(src).read())
        t_code, _ = split_comments(open(os.path.join(HERE, rel)).read())
        print("=== %s" % rel)
        report(rel, tokens(s_code), tokens(t_code), "code tokens")
        print()

    print("=" * 78)
    print("(2) and (3) PER-DECLARATION TOKENS AND COMMENT WORDS")
    print("=" * 78)
    probe = {}
    wanted = set(sum([f for _, f in NEW], []))
    for _, m in ADDED:
        wanted |= set(m.values())
    for fn in sorted(wanted):
        probe[fn] = blocks(os.path.join(PROBE, fn))

    for rel, names in ADDED:
        st, sd = blocks(os.path.join(HERE, rel))
        print("=== %s (declarations added to a production file)" % rel)
        idn = 0
        for nm, fn in names.items():
            pt, pd = probe[fn]
            idn += compare(nm, RENAMED.get(nm, nm), st, sd, pt, pd, fn)
        print("   %d of %d declarations token-identical to the probe's"
              % (idn, len(names)))
        print()

    for rel, srcs in NEW:
        st, sd = blocks(os.path.join(HERE, rel))
        print("=== %s" % rel)
        idn = 0
        for nm in sorted(st, key=list(st).index):
            pnm = RENAMED.get(nm, nm)
            if pnm != nm:
                print("   RENAMED: staged %s is the probe's %s" % (nm, pnm))
            where = [f for f in srcs if pnm in probe[f][0]]
            if not where:
                print("   NOT IN ANY PROBE FILE: %s" % nm)
                continue
            f = where[0]
            pt, pd = probe[f]
            idn += compare(nm, pnm, st, sd, pt, pd, f)
        print("   %d of %d declarations token-identical to the probe's"
              % (idn, len(st)))
        print()

    print("=" * 78)
    print("(4) SCANS OVER staged/")
    print("=" * 78)
    files = []
    for root, _, names in os.walk(os.path.join(HERE, "staged")):
        files += [os.path.join(root, n) for n in names if n.endswith(".v")]
    files.append(os.path.join(HERE, "landing_fidelity.v"))
    for pat in RETIRED + BARRED:
        hits = []
        for f in sorted(files):
            rel = os.path.relpath(f, HERE)
            for i, l in enumerate(open(f).read().split("\n"), 1):
                if re.search(pat, l):
                    hits.append("%s%s:%d: %s"
                                % ("" if rel in LANDED else "[chain] ",
                                   rel, i, l.strip()[:66]))
        print("%-32s %d hit(s)" % (pat, len(hits)))
        for h in hits:
            print("    " + h)
    over = []
    for f in sorted(files):
        rel = os.path.relpath(f, HERE)
        for i, l in enumerate(open(f, "rb").read().split(b"\n"), 1):
            if len(l) > 80:
                over.append("%s%s:%d: %d bytes"
                            % ("" if rel in LANDED else "[chain] ",
                               rel, i, len(l)))
    print("%-32s %d hit(s)" % ("lines over 80 bytes", len(over)))
    for h in over:
        print("    " + h)
    ab = []
    for f in sorted(files):
        rel = os.path.relpath(f, HERE)
        for i, l in enumerate(open(f).read().split("\n"), 1):
            if ABBREV.search(l):
                ab.append("%s%s:%d: %s"
                          % ("" if rel in LANDED else "[chain] ",
                             rel, i, l.strip()[:66]))
    print("%-32s %d hit(s)" % ("abbreviated indistinguishab.", len(ab)))
    for h in ab:
        print("    " + h)
    return 0


if __name__ == "__main__":
    sys.exit(main())
