#!/usr/bin/env python3
"""Prove that landing 2's staged text is its source text plus the listed edits.

Four checks.

  (1) WHOLE-FILE TOKENS for the two files that already exist in production:
      lib/var_dist_supp.v and instances/kim2025/five_card_mixing.v.  Comments
      removed, whitespace normalized, a unified diff of the token streams
      against production.  Every hunk must be one of the listed additions or
      removals.

  (2) PER-DECLARATION TOKENS for the two new files.  Each landed declaration
      is looked up by name in the probe file that declares it and its token
      stream compared.  A declaration whose tokens differ is printed in full.

  (3) COMMENT WORDS of every landed declaration, staged against the probe's,
      as a unified word diff.

  (4) SCANS over the staged tree: retired names, lines over 80 bytes, the
      barred words, and any abbreviation of "indistinguishability".

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
    ("staged/lib/var_dist_supp.v", os.path.join(REPO, "lib/var_dist_supp.v")),
    ("staged/instances/kim2025/five_card_mixing.v",
     os.path.join(REPO, "instances/kim2025/five_card_mixing.v")),
]

# new staged file -> the probe files its declarations come from
NEW = [
    ("staged/manifest/pgg_tableau_arm_relations.v",
     ["p7_mutations.v", "p8_spectral_relation.v"]),
    ("staged/instances/kim2025/five_card_proximity.v",
     ["p4_kim_biased_proximity.v", "p7_mutations.v",
      "p8_spectral_relation.v", "p9_actual_marginals.v"]),
]

# the five lemmas promoted from p1 into lib/var_dist_supp.v, and the one
# moved out of it into five_card_mixing.v
PROMOTED = {
    "var_dist_fdistmap_pair": "p1_joint_law_distance.v",
    "var_dist_prodR": "p1_joint_law_distance.v",
    "var_dist_prodL": "p1_joint_law_distance.v",
    "fdist_prod_snd": "p1_joint_law_distance.v",
    "var_dist_own_marginals": "p9_actual_marginals.v",
}
MOVED = {"card_tnth_count": os.path.join(REPO, "lib/var_dist_supp.v")}

DECL = re.compile(
    r"^(?:Fail\s+)?(Lemma|Definition|Theorem|Fact|Corollary)\s+([A-Za-z_][\w']*)",
    re.M)

# Block boundaries: a declaration ends where the next declaration OR the next
# section-structure sentence begins, so that a Section header following the
# last lemma of a file is not counted as part of that lemma.
CUT = re.compile(
    r"^(?:Fail\s+)?(?:Lemma|Definition|Theorem|Fact|Corollary|Section|End"
    r"|Variables?|Hypothesis|Check|Arguments|Notation|Local|Print)\b", re.M)

RETIRED = ["SpectralDecay", "SpectralCert", r"_indist\b",
           "kim_centi_marginal_bound40", "kim_centi_cut_mixing40",
           "RepricePayload"]
BARRED = [r"\bapex\b", r"\bgate[sd]?\b", r"\bgating\b",
          r"\bposit(s|ed|ing)?\b", r"\bL1\b"]
ABBREV = re.compile(r"indist(?!inguishab)", re.I)


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
    # the doc comment is the (** ... *) immediately above the declaration in
    # the raw text
    docs = {}
    for m in DECL.finditer(raw):
        head = raw[:m.start()]
        j = head.rfind("(**")
        k = head.rfind("*)")
        docs[m.group(2)] = (head[j + 3:k].split()
                            if j != -1 and k > j else [])
    return out, docs


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
    for fn in sorted(set(sum([f for _, f in NEW], []))
                     | set(PROMOTED.values())):
        probe[fn] = blocks(os.path.join(PROBE, fn))

    # the promoted lemmas, in their new home
    st, sd = blocks(os.path.join(HERE, "staged/lib/var_dist_supp.v"))
    print("=== staged/lib/var_dist_supp.v (promoted from the probe)")
    for nm, fn in PROMOTED.items():
        pt, pd = probe[fn]
        if nm not in st:
            print("   MISSING in staged: %s" % nm)
            continue
        report(nm, pt[nm], st[nm], "code tokens")
        report(nm, pd[nm], sd[nm], "comment words")
    print()

    # the moved lemma, in its new home
    mt, md = blocks(os.path.join(HERE,
                                 "staged/instances/kim2025/five_card_mixing.v"))
    print("=== staged/instances/kim2025/five_card_mixing.v (moved from lib)")
    for nm, src in MOVED.items():
        pt, pd = blocks(src)
        report(nm, pt[nm], mt[nm], "code tokens")
        report(nm, pd[nm], md[nm], "comment words")
    print()

    for rel, srcs in NEW:
        st, sd = blocks(os.path.join(HERE, rel))
        print("=== %s" % rel)
        for nm in st:
            where = [f for f in srcs if nm in probe[f][0]]
            if not where:
                print("   NOT IN ANY PROBE FILE: %s" % nm)
                continue
            f = where[0]
            pt, pd = probe[f]
            if pt[nm] != st[nm]:
                report("%s (from %s)" % (nm, f), pt[nm], st[nm], "code tokens")
            if pd[nm] != sd[nm]:
                report("%s (from %s)" % (nm, f), pd[nm], sd[nm],
                       "comment words")
        idn = sum(1 for nm in st
                  if any(nm in probe[f][0] and probe[f][0][nm] == st[nm]
                         for f in srcs))
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
            for i, l in enumerate(open(f).read().split("\n"), 1):
                if re.search(pat, l):
                    hits.append("%s:%d: %s" % (os.path.relpath(f, HERE), i,
                                               l.strip()[:70]))
        print("%-32s %d hit(s)" % (pat, len(hits)))
        for h in hits:
            print("    " + h)
    over = []
    for f in sorted(files):
        for i, l in enumerate(open(f, "rb").read().split(b"\n"), 1):
            if len(l) > 80:
                over.append("%s:%d: %d bytes" % (os.path.relpath(f, HERE), i,
                                                 len(l)))
    print("%-32s %d hit(s)" % ("lines over 80 bytes", len(over)))
    for h in over:
        print("    " + h)
    ab = []
    for f in sorted(files):
        for i, l in enumerate(open(f).read().split("\n"), 1):
            if ABBREV.search(l):
                ab.append("%s:%d: %s" % (os.path.relpath(f, HERE), i,
                                         l.strip()[:70]))
    print("%-32s %d hit(s)" % ("abbreviated indistinguishab.", len(ab)))
    for h in ab:
        print("    " + h)
    return 0


if __name__ == "__main__":
    sys.exit(main())
