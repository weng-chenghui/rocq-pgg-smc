#!/usr/bin/env python3
"""Prove that landing 4's staged text is its source text plus the listed edits.

Five checks.

  (1) WHOLE-FILE TOKENS for the four files that already exist, each against
      its own base: instances/psl211/psl211_analysis.v and
      instances/psl211/psl211_reading_constancy.v against PRODUCTION,
      manifest/pgg_analysis_manifest.v and manifest/pgg_analysis_client.v
      against LANDING 3's staged text, which is the base landing 4 rebases
      onto.  Comments removed, whitespace normalized, a unified diff of the
      token streams.  Every hunk must be one of the additions STATUS.md lists.

  (2) COMMENTS-ONLY for instances/psl211/psl211_reading_constancy.v: its code
      token stream must be byte-for-byte production's, and its comment text
      is printed as a unified word diff and classified in STATUS.md.

  (3) PER-DECLARATION TOKENS.  Each declaration of the two new files is looked
      up by name in the probe file that declares it and its token stream
      compared.  A declaration whose tokens differ is printed in full, and the
      one that is meant to differ is named in EXPECTED below.

  (4) COMMENT WORDS of every landed declaration, staged against the probe's,
      as a unified word diff.

  (5) SCANS over the staged tree: retired names, lines over 80 bytes, the
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
L3 = os.path.join(os.path.dirname(HERE),
                  "2026-09-20-tableau-extensions-landing3", "staged")

WHOLE = [
    ("staged/instances/psl211/psl211_analysis.v",
     os.path.join(REPO, "instances/psl211/psl211_analysis.v"), "production"),
    ("staged/instances/psl211/psl211_reading_constancy.v",
     os.path.join(REPO, "instances/psl211/psl211_reading_constancy.v"),
     "production"),
    ("staged/manifest/pgg_analysis_manifest.v",
     os.path.join(L3, "manifest/pgg_analysis_manifest.v"), "landing 3"),
    ("staged/manifest/pgg_analysis_client.v",
     os.path.join(L3, "manifest/pgg_analysis_client.v"), "landing 3"),
]

COMMENTS_ONLY = [
    ("staged/instances/psl211/psl211_reading_constancy.v",
     os.path.join(REPO, "instances/psl211/psl211_reading_constancy.v")),
]

# staged file -> the probe files its landed declarations come from
NEW = [
    ("staged/instances/psl211/psl211_word_model.v",
     ["p6_psl211_word_model.v"]),
    ("staged/instances/psl211/psl211_word_proximity.v",
     ["p6_psl211_word_proximity.v", "p6_mutations.v"]),
]

# the declarations whose token stream is meant to differ from the probe's,
# and why.  Every other declaration must come out token-identical.
EXPECTED = {
    "psl211_row_word_proximity_rowE":
        "stated at the manifest row psl211_row_word, which did not exist when"
        " the probe was written",
}

# declarations of a landed file that are the landing's own text and appear in
# no probe file.  They are reported and not compared.
LANDING_OWN = set()

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
           "RepricePayload", "idealproximity_ceiling",
           "psl211_spectral_constancy"]
BARRED = [r"\bapex\b", r"\bgate[sd]?\b", r"\bgating\b",
          r"\bposit(s|ed|ing)?\b", r"\bL1\b", r"\bceiling\b"]
ABBREV = re.compile(r"indist(?!inguishab)", re.I)

LANDED = [
    "staged/instances/psl211/psl211_word_model.v",
    "staged/instances/psl211/psl211_analysis.v",
    "staged/manifest/pgg_analysis_manifest.v",
    "staged/manifest/pgg_analysis_client.v",
    "staged/instances/psl211/psl211_reading_constancy.v",
    "staged/instances/psl211/psl211_word_proximity.v",
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


def compare(nm, st, sd, pt, pd, where):
    ok = pt[nm] == st[nm]
    if not ok:
        if nm in EXPECTED:
            print("   EXPECTED DIFFERENCE in %s: %s" % (nm, EXPECTED[nm]))
        report("%s (from %s)" % (nm, where), pt[nm], st[nm], "code tokens")
    if pd[nm] != sd[nm]:
        report("%s (from %s)" % (nm, where), pd[nm], sd[nm], "comment words")
    return ok


def main():
    print("=" * 78)
    print("(1) WHOLE-FILE TOKEN DIFFS AGAINST EACH FILE'S OWN BASE")
    print("=" * 78)
    for rel, src, base in WHOLE:
        s_code, _ = split_comments(open(src).read())
        t_code, _ = split_comments(open(os.path.join(HERE, rel)).read())
        print("=== %s   (base: %s)" % (rel, base))
        report(rel, tokens(s_code), tokens(t_code), "code tokens")
        print()

    print("=" * 78)
    print("(2) COMMENTS-ONLY FILES: CODE IDENTICAL, COMMENT WORDS DIFFED")
    print("=" * 78)
    for rel, src in COMMENTS_ONLY:
        s_code, s_com = split_comments(open(src).read())
        t_code, t_com = split_comments(open(os.path.join(HERE, rel)).read())
        same = tokens(s_code) == tokens(t_code)
        print("=== %s : code tokens identical to production: %s"
              % (rel, "YES" if same else "NO"))
        if not same:
            report(rel, tokens(s_code), tokens(t_code), "code tokens")
        report(rel, " ".join(s_com).split(), " ".join(t_com).split(),
               "comment words")
        print()

    print("=" * 78)
    print("(3) and (4) PER-DECLARATION TOKENS AND COMMENT WORDS")
    print("=" * 78)
    probe = {}
    for fn in sorted(set(sum([f for _, f in NEW], []))):
        probe[fn] = blocks(os.path.join(PROBE, fn))

    for rel, srcs in NEW:
        st, sd = blocks(os.path.join(HERE, rel))
        print("=== %s" % rel)
        idn, cmpd = 0, 0
        for nm in sorted(st, key=list(st).index):
            where = [f for f in srcs if nm in probe[f][0]]
            if not where:
                print("   NOT IN ANY PROBE FILE: %s" % nm)
                continue
            f = where[0]
            pt, pd = probe[f]
            cmpd += 1
            idn += compare(nm, st, sd, pt, pd, f)
        print("   %d of %d declarations token-identical to the probe's"
              " (%d compared, %d in the file)"
              % (idn, cmpd, cmpd, len(st)))
        print()

    print("=" * 78)
    print("(5) SCANS OVER staged/ AND landing_fidelity.v")
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
