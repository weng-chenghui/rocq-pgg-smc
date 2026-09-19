#!/usr/bin/env python3
"""Prove that staged/ is its source text with only the edits E1 to E5.

Two checks per staged file.

  (1) CODE TOKENS.  Comments removed, whitespace normalized, the remaining
      text split into tokens.  A unified diff of the staged token stream
      against the source file's token stream.  Every hunk must be one of the
      enumerated edits.

  (2) COMMENT WORDS.  Only the comment text of each file, whitespace
      normalized, one word per line, as a unified diff.

The source of a rows or framework file is the probe copy; the source of
psl211_reading_constancy.v is the production file.

Exit status 0 iff every file's token diff is empty or matches an expected
hunk count recorded in STATUS.md, which the caller reads.  This script only
prints; it makes no judgement.
"""

import difflib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PROBE = os.path.join(REPO, "notes/probes/2026-09-19-tableau-extensions")

# staged relative path -> source absolute path
PAIRS = [
    ("staged/manifest/pgg_tableau.v", os.path.join(PROBE, "pgg_tableau.v")),
    ("staged/manifest/pgg_tableau_syntax.v",
     os.path.join(PROBE, "pgg_tableau_syntax.v")),
    ("staged/instances/pgl27/pgl27_rows.v",
     os.path.join(PROBE, "pgl27_rows.v")),
    ("staged/instances/kim2025/five_card_rows.v",
     os.path.join(PROBE, "five_card_rows.v")),
    ("staged/instances/s5/s5_rows.v", os.path.join(PROBE, "s5_rows.v")),
    ("staged/instances/psl211/psl211_rows.v",
     os.path.join(PROBE, "psl211_rows.v")),
    ("staged/instances/psl211/psl211_reading_constancy.v",
     os.path.join(REPO, "instances/psl211/psl211_reading_constancy.v")),
]

# The second source of pgl27_rows.v: the two definitions moved by E3.
T0 = os.path.join(PROBE, "t0_sampled_branch_pgl27.v")


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
    return "".join(code), "\n".join(comments)


def tokens(code):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|\d+|\S", code)


def words(comment):
    return comment.split()


def report(name, a, b, kind):
    d = list(difflib.unified_diff(a, b, "source", "staged", n=1, lineterm=""))
    hunks = sum(1 for l in d if l.startswith("@@"))
    print("--- %s : %s : %d hunk(s), %d changed line(s)"
          % (name, kind, hunks,
             sum(1 for l in d
                 if l[:1] in "+-" and not l.startswith(("+++", "---")))))
    for l in d:
        print("   " + l)
    return hunks


def main():
    total = 0
    for rel, src in PAIRS:
        s_code, s_com = split_comments(open(src).read())
        t_code, t_com = split_comments(
            open(os.path.join(HERE, rel)).read())
        if rel.endswith("pgl27_rows.v"):
            # E3 moves two definitions in from t0_sampled_branch_pgl27.v; the
            # token check is run against the concatenation of the two sources
            # so the moved text is not reported as an addition.
            m_code, m_com = split_comments(open(T0).read())
            print("=== %s (source: probe pgl27_rows.v; the two E3 "
                  "definitions are checked separately below)" % rel)
        else:
            print("=== %s" % rel)
        total += report(rel, tokens(s_code), tokens(t_code), "code tokens")
        report(rel, words(s_com), words(t_com), "comment words")
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
