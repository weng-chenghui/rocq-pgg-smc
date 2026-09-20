#!/usr/bin/env python3
"""Stage the comment repoints three production files need after the move.

Each edit is an anchored replacement of an exact block, so the staged copy is
generated from production at run time and cannot freeze against a base that
moves.  Box lines are emitted by one formatter, never counted by hand.

Every replacement is inside a comment.  check_comment_only() proves that by
comparing the comment-stripped text of the two copies.

Usage: python3 stage_edits.py
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OUT = os.path.join(HERE, "staged-comments")
# NOT under staged/: staged/instances/pgl27 is an -R root of _CoqProject,
# so a .v placed there would shadow the production module it copies.

BRIDGED = "instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v"


def box(lines):
    """Content lines to 80-column box-comment lines."""
    out = []
    for s in lines:
        line = ("(* " + s).ljust(78) + "*)"
        assert len(line) == 80, (len(line), s)
        out.append(line)
    return "\n".join(out)


EDITS = {
    "instances/pgl27/pgl27_encoding_r5.v": [
        (box(["clause of pgl27_algebra (pgl27_exec.v), from which the "
              "manifest rows of",
              "pgl27_rows.v descend. Every leakage value below is a value of "
              "the scheme",
              "the rest of the development executes, and not of a variant "
              "of it."]),
         box(["clause of pgl27_algebra (pgl27_exec.v), from which the "
              "manifest rows of",
              "pgl27_tableau_analysis_bridged.v descend. Every leakage "
              "value below is a",
              "value of the scheme the rest of the development executes, "
              "and not of a",
              "variant of it."])),
    ],
    "instances/psl211/psl211_reading_constancy.v": [
        (box(["proves the same field through pgl27_word_view_const of",
              "instances/pgl27/pgl27_rows.v, three-transitivity read as "
              "constancy for",
              "coalitions of fewer than four seats. The dealt statement "
              "rules out one",
              "named ideal and no certificate, this tree carrying no "
              "dealt-mode sample",
              "adapter through which a certificate's ideal could be pinned "
              "to it."]),
         box(["proves the same field through pgl27_word_view_const of",
              "instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v,",
              "three-transitivity read as constancy for coalitions of fewer "
              "than four",
              "seats. The dealt statement rules out one named ideal and no "
              "certificate,",
              "this tree carrying no dealt-mode sample adapter through "
              "which a",
              "certificate's ideal could be pinned to it."])),
    ],
    "manifest/pgg_analysis_manifest.v": [
        (box(["| distribution-to-observer bridges | pgl27_prior_viewE of",
              " " * 23 + "instances/pgl27/pgl27_proximity.v, which "
              "identifies",
              " " * 23 + "the framework's reading of a coalition at this",
              " " * 23 + "model with PGL27Analysis.static_view |"]),
         box(["| distribution-to-observer bridges | pgl27_prior_viewE of",
              " " * 23 + "instances/pgl27/tableau/",
              " " * 23 + "pgl27_tableau_analysis_bridged.v, which "
              "identifies",
              " " * 23 + "the framework's reading of a coalition at this",
              " " * 23 + "model with PGL27Analysis.static_view |"])),
        (box(["| final bridge theorem | pgl27_prior_exact_witness of",
              " " * 25 + "instances/pgl27/pgl27_proximity.v, whose",
              " " * 25 + "independence field is pgl27_view_indep_gen |"]),
         box(["| final bridge theorem | pgl27_prior_exact_witness of",
              " " * 25 + "instances/pgl27/tableau/",
              " " * 25 + "pgl27_tableau_analysis_bridged.v, whose",
              " " * 25 + "independence field is pgl27_view_indep_gen |"])),
    ],
}


def strip_comments(text):
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


def main():
    rc = 0
    for rel, subs in sorted(EDITS.items()):
        src = open(os.path.join(ROOT, rel)).read()
        new = src
        for old, repl in subs:
            if new.count(old) != 1:
                print("FAIL %s: anchor occurs %d times, not once:\n%s"
                      % (rel, new.count(old), old[:200]))
                rc = 1
                continue
            new = new.replace(old, repl)
        dst = os.path.join(OUT, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, "w").write(new)
        same = strip_comments(src).split() == strip_comments(new).split()
        long = [i for i, l in enumerate(new.split("\n"), 1) if len(l) > 80]
        print("%-48s %d edit(s)  comment-only=%s  over-80=%s"
              % (rel, len(subs), same, long or "none"))
        if not same:
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
