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
# NOT under staged/: staged/instances/psl211 is an -R root of _CoqProject,
# so a .v placed there would shadow the production module it copies.

BRIDGED = "psl211_tableau_analysis_bridged.v"


def box(lines):
    """Content lines to 80-column box-comment lines."""
    out = []
    for s in lines:
        line = ("(* " + s).ljust(78) + "*)"
        assert len(line) == 80, (len(line), s)
        out.append(line)
    return "\n".join(out)


EDITS = {
    "instances/psl211/psl211_models.v": [
        (box(["The exact arm's witness over psl211_exact_family is built in",
              "psl211_rows.v, beside the Tableau surface whose ExactWitness "
              "record gives",
              "it its type, which is where the other three instances build "
              "theirs. This",
              "file therefore imports nothing from the manifest layer."]),
         box(["The exact arm's witness over psl211_exact_family is built in",
              "instances/psl211/tableau/" + BRIDGED + ", beside the",
              "Tableau surface whose ExactWitness record gives it its type, "
              "which is",
              "where the other three instances build theirs. This file "
              "therefore",
              "imports nothing from the manifest layer."])),
    ],
    "instances/psl211/psl211_reading_constancy.v": [
        (box(["publishes its all-decks row through the exact arm and its "
              "word row through",
              "the proximity arm, in instances/psl211/psl211_word_proximity.v"
              ", and this",
              "file is what the input-indistinguishability arm would cost "
              "it."]),
         box(["publishes its all-decks row through the exact arm and its "
              "word row through",
              "the proximity arm, in",
              "instances/psl211/tableau/" + BRIDGED + ", and this file",
              "is what the input-indistinguishability arm would cost it."])),
        (box(["field, and the row of instances/psl211/psl211_word_proximity.v"
              " publishes",
              "2^-40 over the word model through the proximity arm."]),
         box(["field, and the row of",
              "instances/psl211/tableau/" + BRIDGED + " publishes",
              "2^-40 over the word model through the proximity arm."])),
        (box(["the row published over the weighted-word adapter "
              "psl211_word_sample in",
              "instances/psl211/psl211_word_proximity.v carries a proximity "
              "certificate,"]),
         box(["the row published over the weighted-word adapter "
              "psl211_word_sample in",
              "instances/psl211/tableau/" + BRIDGED + " carries a",
              "proximity certificate,"])),
        ("    and the row published over it in\n"
         "    instances/psl211/psl211_word_proximity.v carries a proximity "
         "certificate,\n",
         "    and the row published over it in\n"
         "    instances/psl211/tableau/" + BRIDGED + " carries a\n"
         "    proximity certificate,\n"),
    ],
    "manifest/pgg_analysis_manifest.v": [
        (box(["| bound or certificate | psl211_word_proximity_cert of",
              " " * 25 + "instances/psl211/psl211_word_proximity.v, whose",
              " " * 25 + "number is 2^-40 and whose distance field is",
              " " * 25 + "psl211_word_proximity_close |"]),
         box(["| bound or certificate | psl211_word_proximity_cert of",
              " " * 25 + BRIDGED + " in",
              " " * 25 + "instances/psl211/tableau/, whose number is 2^-40",
              " " * 25 + "and whose distance field is",
              " " * 25 + "psl211_word_proximity_close of",
              " " * 25 + "instances/psl211/psl211_word_proximity.v |"])),
        (box(["| final bridge theorem | psl211_word_view_proximity of",
              " " * 25 + "instances/psl211/psl211_word_proximity.v |"]),
         box(["| final bridge theorem | psl211_word_view_proximity of",
              " " * 25 + BRIDGED + " in",
              " " * 25 + "instances/psl211/tableau/ |"])),
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
