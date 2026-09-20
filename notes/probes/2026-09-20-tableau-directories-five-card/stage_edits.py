#!/usr/bin/env python3
"""Find the production files whose comments cite a file this instance retires
or reduces, and stage a repointed copy of each under staged-comments/.

staged-comments/ and never staged/: staged/ is an -R root mapped to pgg_smc,
so a copy there shadows the module it copies.

The scan covers both names.  Nothing outside the two sources of the cut names
five_card_rows.  One production comment names
instances/kim2025/five_card_proximity.v for a lemma that moves out of it,
manifest/pgg_tableau_arm_relations.v, and that one copy is staged here and
APPLIED with this instance.  It is not the dangling case of the PGL(2,7)
audit's ruling 6, the reduced file still existing under that path; it is the
empty-reverse-closure case.  Nothing in the tracked tree Requires
pgg_tableau_arm_relations, so the repoint recompiles one module, and the
batching reason that defers a manifest repoint does not apply to a file
nothing imports.  Left unrepointed it would name, for the length of the
batch, a file that no longer holds the lemma it cites.

Each staged copy is produced by an anchored replacement on production's text,
never by a hand edit, so it cannot freeze against a base that moves.  The
anchor must match exactly once.  Each copy is then verified comment-only by
comparing the comment-stripped text of the two, and no line may exceed 80
bytes.

Usage: python3 stage_edits.py
"""

import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OUT = os.path.join(HERE, "staged-comments")

SOURCES = {os.path.join("instances", "kim2025", "five_card_rows.v"),
           os.path.join("instances", "kim2025", "five_card_proximity.v")}

# The directories _CoqProject maps with -R or -Q.  notes/ and .claude/ are
# not production and are out of scope for this pass.
DIRS = ["lib", "protocol", "groups", "security", "smc", "reconstruct",
        "instances", "manifest", "legacy"]

PAT = re.compile(r"five_card_rows|five_card_proximity")


def boxline(content):
    line = "(* " + content
    assert len(line) <= 77, (len(line), content)
    return line.ljust(78) + "*)"


ARM = os.path.join("manifest", "pgg_tableau_arm_relations.v")

EDITS = {
    ARM: [
        (re.compile(r"^\(\* instances/kim2025/five_card_proximity\.v, holds "
                    r"because its conclusion is +\*\)\n"
                    r"\(\* a theorem there and its premise is discarded\. +"
                    r"\*\)$", re.M),
         boxline("instances/kim2025/tableau/"
                 "five_card_tableau_analysis_bridged.v, holds")
         + "\n"
         + boxline("because its conclusion is a theorem there and its "
                   "premise is discarded.")),
    ],
}


def strip(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def stage(rel):
    src = os.path.join(ROOT, rel)
    text = open(src).read()
    for pat, repl in EDITS[rel]:
        n = len(pat.findall(text))
        assert n == 1, (rel, n, pat.pattern)
        text = pat.sub(lambda _m: repl, text)
    dst = os.path.join(OUT, rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, "w").write(text)
    same = strip(open(src).read()) == strip(text)
    over = [i for i, l in enumerate(text.split("\n"), 1)
            if len(l.encode()) > 80]
    print("%-48s %d edit(s)  comment-only=%s  over-80=%s  APPLY WITH THIS INSTANCE"
          % (rel, len(EDITS[rel]), same, over or "none"))


def main():
    os.makedirs(OUT, exist_ok=True)
    hits = []
    for d in DIRS:
        for base, _, names in os.walk(os.path.join(ROOT, d)):
            for n in names:
                if not n.endswith(".v"):
                    continue
                p = os.path.join(base, n)
                rel = os.path.relpath(p, ROOT)
                lines = [(i, l) for i, l
                         in enumerate(open(p).read().splitlines(), 1)
                         if PAT.search(l)]
                if lines:
                    hits.append((rel, lines))
    for rel, lines in sorted(hits):
        tag = "SOURCE OF THE CUT" if rel in SOURCES else "TO REPOINT"
        print("%-48s %2d citation(s)  %s" % (rel, len(lines), tag))
        for i, l in lines:
            print("      %4d  %s" % (i, l.strip()[:64]))
    todo = [h for h in hits if h[0] not in SOURCES]
    print("")
    for rel, _ in todo:
        stage(rel)
    print("files to repoint: %d, applied with this instance (empty reverse "
          "closure)" % len(todo))


if __name__ == "__main__":
    main()
