#!/usr/bin/env python3
"""Re-copy the thirteen chain files from production and rebuild below them.

The thirteen files are the ones landings 1 and 2 own.  Both are in production,
so production is the source.  A landing-3 compile is evidence only against the
text it loaded, so whenever one of the thirteen moves this script copies them
again, reports whether each changed in code or only in comments, and
recompiles the whole chain in the _CoqProject order.

Usage:  python3 restage.py            copy, report, recompile
        python3 restage.py --check    copy nothing; only report what differs
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
SRC = REPO
L3 = os.path.join(HERE, "staged")

# landing 2's five landed files
CHAIN = [
    "lib/var_dist_supp.v",
    "security/var_dist_joint_law.v",
    "instances/kim2025/five_card_mixing.v",
    "manifest/pgg_tableau_arm_relations.v",
    "instances/kim2025/five_card_proximity.v",
    # landing 1's files, and the one file production alone carries
    "instances/kim2025/five_card_analysis.v",
    "manifest/pgg_tableau.v",
    "manifest/pgg_tableau_syntax.v",
    "instances/pgl27/pgl27_rows.v",
    "instances/kim2025/five_card_rows.v",
    "instances/s5/s5_rows.v",
    "instances/psl211/psl211_reading_constancy.v",
    "instances/psl211/psl211_rows.v",
]

sys.path.insert(0, HERE)
from verify import split_comments, tokens  # noqa: E402


def main():
    check = "--check" in sys.argv[1:]
    moved = []
    for rel in CHAIN:
        a = open(os.path.join(SRC, rel)).read()
        b = open(os.path.join(L3, rel)).read()
        if a == b:
            print("%-48s unchanged" % rel)
            continue
        code = "CODE CHANGED" if tokens(split_comments(a)[0]) != \
            tokens(split_comments(b)[0]) else "comments only"
        print("%-48s %s" % (rel, code))
        moved.append(rel)
        if not check:
            open(os.path.join(L3, rel), "w").write(a)
    if check or not moved:
        print("\n%d file(s) differ; nothing recompiled."
              % len(moved) if check else "\nnothing to do.")
        return 0
    print("\ncopied %d file(s); recompiling the chain." % len(moved))
    return subprocess.run([sys.executable,
                           os.path.join(HERE, "compile.py")],
                          cwd=HERE).returncode


if __name__ == "__main__":
    sys.exit(main())
