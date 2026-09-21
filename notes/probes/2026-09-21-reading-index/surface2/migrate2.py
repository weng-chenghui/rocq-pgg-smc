#!/usr/bin/env python3
"""Rewrite the staged instance files to the three rules of round 2.

  1  |> conclude c by p            ->  |> conclude at c by p
  2  certify InputIndistinguishability at R idx b
                                   ->  ... at R idx by b
  3  |> publish Obstruction o          ->  |> publish Obstruction
        by pf assuming a                     InputDistinguishability at c
                                             by pf assuming a

Rule 3 is not a text substitution: the terminal takes the kind's number
where it took a named payload, so the one site is rewritten by an anchored
replacement of the whole statement, and the number is named beside the
payload in the same file.

The bind spellings are left alone: ;;; conclude c of p and
;;; certify_indistinguishability of c are the payload forms a K16-style
equation puts the surface against, and a migration that changed them would
destroy the evidence.

Every changed line is printed, so the diff is read against the spec rather
than trusted.  Only the staged copies are opened for writing.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
STAGED = os.path.join(HERE, "staged", "instances")

CONCLUDE = re.compile(r"(\|>\s*conclude\s+)(?!at\b)(?=\S)")
FIVE = re.compile(r"(certify\s+InputIndistinguishability\s+at\s+\S+\s+\S+\s+)"
                  r"(?!by\b)(?=\S)")

# The PSL(2,11) obstruction statement, the one site of rule 3.
OBSTR_OLD = """    |> publish Obstruction psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly."""
OBSTR_NEW = """    |> publish Obstruction InputDistinguishability
       at psl211_alldecks_number
       by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly."""

# The number, named beside the payload it is the number of.
NUMBER_ANCHOR = """(** psl211_alldecks_obstruction — the obstruction, at every real field and at
    the one index of the all-decks family: the model is input distinguishable
    at 1/660, the reciprocal of the order of the shuffle group. *)"""
NUMBER_NEW = """(** psl211_alldecks_number — the number the all-decks model is input
    distinguishable at, 1/660, the reciprocal of the order of the shuffle
    group, as a term in the real field and in nothing else. The program's
    terminal writes this name after at, so the number a reader of the
    program meets and the number the payload below carries are one term. *)
Definition psl211_alldecks_number : forall R : realType, R :=
  fun R => (#|pgg_G psl211_M|%:R)^-1.

""" + NUMBER_ANCHOR


def line_pass(path):
    src = open(path).read().split("\n")
    out, changed = [], []
    for i, line in enumerate(src, 1):
        new = CONCLUDE.sub(r"\1at ", line)
        new = FIVE.sub(r"\1by ", new)
        if new != line:
            changed.append((i, line.rstrip(), new.rstrip()))
        out.append(new)
    if changed:
        open(path, "w").write("\n".join(out))
    return changed


def obstruction_pass(path):
    s = open(path).read()
    if OBSTR_OLD not in s:
        return 0
    if NUMBER_ANCHOR not in s:
        sys.exit("%s: the number's anchor was not found" % path)
    s = s.replace(NUMBER_ANCHOR, NUMBER_NEW, 1)
    s = s.replace(OBSTR_OLD, OBSTR_NEW, 1)
    open(path, "w").write(s)
    return 1


def main():
    total = 0
    for root, _dirs, files in os.walk(STAGED):
        for f in sorted(files):
            if not f.endswith(".v"):
                continue
            path = os.path.join(root, f)
            n = obstruction_pass(path)
            changed = line_pass(path)
            rel = os.path.relpath(path, HERE)
            if changed or n:
                print("%-62s %d line(s), %d statement(s)"
                      % (rel, len(changed), n))
                for i, old, new in changed:
                    print("  %4d - %s" % (i, old))
                    print("       + %s" % new)
            total += len(changed) + n
    print("total %d site(s)" % total)


if __name__ == "__main__":
    main()
