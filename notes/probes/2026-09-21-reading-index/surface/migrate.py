#!/usr/bin/env python3
"""Rewrite every Tableau program of the staged instance files to the surface
of section 3.5 of the spec: a certify statement introduces its evidence with
by, and every publish terminal ends with assuming.

The pass is text only and reports every line it changes, so that the diff can
be read against the spec rather than trusted.  It touches the staged copies
alone; the production tree is never opened for writing.

Rules, in the order applied:

  1  certify ExactIndependence X          ->  certify ExactIndependence by X
  2  certify InputIndistinguishability X  ->  ... by X   (not before at)
  3  certify IdealProximity X             ->  certify IdealProximity by X
  4  |> publish Obstruction o             ->  unchanged on that line; the
     by pf a                                  continuation gains assuming
  5  |> publish HEAD rest                 ->  |> publish HEAD assuming rest

Rule 5 inserts after the first token following publish, which is the transfer
status in the three-payload rule and the literal Observed in the terminal
below AnalysisBridged.  A Sampled terminal would need the insertion after its
second token; no file of the tree writes one, and the script refuses the
shape rather than guessing.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
STAGED = os.path.join(HERE, "staged", "instances")

CERTIFY = [
    (re.compile(r"(\bcertify\s+ExactIndependence\s+)(?!by\b)(?=\S)"), r"\1by "),
    (re.compile(r"(\bcertify\s+InputIndistinguishability\s+)(?!by\b|at\b)(?=\S)"),
     r"\1by "),
    (re.compile(r"(\bcertify\s+IdealProximity\s+)(?!by\b)(?=\S)"), r"\1by "),
]

PUBLISH = re.compile(r"(\|>\s*publish\s+)(\S+)(\s+)(?!assuming\b)(?=\S)")
OBSTR_BY = re.compile(r"^(\s*by\s+\S+\s+)(?!assuming\b)(?=\S)")


def migrate(path):
    src = open(path).read().split("\n")
    out, changed, pending_obstruction = [], [], False
    for i, line in enumerate(src, 1):
        new = line
        for pat, rep in CERTIFY:
            new = pat.sub(rep, new)
        if pending_obstruction:
            new2 = OBSTR_BY.sub(r"\1assuming ", new)
            if new2 != new:
                pending_obstruction = False
            new = new2
        m = PUBLISH.search(new)
        if m and m.group(2) == "Sampled":
            sys.exit("%s:%d: a Sampled terminal needs a rule of its own" %
                     (path, i))
        if m and m.group(2) == "Obstruction":
            pending_obstruction = True
        elif m:
            new = PUBLISH.sub(r"\1\2\3assuming ", new)
        elif re.search(r"\|>\s*publish\s*$", new):
            sys.exit("%s:%d: publish at end of line, unhandled" % (path, i))
        if new != line:
            changed.append((i, line.rstrip(), new.rstrip()))
        out.append(new)
    if changed:
        open(path, "w").write("\n".join(out))
    return changed


def main():
    total = 0
    for root, _dirs, files in os.walk(STAGED):
        for f in sorted(files):
            if not f.endswith(".v"):
                continue
            path = os.path.join(root, f)
            changed = migrate(path)
            rel = os.path.relpath(path, HERE)
            print("%-62s %d site(s)" % (rel, len(changed)))
            for i, old, new in changed:
                print("  %4d - %s" % (i, old))
                print("       + %s" % new)
            total += len(changed)
    print("total %d site(s)" % total)


if __name__ == "__main__":
    main()
