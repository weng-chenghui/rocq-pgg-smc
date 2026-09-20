#!/usr/bin/env python3
"""Checks layer F of the Published rename: in comments the noun "row" became
"program" or "path", and nothing else changed.

For every tracked .v file outside notes/ and legacy/ that differs from BASE:
the comment-stripped code tokens are identical; the comment words are
identical position by position, except that a word holding row/rows/Row/Rows
may hold program/programs/Program/Programs or path/paths/Path/Paths at the same
place.  Prints every changed word with its sense, counts what is left, and
scans changed lines for length, box shape and the project's barred words.

usage: check_prose.py [BASE] [-v]     (-v lists every replacement in context)
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = subprocess.check_output(
    ["git", "-C", HERE, "rev-parse", "--show-toplevel"]).decode().strip()
BARRED = re.compile(
    r"\b(apex|gate|gates|gated|gating|posit|posits|posited|positing)\b"
    r"|\bL[0-9]", re.I)
ROW = re.compile(r"(?<![A-Za-z0-9_])([Rr])ow(s?)(?![A-Za-z0-9_])")
FROZEN = set("""algebraic_rigidity card_exchange_pismc cover_tradeoff
covering_scheme graded_resource input_encoding perm_exchange perm_uniform
pgg_algebra_syntax pgg_collusion_bound pgg_execution_plug
pgg_input_commitment pgg_instance pgg_interface pgg_monodromy_profile
pgg_observed_execution pgg_raag pgg_run pgg_security_solver
pgg_session_types pgg_sharing_framework pgg_sum_mod pgl_bound pismc
psl211_blocks psl211_closure psl211_endpoints psl211_exec psl211_group
psl211_orbit psl211_profile psl211_scheme smc_interpreter
smc_session_types transitivity_privacy""".split())


def split(text):
    code, com, depth, i = [], [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
            com.append(" ")
            if i < len(text) and text[i] == "*" and not text.startswith("*)", i):
                i += 1
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            code.append(" ")
            com.append(" ")
        else:
            (com if depth else code).append(text[i])
            (code if depth else com).append("\n" if text[i] == "\n" else " ")
            i += 1
    return "".join(code), "".join(com)


def variants(word):
    """The words an old word may have become."""
    out = {word}
    for noun in ("program", "path"):
        out.add(ROW.sub(
            lambda m: (noun.capitalize() if m.group(1) == "R" else noun)
            + m.group(2), word))
    return out


def main():
    args = [a for a in sys.argv[1:] if a != "-v"]
    verbose = "-v" in sys.argv
    base = args[0] if args else "HEAD"
    files = subprocess.check_output(
        ["git", "-C", REPO, "ls-tree", "-r", "--name-only", base]
    ).decode().split("\n")
    files = [f for f in files if f.endswith(".v")
             and not f.startswith(("notes/", "legacy/"))]
    ok, changed, total = True, 0, {"program": 0, "path": 0}
    for f in files:
        old = subprocess.run(["git", "-C", REPO, "show", f"{base}:{f}"],
                             capture_output=True, text=True, check=True).stdout
        new = open(os.path.join(REPO, f), encoding="utf-8").read()
        if old == new:
            continue
        changed += 1
        if os.path.basename(f)[:-2] in FROZEN:
            ok = False
            print(f"FROZEN FILE CHANGED {f}")
        oc, om = split(old)
        nc, nm = split(new)
        a, b = oc.split(), nc.split()
        c, d = om.split(), nm.split()
        good = a == b and len(c) == len(d)
        n = {"program": 0, "path": 0}
        if a != b:
            print(f"   code tokens differ in {f}")
        if len(c) != len(d):
            print(f"   comment word counts differ in {f}: {len(c)} / {len(d)}")
            for k, (x, y) in enumerate(zip(c, d)):
                if y not in variants(x):
                    print("   first at:", " ".join(c[max(0, k - 6):k + 6]))
                    print("   found   :", " ".join(d[max(0, k - 6):k + 6]))
                    break
        else:
            for k, (x, y) in enumerate(zip(c, d)):
                if x == y:
                    continue
                if y in variants(x):
                    n["program" if "rogram" in y and "rogram" not in x
                      else "path"] += 1
                    if verbose:
                        print("     ", " ".join(d[max(0, k - 5):k + 4]))
                else:
                    good = False
                    print(f"   OTHER CHANGE {f}: "
                          f"{' '.join(c[max(0, k - 4):k + 4])}  ->  "
                          f"{' '.join(d[max(0, k - 4):k + 4])}")
        left = len(ROW.findall(nm))
        ok &= good
        for key in n:
            total[key] += n[key]
        print(f"{'SAME' if good else 'DIFF'}  {f}  program {n['program']}, "
              f"path {n['path']}, left as row {left}")
        old_lines = set(old.splitlines())
        for ln, line in enumerate(new.splitlines(), 1):
            if line in old_lines:
                continue
            if len(line.encode()) > 80:
                ok = False
                print(f"   LONG {f}:{ln} ({len(line.encode())} bytes)")
            if line.startswith("(*") and line.endswith("*)") \
                    and not line.startswith("(**") \
                    and len(line.encode()) >= 78 and not line.endswith(" *)") \
                    and not set(line) <= set("(*)"):
                ok = False
                print(f"   BOX {f}:{ln}: no space before the closing delimiter")
            if BARRED.search(line):
                ok = False
                print(f"   BARRED {f}:{ln}: {line.strip()}")
    print(f"{changed} files changed; program {total['program']}, "
          f"path {total['path']}")
    print("ALL OK" if ok else "PROBLEMS")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
