#!/usr/bin/env python3
"""Compile fidelity.v against the staged text and baseline.v against
production, one Rocq process at a time, and capture the output of each.

baseline.v must NOT see the staged root: a Require resolves to the LAST
matching -R, so with `-R staged/instances/kim2025 pgg_smc` in the flag list
`five_card_proximity` would load the staged reduced copy instead of
production's.  That one line is stripped for the baseline compile.

Usage:  python3 run_fidelity.py [fidelity|baseline]
"""

import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LOCK = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
        "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")
SECONDS = "1800"
MAXMB = "12000"
STAGED_R = "staged/instances/kim2025"


def read_flags(with_staged):
    flags = []
    for raw in open(os.path.join(HERE, "_CoqProject")):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-arg "):
            flags += [p for p in line.split() if p != "-arg"]
        elif line.startswith("-R ") or line.startswith("-Q "):
            parts = line.split()
            if not with_staged and parts[1] == STAGED_R:
                continue
            flags += parts
    return flags


def run(name, with_staged):
    flags = read_flags(with_staged)
    cmd = [LOCK, SECONDS, MAXMB, "rocq", "compile"] + flags + [name + ".v"]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)
    dt = time.time() - t0
    open(os.path.join(HERE, name + ".out"), "w").write(p.stdout)
    open(os.path.join(HERE, name + ".err"), "w").write(p.stderr)
    print("%-10s rc=%d  %6.1f s  staged_root=%s"
          % (name, p.returncode, dt, with_staged))
    if p.returncode != 0:
        sys.stdout.write(p.stderr[-4000:])
    return p.returncode


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "both"
    rc = 0
    if which in ("fidelity", "both"):
        rc |= run("fidelity", True)
    if which in ("baseline", "both"):
        rc |= run("baseline", False)
    return rc


if __name__ == "__main__":
    sys.exit(main())
