#!/usr/bin/env python3
"""Compile the staged surface of probe A, one Rocq process at a time.

The flags come out of ./_CoqProject so that the flags file and this script
cannot drift.  The staged roots are mapped to pgg_smc after production's,
because a Require resolves to the LAST matching -R or -Q entry.

Every invocation goes through the machine-wide rocq1 lock, because a second
agent compiles at the same time.  Nothing is written into the production
tree: each staged .vo lands beside its .v under staged/.

Usage:  python3 compile.py [file ...]      (default: the _CoqProject order)
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


def read_project():
    """Return (flags, files) from _CoqProject."""
    flags, files = [], []
    for raw in open(os.path.join(HERE, "_CoqProject")):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-arg "):
            parts = line.split()
            flags += [p for p in parts if p != "-arg"]
        elif line.startswith("-R ") or line.startswith("-Q "):
            flags += line.split()
        else:
            files.append(line)
    return flags, files


def compile_one(flags, rel):
    cmd = [LOCK, SECONDS, MAXMB, "rocq", "compile"] + flags + ["-time", rel]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)
    dt = time.time() - t0
    return p.returncode, dt, p.stdout, p.stderr


def _over_five(line):
    # "Chars a - b [sentence] 12.345 secs (12.3u,0.0s)"
    try:
        return float(line.split("]")[1].split("secs")[0].strip()) > 5.0
    except (IndexError, ValueError):
        return False


def main():
    flags, files = read_project()
    targets = sys.argv[1:] or files
    rcmax = 0
    for rel in targets:
        rc, dt, out, err = compile_one(flags, rel)
        slow = [l for l in out.splitlines() if "secs" in l and _over_five(l)]
        print("%-58s rc=%d  %6.1f s  slow=%d" % (rel, rc, dt, len(slow)),
              flush=True)
        for l in slow:
            print("    " + l, flush=True)
        if rc != 0:
            sys.stdout.write(err)
            sys.stdout.flush()
            return rc
    return rcmax


if __name__ == "__main__":
    sys.exit(main())
