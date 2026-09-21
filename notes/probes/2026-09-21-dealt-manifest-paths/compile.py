#!/usr/bin/env python3
"""Compile one staged file of this probe through the session lock.

usage: compile.py SECONDS MAXMB FILE [FILE...]

The load-path flags are the -R/-Q lines of ./_CoqProject and its -arg lines
with every word -arg dropped.  Staged roots come last, so a staged copy
shadows the production module of the same name.
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SP = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/"
      "493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad")


def flags():
    out = []
    for line in open(os.path.join(HERE, "_CoqProject")):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        w = line.split()
        if w[0] == "-arg":
            out += [x for x in w if x != "-arg"]
        elif w[0] in ("-R", "-Q"):
            out += w
    return out


def main():
    secs, mb, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    fl = flags()
    for f in files:
        cmd = [os.path.join(SP, "rocq1"), secs, mb, "rocq", "compile"] + fl + [f]
        t0 = time.time()
        p = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)
        dt = time.time() - t0
        print(f"=== {f}  rc={p.returncode}  {dt:.1f}s")
        if p.stdout.strip():
            print(p.stdout[-8000:])
        if p.stderr.strip():
            print(p.stderr[-8000:])
        if p.returncode != 0:
            sys.exit(p.returncode)


main()
