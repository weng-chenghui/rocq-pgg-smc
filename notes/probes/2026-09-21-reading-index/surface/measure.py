#!/usr/bin/env python3
"""Compile one measurement file against the surface before or after the
change, and save the compiler's message beside it.

    python3 measure.py before|after FILE [SLUG]

before drops the staged roots from the flags of ./_CoqProject, so that a
Require of pgg_tableau_syntax resolves to production's .vo and the file is
measured against the surface as it stands in the tree.  after keeps them, so
the same text is measured against the staged surface.

A token that has become a global keyword fails at parsing, and Fail does not
catch a parse error, so the outcome of a measurement is the exit status and
the message.  The message is written to msg/<slug>.<mode>.msg whether the
compile succeeded or failed, so that a pass and a failure leave the same
kind of record.
"""

import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LOCK = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
        "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")
SECONDS = "900"
MAXMB = "12000"


def flags(mode):
    out = []
    for raw in open(os.path.join(HERE, "_CoqProject")):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-arg "):
            out += [p for p in line.split() if p != "-arg"]
        elif line.startswith("-R ") or line.startswith("-Q "):
            if mode == "before" and line.split()[1].startswith("staged/"):
                continue
            out += line.split()
    return out


def main():
    mode, rel = sys.argv[1], sys.argv[2]
    slug = sys.argv[3] if len(sys.argv) > 3 else \
        os.path.basename(rel)[:-2] if rel.endswith(".v") else rel
    cmd = [LOCK, SECONDS, MAXMB, "rocq", "compile"] + flags(mode) + [rel]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)
    dt = time.time() - t0
    msgdir = os.path.join(HERE, "msg")
    os.makedirs(msgdir, exist_ok=True)
    path = os.path.join(msgdir, "%s.%s.msg" % (slug, mode))
    with open(path, "w") as f:
        f.write("$ rocq compile <flags of _CoqProject, %s> %s\n" % (mode, rel))
        f.write("exit status %d, %.1f s\n\n" % (p.returncode, dt))
        f.write(p.stdout)
        f.write(p.stderr)
    print("%-28s %-6s rc=%d  %5.1f s  -> msg/%s.%s.msg"
          % (rel, mode, p.returncode, dt, slug, mode))
    tail = (p.stdout + p.stderr).strip().split("\n")
    for l in tail[-12:]:
        print("    " + l)
    return 0


if __name__ == "__main__":
    sys.exit(main())
