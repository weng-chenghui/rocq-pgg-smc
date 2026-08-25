#!/usr/bin/env python3
"""One-shot: move plain-Require'd infotheo modules under From infotheo."""
import re, sys, pathlib

INFOTHEO = {  # modules resolving into installed infotheo (allowed surface)
    "realType_ext", "ssr_ext", "ssralg_ext", "fdist", "proba",
    "jfdist_cond", "entropy", "dft", "hamming", "linearcode",
    "pismc", "reed_solomon", "smc_interpreter", "smc_session_types",
}
BANNED = {  # handled by Tasks 4-5, never qualified here
    "entropy_fiber", "extra_proba", "extra_entropy", "rouche_capelli",
    "spp_proba", "spp_entropy",
}
pat = re.compile(r"^Require (Import|Export) ([^.]+)\.\s*$")
changed = []
for p in sorted(pathlib.Path(".").rglob("*.v")):
    if ".git" in p.parts:
        continue
    lines, out, touched = p.read_text().splitlines(True), [], False
    for line in lines:
        m = pat.match(line)
        if not m:
            out.append(line)
            continue
        kind, mods = m.group(1), m.group(2).split()
        info = [x for x in mods if x in INFOTHEO]
        rest = [x for x in mods if x not in INFOTHEO]
        if not info:
            out.append(line)
            continue
        touched = True
        out.append(f"From infotheo Require {kind} {' '.join(info)}.\n")
        if rest:
            out.append(f"Require {kind} {' '.join(rest)}.\n")
    if touched:
        p.write_text("".join(out))
        changed.append(str(p))
print("\n".join(changed), file=sys.stderr)
print(f"{len(changed)} files rewritten", file=sys.stderr)
