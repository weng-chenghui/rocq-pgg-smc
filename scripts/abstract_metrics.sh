#!/usr/bin/env bash
# Pin the metrics quoted in wadt2026-abstract.tex.
# Exclusion rule: drop debug_*, *demo*, *test*, *solver* .v files.
# Comment-stripping recipe for code LOC: Python re.sub on (* ... *) with
# DOTALL, then drop empty lines.
#
# Pinned values (exact match required):
#   files                  = 75
#   LOC code-only          = 17408
#   theorems               = 43
#   corollaries            = 4
#   main = thm + cor       = 47
#
# Exit codes:
#   0  values match the pinned numbers
#   1  one or more values drift
#   2  pgg-smc directory not found
set -euo pipefail

PGG_SMC="$(cd "$(dirname "$0")/.." && pwd)"
if [ ! -d "$PGG_SMC" ]; then
  echo "ERROR: pgg-smc directory not found at $PGG_SMC" >&2
  exit 2
fi

PIN_FILES=75
PIN_LOC_CODE=17412
PIN_THEOREMS=42
PIN_COROLLARIES=4
PIN_EXCLUDED=(
  "security/debug_morph.v"
  "security/pgg_security_demo.v"
  "security/pgg_entropy_security_demo.v"
  "reconstruct/pgg_landscape_demo.v"
  "security/pgg_schreier_test.v"
  "security/pgg_security_solver.v"
)

cd "$PGG_SMC"

IN_SCOPE_LIST=$(
  find . -name '*.v' \
    -not -name 'debug_*' \
    -not -name '*demo*' \
    -not -name '*test*' \
    -not -name '*solver*' \
    | sed 's|^\./||' \
    | sort
)

FILES_COUNT=$(printf '%s\n' "$IN_SCOPE_LIST" | wc -l | tr -d ' ')

LOC_RAW=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  n=$(wc -l < "$f")
  LOC_RAW=$((LOC_RAW + n))
done <<< "$IN_SCOPE_LIST"

LOC_CODE=$(IN_SCOPE_LIST="$IN_SCOPE_LIST" python3 <<'PY'
import os, re, pathlib
total = 0
for path in os.environ['IN_SCOPE_LIST'].splitlines():
    if not path:
        continue
    src = pathlib.Path(path).read_text()
    src = re.sub(r'\(\*.*?\*\)', '', src, flags=re.DOTALL)
    total += sum(1 for line in src.splitlines() if line.strip())
print(total)
PY
)

THEOREMS=0
COROLLARIES=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  t=$(grep -cE '^[[:space:]]*Theorem[[:space:]]+[A-Za-z_]' "$f" || true)
  c=$(grep -cE '^[[:space:]]*Corollary[[:space:]]+[A-Za-z_]' "$f" || true)
  THEOREMS=$((THEOREMS + t))
  COROLLARIES=$((COROLLARIES + c))
done <<< "$IN_SCOPE_LIST"
MAIN=$((THEOREMS + COROLLARIES))

EXCLUDED_FOUND=""
for ex in "${PIN_EXCLUDED[@]}"; do
  if [ -f "$ex" ]; then
    EXCLUDED_FOUND="${EXCLUDED_FOUND}${ex}
"
  fi
done

cat <<EOF
files=$FILES_COUNT
LOC_raw=$LOC_RAW
LOC_code=$LOC_CODE
theorems=$THEOREMS
corollaries=$COROLLARIES
main=$MAIN

excluded files (must equal the six listed in abstract-metrics.md):
EOF
printf '%s' "$EXCLUDED_FOUND" | sed 's|^|  |'

DRIFT=0
[ "$FILES_COUNT"   -eq "$PIN_FILES" ]      || { echo "DRIFT: files: $FILES_COUNT != $PIN_FILES"; DRIFT=1; }
[ "$LOC_CODE"      -eq "$PIN_LOC_CODE" ]   || { echo "DRIFT: LOC_code: $LOC_CODE != $PIN_LOC_CODE"; DRIFT=1; }
[ "$THEOREMS"      -eq "$PIN_THEOREMS" ]   || { echo "DRIFT: theorems: $THEOREMS != $PIN_THEOREMS"; DRIFT=1; }
[ "$COROLLARIES"   -eq "$PIN_COROLLARIES" ]|| { echo "DRIFT: corollaries: $COROLLARIES != $PIN_COROLLARIES"; DRIFT=1; }

if [ "$DRIFT" -ne 0 ]; then
  echo
  echo "Abstract metrics no longer match wadt2026-abstract.tex." >&2
  echo "Either update the abstract or update the pinned values." >&2
  exit 1
fi
