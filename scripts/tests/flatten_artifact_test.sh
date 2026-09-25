#!/bin/bash

set -euo pipefail

SCRIPT_UNDER_TEST="${1:-scripts/flatten_artifact.sh}"
SCRIPT_UNDER_TEST="$(cd "$(dirname "$SCRIPT_UNDER_TEST")" && pwd -P)/$(basename "$SCRIPT_UNDER_TEST")"
TEST_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/flatten-artifact-test.XXXXXX")"

cleanup() {
  rm -rf "$TEST_ROOT"
}
trap cleanup EXIT

FIXTURE="$TEST_ROOT/repository"
SHIMS="$TEST_ROOT/shims"
OUTPUT="$TEST_ROOT/output"
MAKE_LOG="$TEST_ROOT/make.log"
mkdir -p "$FIXTURE/scripts" "$FIXTURE/lib" "$FIXTURE/reconstruct" \
  "$SHIMS" "$OUTPUT"

cp "$SCRIPT_UNDER_TEST" "$FIXTURE/scripts/flatten_artifact.sh"
chmod +x "$FIXTURE/scripts/flatten_artifact.sh"

printf '%s\n' \
  '-R lib pgg_smc' \
  '-R reconstruct pgg_reconstruct' \
  'lib/A.v' \
  'reconstruct/B.v' > "$FIXTURE/_CoqProject"
printf '%s\n' 'From pgg_reconstruct Require Import B.' > "$FIXTURE/lib/A.v"
printf '%s\n' 'Definition b := true.' > "$FIXTURE/reconstruct/B.v"

printf '%s\n' \
  '#!/bin/sh' \
  'if [ "${1:-}" = env ]; then exit 0; fi' \
  'exit 1' > "$SHIMS/opam"
printf '%s\n' \
  '#!/bin/sh' \
  'if [ "${1:-}" = makefile ]; then : > Makefile.coq; exit 0; fi' \
  'exit 1' > "$SHIMS/rocq"
printf '%s\n' \
  '#!/bin/sh' \
  'printf "%s\n" "$*" >> "$FLATTEN_TEST_MAKE_LOG"' \
  'while IFS= read -r source; do' \
  '  case "$source" in' \
  '    *.v) : > "${source%.v}.vo" ;;' \
  '  esac' \
  'done < _CoqProject' > "$SHIMS/make"
chmod +x "$SHIMS/opam" "$SHIMS/rocq" "$SHIMS/make"

git -C "$FIXTURE" init -q -b main
git -C "$FIXTURE" config user.name 'Flatten Test'
git -C "$FIXTURE" config user.email 'flatten-test@example.invalid'
git -C "$FIXTURE" add -- .
git -C "$FIXTURE" commit -q -m 'fixture'

ARCHIVE="$OUTPUT/fixture-flat.tar.gz"
BUILT_ARCHIVE="$OUTPUT/fixture-built.tar.gz"
(
  cd "$FIXTURE"
  PATH="$SHIMS:$PATH" \
    FLATTEN_TEST_MAKE_LOG="$MAKE_LOG" \
    ROCQ_OPAM_SWITCH=test-switch \
    FLATTEN_JOBS=1 \
    ./scripts/flatten_artifact.sh HEAD "$ARCHIVE" "$BUILT_ARCHIVE"
)

grep -Fx -- '-f Makefile.coq -j1' "$MAKE_LOG"
tar -xOf "$ARCHIVE" ARTIFACT-README.txt \
  | grep -F 'make -f Makefile.coq -j1'
tar -xOf "$ARCHIVE" A.v \
  | grep -F 'From pgg_smc Require Import B.'
if tar -tzf "$ARCHIVE" | grep -q '\.vo$'; then
  printf 'source archive unexpectedly contains compiled files\n' >&2
  exit 1
fi
tar -tzf "$BUILT_ARCHIVE" | grep -Fx 'A.vo'
tar -tzf "$BUILT_ARCHIVE" | grep -Fx 'B.vo'
test "$(tar -xOf "$ARCHIVE" A.v | shasum -a 256)" = \
  "$(tar -xOf "$BUILT_ARCHIVE" A.v | shasum -a 256)"
test "$(tar -xOf "$ARCHIVE" _CoqProject | shasum -a 256)" = \
  "$(tar -xOf "$BUILT_ARCHIVE" _CoqProject | shasum -a 256)"

for invalid_jobs in 0 two; do
  INVALID_LOG="$TEST_ROOT/invalid-${invalid_jobs}.log"
  if (
    cd "$FIXTURE"
    PATH="$SHIMS:$PATH" \
      FLATTEN_TEST_MAKE_LOG="$MAKE_LOG" \
      ROCQ_OPAM_SWITCH=test-switch \
      FLATTEN_JOBS="$invalid_jobs" \
      ./scripts/flatten_artifact.sh HEAD \
        "$OUTPUT/invalid-${invalid_jobs}.tar.gz"
  ) > "$INVALID_LOG" 2>&1; then
    printf 'FLATTEN_JOBS=%s unexpectedly succeeded\n' "$invalid_jobs" >&2
    exit 1
  fi
  grep -F 'FLATTEN_JOBS must be a positive integer' "$INVALID_LOG"
done

printf 'flatten_artifact_test: PASS\n'
