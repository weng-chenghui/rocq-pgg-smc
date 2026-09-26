#!/bin/bash

set -euo pipefail

SCRIPT_UNDER_TEST="${1:-scripts/build_flat_artifact.sh}"
SCRIPT_UNDER_TEST="$(cd "$(dirname "$SCRIPT_UNDER_TEST")" && pwd -P)/$(basename "$SCRIPT_UNDER_TEST")"
TEST_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/build-flat-artifact-test.XXXXXX")"

cleanup() {
  rm -rf "$TEST_ROOT"
}
trap cleanup EXIT

FIXTURE="$TEST_ROOT/repository"
SOURCE_DIR="$TEST_ROOT/source"
SHIMS="$TEST_ROOT/shims"
OUTPUT="$TEST_ROOT/output"
MAKE_LOG="$TEST_ROOT/make.log"
mkdir -p "$FIXTURE/scripts" "$SOURCE_DIR" "$SHIMS" "$OUTPUT"

cp "$SCRIPT_UNDER_TEST" "$FIXTURE/scripts/build_flat_artifact.sh"
chmod +x "$FIXTURE/scripts/build_flat_artifact.sh"
SCRIPT_UNDER_TEST="$FIXTURE/scripts/build_flat_artifact.sh"
printf '%s\n' 'preserve this tracked file' > "$FIXTURE/protected.txt"
git -C "$FIXTURE" init -q -b main
git -C "$FIXTURE" config user.name 'Build Flat Test'
git -C "$FIXTURE" config user.email 'build-flat-test@example.invalid'
git -C "$FIXTURE" add -- .
git -C "$FIXTURE" commit -q -m 'fixture'

printf '%s\n' '-Q . pgg_smc' 'A.v' 'B.v' > "$SOURCE_DIR/_CoqProject"
printf '%s\n' 'From pgg_smc Require Import B.' > "$SOURCE_DIR/A.v"
printf '%s\n' 'Definition b := true.' > "$SOURCE_DIR/B.v"
printf '%s\n' 'flat source fixture' > "$SOURCE_DIR/README.md"
printf '%s\n' 'all:' > "$SOURCE_DIR/Makefile"
SOURCE_ARCHIVE="$OUTPUT/fixture-flat.tar.gz"
COPYFILE_DISABLE=1 tar --no-xattrs -czf "$SOURCE_ARCHIVE" -C "$SOURCE_DIR" \
  A.v B.v _CoqProject Makefile README.md

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
  'printf "%s\n" "$*" >> "$BUILD_FLAT_TEST_MAKE_LOG"' \
  'while IFS= read -r source; do' \
  '  case "$source" in' \
  '    *.v) : > "${source%.v}.vo" ;;' \
  '  esac' \
  'done < _CoqProject' > "$SHIMS/make"
chmod +x "$SHIMS/opam" "$SHIMS/rocq" "$SHIMS/make"

BUILT_ARCHIVE="$OUTPUT/fixture-built.tar.gz"
PATH="$SHIMS:$PATH" \
  BUILD_FLAT_TEST_MAKE_LOG="$MAKE_LOG" \
  ROCQ_OPAM_SWITCH=test-switch \
  ROCQ_JOBS=1 \
  "$SCRIPT_UNDER_TEST" "$SOURCE_ARCHIVE" "$BUILT_ARCHIVE"

grep -Fx -- '-f Makefile.coq -j1' "$MAKE_LOG"
tar -tzf "$BUILT_ARCHIVE" | grep -Fx 'A.vo'
tar -tzf "$BUILT_ARCHIVE" | grep -Fx 'B.vo'
tar -tzf "$BUILT_ARCHIVE" | grep -Fx 'Makefile'
tar -tzf "$BUILT_ARCHIVE" | grep -Fx 'README.md'
if tar -tzf "$BUILT_ARCHIVE" | grep -Eq '(^|/)Makefile\.coq'; then
  printf 'built archive unexpectedly contains generated Makefile files\n' >&2
  exit 1
fi
test "$(tar -xOf "$SOURCE_ARCHIVE" A.v | shasum -a 256)" = \
  "$(tar -xOf "$BUILT_ARCHIVE" A.v | shasum -a 256)"
test "$(tar -xOf "$SOURCE_ARCHIVE" _CoqProject | shasum -a 256)" = \
  "$(tar -xOf "$BUILT_ARCHIVE" _CoqProject | shasum -a 256)"

PROTECTED_HASH="$(shasum -a 256 "$FIXTURE/protected.txt")"
for protected_output in \
  "$FIXTURE/protected.txt" \
  "$FIXTURE/.git/config" \
  "$SOURCE_ARCHIVE"; do
  PROTECTED_LOG="$TEST_ROOT/protected-$(basename "$protected_output").log"
  if PATH="$SHIMS:$PATH" \
    BUILD_FLAT_TEST_MAKE_LOG="$MAKE_LOG" \
    ROCQ_OPAM_SWITCH=test-switch \
    ROCQ_JOBS=1 \
    "$SCRIPT_UNDER_TEST" "$SOURCE_ARCHIVE" \
      "$protected_output" > "$PROTECTED_LOG" 2>&1; then
    printf 'protected output path unexpectedly succeeded: %s\n' \
      "$protected_output" >&2
    exit 1
  fi
done
test "$PROTECTED_HASH" = "$(shasum -a 256 "$FIXTURE/protected.txt")"

for invalid_jobs in 0 two; do
  INVALID_LOG="$TEST_ROOT/invalid-${invalid_jobs}.log"
  if PATH="$SHIMS:$PATH" \
    BUILD_FLAT_TEST_MAKE_LOG="$MAKE_LOG" \
    ROCQ_OPAM_SWITCH=test-switch \
    ROCQ_JOBS="$invalid_jobs" \
    "$SCRIPT_UNDER_TEST" "$SOURCE_ARCHIVE" \
      "$OUTPUT/invalid-${invalid_jobs}.tar.gz" > "$INVALID_LOG" 2>&1; then
    printf 'ROCQ_JOBS=%s unexpectedly succeeded\n' "$invalid_jobs" >&2
    exit 1
  fi
  grep -F 'ROCQ_JOBS must be a positive integer' "$INVALID_LOG"
done

printf 'build_flat_artifact_test: PASS\n'
