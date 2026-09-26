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
TOOL_LOG="$TEST_ROOT/tool.log"
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
printf '%s\n' 'opam-version: "2.0"' > "$FIXTURE/rocq-pgg-smc.opam"
printf '%s\n' 'FROM example/base@sha256:0123' \
  'COPY dist/pgg-smc-flat.tar.gz /tmp/' > "$FIXTURE/Dockerfile"

printf '%s\n' \
  '#!/bin/sh' \
  'printf "%s\n" "$(basename "$0") $*" >> "$FLATTEN_TEST_TOOL_LOG"' \
  'exit 99' > "$SHIMS/opam"
cp "$SHIMS/opam" "$SHIMS/rocq"
cp "$SHIMS/opam" "$SHIMS/make"
chmod +x "$SHIMS/opam" "$SHIMS/rocq" "$SHIMS/make"

git -C "$FIXTURE" init -q -b main
git -C "$FIXTURE" config user.name 'Flatten Test'
git -C "$FIXTURE" config user.email 'flatten-test@example.invalid'
git -C "$FIXTURE" add -- .
git -C "$FIXTURE" commit -q -m 'fixture'
SOURCE_COMMIT="$(git -C "$FIXTURE" rev-parse HEAD)"

ARCHIVE="$OUTPUT/fixture-flat.tar.gz"
(
  cd "$FIXTURE"
  PATH="$SHIMS:$PATH" \
    FLATTEN_TEST_TOOL_LOG="$TOOL_LOG" \
    ./scripts/flatten_artifact.sh HEAD "$ARCHIVE"
)

test ! -e "$TOOL_LOG"
test "$(tar -tzf "$ARCHIVE" | LC_ALL=C sort | tr '\n' ' ')" = \
  '.dockerignore A.v B.v Dockerfile Makefile README.md _CoqProject rocq-pgg-smc.opam '
tar -xOf "$ARCHIVE" Makefile \
  | grep -F 'rocq makefile -f _CoqProject -o $(ROCQMAKEFILE)'
tar -xOf "$ARCHIVE" Makefile | grep -q '^	\$(RAISE_STACK); \$(MAKE)'
tar -xOf "$ARCHIVE" Makefile | grep -q '^docker-check: docker-build$'
tar -xOf "$ARCHIVE" Makefile | grep -F -- '--file Dockerfile --tag "$(DOCKER_IMAGE)" .'
tar -xOf "$ARCHIVE" Dockerfile | grep -Fx 'FROM example/base@sha256:0123'
tar -xOf "$ARCHIVE" Dockerfile | grep -Fx 'COPY . .'
tar -xOf "$ARCHIVE" Dockerfile | grep -F "revision=\"$SOURCE_COMMIT\""
if tar -xOf "$ARCHIVE" Dockerfile | grep -q 'dist/'; then
  printf 'flat Dockerfile unexpectedly reads a tarball\n' >&2
  exit 1
fi
tar -xOf "$ARCHIVE" .dockerignore | grep -Fx '*.vo'
if tar -xOf "$ARCHIVE" Makefile | grep -q 'flatten_artifact'; then
  printf 'flat Makefile unexpectedly refers to repository-only targets\n' >&2
  exit 1
fi
tar -xOf "$ARCHIVE" README.md \
  | grep -F "Source repository commit: \`$SOURCE_COMMIT\`"
tar -xOf "$ARCHIVE" README.md \
  | grep -F 'opam install ./rocq-pgg-smc.opam --deps-only'
tar -xOf "$ARCHIVE" A.v \
  | grep -F 'From pgg_smc Require Import B.'
if tar -tzf "$ARCHIVE" | grep -q '\.vo$'; then
  printf 'source archive unexpectedly contains compiled files\n' >&2
  exit 1
fi

printf 'flatten_artifact_test: PASS\n'
