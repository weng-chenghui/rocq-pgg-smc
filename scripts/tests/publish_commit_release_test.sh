#!/bin/bash

set -euo pipefail

SCRIPT_UNDER_TEST="${1:-scripts/publish_commit_release.sh}"
SCRIPT_UNDER_TEST="$(cd "$(dirname "$SCRIPT_UNDER_TEST")" && pwd -P)/$(basename "$SCRIPT_UNDER_TEST")"
TEST_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/publish-release-test.XXXXXX")"

cleanup() {
  rm -rf "$TEST_ROOT"
}
trap cleanup EXIT

SHIMS="$TEST_ROOT/shims"
LOG="$TEST_ROOT/gh.log"
mkdir -p "$SHIMS"

cat > "$SHIMS/gh" <<'EOF'
#!/bin/bash
set -euo pipefail
printf '%q ' "$@" >> "$RELEASE_TEST_LOG"
printf '\n' >> "$RELEASE_TEST_LOG"
printf '%s\n' "$@" >> "$RELEASE_TEST_LOG"
if [[ "${1:-}" == release && "${2:-}" == view ]]; then
  if [[ "${RELEASE_TEST_CREATE_RACE:-0}" == 1 && -f "$RELEASE_TEST_STATE/created" ]]; then
    if [[ "$*" == *"--json assets"* && "${RELEASE_TEST_ASSET_EXISTS:-0}" == 1 ]]; then
      printf '%s\n' "$RELEASE_TEST_ASSET_NAME"
    fi
    exit 0
  fi
  if [[ "${RELEASE_TEST_EXISTS:-0}" == 1 ]]; then
    if [[ "$*" == *"--json assets"* && "${RELEASE_TEST_ASSET_EXISTS:-0}" == 1 ]]; then
      printf '%s\n' "$RELEASE_TEST_ASSET_NAME"
    fi
    exit 0
  fi
  exit 1
fi
if [[ "${1:-}" == release && "${2:-}" == create && "${RELEASE_TEST_CREATE_RACE:-0}" == 1 ]]; then
  touch "$RELEASE_TEST_STATE/created"
  exit 1
fi
EOF
chmod +x "$SHIMS/gh"

SHA=0123456789abcdef0123456789abcdef01234567
REPO=weng-chenghui/rocq-pgg-smc
ARCHIVE="$TEST_ROOT/rocq-pgg-smc-flat-$SHA.tar.gz"
touch "$ARCHIVE"

PATH="$SHIMS:$PATH" RELEASE_TEST_LOG="$LOG" RELEASE_TEST_EXISTS=0 \
  RELEASE_TEST_STATE="$TEST_ROOT" \
  "$SCRIPT_UNDER_TEST" source "$REPO" "$SHA" "$ARCHIVE"
grep -Fq "release view wadt2026-$SHA" "$LOG"
grep -Fq "release create wadt2026-$SHA" "$LOG"
grep -Fq -- "--target $SHA" "$LOG"
grep -Fq -- "--prerelease" "$LOG"
grep -Fq -- "--latest=false" "$LOG"

: > "$LOG"
PATH="$SHIMS:$PATH" RELEASE_TEST_LOG="$LOG" RELEASE_TEST_EXISTS=1 \
  RELEASE_TEST_ASSET_EXISTS=1 RELEASE_TEST_ASSET_NAME="$(basename "$ARCHIVE")" \
  RELEASE_TEST_STATE="$TEST_ROOT" \
  "$SCRIPT_UNDER_TEST" source "$REPO" "$SHA" "$ARCHIVE"
if grep -Fq "release upload" "$LOG"; then
  printf 'existing source asset was replaced\n' >&2
  exit 1
fi
if grep -Fq "release create" "$LOG"; then
  printf 'existing release was created again\n' >&2
  exit 1
fi

: > "$LOG"
rm -f "$TEST_ROOT/created"
PATH="$SHIMS:$PATH" RELEASE_TEST_LOG="$LOG" RELEASE_TEST_EXISTS=0 \
  RELEASE_TEST_CREATE_RACE=1 RELEASE_TEST_ASSET_EXISTS=0 \
  RELEASE_TEST_ASSET_NAME="$(basename "$ARCHIVE")" \
  RELEASE_TEST_STATE="$TEST_ROOT" \
  "$SCRIPT_UNDER_TEST" source "$REPO" "$SHA" "$ARCHIVE"
grep -Fq "release create wadt2026-$SHA" "$LOG"
grep -Fq "release upload wadt2026-$SHA" "$LOG"

: > "$LOG"
IMAGE="ghcr.io/$REPO@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
PATH="$SHIMS:$PATH" RELEASE_TEST_LOG="$LOG" RELEASE_TEST_EXISTS=1 \
  RELEASE_TEST_STATE="$TEST_ROOT" \
  "$SCRIPT_UNDER_TEST" image "$REPO" "$SHA" "$IMAGE"
grep -Fq "release edit wadt2026-$SHA" "$LOG"
grep -Fq "$IMAGE" "$LOG"
grep -Fq "docker pull" "$LOG"

printf 'publish_commit_release_test: PASS\n'
