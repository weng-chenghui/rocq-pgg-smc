#!/bin/bash
#
# Compile a flat Rocq source archive and package its source and compiled files.
#
# Usage:
#   scripts/build_flat_artifact.sh SOURCE_TARBALL OUT_BUILT_TARBALL

set -euo pipefail

log() {
  printf '[build_flat_artifact] %s\n' "$*" >&2
}

fail() {
  printf '[build_flat_artifact] FATAL: %s\n' "$*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
MAIN_REPO_ROOT="$(
  realpath "$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"
)"

normalize_absolute_path() {
  awk -v path="$1" 'BEGIN {
    count = split(path, part, "/")
    top = 0
    for (i = 1; i <= count; i++) {
      if (part[i] == "" || part[i] == ".")
        continue
      if (part[i] == "..") {
        if (top > 0)
          top--
        continue
      }
      component[++top] = part[i]
    }
    result = "/"
    for (i = 1; i <= top; i++) {
      if (i > 1)
        result = result "/"
      result = result component[i]
    }
    print result
  }'
}

resolve_output_path() {
  local candidate="$1"
  local ancestor="$candidate"
  local suffix=""
  local component

  if [[ -L "$candidate" && ! -e "$candidate" ]]; then
    fail "archive path is a dangling symbolic link: $candidate"
  fi
  if [[ -e "$candidate" ]]; then
    realpath "$candidate"
    return
  fi
  while [[ ! -e "$ancestor" ]]; do
    component="$(basename "$ancestor")"
    suffix="/${component}${suffix}"
    ancestor="$(dirname "$ancestor")"
  done
  normalize_absolute_path "$(realpath "$ancestor")${suffix}"
}

[[ "$#" -eq 2 ]] \
  || fail "expected SOURCE_TARBALL and OUT_BUILT_TARBALL"

INVOCATION_DIR="$(pwd -P)"
SOURCE_TARBALL="$1"
OUT_BUILT_TARBALL="$2"
if [[ "$SOURCE_TARBALL" != /* ]]; then
  SOURCE_TARBALL="${INVOCATION_DIR}/${SOURCE_TARBALL}"
fi
SOURCE_TARBALL="$(realpath "$SOURCE_TARBALL")"
[[ -f "$SOURCE_TARBALL" ]] \
  || fail "source archive is not a file: $SOURCE_TARBALL"

if [[ "$OUT_BUILT_TARBALL" != /* ]]; then
  OUT_BUILT_TARBALL="${INVOCATION_DIR}/${OUT_BUILT_TARBALL}"
fi
OUT_BUILT_TARBALL="$(
  resolve_output_path "$(normalize_absolute_path "$OUT_BUILT_TARBALL")"
)"
[[ ! -d "$OUT_BUILT_TARBALL" ]] \
  || fail "built archive path names an existing directory: $OUT_BUILT_TARBALL"
[[ "$OUT_BUILT_TARBALL" != "$SOURCE_TARBALL" ]] \
  || fail "built archive path must differ from the source archive"

GIT_DIR_ABS="$(
  realpath "$(git -C "$MAIN_REPO_ROOT" rev-parse --absolute-git-dir)"
)"
case "$OUT_BUILT_TARBALL" in
  "$GIT_DIR_ABS"|"$GIT_DIR_ABS"/*)
    fail "built archive path must not be inside Git metadata"
    ;;
esac
case "$OUT_BUILT_TARBALL" in
  "$MAIN_REPO_ROOT"/*)
    OUTPUT_REPO_PATH="${OUT_BUILT_TARBALL#"$MAIN_REPO_ROOT"/}"
    if git -C "$MAIN_REPO_ROOT" ls-files --error-unmatch \
      -- "$OUTPUT_REPO_PATH" >/dev/null 2>&1; then
      fail "built archive path names a tracked file: $OUTPUT_REPO_PATH"
    fi
    ;;
esac

ROCQ_JOBS="${ROCQ_JOBS:-1}"
case "$ROCQ_JOBS" in
  ''|*[!0-9]*|0)
    fail "ROCQ_JOBS must be a positive integer"
    ;;
esac

TIMESTAMP="$(date +%Y%m%d-%H%M%S)"
BASE_TMP="${TMPDIR:-/tmp}"
BASE_TMP="${BASE_TMP%/}"
BUILD_DIR="${BASE_TMP}/build-flat-artifact-${TIMESTAMP}-$$"
BUILD_LOG="${BASE_TMP}/build-flat-artifact-${TIMESTAMP}-$$.log"
SOURCE_TAR_LIST="${BASE_TMP}/build-flat-source-tar-${TIMESTAMP}-$$.txt"
BUILT_TAR_LIST="${BASE_TMP}/build-flat-built-tar-${TIMESTAMP}-$$.txt"
BUILT_ARCHIVE_TMP="${BASE_TMP}/pgg-smc-built-${TIMESTAMP}-$$.tar.gz"

cleanup() {
  local ec=$?
  rm -rf "$BUILD_DIR"
  if [[ "$ec" -eq 0 ]]; then
    rm -f "$BUILD_LOG" "$SOURCE_TAR_LIST" "$BUILT_TAR_LIST"
  fi
  rm -f "$BUILT_ARCHIVE_TMP"
  return "$ec"
}
trap cleanup EXIT

tar -tzf "$SOURCE_TARBALL" > "$SOURCE_TAR_LIST" \
  || fail "could not read source archive"
if grep -q '/' "$SOURCE_TAR_LIST"; then
  fail "source archive contains a path below the flat root"
fi
if grep -q '^legacy' "$SOURCE_TAR_LIST"; then
  fail "source archive contains a legacy entry"
fi
grep -Fxq '_CoqProject' "$SOURCE_TAR_LIST" \
  || fail "source archive has no _CoqProject"
grep -Fxq 'ARTIFACT-README.txt' "$SOURCE_TAR_LIST" \
  || fail "source archive has no ARTIFACT-README.txt"

mkdir -p "$BUILD_DIR"
tar -xzf "$SOURCE_TARBALL" -C "$BUILD_DIR" \
  || fail "could not extract source archive"
cd "$BUILD_DIR"

VFILES=()
while IFS= read -r source; do
  [[ -z "$source" ]] && continue
  VFILES+=("$source")
done < <(sed -E 's/[[:space:]]+$//' _CoqProject | grep -E '^[^[:space:]]+\.v$')
[[ "${#VFILES[@]}" -gt 0 ]] || fail "_CoqProject lists no Rocq source files"
for source in "${VFILES[@]}"; do
  [[ "$source" != */* ]] || fail "source is not flat: $source"
  [[ -f "$source" ]] || fail "source is missing: $source"
done

command -v opam >/dev/null 2>&1 || fail "opam is not available"
OPAM_SWITCH_DIR="${ROCQ_OPAM_SWITCH:-$(opam switch show --safe)}"
log "activating opam switch at $OPAM_SWITCH_DIR"
eval "$(opam env --switch="$OPAM_SWITCH_DIR" --set-switch)" \
  || fail "could not activate opam switch at $OPAM_SWITCH_DIR"
command -v rocq >/dev/null 2>&1 \
  || fail "rocq is unavailable after activating the opam switch"

rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
rocq makefile -f _CoqProject -o Makefile.coq \
  || fail "rocq makefile failed"
log "building the flattened project with $ROCQ_JOBS job(s)"
if ! make -f Makefile.coq -j"$ROCQ_JOBS" > "$BUILD_LOG" 2>&1; then
  log "build failed; tail of $BUILD_LOG:"
  tail -n 200 "$BUILD_LOG" >&2
  fail "the flattened project does not compile"
fi
log "build succeeded"
rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

BUILT_ENTRIES=()
for source in "${VFILES[@]}"; do
  stem="${source%.v}"
  [[ -f "${stem}.vo" ]] || fail "compiled output '${stem}.vo' is missing"
  BUILT_ENTRIES+=("${stem}.vo")
  for suffix in glob vos vok; do
    [[ -f "${stem}.${suffix}" ]] && BUILT_ENTRIES+=("${stem}.${suffix}")
  done
  [[ -f ".${stem}.aux" ]] && BUILT_ENTRIES+=(".${stem}.aux")
done

cat > ARTIFACT-README.txt <<EOF
This built archive contains the flat Rocq sources and their compiled files.
_CoqProject maps this directory to the logical root 'pgg_smc'.

The files were compiled with:
    rocq makefile -f _CoqProject -o Makefile.coq
    make -f Makefile.coq -j${ROCQ_JOBS}

The generated Makefile is not included.  This archive was created on
$(date -u +%Y-%m-%dT%H:%M:%SZ).  The complete legacy/ directory is excluded.
EOF

COPYFILE_DISABLE=1 tar --no-xattrs -czf "$BUILT_ARCHIVE_TMP" \
  "${VFILES[@]}" _CoqProject ARTIFACT-README.txt "${BUILT_ENTRIES[@]}" \
  || fail "could not create temporary built archive"
tar -tzf "$BUILT_ARCHIVE_TMP" > "$BUILT_TAR_LIST" \
  || fail "could not read temporary built archive"
if grep -q '/' "$BUILT_TAR_LIST"; then
  fail "built archive contains a path below the flat root"
fi
if grep -q '^legacy' "$BUILT_TAR_LIST"; then
  fail "built archive contains a legacy entry"
fi

mkdir -p "$(dirname "$OUT_BUILT_TARBALL")"
mv -f "$BUILT_ARCHIVE_TMP" "$OUT_BUILT_TARBALL"

cat <<SUMMARY

=== build_flat_artifact.sh: done ===
Source archive:   $SOURCE_TARBALL
Built archive:    $OUT_BUILT_TARBALL
Rocq file count:  ${#VFILES[@]}
Built entries:    $(wc -l < "$BUILT_TAR_LIST" | tr -d '[:space:]')
SUMMARY
