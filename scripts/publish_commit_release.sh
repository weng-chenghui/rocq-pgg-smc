#!/bin/bash

set -euo pipefail

fail() {
  printf '[publish_commit_release] FATAL: %s\n' "$*" >&2
  exit 1
}

[[ "$#" -eq 4 ]] \
  || fail "expected MODE REPOSITORY COMMIT ARTIFACT"

MODE="$1"
REPOSITORY="$2"
COMMIT="$3"
ARTIFACT="$4"

[[ "$REPOSITORY" == */* ]] || fail "repository must have OWNER/NAME form"
[[ "$COMMIT" =~ ^[0-9a-f]{40}$ ]] || fail "commit must be a full Git SHA"
command -v gh >/dev/null 2>&1 || fail "gh is not available"

RELEASE_TAG="wadt2026-${COMMIT}"
RELEASE_TITLE="WADT2026 ${COMMIT:0:12}"

source_asset_exists() {
  gh release view "$RELEASE_TAG" \
    --repo "$REPOSITORY" \
    --json assets \
    --jq '.assets[].name' \
    | grep -Fxq "$SOURCE_NAME"
}

ensure_source_asset() {
  if source_asset_exists; then
    printf 'kept existing source asset %s on release %s\n' \
      "$SOURCE_NAME" "$RELEASE_TAG"
    return
  fi
  if gh release upload "$RELEASE_TAG" "$ARTIFACT" --repo "$REPOSITORY"; then
    return
  fi
  source_asset_exists \
    || fail "source asset could not be added to release $RELEASE_TAG"
}

case "$MODE" in
  source)
    [[ -f "$ARTIFACT" ]] || fail "source archive is not a file: $ARTIFACT"
    SOURCE_NAME="$(basename "$ARTIFACT")"
    SOURCE_NOTES="Flattened Rocq sources for commit \`${COMMIT}\`.

The Docker package is still being built. This release will be updated with
its immutable GHCR digest when the build finishes."
    if gh release view "$RELEASE_TAG" --repo "$REPOSITORY" >/dev/null 2>&1; then
      ensure_source_asset
    else
      if gh release create "$RELEASE_TAG" "$ARTIFACT" \
        --repo "$REPOSITORY" \
        --target "$COMMIT" \
        --title "$RELEASE_TITLE" \
        --notes "$SOURCE_NOTES" \
        --prerelease \
        --latest=false; then
        :
      else
        gh release view "$RELEASE_TAG" --repo "$REPOSITORY" >/dev/null 2>&1 \
          || fail "release could not be created: $RELEASE_TAG"
        ensure_source_asset
      fi
    fi
    printf 'published source asset %s on release %s\n' \
      "$SOURCE_NAME" "$RELEASE_TAG"
    ;;
  image)
    [[ "$ARTIFACT" =~ ^ghcr\.io/.+@sha256:[0-9a-f]{64}$ ]] \
      || fail "image must be an immutable GHCR digest reference"
    gh release view "$RELEASE_TAG" --repo "$REPOSITORY" >/dev/null 2>&1 \
      || fail "source release does not exist: $RELEASE_TAG"
    IMAGE_NOTES="Flattened Rocq sources and a compiled Docker package for
commit \`${COMMIT}\`.

The flattened source tar is attached to this release.

Docker package:

\`\`\`shell
docker pull ${ARTIFACT}
docker run --rm -it ${ARTIFACT} sh
\`\`\`

Platform: \`linux/amd64\`."
    gh release edit "$RELEASE_TAG" \
      --repo "$REPOSITORY" \
      --title "$RELEASE_TITLE" \
      --notes "$IMAGE_NOTES" \
      --prerelease \
      --latest=false
    printf 'recorded image %s on release %s\n' "$ARTIFACT" "$RELEASE_TAG"
    ;;
  *)
    fail "mode must be source or image"
    ;;
esac
