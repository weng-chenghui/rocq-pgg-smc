# Incremental commit release

Each `main` commit has one prerelease named by its full commit SHA. The source
archive appears as soon as flattening finishes. The longer Docker build then
adds an immutable container digest to that same release.

```text
object commit SHA                              // published artifacts: 0
flatten SHA via flatten_artifact.sh            // published artifacts: source tar
release wadt2026-SHA via GitHub Releases       // published artifacts: source tar
build source tar via Dockerfile                // published artifacts: source tar
push image via GHCR                            // published artifacts: source tar + image
update wadt2026-SHA via GitHub Releases        // published artifacts: source tar + image digest
```

The repeated operation adds one artifact while preserving the commit SHA. The
flow is indexed by the commit before and after each step. It therefore follows
the useful part of a parameterised monad rather than a plain monad. Composition
is valid only when every stage uses the same SHA.

GitHub Releases receives the source tar through `gh release`. GHCR receives
the compiled image through the Docker registry interface. The Dockerfile
installs the flattened development during image construction, so starting a
container never triggers compilation. The old compiled-source tar remains a
local diagnostic format and is outside this release flow.

The release helper is idempotent. A repeated source job keeps the first source
asset and does not create another release. The image job downloads that asset
from the release before it builds. A repeated image job rewrites the release
notes with the current immutable digest. Runs for the same commit are serial,
so they do not race while creating the release.
