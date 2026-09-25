# GitHub Flattened Build Design

## Goal

Publish the existing source repository as the public GitHub repository
`weng-chenghui/rocq-pgg-smc`. Every push to `main` must first publish the
flattened non-legacy Rocq sources, then compile that exact archive and publish a
second built archive. The `WADT2026` tag is created only after both jobs succeed.

## Problem

The source archive must not wait for the expensive Rocq build. Otherwise an
installation or compilation failure also prevents publication of the already
valid flattened sources. The workflow therefore separates source preparation
from compilation and passes the source archive between the two jobs.

The flattened tree is a build output.  It must not become a second repository
or a maintained branch on GitHub.

## Repository Publication

The existing `main` history is published without rewriting it.  The new remote
is named `origin` and points to the public repository
`https://github.com/weng-chenghui/rocq-pgg-smc`.  Only committed content is
pushed.  Existing staged and untracked local files outside this work remain
local.

The implementation commit is restricted by explicit paths.  Its staged-file
list is checked before and after committing so the existing staged deletion is
not included.  Publication uses an explicit `main:main` push.  It never uses a
command that pushes every local branch because generated `flat-artifact-*`
branches already exist locally.

The implementation commit contains the workflow and the flatten script needed
by that workflow.  The script is currently untracked, so publishing it is part
of this work.

## Workflow

`.github/workflows/flattened-build.yml` runs on each push to `main` with
read-only repository permissions. It has two jobs.

The `flatten-source` job checks out the pushed commit, configures the temporary
Git identity, runs `scripts/flatten_artifact.sh`, and uploads the dated source
tarball. It does not start Rocq, opam, or `make`.

The `build-flattened` job depends on `flatten-source`. It runs in the pinned
MathComp 2.5.0 and Rocq 9.0 image, checks out the repository to obtain the opam
manifest and build helper, and installs only the missing dependencies. It then
downloads the source artifact, compiles it with one job through
`scripts/build_flat_artifact.sh`, and uploads the dated built tarball.

Official third-party actions are pinned to immutable commit SHAs.  Their major
release names are recorded in comments so future updates are deliberate.

## Script Interfaces

`scripts/flatten_artifact.sh` keeps its existing positional interface:

```text
scripts/flatten_artifact.sh SOURCE_REF OUT_TARBALL
```

This script only rewrites and archives the source tree. It does not require a
Rocq installation.

The build helper consumes that archive directly:

```text
scripts/build_flat_artifact.sh SOURCE_TARBALL OUT_BUILT_TARBALL
```

It accepts `ROCQ_JOBS`, which defaults to `1`. It requires every `.v` file to
produce a matching `.vo`, retains optional Rocq side files, and excludes the
generated Makefile and environment-specific configuration.

The macOS-only in-place `sed` call is replaced by a portable rewrite to a
temporary file followed by `mv`.  The rewritten content remains identical on
macOS, Alpine Linux, and Ubuntu.

The second job passes `ROCQ_OPAM_SWITCH` from the active switch in the MathComp
image. No GitHub-specific switch path is embedded in the helper.

## Resource Handling

The build runs sequentially because individual Rocq files already use
substantial memory. The second job raises the stack limit because
`pgl27_spectral.v` exceeds the usual 8 MiB soft limit. A paid runner remains
outside this design.

## Failure Behavior

Flattening and source upload must succeed before the build job starts. Once the
source artifact is uploaded, a later dependency or compilation failure does not
remove it. The workflow does not push generated branches or modify `main`.

No `WADT2026` tag is created while the workflow is queued, running, cancelled,
or unsuccessful.  After a successful run, an annotated local tag is created at
the exact tested `main` commit and pushed to `origin`.

## Verification

Before publication, the implementation receives these local checks:

- the shell script parses successfully;
- the source-only script never invokes opam, Rocq, or `make`;
- the build helper compiles only files received in the source tarball;
- `ROCQ_JOBS=1` reaches the generated build command and invalid counts fail;
- source files and `_CoqProject` are identical in the source and built archives;
- import rewriting produces the same result with GNU and BSD userlands;
- the workflow has two jobs and the build job depends on the source job;
- the upload and download artifact names match exactly;
- the Git diff contains only the intended workflow, script, and related
  documentation.

After publication, `gh` is used to observe the exact workflow run started by
the pushed implementation commit.  Success means GitHub reports the run's
conclusion as `success` and the run contains both tarball artifacts. Only then
is `WADT2026` pushed.

## Non-goals

- No generated source branch is published.
- No command pushes all local branches.
- No release object is created.
- No tag is created for a failed or untested commit.
- No paid GitHub runner is selected.
- Existing unrelated local changes are not committed or pushed.

## External References

- GitHub workflow syntax:
  https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax
- Artifact upload action:
  https://github.com/actions/upload-artifact
- Artifact download action:
  https://github.com/actions/download-artifact
