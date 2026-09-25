# GitHub Flattened Build Design

## Goal

Publish the existing source repository as the public GitHub repository
`weng-chenghui/rocq-pgg-smc`.  Every push to `main` must build the flattened
non-legacy Rocq sources and retain the resulting tarball as a GitHub Actions
artifact.  The `WADT2026` tag is created only after the first workflow run for
the CI implementation commit succeeds.

## Problem

The repository has a script that relocates the non-legacy Rocq sources into one
directory, rewrites their logical root, compiles that flattened development,
and creates a tarball.  The script currently assumes a local opam switch and
always compiles with four jobs.  Those assumptions do not fit a GitHub-hosted
runner, where the switch path differs and concurrent Rocq processes can exceed
the available memory.  Its in-place `sed` form is also specific to macOS and
fails on the Ubuntu runner.

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

`.github/workflows/flattened-build.yml` runs on each push to `main`.  It has one
Ubuntu job with read-only repository permissions and these steps:

1. Check out the pushed commit.
2. Install OCaml 4.14 and opam with `ocaml/setup-ocaml`.
3. Add the released Rocq opam repository and run
   `opam install . --deps-only --yes`.  This installs the dependencies declared
   by `rocq-pgg-smc.opam` without compiling the original source tree.
4. Configure an identity for the temporary commit made inside the flatten
   worktree.
5. In one shell step, raise the stack limit, read the active switch with
   `opam switch show --safe`, and run the flatten script with one compilation
   job.  The script receives `$GITHUB_SHA`, not `HEAD`.
6. Read the pushed commit's committer epoch with `%ct` and format it in UTC as
   `YYYYMMDD-HHMMSS-pgg-smc-flat.tar.gz`.
7. Upload that tarball as the workflow artifact.  A missing tarball fails the
   workflow.

Official third-party actions are pinned to immutable commit SHAs.  Their major
release names are recorded in comments so future updates are deliberate.

## Flatten Script Interface

`scripts/flatten_artifact.sh` keeps its existing positional interface:

```text
scripts/flatten_artifact.sh SOURCE_REF OUT_TARBALL
```

It also accepts `FLATTEN_JOBS`, a positive integer whose default remains `4` for
local compatibility.  The workflow sets it to `1`.  The chosen value controls
both the actual `make` invocation and the rebuild command written into
`ARTIFACT-README.txt`.

The macOS-only in-place `sed` call is replaced by a portable rewrite to a
temporary file followed by `mv`.  The rewritten content remains identical on
macOS, Alpine Linux, and Ubuntu.

The workflow passes `ROCQ_OPAM_SWITCH` using the switch selected by
`ocaml/setup-ocaml`.  No GitHub-specific path is embedded in the script.

## Resource Handling

The flattened build runs sequentially because individual Rocq files already
use substantial memory.  The workflow raises the stack limit before invoking
the script because `pgl27_spectral.v` exceeds the usual 8 MiB soft limit.  The
first real workflow run determines whether the standard public runner has
enough memory for `psl211_endpoints.v`.  If it does not, the workflow log is
kept as evidence and no tag is created.  An available-disk check may justify a
runner-local swap file in a follow-up commit.  A paid runner is outside this
design and requires separate approval.

## Failure Behavior

Dependency installation, flattening, compilation, archive validation, and
artifact upload are all required steps.  Any nonzero exit status fails the job.
The workflow does not push generated branches or modify `main`.

No `WADT2026` tag is created while the workflow is queued, running, cancelled,
or unsuccessful.  After a successful run, an annotated local tag is created at
the exact tested `main` commit and pushed to `origin`.

## Verification

Before publication, the implementation receives these local checks:

- the shell script parses successfully;
- `FLATTEN_JOBS=1` reaches the generated build command;
- invalid job counts are rejected;
- import rewriting produces the same result with GNU and BSD userlands;
- the workflow YAML parses and names only the intended `main` push trigger;
- the Git diff contains only the intended workflow, script, and related
  documentation.

After publication, `gh` is used to observe the exact workflow run started by
the pushed implementation commit.  Success means GitHub reports the run's
conclusion as `success` and the run contains the flattened tarball artifact.
Only then is `WADT2026` pushed.

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
- OCaml and opam setup action:
  https://github.com/ocaml/setup-ocaml
- Artifact upload action:
  https://github.com/actions/upload-artifact
