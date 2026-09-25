# GitHub Flattened Build Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Publish `rocq-pgg-smc` publicly, build the flattened Rocq archive on
every `main` push, and tag the first successful CI commit as `WADT2026`.

**Architecture:** The existing flatten script remains the sole archive
producer.  GitHub Actions installs opam dependencies and invokes it with one
job and an unlimited stack.  Only local `main` is pushed to remote `main`.

**Tech Stack:** Bash, Git, GitHub CLI, GitHub Actions, opam, Rocq, Ruby YAML.

**Spec:** `docs/superpowers/specs/2026-09-25-github-flattened-build-design.md`

## Global Constraints

- Publish `weng-chenghui/rocq-pgg-smc` with `PUBLIC` visibility.
- Treat the flattened tree only as an uploaded build artifact.
- Keep all unrelated staged and untracked local files out of commits.
- Build sequentially and raise the stack limit.
- Pin official actions to immutable commit SHAs.
- Create `WADT2026` only for the exact successful workflow SHA.
- Do not select a paid runner without separate approval.

## Review Focus

- GNU and BSD text tools must rewrite imports identically.
- `FLATTEN_JOBS` must reject invalid values and reach `make` and the README.
- The workflow must react only to `main` pushes and use pinned actions.
- Explicit path commits and `main:main` push must preserve unrelated state.
- Any failed run or missing artifact must prevent the tag.

---

### Task 1: Portable flatten script with configurable jobs

**Files:**
- Create: `scripts/tests/flatten_artifact_test.sh`
- Modify: `scripts/flatten_artifact.sh`

**Interfaces:**
- Consumes: `SOURCE_REF`, `OUT_TARBALL`, and `ROCQ_OPAM_SWITCH`.
- Produces: validated `FLATTEN_JOBS`, used by `make` and the archive README.

- [ ] **Step 1: Write the failing regression test**

Create a shell test that builds a temporary two-file Git fixture, installs
small `opam`, `rocq`, and `make` shims on `PATH`, and calls the real script.
Assert that `FLATTEN_JOBS=1` produces `-j1` in the make shim log and in
`ARTIFACT-README.txt`, and rewrites
`From pgg_reconstruct Require Import B.` to
`From pgg_smc Require Import B.`.  Also assert that `0` and `two` fail with
`FLATTEN_JOBS must be a positive integer`.

- [ ] **Step 2: Observe RED**

Run:
```bash
bash scripts/tests/flatten_artifact_test.sh scripts/flatten_artifact.sh
```
Expected: failure because the script still uses `-j4`.

- [ ] **Step 3: Implement GREEN**

Add this validation after the current switch setting:
```bash
FLATTEN_JOBS="${FLATTEN_JOBS:-4}"
case "$FLATTEN_JOBS" in
  ''|*[!0-9]*|0) fail "FLATTEN_JOBS must be a positive integer" ;;
esac
```

Replace `sed -i ''` with `sed -E ... > "${source}.flat-root"` followed by
`mv`.  Use `-j"$FLATTEN_JOBS"` in the build and `-j${FLATTEN_JOBS}` in the
archive README.

- [ ] **Step 4: Verify locally and on GNU userland**

Run:
```bash
bash -n scripts/flatten_artifact.sh
bash -n scripts/tests/flatten_artifact_test.sh
bash scripts/tests/flatten_artifact_test.sh scripts/flatten_artifact.sh
docker run --rm --volume "$PWD:/repo:ro" ubuntu:24.04 bash -lc \
  'apt-get update -qq && apt-get install -y -qq git ca-certificates coreutils tar && bash /repo/scripts/tests/flatten_artifact_test.sh /repo/scripts/flatten_artifact.sh'
```
Expected: all four commands exit 0.

- [ ] **Step 5: Commit exact paths**

Run:
```bash
git add -- scripts/flatten_artifact.sh scripts/tests/flatten_artifact_test.sh
git diff --cached --name-status
git commit --only -m "build: make flattened archive portable" -- \
  scripts/flatten_artifact.sh scripts/tests/flatten_artifact_test.sh
git diff --cached --name-status
```
Expected: the commit has exactly two files, and the earlier staged deletion
remains staged.

### Task 2: Main-push workflow and configuration test

**Files:**
- Create: `scripts/tests/flattened_build_workflow_test.rb`
- Create: `.github/workflows/flattened-build.yml`

**Interfaces:**
- Consumes: the pushed SHA, opam manifest, and flatten script.
- Produces: a dated flattened tarball as an Actions artifact.

- [ ] **Step 1: Write the failing workflow test**

Parse YAML and require exactly `push.branches: [main]`, read-only contents
permission, and these action references:
```text
actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803
ocaml/setup-ocaml@93303b622b2522e4411e295f9e77411a24912ac7
actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a
```
Require the workflow text to contain `opam install . --deps-only --yes`,
`$GITHUB_SHA`, `opam switch show --safe`, `FLATTEN_JOBS=1`,
`ulimit -s unlimited`, `%ct`, `date -u`, and `if-no-files-found: error`.

- [ ] **Step 2: Observe RED**

Run:
```bash
ruby scripts/tests/flattened_build_workflow_test.rb .github/workflows/flattened-build.yml
```
Expected: failure because the workflow does not exist.

- [ ] **Step 3: Add the workflow**

Use `actions/checkout` v6, `ocaml/setup-ocaml` v3 with OCaml 4.14 and the
`coq-released` repository, and `actions/upload-artifact` v7 at the SHAs above.
The build step must run in one Bash process:
```bash
set -euo pipefail
ulimit -s unlimited
commit_epoch="$(git show -s --format=%ct "$GITHUB_SHA")"
archive_stamp="$(date -u -d "@${commit_epoch}" +%Y%m%d-%H%M%S)"
archive_path="dist/${archive_stamp}-pgg-smc-flat.tar.gz"
active_switch="$(opam switch show --safe)"
ROCQ_OPAM_SWITCH="$active_switch" FLATTEN_JOBS=1 \
  ./scripts/flatten_artifact.sh "$GITHUB_SHA" "$archive_path"
echo "archive_path=$archive_path" >> "$GITHUB_OUTPUT"
```
Configure the GitHub Actions bot identity before this step.  Upload
`${{ steps.flattened.outputs.archive_path }}` with missing files treated as an
error.

- [ ] **Step 4: Verify and commit exact paths**

Run:
```bash
ruby scripts/tests/flattened_build_workflow_test.rb .github/workflows/flattened-build.yml
git diff --check -- .github/workflows/flattened-build.yml scripts/tests/flattened_build_workflow_test.rb
git add -- .github/workflows/flattened-build.yml scripts/tests/flattened_build_workflow_test.rb
git commit --only -m "ci: build flattened Rocq archive" -- \
  .github/workflows/flattened-build.yml scripts/tests/flattened_build_workflow_test.rb
git diff --cached --name-status
```
Expected: tests exit 0 and the earlier staged deletion remains staged.

### Task 3: Publish only `main`

**Files:** No file changes.

**Interfaces:**
- Consumes: verified local `main`.
- Produces: public `weng-chenghui/rocq-pgg-smc` with remote `main`.

- [ ] **Step 1: Repeat both local test suites**

Run the Task 1 local shell test and Task 2 Ruby test.  Run `git diff --check`
for the implementation commits and inspect each commit's file list.

- [ ] **Step 2: Create the public repository without an implicit push**

Run:
```bash
gh repo create weng-chenghui/rocq-pgg-smc --public --source . --remote origin
gh repo view weng-chenghui/rocq-pgg-smc --json nameWithOwner,visibility,url
```
Expected: visibility is `PUBLIC`.

- [ ] **Step 3: Push only `main`**

Run:
```bash
git push --set-upstream origin main:main
git ls-remote --heads origin
```
Expected: only `refs/heads/main` is present.

### Task 4: Observe the real workflow

**Files:** Modify Task 1 or Task 2 files only if the real run exposes an
implementation defect.

**Interfaces:**
- Consumes: a run whose `headSha` equals local `main`.
- Produces: `success` plus one nonempty, non-expired archive artifact.

- [ ] **Step 1: Find and watch the exact run**

Use `gh run list` filtered by workflow, branch, and local SHA.  Watch its
database ID with `gh run watch --exit-status --interval 10`.

- [ ] **Step 2: Handle a failure within the approved design**

Read `gh run view --log-failed`, reproduce the failing step where practical,
fix only that step under RED to GREEN testing, commit exact paths, push
`main:main`, and watch the new SHA.  If the only remaining failure is runner
memory, stop without creating a tag.

- [ ] **Step 3: Verify the successful artifact**

Use `gh run view --json headSha,status,conclusion,url` and the run artifacts API.
Require `completed`, `success`, the local SHA, a positive byte count, and
`expired: false`.

### Task 5: Tag the tested commit

**Files:** No file changes.

**Interfaces:**
- Consumes: the successful workflow SHA and verified artifact.
- Produces: annotated remote tag `WADT2026` at that SHA.

- [ ] **Step 1: Compare local, remote, and workflow SHAs**

Fetch `origin/main` and require it to equal local `HEAD` and the run `headSha`.
Require that neither local nor remote already has `WADT2026`.

- [ ] **Step 2: Create, push, and verify the tag**

Run:
```bash
git tag -a WADT2026 "$run_sha" -m "WADT 2026 artifact"
git push origin refs/tags/WADT2026
git ls-remote --tags origin WADT2026 'WADT2026^{}'
gh api repos/weng-chenghui/rocq-pgg-smc/git/ref/tags/WADT2026
```
Expected: the peeled annotated tag target equals the workflow SHA.
