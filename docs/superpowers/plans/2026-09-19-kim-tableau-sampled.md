# Plan: Kim's two five-card rows as Tableau programs

Date: 2026-09-19. Spec: `notes/20260919-kim-tableau-sampled-design.md`.
Verbatim source: the probe `notes/probes/2026-09-19-kim-tableau-sampled/`
(PROBE), file `five_card_rows_landing.v`, commit 2e567e0. Audits: soundness GO,
naming GO in round 3.

This plan is also the as-built record. Every deviation is written under its
task: before, after, why.

## Rules for every task

- The edit to the `.v` file is made by an Opus `rocq-prover` subagent. The main
  session verifies with its own compile and scans, then commits.
- Never rebuild the tree. Compile one file with `rocq compile` and the flags of
  the production `_CoqProject`, writing the `.vo` next to its source. No
  `make`. One Rocq process at a time.
- Branch `feat/kim-tableau-sampled`. At the end `main` is moved to the branch
  head without rewriting any file.
- Nothing under `notes/probes/` is deleted. Nothing under `manifest/` changes.

## Construction choices, each with its reason

1. **The permanent text is the landing copy, copied with `cp`.** Reason: it is
   the text two audits read and the text that compiled. The copy imports no
   probe file, so no line is substituted.
2. **Only `instances/kim2025/five_card_rows.v` changes.** Reason: it has no
   importer, so nothing else is invalidated and nothing else is compiled.
3. **`kim_centi_small` lands in this file, above its one use.** Reason:
   `instances/kim2025/five_card_kim.v`, where `kim_centi_lt`, `kim_centi_gt`
   and `kim_centi_spec` live, has 20 importers, and the rule is to compile only
   related files. It moves there when that file is next edited for another
   reason.
4. **No `certify` arm is added and both Kim programs stop at `Sampled`.**
   Reason: the repeated row's theorem bounds one starting position's endpoint
   marginal, and the biased row's bounds a conditional mutual information.
   Neither is what an arm of `certify` asks for, and an arm that carried either
   would let it reach the level that, in a program, means a coalition result.
5. **Two mutations land in the file, two stay in the probe.** The program
   sampling another instance's family and the biased program at the manifest's
   level are clean terms and read as the file's existing `Fail` does. The two
   mutations of the endpoint bound are `ltac:` terms inside a `Fail` and stay
   in the probe. Reason: a permanent file should not carry probe idiom.
6. **No permanent file carries `Print Assumptions`.** Task 2 checks assumptions
   from a probe file that imports the production module.

## Tasks

### Task 1. `instances/kim2025/five_card_rows.v`

Replace the file with `PROBE/five_card_rows_landing.v`, byte for byte. Compile
it, with `-time`.

Passes when: exit 0; `diff` against the landing copy is empty; every line that
`git diff` removes is a comment line of the file header; after stripping
comments the 146 code lines of the old file all survive, in order, among the
214 of the new one; no sentence costs more than a tenth of a second beyond its
landing-copy counterpart.

### Task 2. As-built fidelity, in the probe

New probe file `PROBE/kim_production_fidelity.v`: `kim_fidelity.v` with its
import pointed at the production module `pgg_smc.five_card_rows`. It runs
`Print Assumptions` on the eleven landed declarations and repeats, against the
permanent file, the two positive facts the programs rest on: that each
program's law is the law its manifest row's theorems name, by `erefl`, and that
the same `erefl` at the uniform family is rejected.

Passes when: exit 0; ten blocks report the three `boolp` axioms and
`five_card_row_biased_levelE` reports `Closed under the global context`.

### Task 3. Merge and record

The main session recompiles task 1 and task 2 into a scratch directory, runs
the word scans in Python, confirms `git status` shows no file outside the plan,
moves `main` to the branch head, and updates the spec's status line, the
probe's `STATUS.md` and the project memory.

## Out of scope

A new `certify` arm. Any edit under `manifest/`. The paper. A coalition result
for Kim's biased or repeated cuts. Moving `kim_centi_small` into
`five_card_kim.v`. The `s5_row_word` program.
