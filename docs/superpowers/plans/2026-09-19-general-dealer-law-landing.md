# Plan: land the general dealer law

Date: 2026-09-19. Spec: `notes/20260918-general-dealer-law-landing-design.md`.
Verbatim source: the landing probe
`notes/probes/2026-09-18-general-dealer-law-landing/` (LAND), commit 82e7d4e.
Audits: soundness GO; naming round 2 must be GO before task 1 starts.

This plan is also the as-built record. Every deviation is written under its
task: before, after, why.

## Rules for every task

- All edits to `.v` files are made by an Opus `rocq-prover` subagent. The main
  session verifies each task with its own compile and scans, then commits.
- Never rebuild the tree. Compile one file at a time with `rocq compile` and
  the flags of the production `_CoqProject`, writing the `.vo` next to its
  source. No `make`. One Rocq process at a time.
- Compile exactly the files this plan lists. `psl211_endpoints`,
  `psl211_profile` and `psl211_exec` are not among them. If a load reports
  inconsistent assumptions, recompile only the minimal chain of files that the
  failing file depends on, bottom-up. If that chain reaches
  `psl211_endpoints`, move every remaining edit below it first and compile it
  once, alone.
- Branch `feat/dealer-privacy` from `main`. One commit per task. At the end
  `main` is moved to the branch head without rewriting any file.
- Nothing under `notes/probes/` is deleted.

## Construction choices, each with its reason

1. **The permanent text of each file is its landing copy, not a fresh edit.**
   The copies are what two audits read and what compiled. Reason: any
   re-typing loses that evidence.
2. **Three lines of the copies are not taken verbatim.** In
   `pgl27_profile_privacy.v` and `psl211_models.v`,
   `From general_dealer_law_landing Require Import dealer_privacy.` becomes
   `From pgg_reconstruct Require Import dealer_privacy.`. In
   `psl211_models.v` the line importing `design_privacy_landing` is deleted.
   Reason: a permanent file must not import a probe file, and after the
   landing the two fiber lemmas come from `design_privacy`, which the file
   already imports.
3. **`reconstruct/dealer_privacy.v` carries no `Fail`.** Reason: no file under
   `reconstruct/` has one. The mutations of the dealer kernel live in the
   probe's `landing_fidelity.v`. The two instance files keep theirs, as six
   files under `instances/` do.
4. **No permanent file carries `Print Assumptions`.** Reason: none in the tree
   does. Task 6 checks assumptions from a probe file.
5. **Edits first, importers last.** Tasks 1 to 4 each compile only the file
   they write. Task 5 compiles the remaining importers once, in dependency
   order. Reason: `psl211_models.v` is both an edited file and an importer of
   `design_privacy.v`, so compiling importers after each edit would compile
   it, and everything above it, twice.
6. **`_CoqProject` gains one line**, `reconstruct/dealer_privacy.v`, directly
   after `reconstruct/transitivity_privacy.v`. Reason: it imports that file and
   nothing later, and its first importer comes eight lines further down.

## Tasks

### Task 1. `reconstruct/dealer_privacy.v` and `_CoqProject`

Write `reconstruct/dealer_privacy.v` with the content of
`LAND/dealer_privacy.v`, byte for byte. Insert
`reconstruct/dealer_privacy.v` into `_CoqProject` after
`reconstruct/transitivity_privacy.v`. Compile the new file.

Passes when: exit 0; the file has three sections and eight declarations; no
`Fail`, `Print Assumptions`, `Admitted`, `Abort`, `Axiom`; `diff` against the
landing copy is empty.

### Task 2. `reconstruct/design_privacy.v`

Replace the file with the content of `LAND/design_privacy_landing.v`. Compile
it.

Passes when: exit 0; `diff` against the landing copy is empty; `git diff` shows
only the header table lines, the new `uniform_fdistmap_pointE`, the new proof
of `uniform_fdistmap_fiberE` under an unchanged statement, and the new
`uniform_fdistmap_fiberTE`.

### Task 3. `instances/pgl27/pgl27_profile_privacy.v`

Replace the file with the content of `LAND/pgl27_profile_privacy_landing.v`
after the import substitution of choice 2. Compile it.

Passes when: exit 0; `git diff` has no removed line; `diff` against the landing
copy shows the one substituted import line and nothing else.

### Task 4. `instances/psl211/psl211_models.v`

Replace the file with the content of `LAND/psl211_models_landing.v` after the
two changes of choice 2. Compile it, with `-time`.

Passes when: exit 0; `git diff` has no removed line; `diff` against the landing
copy shows one substituted line and one deleted line; no sentence costs more
than its landing-copy counterpart beyond a tenth of a second.

### Task 5. The remaining importers, once each, in this order

`instances/psl211/psl211_secrecy.v`, `instances/psl211/psl211_analysis.v`,
`manifest/pgg_analysis_manifest.v`, `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v`, `instances/pgl27/pgl27_rows.v`,
`instances/kim2025/five_card_rows.v`, `instances/s5/s5_rows.v`,
`instances/psl211/psl211_rows.v`, `manifest/pgg_analysis_client.v`.

No source changes. Record wall time and peak memory of each. None of these
sources is newer than its `.vo` today, so each recompile is forced only by the
new `design_privacy.vo` and `psl211_models.vo`.

Passes when: all ten exit 0. A failure here is a finding against audit item A8
and is diagnosed before anything else moves.

### Task 6. As-built fidelity, in the probe

New probe file `LAND/production_fidelity.v`: `landing_fidelity.v` with its
imports pointed at the production modules (`pgg_reconstruct.dealer_privacy`,
`pgg_reconstruct.design_privacy`, `pgg_smc.pgl27_profile_privacy`,
`pgg_smc.psl211_models`). It repeats, against the permanent files, the two-way
type ascriptions of the three `_via_dealer` theorems in both the `ltac:` and
the written form, the check that `uniform_fdistmap_fiberE` has its old
statement, and `Print Assumptions` on every landed declaration.

Passes when: exit 0 and every `Print Assumptions` block is either the three
`boolp` axioms or `Closed under the global context`. This closes ledger row
L10.

### Task 7. Merge and record

The main session recompiles tasks 1 to 4 and task 6 into a scratch directory,
runs the word scans in Python, confirms `git status` shows no file outside the
plan, moves `main` to the branch head, and updates the spec's status line, the
landing `STATUS.md` and the project memory.

## Out of scope

`Arguments` directives, the text of the paper, a Tableau or manifest row for
the dealer law, necessity of `uniq`, necessity of the uniform PSL(2,11) dealer
law, and any file the list above does not name.
