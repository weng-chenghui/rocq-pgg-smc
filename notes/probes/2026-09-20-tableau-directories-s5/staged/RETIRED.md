# What the `cp` retires, and every reference to it

Checked at HEAD `6f3612e` on branch `feat/tableau-extensions-probe`.
`grep -rn s5_rows` over the whole working tree, with the agent worktrees under
`.claude/` and this probe directory excluded.

## Files to `git rm`

| Path | Lines | Contents |
|---|---|---|
| `instances/s5/s5_rows.v` | 394 | 18 declarations, two recorded `Fail`s and one bare `Check`, all of which land in `instances/s5/tableau/` |

Nothing else is retired. `instances/s5/s5_exec.v`, `instances/s5/s5_models.v`
and `instances/s5/s5_analysis.v` are untouched, and so is every file below
them.

## References that must change, in code

| File:line | Text at that line | What it becomes |
|---|---|---|
| `_CoqProject:226` | `instances/s5/s5_rows.v` | the six `instances/s5/tableau/…` lines, in phase order; see STATUS.md |
| `instances/kim2025/five_card_proximity.v:146` | `From pgg_smc Require Import five_card_rows s5_rows.` | `From pgg_smc Require Import five_card_rows s5_tableau_analysis_bridged.` |

The staged `five_card_proximity.v` in this directory already carries that
second change and nothing else; its other 592 lines are byte-identical to
production's. It is the only importer of `s5_rows` anywhere in the tree.
`s5_rand_exact_witness` is the only name it takes from that module, and that
name is now in `s5_tableau_analysis_bridged.v`.

## References that must change, in a comment

| File:line | Text at that line |
|---|---|
| `instances/kim2025/five_card_rows.v:59` | `(* criteria are met at both Kim rows. instances/s5/s5_rows.v records the      *)` |

The sentence runs to line 61 and cites the retired file for the S5 word-model
reasoning. That reasoning is now the third paragraph of the header of
`instances/s5/tableau/s5_tableau_sampled.v`, so the path in the comment
becomes `instances/s5/tableau/s5_tableau_sampled.v`. The replacement is one
line longer than the line it replaces at 80 columns, so the sentence needs
rewrapping across lines 59 to 61.

This is a comment, so it changes no term, but editing it does rebuild
`five_card_rows.vo` and through it `five_card_proximity.vo`. Neither is in the
forward closure of `psl211_endpoints.v`. No staged copy of `five_card_rows.v`
is in this directory: the main session makes this edit directly.

`instances/s5/s5_rows.v:4` is the retired file's own header line and goes with
the file.

## References outside the code, for the owner's note. Not edited here

No file under `paper/`, `paper-wadt2026/` or
`paper-wadt2026-baseline-application/` mentions `s5_rows`, and neither does
`README.md`. Every remaining occurrence is in a dated plan under `docs/`, which
records what a past batch did and is not a description of the tree at HEAD.

| File:line | Kind |
|---|---|
| `docs/superpowers/plans/2026-09-19-kim-spectral-landing.md:32` | file list of a landed batch |
| `docs/superpowers/plans/2026-09-19-kim-spectral-landing.md:60` | file list of a landed batch |
| `docs/superpowers/plans/2026-09-19-kim-spectral-landing.md:85` | staging instruction of a landed batch |
| `docs/superpowers/plans/2026-09-19-general-dealer-law-landing.md:102` | file list of a landed batch |
| `docs/superpowers/plans/2026-09-19-general-dealer-law-landing.md:157` | a count of declarations per rows file |
| `docs/superpowers/plans/2026-09-15-psl211-plan-b-alldecks.md:2248` | a `_CoqProject` insertion point |
| `docs/superpowers/plans/2026-09-15-psl211-plan-b-alldecks.md:2362` | a `_CoqProject` insertion point |
| `docs/superpowers/plans/2026-09-15-psl211-plan-b-alldecks.md:2801` | `s5_rows.v:256`, a line citation |

Dated notes under `notes/` also cite the name; they are the same kind of
record and are left alone for the same reason.
