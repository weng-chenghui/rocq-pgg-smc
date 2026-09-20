# What the `cp` retires at five-card, and every reference to it

Checked at HEAD `c58c60f` on branch `feat/tableau-extensions-probe`, after
the S5, PSL(2,11) and PGL(2,7) tableau directories landed.
`git grep -n five_card_rows` and `git grep -n five_card_proximity` over the
whole tracked tree, with `notes/` and the agent worktrees under `.claude/`
excluded. Reverse closures computed from the `Require` lines of every file in
a `-R` or `-Q` directory of `_CoqProject`, transitively.

## Files to `git rm`

| Path | Lines | Contents |
|---|---|---|
| `instances/kim2025/five_card_rows.v` | 998 | 61 declarations, five of them recorded `Fail`s, all of which land in `instances/kim2025/tableau/` |

## Files replaced in place

| Path | Lines before | Lines after | What leaves |
|---|---|---|---|
| `instances/kim2025/five_card_proximity.v` | 594 | 169 | 28 of its 32 declarations, and its `Require` of `five_card_rows`, `s5_tableau_analysis_bridged`, `s5_exec`, `s5_models`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax` and `pgg_observed_execution pgg_analysis_status`; it gains nothing |

The staged reduced copy is
`staged/instances/kim2025/five_card_proximity.v`. It keeps
`five_card_uniform_pairE`, `five_card_reading_secretE`,
`five_card_arg_cut_prodE` and `kim_biased_proximity_close` with the section
that scopes them, each token-identical to production's, and its innermost
`Local Open Scope` is unchanged.

Unlike PGL(2,7), it gains no declaration from the retired rows file. The two
files differ in which side the exact arm's link lemmas fall on:
`pgl27_word_proximity_close` rewrites twice with `pgl27_static_obsE`, so that
lemma had to come down into the mathematics, while
`kim_biased_proximity_close` names `five_card_static_obsE` nowhere, so the
six link lemmas of this instance go up into the AnalysisBridged file beside
the witness they build. All 61 declarations of `five_card_rows.v` land in
`instances/kim2025/tableau/`.

The last import dropped from the reduced file was measured and not guessed:
each remaining `From` line was removed in turn and the file recompiled.
`pgg_observed_execution pgg_analysis_status` and
`pgg_instance pgg_sample_adapter` were each droppable alone and not together,
one covering the other; `pgg_instance` is the file that declares
`static_coalition_obs`, so it is the one kept.

## References that must change, in code

| File | Text | What it becomes |
|---|---|---|
| `_CoqProject` | the line `instances/kim2025/five_card_rows.v` | removed |
| `_CoqProject` | after the line `instances/kim2025/five_card_proximity.v` | the six phase file lines, in phase order; see `../STATUS.md` |
| `instances/kim2025/five_card_proximity.v:146` | `From pgg_smc Require Import five_card_rows s5_tableau_analysis_bridged.` | removed, along with five further module names nothing that stays uses; the staged reduced copy's import list carries the change |

**Derive the `_CoqProject` positions by name.** The retired file's line number
moved under this work, from 225 at the first look to 231 at the second, the
PGL(2,7) landing having been applied in between. The six new lines go after
`instances/kim2025/five_card_proximity.v` and not at the retired file's own
position, because the AnalysisBridged file requires the reduced proximity
file and the checks file requires `s5_tableau_analysis_bridged`, whose six
lines sit between the two positions. Nothing between them depends on
`five_card_rows`.

`instances/kim2025/five_card_proximity.v` is the only file in the tree that
`Require`s `five_card_rows`, and the cut removes that arrow. No file
`Require`s `five_card_proximity`. No source anywhere writes a fully qualified
`pgg_smc.<module>.<ident>` for a name this batch moves, so no cited name
changes.

## References that must change, in a comment

One, and it is **applied with this instance**, not deferred.

`manifest/pgg_tableau_arm_relations.v:48` cites
`instances/kim2025/five_card_proximity.v` for the implication
`five_card_biased_indistinguishability_implies_proximity`, which moves into
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`.

This is not the dangling case of the PGL(2,7) audit's ruling 6: the reduced
file still exists under that path after the `git rm`, so the citation does
not point at nothing. It is the empty-reverse-closure case. Nothing in the
tracked tree `Require`s `pgg_tableau_arm_relations`, so the repoint
recompiles one module, and the reason that defers a repoint of
`manifest/pgg_analysis_manifest.v`, rebuilding it once rather than four
times, does not apply to a file nothing imports. Left unrepointed the
comment would name, for the length of the batch, a file that no longer holds
the lemma it cites.

| File:line | Text at that line | What it becomes |
|---|---|---|
| `manifest/pgg_tableau_arm_relations.v:48` | `(* instances/kim2025/five_card_proximity.v, holds because its conclusion is   *)` | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`, where that lemma lands; the sentence is re-wrapped over two box lines |

The staged copy is `staged-comments/manifest/pgg_tableau_arm_relations.v`,
never under `staged/`, which is an `-R` root and would shadow the module it
copies. It is produced by `../stage_edits.py` from production by an anchored
replacement whose anchor must match exactly once, so it cannot freeze against
a base that moves; it is verified comment-only by comparing the
comment-stripped text of the two copies, and no line exceeds 80 bytes.

| File | Modules that recompile |
|---|---|
| `manifest/pgg_tableau_arm_relations.v` | 0: nothing in the tracked tree requires it |

It is not in the forward closure of `instances/psl211/psl211_endpoints.v`: it
sits above it in the `Require` graph, so the edit cannot rebuild it.

### The scan behind that, over every tracked file

`git grep -n five_card_rows` and `git grep -n five_card_proximity` over the
whole tracked tree with only `notes/` and `.claude/` excluded, which is the
scan the PGL(2,7) audit's F5 asks for after a cross-instance file was missed
there. Every hit, with its reason:

| Hit | Reason it is or is not repointed |
|---|---|
| `_CoqProject:231`, `:238` | the build-order edit above, derived by name |
| `instances/kim2025/five_card_rows.v:4` | the retired file's own header |
| `instances/kim2025/five_card_proximity.v:16`, `:27`, `:146` | the two sources of the cut; the reduced copy's authored header and import list carry the change |
| `manifest/pgg_tableau_arm_relations.v:48` | repointed, applied with this instance |
| `docs/superpowers/plans/2026-09-15-psl211-plan-b-alldecks.md:2801` | a dated plan, not edited |
| `docs/superpowers/plans/2026-09-19-general-dealer-law-landing.md:102`, `:157` | a dated plan, not edited |
| `docs/superpowers/plans/2026-09-19-kim-spectral-landing.md:28`, `:64`, `:84` | a dated plan, not edited |
| `docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md:5`, `:28`, `:50`, `:52`, `:64`, `:94`, `:103` | a dated plan, not edited |

**No `.v` file of another instance cites either name.** `instances/s5/`,
`instances/s5/tableau/`, `instances/psl211/`, `instances/pgl27/`,
`instances/pgl27/tableau/`, `instances/denboer1989/`, `manifest/` apart from
the one row above, `lib/`, `protocol/`, `groups/`, `security/`, `smc/`,
`reconstruct/` and `legacy/` are all clear. The cross-instance miss that
PGL(2,7)'s F5 recorded does not repeat here, and the scan is the evidence
rather than the absence of a memory of one.

## References in notes and plans, which are not edited

`docs/superpowers/plans/2026-09-15-psl211-plan-b-alldecks.md`,
`docs/superpowers/plans/2026-09-19-general-dealer-law-landing.md`,
`docs/superpowers/plans/2026-09-19-kim-spectral-landing.md` and
`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md` cite
`five_card_rows.v` with line numbers. They are dated records of work already
done and are left as written, as the S5, PSL(2,11) and PGL(2,7) landings left
their own. Nothing under `paper/`, `paper-wadt2026/`,
`paper-wadt2026-baseline-application/`, `README.md`, `Makefile`,
`Makefile.rocq`, `scripts/` or `blueprint/` mentions either file name.
`.Makefile.rocq.d` is generated and untracked.
