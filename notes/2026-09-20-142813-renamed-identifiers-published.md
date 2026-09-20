# Renamed identifiers: `PublishedRow` becomes `Published` (2026-09-20)

Status: AS BUILT for the identifiers (tracker step 2.6c, first commit). The
list is for the owner's own edits of texts that cite the code. No `.tex` file
was edited. The word "row" in comments is a separate, audited pass (second
commit; `notes/probes/2026-09-20-published-rename/prose_sheet.md`).

How it was checked: all 110 new names answered "No object of basename" to
`Locate` under the union of the renamed files' imports before any edit; the map
was applied as a whole-identifier substitution by an Opus `rocq-prover`;
`check_rename.py` (code tokens and comment words of every tracked file equal to
the parent commit's under the map, no old name left) says ALL OK, run by the
prover and again by the main session; the reverse closure of 30 files was
recompiled single-file, all rc=0; the 16 recorded `Fail` commands that hold a
renamed name were each recompiled without `Fail` under their own file's prefix
and all 16 still fail inside the term with the rejection their comment
describes (`fail_recheck.md`).

Decision: `notes/2026-09-20-111257-published-row-rename-plan.md` (the owner chose
`Published`, all six layers). The machine-readable map with its checks is
`notes/probes/2026-09-20-published-rename/rename_map.tsv` (`build_map.py` checks
that it is injective and that no new name was already an identifier of the tree).

## What a citing text has to change

Nothing today. A scan on 2026-09-20 of `paper/`, `paper-wadt2026/`,
`paper-wadt2026-baseline-application/`, `blueprint/` and `README.md`, with and
without the LaTeX escape of the underscore, finds none of the 110 old names.
Three dated plans under `docs/superpowers/plans/` hold old names; they are
records of past work and stay as written.

In a paper's prose the noun for a value of type `Published` is "a published
claim"; the manifest's record is "an analysis path".

## The naming rule

| Object | Old shape | New shape |
|---|---|---|
| The type of a finished program | `PublishedRow`, `PublishedRowAt c` | `Published`, `PublishedAt c` |
| The manifest's record | `AnalysisPathRow`, fields `apr_*` | `AnalysisPath`, fields `ap_*` |
| A manifest record of an instance | `<inst>_row_<model>` | `<inst>_<model>_path` |
| A finished program | `<inst>_row_<model>_tableau`, `<inst>_row_<model>_<arm>` | `<inst>_<model>[_<arm>]_published` |
| A finished program concluded at a bound | `<inst>_row_<model>39` | `<inst>_<model>_published39` |
| The equation between a program's record and the manifest's | `*_rowE` | `<value>_pathE` |
| The three status fields of a program's record | `*_publishedE` | `<value>_path_fieldsE` |
| Other statements about a finished program | `<inst>_row_<model>..._armE`, `_atE`, `_sampledE` | `<value>_armE`, `_atE`, `_sampledE` |

Two five-card values of type `Tableau Sampled` carried the manifest's word and
take the Sampled scheme of the `tableau/` directories:
`five_card_row_repeated_tableau` becomes `five_card_repeated_sampled`, and
`five_card_row_biased_tableau` becomes `five_card_biased_sampled`.

Identifiers where "row" means a row of a matrix, of a deck table or of a trace
(`ad_row`, `row_mx`, `pgl27_exec_rowE`, `psl211_alldecks_row`, and about fifty
more) are unrelated and unchanged.

## The framework and the manifest (11 names)

| Old | New | Uses |
|---|---|---|
| `AnalysisPathRow` | `AnalysisPath` | 48 |
| `MkAnalysisPathRow` | `MkAnalysisPath` | 17 |
| `MkPublishedRow` | `MkPublished` | 2 |
| `PublishedRow` | `Published` | 15 |
| `PublishedRowAt` | `PublishedAt` | 21 |
| `apr_assumptions` | `ap_assumptions` | 18 |
| `apr_completion` | `ap_completion` | 22 |
| `apr_model` | `ap_model` | 24 |
| `apr_observed` | `ap_observed` | 10 |
| `apr_transfer` | `ap_transfer` | 18 |
| `published_row` | `published_path` | 25 |

## Manifest records (11 names)

| Old | New | Uses |
|---|---|---|
| `five_card_row_biased` | `five_card_biased_path` | 15 |
| `five_card_row_repeated` | `five_card_repeated_path` | 11 |
| `five_card_row_uniform` | `five_card_uniform_path` | 11 |
| `pgl27_row_exact` | `pgl27_exact_path` | 11 |
| `pgl27_row_prior_exact` | `pgl27_prior_exact_path` | 11 |
| `pgl27_row_word` | `pgl27_word_path` | 13 |
| `psl211_row_alldecks` | `psl211_alldecks_path` | 15 |
| `psl211_row_word` | `psl211_word_path` | 11 |
| `s5_row_det` | `s5_det_path` | 10 |
| `s5_row_rand` | `s5_rand_path` | 11 |
| `s5_row_word` | `s5_word_path` | 11 |

## Programs, their statements, and recorded rejections (88 names)

| Old | New | Uses |
|---|---|---|
| `five_card_row_biased_arm_neq` | `five_card_biased_published_arm_neq` | 2 |
| `five_card_row_biased_at_manifest_level` | `five_card_biased_sampled_at_manifest_level` | 1 |
| `five_card_row_biased_branch_indistinguishability` | `five_card_biased_branch_indistinguishability_published` | 8 |
| `five_card_row_biased_branch_indistinguishability_armE` | `five_card_biased_branch_indistinguishability_published_armE` | 2 |
| `five_card_row_biased_branch_indistinguishability_atE` | `five_card_biased_branch_indistinguishability_published_atE` | 2 |
| `five_card_row_biased_branch_indistinguishability_rowE` | `five_card_biased_branch_indistinguishability_published_pathE` | 2 |
| `five_card_row_biased_forms_publishedE` | `five_card_biased_forms_pathE` | 3 |
| `five_card_row_biased_indistinguishability_armE` | `five_card_biased_indistinguishability_published_armE` | 2 |
| `five_card_row_biased_indistinguishability_publishedE` | `five_card_biased_indistinguishability_published_path_fieldsE` | 2 |
| `five_card_row_biased_indistinguishability_rowE` | `five_card_biased_indistinguishability_published_pathE` | 3 |
| `five_card_row_biased_indistinguishability_sampledE` | `five_card_biased_indistinguishability_published_sampledE` | 3 |
| `five_card_row_biased_indistinguishability_tableau` | `five_card_biased_indistinguishability_published` | 15 |
| `five_card_row_biased_inv25` | `five_card_biased_published_inv25` | 8 |
| `five_card_row_biased_inv25_armE` | `five_card_biased_published_inv25_armE` | 3 |
| `five_card_row_biased_inv25_sampledE` | `five_card_biased_published_inv25_sampledE` | 3 |
| `five_card_row_biased_leak_bound` | `five_card_biased_leak_bound` | 3 |
| `five_card_row_biased_levelE` | `five_card_biased_path_levelE` | 3 |
| `five_card_row_biased_modelE` | `five_card_biased_sampled_modelE` | 2 |
| `five_card_row_biased_prefixE` | `five_card_biased_sampled_prefixE` | 2 |
| `five_card_row_biased_proximity` | `five_card_biased_proximity_published` | 13 |
| `five_card_row_biased_proximity_armE` | `five_card_biased_proximity_published_armE` | 2 |
| `five_card_row_biased_proximity_publishedE` | `five_card_biased_proximity_published_path_fieldsE` | 2 |
| `five_card_row_biased_proximity_rowE` | `five_card_biased_proximity_published_pathE` | 3 |
| `five_card_row_biased_tableau` | `five_card_biased_sampled` | 16 |
| `five_card_row_repeated39` | `five_card_repeated_published39` | 8 |
| `five_card_row_repeated39_armE` | `five_card_repeated_published39_armE` | 3 |
| `five_card_row_repeated39_atE` | `five_card_repeated_published39_atE` | 3 |
| `five_card_row_repeated39_sampledE` | `five_card_repeated_published39_sampledE` | 3 |
| `five_card_row_repeated39_unindexed` | `five_card_repeated_published39_unindexed` | 1 |
| `five_card_row_repeated_endpoint_lt` | `five_card_repeated_endpoint_lt` | 3 |
| `five_card_row_repeated_indistinguishability_armE` | `five_card_repeated_indistinguishability_published_armE` | 2 |
| `five_card_row_repeated_indistinguishability_publishedE` | `five_card_repeated_indistinguishability_published_path_fieldsE` | 2 |
| `five_card_row_repeated_indistinguishability_rowE` | `five_card_repeated_indistinguishability_published_pathE` | 3 |
| `five_card_row_repeated_indistinguishability_sampledE` | `five_card_repeated_indistinguishability_published_sampledE` | 3 |
| `five_card_row_repeated_indistinguishability_tableau` | `five_card_repeated_indistinguishability_published` | 13 |
| `five_card_row_repeated_indistinguishability_uniform_rowE` | `five_card_repeated_indistinguishability_published_uniform_pathE` | 1 |
| `five_card_row_repeated_modelE` | `five_card_repeated_sampled_modelE` | 2 |
| `five_card_row_repeated_prefixE` | `five_card_repeated_sampled_prefixE` | 2 |
| `five_card_row_repeated_proximity` | `five_card_repeated_proximity` | 1 |
| `five_card_row_repeated_tableau` | `five_card_repeated_sampled` | 10 |
| `five_card_row_s5_family` | `five_card_s5_family_sampled` | 1 |
| `five_card_row_uniform_armE` | `five_card_uniform_published_armE` | 3 |
| `five_card_row_uniform_rowE` | `five_card_uniform_published_pathE` | 5 |
| `five_card_row_uniform_sampledE` | `five_card_uniform_published_sampledE` | 3 |
| `five_card_row_uniform_tableau` | `five_card_uniform_published` | 10 |
| `pgl27_row_exact_armE` | `pgl27_exact_published_armE` | 3 |
| `pgl27_row_exact_leak7` | `pgl27_exact_published_leak7` | 1 |
| `pgl27_row_exact_rowE` | `pgl27_exact_published_pathE` | 4 |
| `pgl27_row_exact_sampledE` | `pgl27_exact_published_sampledE` | 3 |
| `pgl27_row_exact_tableau` | `pgl27_exact_published` | 8 |
| `pgl27_row_prior_exact_armE` | `pgl27_prior_exact_published_armE` | 3 |
| `pgl27_row_prior_exact_rowE` | `pgl27_prior_exact_published_pathE` | 4 |
| `pgl27_row_prior_exact_sampledE` | `pgl27_prior_exact_published_sampledE` | 3 |
| `pgl27_row_prior_exact_tableau` | `pgl27_prior_exact_published` | 10 |
| `pgl27_row_word39` | `pgl27_word_published39` | 8 |
| `pgl27_row_word39_armE` | `pgl27_word_published39_armE` | 3 |
| `pgl27_row_word39_bind` | `pgl27_word_published39_bind` | 4 |
| `pgl27_row_word39_bindE` | `pgl27_word_published39_bindE` | 3 |
| `pgl27_row_word39_unindexed` | `pgl27_word_published39_unindexed` | 1 |
| `pgl27_row_word39_unindexed_bind` | `pgl27_word_published39_unindexed_bind` | 1 |
| `pgl27_row_word41` | `pgl27_word_published41` | 1 |
| `pgl27_row_word_armE` | `pgl27_word_published_armE` | 3 |
| `pgl27_row_word_arm_neq` | `pgl27_word_published_arm_neq` | 3 |
| `pgl27_row_word_branch39` | `pgl27_word_branch_published39` | 9 |
| `pgl27_row_word_branch39_armE` | `pgl27_word_branch_published39_armE` | 3 |
| `pgl27_row_word_certE` | `pgl27_word_published_certE` | 3 |
| `pgl27_row_word_families_sampledE` | `pgl27_word_published_families_sampledE` | 2 |
| `pgl27_row_word_obs_sampledE` | `pgl27_word_published_obs_sampledE` | 2 |
| `pgl27_row_word_proximity` | `pgl27_word_proximity_published` | 11 |
| `pgl27_row_word_proximity_armE` | `pgl27_word_proximity_published_armE` | 3 |
| `pgl27_row_word_proximity_rowE` | `pgl27_word_proximity_published_pathE` | 3 |
| `pgl27_row_word_rowE` | `pgl27_word_published_pathE` | 5 |
| `pgl27_row_word_sampledE` | `pgl27_word_published_sampledE` | 3 |
| `pgl27_row_word_tableau` | `pgl27_word_published` | 12 |
| `psl211_row_alldecks_armE` | `psl211_alldecks_published_armE` | 2 |
| `psl211_row_alldecks_rowE` | `psl211_alldecks_published_pathE` | 3 |
| `psl211_row_alldecks_sampledE` | `psl211_alldecks_published_sampledE` | 4 |
| `psl211_row_alldecks_tableau` | `psl211_alldecks_published` | 10 |
| `psl211_row_vm_reuse` | `psl211_vm_reuse_sampled` | 1 |
| `psl211_row_word_proximity` | `psl211_word_proximity_published` | 7 |
| `psl211_row_word_proximity_armE` | `psl211_word_proximity_published_armE` | 2 |
| `psl211_row_word_proximity_rowE` | `psl211_word_proximity_published_pathE` | 2 |
| `psl211_row_word_proximity_sampledE` | `psl211_word_proximity_published_sampledE` | 4 |
| `s5_dealt_row_observedE` | `s5_dealt_path_observedE` | 2 |
| `s5_row_rand_armE` | `s5_rand_published_armE` | 2 |
| `s5_row_rand_rowE` | `s5_rand_published_pathE` | 2 |
| `s5_row_rand_sampledE` | `s5_rand_published_sampledE` | 3 |
| `s5_row_rand_tableau` | `s5_rand_published` | 7 |
