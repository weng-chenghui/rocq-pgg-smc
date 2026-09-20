# Tableau campaign tracker (opened 2026-09-19)

Owner's instruction, 2026-09-19: "do all until C is fully done". This note is
the single list of what that covers, in execution order, with the state of
each step. Update it at every commit.

Standing rules: every `.v` edit by an Opus `rocq-prover` subagent; the main
session verifies by its own recompile from source; every fix pass audited by an
Opus agent or the main session, and the report says which; one Rocq process at
a time through the lock wrapper; single-file compiles, never `make`; never
compile `instances/psl211/psl211_endpoints.v`, never edit a file in its forward
closure (35 modules, list computed on 2026-09-19; none of the files below is in
it, re-check before each step); never delete under `notes/probes/`; no paper
file edited; "indistinguishability" is always spelled out.

## Step 0. Names

| # | Step | State |
|---|---|---|
| 0.1 | Production rename of the arm `SpectralDecay` to `InputIndistinguishability` (map in section "Rename map"), six files plus the recompile of `psl211_rows.v` | done, bf42b4d |
| 0.2 | Main-session check: code identical modulo the map (one intended difference, the notation literal), recompile of seven files rc=0 | done |
| 0.3 | Opus audit of the rewritten comment prose: NO-GO with two MUST (a clause lost in a rewrap, a secret attributed to the arm), report `notes/2026-09-19-230000-audit-rename-input-indistinguishability-arm.md`; fix pass by an Opus rocq-prover, audited by the main session (code identical by script, word diff, recompile). F4 is left to the landing of stage A, F5 to step 0.4 | done |
| 0.4 | Production rename of the remaining `_indist` lemma names and of the file `psl211_spectral_constancy.v` to `psl211_reading_constancy.v` (after its main definition `coalition_reading_constancy`). Files: `five_card_analysis.v`, `five_card_mixing.v`, `pgg_analysis_client.v`, `pgg_analysis_manifest.v`, `pgl27_analysis.v`, `pgl27_models.v`, `pgl27_rows.v`, `pgl27_spectral.v`, `pgl27_word_privacy.v`, plus importers to recompile | done: fifteen names, file renamed, by an Opus rocq-prover; audited by the main session (code tokens identical modulo the map, whole-file word diff empty, sixteen files recompiled rc=0, `pgl27_spectral.v` 390 s) |
| 0.5 | The same combined map, and the prose of the step 0.3 fix pass where the passage exists, applied to the probe copy `notes/probes/2026-09-19-tableau-extensions/` (it is the landing source), recompiled from source | done: by an Opus rocq-prover; audited by the main session (24 files token-identical under the map, fresh-directory recompile rc=0, axiom block counts unchanged); record in the probe's `STATUS.md`, last section |

Facts for step 0.4, computed on 2026-09-19. The reverse closure of its ten
files has 16 modules and does not contain `psl211_endpoints`; it does contain
`pgl27_exec`, `pgl27_models`, `pgg_tableau`, `pgg_tableau_syntax` and the four
rows files, so the chain is recompiled once more after step 0.1. The paper
drafts cite two of the names, `pgl27_word_view_indist` and
`pgl27_word_trace_indist`: `paper-wadt2026/main.tex` lines 134, 135, 1639,
1708, 1709 and `paper-wadt2026-baseline-application/candidate-main.tex` lines
145, 146, 1700, 1762, and `paper-wadt2026/analysis/shinagawa21-paragraph-baseline.tex`
lines 5015, 5016, 5019, 5022 (found by the later full scan). The complete list
of renamed names is
`notes/2026-09-19-230614-renamed-identifiers-input-indistinguishability.md`;
the owner edits the `.tex` files from it. No paper file is edited by this campaign, so after step
0.4 those lines are the owner's to change (deadline of the full paper:
2026-09-24).

## Step 1. Landing of the extensions (spec: `notes/20260919-tableau-three-extensions-probe-design.md`, last section)

| # | Step | State |
|---|---|---|
| 1.A | LANDING 1 (design `notes/2026-09-20-000000-tableau-extensions-landing-design.md`, which regroups the landings: the framework lands once with stages A and B together, then rows): framework, four rows files, `psl211_reading_constancy.v` comments, withdrawal of `kim_centi_cert40` and its `_epsE`, `pgl27_word_sampled` and `pgl27_row_word_branch39` moved into `pgl27_rows.v` | DONE, production commit b03b467: staged build, soundness and naming audits, fix pass 1, its audit, fix pass 2 audited by the main session, `cp`, seven files recompiled, as-built fidelity rc=0 (record: the landing directory's `STATUS.md`) |
| 1.B | LANDING 2: `lib/var_dist_supp.v` (`card_tnth_count` leaves), new `security/var_dist_joint_law.v` (the five joint-law lemmas, so that `lib/` keeps no dependency on `security/`), `five_card_mixing.v` (`card_tnth_count` arrives, the two `*40` declarations leave), new `manifest/pgg_tableau_arm_relations.v`, new `instances/kim2025/five_card_proximity.v` | DONE, production commit 0397f8e: staged build, two audits, fix pass 1, its audit (GO), fix pass 2 audited by the main session, `cp`, fifteen files recompiled, three `_CoqProject` lines, as-built fidelity rc=0. `card_tnth_count` moved (item 3.2 closed); `idealproximity_ceiling` landed as `idealproximity_prop_at2` |
| 1.C | LANDING 3, stage C: `pgl27_prior_sample`, the prior-indexed family, its manifest row, the word proximity row; clean the `first [...]` list in `var_dist_fdist1_uniform` | DONE, production commit 31468b6: staged build, two audits, fix pass 1, its audit, fix pass 2 audited by the main session, `cp` of seven files (`lib/var_dist_supp.v` received `var_dist_fdist1_uniform`), nineteen files recompiled, as-built fidelity rc=0. New names `pgl27_row_word_families_sampledE`, `pgl27_word_uniform_ideal_close_false`; the `first [...]` list is gone |
| 1.D | LANDING 4, stage D: new file `instances/psl211/psl211_word_model.v`, its manifest row, the word proximity row, rewrite of the production comment of `psl211_alldecks_constancy_false_word584` | DONE, production commit 2373576: staged build, two audits, fix pass 1, its audit, fix pass 2 audited by the main session, `cp` of six files, two `_CoqProject` lines, fifteen files recompiled, as-built fidelity rc=0. New names `psl211_word_law_le40`, `psl211_word_law_by_var_dist_le2` |
| 1.E | As-built record of the four landings | DONE: `notes/2026-09-20-054425-tableau-extensions-as-built.md`; the spec carries the landed status and the correction of its change 5 |

## Step 2. Per-instance `tableau/` directory (proposal: `notes/2026-09-19-124500-instance-tableau-directory-proposal.md`)

Design with the decisions: `notes/2026-09-20-060000-instance-tableau-directory-design.md` (one directory per instance, one file per phase, `<inst>_tableau_<phase>.v`, plus a checks file; the mathematics does not move; no `-R` line). Template for the provers: `notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md`.

| # | Instance | State |
|---|---|---|
| 2.1 | S5 (pilot) | DONE: `instances/s5/tableau/`, six files, `s5_rows.v` retired; staged build, audit, fix pass audited by the main session, `cp`, as-built fidelity rc=0 |
| 2.2 | PSL(2,11) | DONE: `instances/psl211/tableau/`, six files, `psl211_rows.v` retired, `psl211_word_proximity.v` reduced to the distance mathematics; staged build, audit, fix pass audited by the main session, `cp`, as-built fidelity rc=0. Two comment repoints deferred to 2.5 |
| 2.3 | PGL(2,7) | DONE: `instances/pgl27/tableau/`, six files, `pgl27_rows.v` retired, `pgl27_proximity.v` reduced to the reading and the distance mathematics (it imports no tableau module); the AnalysisBridged header carries a locator table of the seven published rows; staged build, audit, fix pass audited by the main session, `cp`, as-built output byte-identical. Two comment repoints deferred to 2.5 |
| 2.4 | five-card | DONE: `instances/kim2025/tableau/`, six files, `five_card_rows.v` retired, `five_card_proximity.v` reduced to three laws and the distance; Kim's input-privacy bound is carried at Sampled, and the AnalysisBridged header names per row by what the manifest reaches its level; staged build, two pre-audit passes, audit, fix pass audited by the main session, `cp`, as-built output byte-identical |
| 2.5 | Closing pass | DONE (comments only, 16 files): six citations of retired or reduced files repointed to the file that holds the declaration, ten of the twelve cross-instance wording items brought to one true form per instance (S5 branches at Executable and its cut is the identity, so it keeps its own sentences; two items needed no edit); by an Opus rocq-prover, audited by the main session (code tokens identical by script over all 16 files); 41 files recompiled rc=0. As-built note: `notes/2026-09-20-103832-tableau-directories-as-built.md`. Open: the docstring of `pgl27_algebraic_start` says "three probability models" where the header now says families |

## Step 2.6. Owner's two naming decisions (2026-09-20)

| # | Item | State |
|---|---|---|
| 2.6a | `Reprice` -> `ConcludedBound`, `no_reprice` -> `no_concluded_bound`, `*_reprice39` -> `*_bound39` and the rest, nine names, 65 occurrences in five files; no prose used the word | DONE by an Opus rocq-prover; audited by the main session (code tokens and comment words identical to HEAD under the map, by script; the 28 files of the framework's reverse closure recompiled rc=0; four recorded rejections re-checked without `Fail`, same reasons) |
| 2.6b | The economic words for a relation ("spends", "price", "currencies", "pays", "buys", "owes", "charges") replaced by the field's terms: a hop of a hybrid and the loss it adds ("loses at most"), perfect against statistical security, tight against slack, "fuel" for the interpreter step bound, the plain relation elsewhere; measured times keep "costs". 37 files, comments only | DONE. 119 passages by an Opus rocq-prover (`notes/probes/2026-09-20-economic-words-pass/economic_words_changes.md`); two Opus audits (`audit-security-rows.md`, `audit-plain-rows.md`: no lost clause, no false count, two MUST each, all one-line); fix pass 1 by an Opus rocq-prover on the main session's thirteen rulings (`fix_pass_1.md`; two of the auditors' replacement sentences were not taken because they were false of the declaration), audited by the main session (code tokens identical to HEAD in all 37 files, the delta read sentence by sentence); reverse closure of 95 files recompiled single-file, all rc=0 (`closure_compile.log`) |
| 2.6c | `PublishedRow` -> `Published`, `PublishedRowAt` -> `PublishedAt`, `AnalysisPathRow` -> `AnalysisPath`, `*_rowE` -> `*_pathE`, instance values `<inst>_<model>_published` and `<inst>_<model>_path`, then the prose (868 uses of "row" in 26 files) as an audited comment pass. Owner decided 2026-09-20: `Published`, all layers. Plan: `notes/2026-09-20-111257-published-row-rename-plan.md`. Runs after 2.6a and 2.6b | DONE in two commits. First (c07f6a8): layers A to E, 110 identifiers, 710 occurrences, 16 files; map, checker, Locate probe, closure log and the re-check of 16 recorded `Fail` commands in `notes/probes/2026-09-20-published-rename/`; names list `notes/2026-09-20-142813-renamed-identifiers-published.md`. Second: the prose, 44 files, 823 nouns changed one for one by four Opus rocq-provers under `prose_sheet.md` (program 592, path 231; about 230 rows of matrices, tables and traces keep the word), 109 ruled regions (`prose_rulings.md`: 38 rulings on the agents' lists, then 22 on two Opus audits that read all 847 sites and opened about 280: `audit-prose-kim-pgl27.md`, `audit-prose-manifest-psl-s5.md`; the largest finding: 22 sites of `pgl27_profile_privacy.v` are neither program nor path and read "analysis"), two fix passes audited by the main session with `check_prose.py` (every region mapped to a ruling id; code tokens identical but for two ruled items: the bound variable of the manifest's last `Check`, and two `Check` lines the client lacked since landings 3 and 4); reverse closure of 60 files recompiled single-file, all rc=0. Frozen: two sites of `instances/psl211/psl211_exec.v` (127, 129) in the program sense, for the owner (`frozen_prose_occurrences.md`) |
| 2.6d | Reminder owed to the owner when every other task is done: twelve files in the forward closure of `psl211_endpoints.v` still hold 49 economic words, and four more `-ing`/`-ed` forms found later (`notes/probes/2026-09-20-economic-words-pass/frozen_occurrences.md` and its addendum; the largest: `protocol/pgg_instance.v`, `instances/psl211/psl211_exec.v`, `instances/psl211/psl211_profile.v`, whose three sentences are word-for-word twins of sentences already rewritten in `pgl27_profile.v`). Also for that reminder: `L1`, `L2` as list variable names in code (`security/pgg_schreier.v`, `security/pgg_schreier_weighted.v`, `instances/pgl27/pgl27_orbit.v`, `instances/psl211/psl211_alldecks.v`, and the frozen `psl211_orbit.v`, `transitivity_privacy.v`, `smc_interpreter.v`). Editing a frozen file means recompiling the endpoint file (900 s, 17 GB), which is the owner's call | open |
| 2.6e | The project's barred words already in production comments of editable files (scan of 2026-09-20): the logic-circuit word as a metaphor for a premise, 13 uses in `reconstruct/invariant_profiler.v` (6), `groups/pgg_raag_clique.v` (4), `reconstruct/gap_dimension.v`, `reconstruct/s5_nogo.v`, `instances/denboer1989/den_boer_profile.v`; the norm abbreviation for the sum of absolute differences, 22 uses in `security/pgg_schreier.v` (8), `security/pgg_mixing.v` (5), `instances/s5/s5_models.v` (4), `instances/s5/s5_analysis.v` (2), `security/pgg_schreier_weighted.v` (2), `instances/kim2025/five_card_kim.v` (1). `legacy/` is out of scope. Comments only, after 2.6c because the files overlap | DONE for comments of editable files: 9 files, 27 sites by an Opus rocq-prover (`notes/probes/2026-09-20-barred-words-pass/changes.md`), audited by the main session (code tokens identical to the parent in all nine; every sentence read). The pass found that the identifier the three `reconstruct/` comments named exists nowhere in the tree; they name the predicate `feasible` of `invariant_profiler.v`. Left for the owner (`frozen_and_code_residue.md`): two comment sites of the frozen `reconstruct/algebraic_rigidity.v`, and word-length variables spelled with a capital letter and a digit in code of six files with the comments that mirror them. Reverse closure of 60 files recompiled single-file after the P8 probe released the compile lock, all rc=0 |
| 2.6f | Owner, 2026-09-20: two more barred nouns, the one that named a constructor of the framework's sum type of security evidence, and "port" for that sum type. No single synonym: each site says what the thing is. Identifiers: `SecurityProperty` with `*Property` values, `security_property_of`, `*_propertyE`, `SecurityEvidence`, `EvidenceProp`, `ab_evidence`, `evidence_conclude`, `evidence_property`, file `manifest/pgg_tableau_security_property_relations.v` (36 identifiers, 166 occurrences; map and checker in `notes/probes/2026-09-20-security-property-rename/`). Prose: about 360 sites by `prose_sheet.md` there, audited. Git history is left as it is (owner). P8 (3.4) lands after this | DONE in two commits. Identifiers (77a2c84): 36 names, 166 occurrences, the file moved to `manifest/pgg_tableau_security_property_relations.v`; names list `notes/2026-09-20-205851-renamed-identifiers-security-property-and-evidence.md`. Prose: 362 sites in 24 files rewritten by three Opus rocq-provers under `prose_sheet.md` (each site says what the thing is: the security property, the evidence, the proposition the evidence proves, the certify statement, a tail lemma; the verb rule made about 25 sentences true that were untrue before the pass), two Opus audits that read all 360 sites with old and new text (`audit-prose-framework.md`, `audit-prose-instances.md`), one fix pass of 48 edits on the main session's rulings (`prose_rulings.md`, `prose_fix_pass.md`), audited by the main session (code tokens identical to the parent in all 24 files; zero occurrences left outside one frozen site); one recompile of the batch, 41 files, all rc=0. Frozen: `instances/psl211/psl211_exec.v:127`, for the owner. Git history left as it is (owner) | 

## Step 3. Recorded small items

| # | Item | State |
|---|---|---|
| 3.1 | "deck description" in `instances/psl211/psl211_models.v`: the tree's word for the whole run argument `psl211_inputT` (a chirality bit and a deal); 21 of 30 sites meant the deal `psl211_deal` and now say so, 9 kept | done by an Opus rocq-prover, audited by the main session (code tokens identical by script, the two notations read, sixteen files recompiled rc=0) |
| 3.2 | Home of `card_tnth_count`: decided, `instances/kim2025/five_card_mixing.v`, its only user, whose den Boer colour census its comment already speaks of; moved at the landing of stage B, which edits `lib/var_dist_supp.v` anyway | done with landing 2 (0397f8e) |
| 3.3 | Dated note recording the removed `five_card_row_repeated_at_manifest_level` | done: `notes/2026-09-19-223500-removed-five-card-row-repeated-at-manifest-level.md` |
| 3.5 | Pass over production comments recorded by the landing audits | partly done in the same commit: witness and port in `five_card_proximity.v`, "in one column" (one of two sentences) in `psl211_word_proximity.v`, nine "ceiling" in `five_card_rows.v`. Still open: the second "in one column" sentence of `psl211_word_proximity.v` (about lines 23-25), and everything that waits for the owner: "spend", "price", "currency", "cost", and `Reprice` |
| 3.4 | P8, the two parts that were argued and not compiled: that no implication into the ideal-proximity proposition holds uniformly in the certificate at a number below two, and the ideal-proximity proposition derived from an input-indistinguishability certificate's own fields | DONE. Spec `notes/20260920-p8-arm-relations-probe-design.md` (ledger of twelve claims, probe, two audits folded), plan `notes/2026-09-20-221500-p8-landing-plan.md`, probe and landing records in `notes/probes/2026-09-20-p8-arm-relations/`. Landed by an Opus rocq-prover: `manifest/pgg_tableau_security_property_relations.v` (one certificate over every model whose two secrets are the constants true and false refutes the proposition below two, with no premise; the universal over certificates; under the hypothesis that the run argument's finite coordinate is independent of the cut, the certificate and the proposition at the marginal bound's epsilon once), `lib/var_dist_supp.v` (disjoint supports are at two), new `lib/fdist_prod_cst_cond.v`, `security/var_dist_joint_law.v`, the product hypothesis at the PGL(2,7) word model and the five-card one-cut model in the exact shape the construction asks for, and three comparisons of numbers. Two Opus audits of the landing (soundness, naming), one fix pass on the main session's rulings, audited by the main session: reverse closure of 43 files recompiled single-file with `scripts/comment_pass/`, fidelity file of 32 declarations and 8 field projections recompiled against production, three classical axioms only |

## Step 4. Roadmap groups of the spec (each probe-first: spec and ledger, probe, two audits, fold, plan, landing)

| # | Group | State |
|---|---|---|
| 4.1 | Observers | open |
| 4.2 | Refutation rows and NegativeTransfer | open |
| 4.3 | Terminals below AnalysisBridged | open |
| 4.4 | One-position marginal bounds | open |

## Rename map (step 0.1)

`SpectralDecay` -> `InputIndistinguishability`; `SpectralCert` ->
`IndistinguishabilityCert`; `MkSpectralCert` -> `MkIndistinguishabilityCert`;
`sc_b`, `sc_Hd`, `sc_ideal`, `sc_close`, `sc_const` -> `ic_*` (the prefix
`sc_` is also the prefix of the fields of `SpectralCertificate` in
`security/pgg_schreier.v`, a record that does hold a spectral gap);
`SpectralPayload` -> `IndistinguishabilityPayload`; `SpectralPropAt` ->
`IndistinguishabilityPropAt`; `certify_spectral` ->
`certify_indistinguishability`; `spectral_tail` -> `indistinguishability_tail`;
`mk_spectral` -> `mk_indistinguishability`; `view_indist_of` ->
`view_indistinguishability_of`; the seven `five_card_row_*spectral*` names with
`spectral` replaced by `indistinguishability`;
`spectral_cert_reading_constancy` ->
`indistinguishability_cert_reading_constancy`.

The word "spectral" stays on results that do hold a spectral gap or a
convergence rate: `kim_spectral_gap*`, `kim_spectral_convergence`,
`pgl27_spectral_*`, `s5_spectral_*`, `SpectralCertificate`.

Check script (session-local): `scratchpad/check_rename_arm.py`.
