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
| 1.C | LANDING 3, stage C: `pgl27_prior_sample`, the prior-indexed family, its manifest row, the word proximity row; clean the `first [...]` list in `var_dist_fdist1_uniform` | staged build running in `notes/probes/2026-09-20-tableau-extensions-landing3/` |
| 1.D | LANDING 4, stage D: new file `instances/psl211/psl211_word_model.v`, its manifest row, the word proximity row, rewrite of the production comment of `psl211_alldecks_constancy_false_word584` | open |
| 1.E | As-built fidelity note for the four landings | open |

## Step 2. Per-instance `tableau/` directory (proposal: `notes/2026-09-19-124500-instance-tableau-directory-proposal.md`)

Open. One file per phase, per instance. Needs its own plan after step 1.

## Step 3. Recorded small items

| # | Item | State |
|---|---|---|
| 3.1 | Eighteen "deck description" sentences in `instances/psl211/psl211_models.v` (file is not in the endpoint file's forward closure) | open |
| 3.2 | Home of `card_tnth_count`: decided, `instances/kim2025/five_card_mixing.v`, its only user, whose den Boer colour census its comment already speaks of; moved at the landing of stage B, which edits `lib/var_dist_supp.v` anyway | done with landing 2 (0397f8e) |
| 3.3 | Dated note recording the removed `five_card_row_repeated_at_manifest_level` | done: `notes/2026-09-19-223500-removed-five-card-row-repeated-at-manifest-level.md` |
| 3.4 | P8, the two parts not compiled: a countermodel for the implication below the ceiling two; proximity derived from the certificate's own fields | open |

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
