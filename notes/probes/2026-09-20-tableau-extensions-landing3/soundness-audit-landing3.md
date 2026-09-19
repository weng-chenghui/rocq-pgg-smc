# Soundness audit of landing 3 (PGL(2,7)) of the Tableau extensions

Date: 2026-09-20. Repository `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc`,
branch `feat/tableau-extensions-probe`, HEAD `0c4a4ef`. Audited object: the
frozen export
`notes/probes/2026-09-20-tableau-extensions-landing3/`, the six files landing 3
copies into production.

Independent compiles were run only in
`/private/tmp/claude-501/.../scratchpad/land3_sound/`, one Rocq process at a
time through the `rocq1` lock, against the staged `.vo` objects already in the
frozen directory. No repository file was written except this report.
`instances/psl211/psl211_endpoints.v` was never compiled and `make` was never
used.

## Verdict

**GO, conditional on the single MUST below, which is a comment-only edit.**

The code is sound. Every landed statement is the one its declaration proves,
every number checks out, the recompile closure is complete and contains no
cycle, the three recorded `Fail`s each fail for the reason its comment gives,
all three verified here by compiling un-`Fail`ed copies, the mutation check
bites, and all 29 `Print Assumptions` report the classical trio alone.

One comment sentence in `pgl27_proximity.v` states a false impossibility, and
I disproved it by compiling. It is permanent text describing what the
proximity arm refuses, which is the file's own subject, so it must be fixed
before the `cp`. Nothing else blocks.

## Findings

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| L3-1 | MUST | `staged/instances/pgl27/pgl27_proximity.v:495-497` | "A proximity certificate over a prior-indexed actual model therefore cannot take the tree's exact family as its ideal, whatever the two models' distance is." | False. The declaration is `Fail Definition pgl27_word_proximity_cert_unit_ideal ... : IdealProximityCert (amf_sample pgl27_word_family R secretP)` whose ideal is written `amf_sample pgl27_exact_family R secretP`. Compiling that term without its `Fail` gives `The term "secretP" has type "{fdist bool}" while it is expected to have type "amf_index pgl27_exact_family R"` (rc 1, `unfail_unit.v`), which is what the sentence before it says and is a fact about the index written, not about the family. The family at its own index IS a legal ideal here: `Check (fun (R : realType) (secretP : R.-fdist bool) => @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params (amf_sample pgl27_word_family R secretP) (amf_sample pgl27_exact_family R tt) (@pgl27_exact_witness R tt) (pgl27_word_secret secretP))` compiles rc 0 (`pos_checks.v`), leaving `forall ipc_eps, (distance field) -> IdealProximityCert (amf_sample pgl27_word_family R secretP)`. Compiling the next guard without its `Fail` errors at the distance field alone (rc 1, `unfail_uniform.v`), and that guard's own comment (`:601-611`) says so: "it is a well-typed ideal for a word model at any prior: the index is supplied as tt … What the kernel rejects is the distance field". The two comments contradict each other and the second is the true one. | "The term written here is therefore refused before any distance is considered. The same family at its own index tt is a well-typed ideal for this actual model, and what refuses it there is the distance field, which the guard below records." |
| L3-2 | SHOULD | `staged/instances/pgl27/pgl27_proximity.v:283-285` | "The only inexact quantity is that number: the ideal, its witness and the secret are the terms the ideal row already publishes." | Two of the three, not three. The certificate's `ipc_secret` field is `pgl27_word_secret secretP`, typed `{RV (sa_sampleP (pgl27_word_sample secretP)) -> bool}` (`:207-208`), a random variable on the WORD sample space. What `pgl27_row_prior_exact_tableau` publishes is the model `amf_sample pgl27_prior_exact_family R secretP` and the port `ExactIndependence (pgl27_prior_exact_witness secretP)`, whose `ew_secret` is `pgl27_secret R` on the ideal's sample space (`:156-165`). The word secret is not a term that row publishes; the field enumeration two sentences earlier gets this right ("the dealt secret of the word model"). | "The only inexact quantity is that number: the ideal and its witness are the terms the ideal row already publishes, and the secret is the word model's own first projection, typed at the carrier that witness names." |
| L3-3 | SHOULD | `staged/instances/pgl27/pgl27_proximity.v:192-193` | "…so the manifest's description of this path is read off the program and not written beside it." | Under its natural reading the sentence is contradicted by a `Definition`. `pgl27_row_prior_exact` is written out by hand with all five coordinates at `staged/manifest/pgg_analysis_manifest.v:986-988`; what the lemma `published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact` establishes is that the hand-written row and the row `publish` computes (`manifest/pgg_tableau.v:937-941`, `@MkAnalysisPathRow (ab_obs q) AnalysisBridged (ab_f q) t a`) agree by conversion. The tree already has exact wording for this, at `instances/pgl27/pgl27_rows.v:342-344`: "The two rowE lemmas together are what makes the manifest a claim this file discharges rather than a table maintained beside it." | "…so the manifest's row for this path is a claim this equation discharges rather than a table maintained beside the program." |
| L3-4 | SHOULD | `staged/instances/pgl27/pgl27_proximity.v:70-72` | "pgl27_word_proximity_close == the two models' joint laws of reading and secret are within 2^-40" | The header index drops the premise that carries the whole security content. The declaration (`:224-238`) is `(#|C| < profile_k (instance_profile pgl27_algebra))%N -> var_dist … <= 2%:R^-40`, and `profile_k (instance_profile pgl27_algebra) = 4` closes `by []` (`pos_checks.v`, rc 0), so the bound is stated only at coalitions of at most three of the eight seats. Read without the premise the entry states an unconditional bound the file does not prove. The sibling entry at `:100-103` does carry its scope, so this is not the file's convention. | "== below the four-seat threshold, the two models' joint laws of reading and secret are within 2^-40" (re-pad to the file's 80-column banner) |
| L3-5 | SHOULD | `staged/instances/pgl27/pgl27_proximity.v:344` and `:81` | "The certificate's number is under 2^-39, the constant the word row publishes…"; index "== the certificate's number is under 2^-39" | The statement is `ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39 :> R` (`:348-349`), a non-strict bound; "under" reads as strict. The strict fact is true and is proved elsewhere, in `landing_fidelity.v:179-185` (`f_pgl27_word_proximity_lt39`), not by this lemma. The clause that follows ("it is met strictly, the certificate's number being half of the published one") is correct and supported by `pgl27_word_proximity_cert_epsE` giving `2%:R^-40`; keep it. | docstring: "The certificate's number is at most 2^-39, the constant the word row publishes…"; index: "== the certificate's number is at most 2^-39" |
| L3-6 | NOTE | `staged/manifest/pgg_analysis_manifest.v:756-758` | "Row 1 records the same instance and the same cut at the uniform secret alone, its family being indexed by the unit type; the two rows differ in that index and in nothing else." | A cross-row claim no declaration states, which is the class of claim STATUS.md's ruling Q4 dropped from `pgl27_row_prior_exact_rowE`'s docstring. It is also loose: `pgl27_row_exact` (`:864-866`) and `pgl27_row_prior_exact` (`:986-988`) agree literally in four coordinates and differ in `apr_model`, and the two families differ in the index type AND in the sample map (`fun R _ => pgl27_sample R` against `fun R p => @pgl27_prior_sample R p`, `instances/pgl27/pgl27_models.v:417-419` and `staged/instances/pgl27/pgl27_models.v:432-434`). The maps do agree at the uniform prior: `amf_sample pgl27_exact_family R tt = amf_sample pgl27_prior_exact_family R (fdist_uniform (R := R) card_bool)` closes `by []` (`pos_checks.v`, rc 0). | Shortest: end the sentence at "indexed by the unit type." If the relation is worth keeping, the verified form is: "The two rows agree in their other four coordinates, and the member of this row's family at the uniform prior is the member of Row 1's at tt." |
| L3-7 | NOTE | `staged/instances/pgl27/pgl27_proximity.v:510-513` | "This is the quantity a proximity bound between two models whose secrets are drawn from those two laws has to beat, whatever the rest of the two executions does." | "beat" is a narrative word for a relation, which the project's rule on metaphor words for mathematical results excludes. The relation is the one `pgl27_word_uniform_ideal_not_close` uses: pushing both joint laws along the secret coordinate leaves the two priors, `var_dist` between them is 1 (`:514-516`), and `var_dist_fdistmap` makes the joint distance at least that, so any `ipc_eps` a certificate can carry between such models is at least one. The sentence is otherwise true. It is token-identical to the probe's, so this is a new-permanent-text finding and not a landing edit. | "Any number a proximity certificate can carry between two models whose secrets are drawn from those two laws is therefore at least one, whatever the rest of the two executions does." |
| L3-8 | NOTE | `staged/instances/pgl27/pgl27_proximity.v:391-392` | "The proximity row publishes the manifest's row for the word path, as its input-indistinguishability sibling does." | The sibling this file names everywhere else is `pgl27_row_word_branch39` (`:416`, `:428`, `:442`), and there is no `published_row pgl27_row_word_branch39 = pgl27_row_word` anywhere: `instances/pgl27/pgl27_rows.v` declares `pgl27_row_word_branch39` (`:493`) and `pgl27_row_word_branch39_armE` (`:502`) and no `rowE`. The equation that IS stated is `pgl27_row_word_rowE : published_row pgl27_row_word_tableau = pgl27_row_word` (`pgl27_rows.v:345-347`), about the other word program. The claim is true of branch39 by conversion but unstated, so the comparison points at nothing a reader can open. | "The proximity row publishes the manifest's row for the word path, as pgl27_row_word_rowE of pgl27_rows.v says of the word program." |
| L3-9 | NOTE | `landing_fidelity.v:59-72` | section banner "The four additions to the edited files" | Landing 3 adds five declarations to the four edited production files: `pgl27_prior_sample`, `pgl27_prior_exact_family`, `PGL27Analysis.prior_sample`, `PGL27Analysis.prior_exact_family`, `pgl27_row_prior_exact`. Four are ascribed at a type (`:63-72`); `PGL27Analysis.prior_sample` appears only as the bare provenance `Check` at `:52`, which prints a type and asserts none, so an alias pointed at the wrong constant would pass the fidelity file and be caught only by the token diff. The added ascription compiles: `pos_checks.v` (rc 0) contains it verbatim and Rocq answers `forall R : realType, {fdist bool} -> SampleAdapter R pgl27_exec_plug`. | Retitle to "The five additions to the edited files" and add, beside the other four: `Check (PGL27Analysis.prior_sample : forall (R : realType) (secretP : R.-fdist bool), SampleAdapter R pgl27_exec_plug).` |
| L3-10 | NOTE | `staged/instances/pgl27/pgl27_proximity.v:73-74` | "pgl27_word_proximity_cert_idealE == the certificate's ideal is the ideal row" | The lemma (`:302-308`) is a conjunction of two equations, and neither says the ideal is a row: `ipc_ideal (…) = amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP` and `ExactIndependence (ipc_witness (…)) = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP`. A model is not a row. The declaration's own docstring states this correctly. | "== the certificate's ideal and witness are the model and the port the ideal row publishes" |
| L3-11 | NOTE | `staged/instances/pgl27/pgl27_proximity.v:64` and `:136` | "the instance's coalition view" | Landing 2's N10 convention, which this landing applies at `:468` (the probe's "view" became "reading"), keeps "view" inside identifiers and writes "reading" in prose. Two prose occurrences were left. Low confidence that this is worth a token change: both sentences are about `pgl27_view`, so naming the identifier's concept is defensible. | If applied: "the instance's coalition reading" in both places. |

## What was checked and found sound

Numbers and type honesty.

- `ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40` (`pgl27_word_proximity_cert_epsE`), the field being `sw_bound_eps (pgl27_word_marginal_bound R)` whose epsilon is `2%:R^-40` (`instances/pgl27/pgl27_word_privacy.v:90-92`).
- The terminal's obligation is `ipc_eps cert <= odflt (ipc_eps cert) (c R)` (`manifest/pgg_tableau.v:848`), and `pgl27_reprice39 = fun R => Some (2%:R^-39 : R)` (`pgl27_rows.v:417`), so the obligation the row discharges is `ipc_eps cert <= 2^-39`, met with `2^-40` and therefore strictly. `landing_fidelity.v:179-185` states the strict form separately, which is the right place for it.
- The header's advantage reading, `:39-41`, is correct: `var_dist` is the sum of absolute differences, twice the total variation distance, the row publishes `2^-39` on it, and half of `2^-39` is `2^-40`, which is the number the header gives for a distinguisher's advantage against the published row.
- `cert_eps` is `sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` (`pgg_tableau.v:470-473`), so `pgl27_word_proximity_eps_halfE` and the header's "that number added to itself" are exact.
- `pgl27_word_proximity_cert_eps_lt2`'s "about 4.5e-13 of that bound": `2^-40 / 2 = 2^-41 = 4.547e-13`. Correct.
- The comparison "not a weak one, as the proximity certificate of Kim's one-cut model is" is qualitative and consistent with `instances/kim2025/five_card_proximity.v:293`, `ipc_eps … = 1 / 50`.
- No sentence calls an upper bound "the distance", and the certificate's number is described as a number the instance chooses (`:326-329`), matching the record's own comment (`pgg_tableau.v:210-214`).

The threshold premise.

- `pgl27_word_proximity_close` keeps `(#|C| < profile_k (instance_profile pgl27_algebra))%N` (`:226`), the record's own premise shape (`pgg_tableau.v:222-223`). `profile_k = 4` here, confirmed both by `profile_k_pgl27` (`instances/pgl27/pgl27_profile.v:122-123`) and by my own `Goal profile_k (instance_profile pgl27_algebra) = 4. Proof. by []. Qed.` (rc 0). Coalitions satisfying the premise are the subsets of the eight seats of size at most three.
- Every sentence about that lemma except the header index entry (L3-4) carries the restriction. Its docstring's "the proof spends it twice, on the ideal model's own independence and on pgl27_view_mixing" matches the proof body (`:271`, `:273`). Its closing remark, that `pgl27_word_mixing` carries no coalition premise so the same bound is reachable at every coalition by another route, is true of the statement it is attached to, whose right-hand side is the ideal's joint law and not a product of marginals; `pgl27_view_mixing`'s own proof uses the coalition premise only for the independence rewrite (`pgl27_word_privacy.v:243-246`).
- The header's above-threshold citations are stated correctly. `pgl27_view_dep_k4` (`instances/pgl27/pgl27_secrecy.v:116-118`) is `#|pgl27_leak_coalition| = 4 /\ ~ pgl27P |= pgl27_secret _|_ pgl27_view pgl27_leak_coalition`, and `pgl27P` is `(fdist_uniform card_bool) `x (`U pgl27_G_pos)` (`:66-67`), the uniform prior, exactly as the header says; `pgl27_view_leak_k4` (`:192-194`) gives `0 < `I(pgl27_secret ; pgl27_view pgl27_leak_coalition)`, strictly positive mutual information, again as the header says. Both are at the fixed deck pair, `pgl27_view` reading `orbit_encode u.1` (`:73-75`).

Vacuity of the prior-indexed witness.

- `pgl27_prior_exact_witness`'s secret is `pgl27_secret R`, the first projection of the sample point (`pgl27_secrecy.v:71`), a genuinely non-constant function of the sample space, not a constant.
- Its independence field is `pgl27_view_indep_gen secretP H3` transported along `pgl27_prior_viewE`. `pgl27_view_indep_gen` (`pgl27_word_privacy.v:222-224`) holds at every `secretP : R.-fdist bool`, degenerate ones included, because it descends from three-transitivity of PGL(2,7), which does not mention the secret's law. No comment claims more than that. At a point mass the independence is trivially true and the header does not pretend otherwise; the non-degenerate content is visible at the uniform prior, where `pgl27_view_dep_k4` shows the threshold is sharp. I found no vacuity overclaim.

Manifest Row 10 (`staged/manifest/pgg_analysis_manifest.v:699-758`).

- Field order and the capabilities-plus-level-justification shape match Row 9's (`:629-697`) and the other rows'.
- `completion level AnalysisBridged`, `transfer status StaticExecutedOnly`, `assumption status BaselineClassicalOnly` and `typed row pgl27_row_prior_exact` are the five fields of the `Definition` at `:986-988` and of the row `publish` computes; `landing_fidelity.v:100-102` closes the equation by the landed lemma.
- The `StaticExecutedOnly` reason holds: `pgl27_prior_sample`'s distribution is `pgl27P_gen secretP` (`staged/instances/pgl27/pgl27_exec.v:640ff`) and `pgl27P_gen secretP = secretP `x (`U pgl27_G_pos)` (`pgl27_word_privacy.v:97-99`), the given prior times the uniform law on the group, so the model compares no idealized shuffle with a real one.
- "bound or certificate: none" holds: the row's port is the exact arm, and `ExactWitness` (`pgg_tableau.v:171-179`) has no epsilon field.
- The two bridge names resolve: the distribution-to-observer bridge `pgl27_prior_viewE` has `pgl27_view R C` on the right (`:145`) and `PGL27Analysis.static_view := @pgl27_view` (`staged/instances/pgl27/pgl27_analysis.v:138`); the final bridge `pgl27_prior_exact_witness` does carry `pgl27_view_indep_gen`, transported along `pgl27_prior_viewE`, which the block's phrasing "whose independence field is pgl27_view_indep_gen" compresses but does not misstate.
- "the profile's own privacy threshold being four" matches `profile_k = 4`.
- Ten typed rows: I counted `Definition … : AnalysisPathRow :=` in the staged manifest and got exactly 10. Both "the ten typed rows" banners, `pgg_analysis_manifest.v:1984` and `staged/manifest/pgg_analysis_client.v`, are right.

The three intended differences from the probe.

- (a) `var_dist_fdist1_uniform`'s `by rewrite fdist1E.` The statement is unchanged and `landing_fidelity.v:243-246` closes the probe's statement by `exact:`.
- (b) `pgl27_cross_model_proximity`. Compiling the term without its `Fail` (`unfail_cross.v`) gives rc 1 and `The term "pgl27_word_proximity_cert" has type "forall (R : realType) (secretP : {fdist bool}), IdealProximityCert (amf_sample pgl27_word_family R secretP)" while it is expected to have type "IdealProximityPayload (tableau_at (pgl27_dealt sample pgl27_exact_family))" (cannot unify "amf_index (sp_f (tableau_at (pgl27_dealt sample pgl27_exact_family))) R" and "{fdist bool}")`. That is the index-type mismatch the comment states, not an unknown reference and not a parse error. The respelling did its job.
- (c) `pgl27_row_prior_exact_rowE` restated at `pgl27_row_prior_exact`. Dropping the probe's `pgl27_row_exact` clause was right: nothing in the tree states it. The new docstring's five-coordinate reading is accurate against `publish`; its closing clause is L3-3.

Placement, closure and cycles (ruling Q1).

- `pgl27_prior_viewE` needs `pgl27_static_obsE` (`pgl27_rows.v:159`) and `pgl27_prior_exact_witness` needs `ExactWitness` (`pgg_tableau.v:171`). Following `Require` lines, `pgl27_rows` requires `pgg_tableau`, which requires `pgg_analysis_manifest`, which requires the facades, which require `pgl27_models`. Neither name can be in scope in `pgl27_models.v`, so the design's section-2 placement is impossible and `pgl27_proximity.v` is the correct home.
- A Python walk over every `Require` line outside `notes/`, `_build` and `.git` gives the reverse closure of the five edited files as exactly 13 modules: `pgl27_models`, `pgl27_analysis`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client`, `pgg_tableau_arm_relations`, `five_card_proximity`. Every one is among the eighteen staged files, so the closure the landing recompiles is complete; nothing outside it imports `pgl27_exec`, `pgl27_models`, `pgl27_analysis`, `pgg_analysis_manifest` or `pgg_analysis_client`.
- `pgl27_proximity` is a new leaf: no module in the tree requires it, and its own requires all sit strictly above it, so the `cp` introduces no cycle. No duplicate module basenames exist in the tree, so no `Require` can be captured.
- The forward closure of `instances/psl211/psl211_endpoints.v` is 34 modules besides itself, and its intersection with the nineteen staged files plus `pgl27_proximity` is empty. `psl211_endpoints.v` therefore does not need recompiling and its `.vo` stays valid for `psl211_reading_constancy`, `psl211_models` and `psl211_analysis`, the three modules that load it.

`landing_fidelity.v`.

- All 24 non-`Fail` declarations of `pgl27_proximity.v` are restated or ascribed, and the four additions to production files are ascribed at a type; the fifth, `PGL27Analysis.prior_sample`, is L3-9.
- The three forced differences are handled as STATUS.md says: the R7 pair at the probe's unprefixed statements (`:167-171`), and `pgl27_row_prior_exact_rowE` in both the landed form (`:100-102`) and the probe's raw-family form (`:106-110`).
- The six provenance `Check`s would each be an error against production's `.vo`. I grepped every `.v` file outside `notes/`, `_build` and `.git` for `pgl27_prior_sample`, `pgl27_prior_exact_family`, `prior_exact_family`, `Definition prior_sample` and `pgl27_row_prior_exact`: not one occurrence anywhere in production. `pgl27_proximity` is not a module of the tree at all, so the sixth `Check` has no production reading either.
- Mutation check. I restated `f_pgl27_word_proximity_le39` with `2%:R^-41` in place of `2%:R^-39` and kept `exact: pgl27_word_proximity_le39.` The compile fails, rc 1, `Error: Cannot apply lemma pgl27_word_proximity_le39` (`mut_le39.v`). The restatements are load-bearing.
- Assumptions. `landing_fidelity.out` holds 29 `Print Assumptions` blocks, the distinct axiom names across all of them being `constructive_indefinite_description`, `functional_extensionality_dep` and `propositional_extensionality`, with no block reporting closure under the global context and no `Error` line in the run. The 29 are the five landed declarations outside the new file and the 24 non-`Fail` declarations inside it, so every landed lemma and row is covered.

Scans.

- I re-ran the scan for the project's banned vocabulary list over the six landed files: no hit. `ceiling` survives only in `five_card_rows.v`, a chain-consistency copy this landing does not own, matching `verify.out`.
- No `Axiom`, `Parameter`, `Admitted` or `Abort` is introduced by any landed file.

## What I did not re-do

The mathematics of the 24 statements, audited in
`notes/probes/2026-09-19-tableau-extensions/soundness-audit-stageC.md`, and the
token identity with the probe, verified by `verify.py` and printed in
`verify.out`.

## Files compiled for this audit

All in `/private/tmp/claude-501/.../scratchpad/land3_sound/`, load path
production first, then `-Q . land3_audit`, then the frozen directory's staged
roots last.

| file | rc | what it establishes |
|---|---|---|
| `pos_checks.v` | 0 | the exact family at `tt` is a well-typed ideal for the word model at a free prior; `PGL27Analysis.prior_sample`'s ascription; `profile_k = 4`; the two exact families agree at the uniform prior |
| `unfail_unit.v` | 1 | the first guard fails on the index type, `secretP : {fdist bool}` against `amf_index pgl27_exact_family R` |
| `unfail_uniform.v` | 1 | the second guard fails at the distance field and nowhere earlier |
| `unfail_cross.v` | 1 | the third guard fails on the index type of the Sampled coordinate's family |
| `mut_le39.v` | 1 | a mutated fidelity restatement does not close |
