# Naming, style and record audit of stage C

2026-09-19. Opus auditor, independent of the prover and of the stage A and
stage B audit rounds. Object: the frozen export of
`notes/probes/2026-09-19-tableau-extensions/` at commit `777f5cf`, under
`<scratchpad>/extC_frozen/notes/probes/2026-09-19-tableau-extensions/`. Every
line number below without a path is a line of that frozen copy. Production line
numbers carry their path.

Rocq work: one renamed copy of the probe at `<scratchpad>/extC_naming/ren`,
compiled through the shared lock against the main session's `.vo` set. No repo
file was edited except this one. `instances/psl211/psl211_endpoints.v` was never
read, never compiled, and no `make` was run.

Stage B's naming audit kept the long `IdealProximity*` / `certify_idealproximity`
/ `ipc_*` names; that decision is not re-raised. Stage B's prose defects were
re-checked against stage C and **none of them recurs**: no "the whole advantage"
or "the whole of what is lost" phrasing (S1, S2), no one word for two provably
different numbers (S3), no banner or index line off 80 bytes (N1).

## Findings

| ID | Severity | File:line | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| C1 | BLOCKING | `p5_mutations.v:66-76` | The rendered comment on the second recorded rejection ends: "The rejection is the arm refusing to compare two models whose secrets are drawn from different laws, which is what a distance of `2^-40` could not bound: pushing both joint laws forward along the secret coordinate leaves the two priors themselves, and those are one apart in the sum of absolute differences when the prior is a point mass." | Two defects. (a) Nothing in the probe proves that last sentence. `STATUS-stageC.md:274-284` says so explicitly — "The semantic half of this rejection is argued and not compiled, and is marked as argued here" — and lists the two missing ingredients (a lower bound on `var_dist` by one of its terms, and an evaluation of `var_dist (fdist1 true) (fdist_uniform card_bool)`). The file carries no such marking: a regex for `argued`, `not compiled`, `judged not` over `p5_mutations.v` returns nothing. The brief requires the marking wherever the claim appears. (b) The `Fail` at `:77-86` rejects one written term. It is not a proof that no term of that type exists, and the sentence "which is what a distance of `2^-40` could not bound" asserts exactly that. | Replace the last two sentences with: "What the kernel rejects is the distance field, whose proof is stated between the word model at secretP and the exact model at secretP and not between the word model at secretP and the exact model at the uniform prior. This rejects the term written here and not every term. That no proof of the field exists at a non-uniform prior is argued and not compiled: pushing both joint laws forward along the secret coordinate leaves the two priors themselves, which are one apart in the sum of absolute differences at a point-mass prior, against a bound of `2^-40`." Re-read against the `Fail Definition` at `:77-86` and against `STATUS-stageC.md:274-284`; it drops no claim and adds no new one. Comment only. The file compiles unchanged around it (`p5_mutations.v` rc=0, 4 s, in my renamed copy). |
| C2 | BLOCKING | `STATUS-stageC.md:226-228`, and the same claim in `p5_pgl27_word_proximity.v:247-248` | "Every row equation in the two program files closes by `exact: erefl` and never by `by []`, `done` or `by split`, following the hang shape recorded in `STATUS.md`." | False. I listed all seventeen `Proof.` lines of the two files by script. `exact: erefl` closes three: `pgl27_word_proximity_cert_epsE` (`:185`), `pgl27_row_word_proximity_rowE` (`:256`), `pgl27_row_word_arms_sampledE` (`:285`). Five close otherwise: `pgl27_row_prior_exact_armE` (`p5_pgl27_prior_ideal.v:144`, `by []`), `pgl27_row_prior_exact_publishedE` (`:157`, `by []`, three equations on `published_row pgl27_row_prior_exact_tableau`), `pgl27_word_proximity_cert_idealE` (`p5_pgl27_word_proximity.v:175`, `by split`, two equations on `published_at pgl27_row_prior_exact_tableau`), `pgl27_row_word_proximity_armE` (`:265`, `by []`), `pgl27_row_word_branch39_armE` (`:271`, `by []`). Each matches the tactic its counterpart in `p4_kim_biased_proximity.v` uses (`:190`, `:310`, `:318`, `:327`), so the code is right and the record is wrong. | For the note: "Three statements close by `exact: erefl`: `pgl27_word_proximity_cert_epsE`, `pgl27_row_word_proximity_rowE` and `pgl27_row_word_arms_sampledE`. Five close by `by []` or `by split`: `pgl27_row_prior_exact_armE`, `pgl27_row_prior_exact_publishedE`, `pgl27_word_proximity_cert_idealE`, `pgl27_row_word_proximity_armE` and `pgl27_row_word_branch39_armE`, each with the tactic its counterpart in `p4_kim_biased_proximity.v` uses, and none of them hangs. No statement in stage C places one row's coordinate against another row's, which is the hang shape recorded in `STATUS.md`; the one such equation that was tried is the `ab_obs` row of the table above." For the file comment at `:247-248`, drop the false generalisation and keep the mechanism: `(* exact: erefl and not by []: done does not return on an equation between two rows' coordinates. *)`. I re-read both against the seventeen `Proof.` lines and against `STATUS-stageC.md:24-29` and `:213`, which already record that the two-row equation is not in the file. |
| S1 | SHOULD | `p5_pgl27_word_proximity.v:273-279` | The 48 s / 4 ms measurement sits inside the rendered `(** *)` docstring of `pgl27_row_word_arms_sampledE`, and reads "an equation between the two rows' observed executions is decided by conversion in 48 seconds, against four milliseconds for the family". | Two defects. (a) Placement: a measurement is proof strategy and belongs in a non-rendered comment. The file's own other measurement block, the 78.7 s / 24.3 s / 24.1 s note at `:294-303`, is correctly a `(* *)` inside the proof; this one is not. (b) Column: `STATUS-stageC.md:213-214` gives the `ab_obs` equation at 96.0 s by `exact: erefl` and 48.1 s by `reflexivity`, and the `ab_f` equation at 0.000 s by `exact: erefl` and 0.004 s by `reflexivity`. The proof at `:285` is `split; exact: erefl`. The docstring therefore quotes 48 s from the `reflexivity` column for the rejected side and 4 ms from the `reflexivity` column for the kept side, while the file runs `exact: erefl`, where the two figures are 96.0 s and 0.000 s. The rejected side's real cost under the tactic in use is understated by a factor of two. | Docstring, mathematics only: "Both rows over the word model read their analysis model family off the one named Tableau Sampled value, so the pair differs in the arm and in nothing about the algebra, the run or the law. The statement is on the family and not on the whole observed execution, and the family is what a continuation reads off the name." Then inside the proof, above `split`: `(* The ab_obs half was measured on 2026-09-19 at 96.0 s by exact: erefl and 48.1 s by reflexivity, against 0.000 s for this one; it is therefore not stated. *)` Numbers taken from `STATUS-stageC.md:213-214`; re-read against the statement at `:280-284`. |
| S2 | SHOULD | `p5_pgl27_word_proximity.v:168`, `:247`; `p5_mutations.v:93` | Three rendered or in-proof comments point at probe files that do not survive a landing. `:168` "the row `p5_pgl27_prior_ideal.v` publishes"; `:247` "recorded in `STATUS.md`"; `p5_mutations.v:93` "as they are for the exact and the spectral payloads of `t0_sampled_branch_pgl27.v`". | `STATUS-stageC.md:321` sends `pgl27_word_proximity_cert` and the ideal's declarations into one file, `instances/pgl27/pgl27_rows.v`, so after a landing `p5_pgl27_prior_ideal.v` names nothing and the two declarations are neighbours. `STATUS.md` is a probe note. p4's parallel comment at `:183-184` already avoids this: it says "the row the manifest already carries", naming no file. | `:168`: "so the ideal a word row is measured against is the model `pgl27_row_prior_exact_tableau` publishes and not a second description of it." `:247`: see C2. `p5_mutations.v:93`: "Two models of one instance are separated here as they are for the exact and the spectral payloads at `pgl27_exact_sampled`." Each names a declaration instead of a file; `pgl27_exact_sampled` is at `t0_sampled_branch_pgl27.v:79` and the two failures it carries are at `:185` and `:190`. The two file-header mentions at `:7` and `:16` are the probe's own structure and are left alone. |
| S3 | SHOULD | `p5_pgl27_prior_ideal.v:140-144` | The comment on `pgl27_row_prior_exact_armE` says the equation "is what makes the model a proximity certificate calls ideal a model whose own privacy is a theorem rather than a bare law". | Type-honest phrasing. The lemma states `security_arm_of pgl27_row_prior_exact_tableau R idx = ExactIndependenceArm`, an equation between two labels of the `SecurityArm` enumeration. What makes the ideal's privacy a theorem is `pgl27_prior_exact_witness` at `:109-118`, whose independence field is `pgl27_view_indep_gen` (`instances/pgl27/pgl27_word_privacy.v:220`). A label carries no proof. p4's parallel comment at `:323-327` does not make this move; it stops at the table sentence. | "The arm the ideal row carries, at every real field and prior: independence of the dealt secret, and not a distance to some other model. This is the value a paper's table prints in the arm column for the ideal row." Re-read against the statement at `:141-144`. The clause that was carrying the real content is already stated, correctly, on the witness at `:101-108` ("The reading carries no information about the secret at all and not a small amount, so this model is an execution a proximity certificate may call ideal"). |
| S4 | SHOULD | `p4_kim_biased_proximity.v:185` (stage B) against `p5_pgl27_word_proximity.v:169` | Same concept, two name shapes, and **p4 is the side that should move**. p5 writes `pgl27_word_proximity_cert_idealE`, keyed to `pgl27_word_proximity_cert`. p4 writes `kim_biased_cert_idealE` for a lemma about `kim_biased_proximity_cert`. | `kim_biased_cert` is a different declaration and it is the **spectral** certificate: `instances/kim2025/five_card_rows.v:579` defines it and `:608` writes `certify SpectralDecay kim_biased_cert`. p4 itself uses it that way at `:210`, `cert_eps (kim_biased_cert R idx)`. So `kim_biased_cert_idealE` names the spectral certificate and states a fact about the proximity one, in a file where both are in scope. p5's shape is the correct one. | Rename `kim_biased_cert_idealE` to `kim_biased_proximity_cert_idealE` in `p4_kim_biased_proximity.v:185`, its header index line at `:39`, and `STATUS-stageB.md` wherever it is cited. Token free: no occurrence of the new name in any of the 230 `.v` files scanned. **Not compiled** — stage B is live under the prover and I did not touch it; the change is a single-token rename of a lemma with no dependants inside the probe (checked: `kim_biased_cert_idealE` occurs only at `p4:185` and in the two notes). |
| S5 | SHOULD | `p5_pgl27_word_proximity.v:29-43`, `p5_pgl27_prior_ideal.v:26-37` | The header indexes are thinner than the tree's. `p5_pgl27_prior_ideal.v` lists 6 of 7 declarations; `p5_pgl27_word_proximity.v` lists 7 of 17. | Production `instances/pgl27/pgl27_rows.v` indexes 25 of 31, so the convention is selective but near-complete, not 41%. Three of the omissions are declarations the record itself treats as headline: `pgl27_row_prior_exact_publishedE` is what `STATUS-stageC.md:344-348` names as the file's substitute for the withdrawn manifest equation; `pgl27_row_word_arms_sampledE` and `pgl27_row_word_arm_neq` are quoted verbatim in `STATUS-stageC.md:141-149` as key statements and are two of the spec's item-3 deliverables. | Add to `p5_pgl27_prior_ideal.v` Key results: `pgl27_row_prior_exact_publishedE == the three coordinates the ideal row publishes`. Add to `p5_pgl27_word_proximity.v` Key results: `pgl27_row_word_arms_sampledE == both rows read one Sampled value` and `pgl27_row_word_arm_neq == the two rows carry different arms`. Glosses re-read against `:150-157`, `:280-285`, `:290-292`. The remaining omissions (`_epsE`, the two `Fact`s, `_le39`, `_eps_lt2`, `_rowE`, the two `_armE`) are lemma-grade and match p4's own selection. |
| S6 | SHOULD | `p5_pgl27_word_proximity.v:198`, `:202` | `pgl27_pow2_40_ge1` and `pgl27_pow2_40_gt0` carry an instance qualifier on statements that mention no PGL(2,7) object. | `Fact pgl27_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40` and `Fact pgl27_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40` are facts about `2%:R` in an arbitrary real field. The tree's own precedent is one line away: `instances/pgl27/pgl27_word_privacy.v:180` is `Fact pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.`, a pure numeric fact inside a PGL(2,7) production file with no instance prefix, and `pgl27_word_proximity_le39` uses `pow2_split R` at `:212`, immediately above its use of `pgl27_pow2_40_gt0` at `:211`. | See the rename table. Compiled, rc=0. |
| N1 | NOTE | `p5_pgl27_prior_ideal.v:131`, `:141`, `:150` | Whether `pgl27_row_prior_exact_*` reads as "the exact row indexed by the prior" or as "a previous exact row". | The brief's question, answered with evidence and **no rename demanded**. "Prior" is the tree's word for the law on the dealt secret: `instances/pgl27/pgl27_exec.v:535` "the secret prior secretP", `instances/pgl27/pgl27_models.v:415-416` "sending a secret prior to `pgl27_word_sample` at that prior", `manifest/pgg_analysis_manifest.v:794-795` "the word model family indexed by the secret prior". The row name derives mechanically the way the tree's other row names do: `pgl27_row_` + the family's distinguishing token + `_tableau`, as `pgl27_row_exact_tableau` and `pgl27_row_word_tableau` derive from `pgl27_exact_family` and `pgl27_word_family`. The family and adapter names put the qualifier first, which is the tree's convention at that layer: `pgl27_fixed_sample` and `pgl27_fixed_word_sample` at `instances/pgl27/pgl27_models.v:118` and `:126`. The "previous" reading is available in English and nothing in the tree licenses it. | None offered. Every candidate is worse: `_gen`, the tree's own suffix for this generalisation (`pgl27P_gen`, `pgl27P_word_gen`, `pgl27_view_indep_gen`, all in `instances/pgl27/pgl27_word_privacy.v:96`, `:102`, `:220`), would put a second word for one concept into files that use "prior" 44 and 28 times; `pgl27_row_exact_prior_tableau` reads as "the exact prior". Recorded so the coordinator can decide; I compiled no rename here. |
| N2 | NOTE | `p5_pgl27_word_proximity.v:208` against `p4_kim_biased_proximity.v:227` | `_le39` against p4's `_le_inv25`. | Not a divergence. Digits glue in the tree: `pgl27_reprice39` (`pgl27_rows.v:407`), `pgl27_row_word39` (`:415`), `pgl27_row_word39_bind`, `pgl27_row_word39_armE`, `pgl27_row_word_branch39` (`t0_sampled_branch_pgl27.v:145`). An alphabetic token takes a separator: `five_card_reprice_inv25`, `five_card_row_biased_inv25`. Each file follows its own instance. | None. |
| N3 | NOTE | `p5_pgl27_word_proximity.v:219-222` against `p4_kim_biased_proximity.v:236-238` | The two `_eps_lt2` comments compare against different partners. p4: "a weak separation and not a cryptographic one, as the spectral certificate of the same model is". p5: "a cryptographic separation and not a weak one, as the proximity certificate of Kim's one-cut model is". | Both are true and each names the informative partner at its own instance, so neither side has to move. Two small things ride on it: "4.5e-13" is the only scientific-notation literal in any rendered comment of the probe, where the tree writes numbers in words ("sqrt 5 over eighty", "one twenty-fifth"); and the figure is right, `2^-41 = 4.547e-13`. | Optional: "At about four and a half parts in ten million million of the ceiling". Nothing turns on it. |
| N4 | NOTE | `p5_mutations.v:3-20` | The header carries no index of the three recorded failures, where `p7_mutations.v:26-32` carries labelled `Lemmas:` and `Definitions:` blocks. | The file declares nothing but three `Fail Definition`s, and `p7_mutations.v` does not index its own `Fail`s either, so "no index" is defensible. The header's prose does name all three rejections (`:8-11`). | Optional, for parity with how the rest of the probe is read: a `Recorded failures:` block naming `pgl27_word_proximity_cert_unit_ideal`, `pgl27_word_proximity_cert_uniform_ideal` and `pgl27_cross_model_proximity` with one-line glosses. Glosses checked against `:55`, `:77`, `:94`. |

## Rename table

| old | new | reason | precedent in the tree | compiled |
|---|---|---|---|---|
| `pgl27_pow2_40_ge1` | `pow2_40_ge1` | statement mentions no PGL(2,7) object; the instance qualifier is false | `pow2_split`, `instances/pgl27/pgl27_word_privacy.v:180` | yes |
| `pgl27_pow2_40_gt0` | `pow2_40_gt0` | ditto | ditto | yes |
| `kim_biased_cert_idealE` | `kim_biased_proximity_cert_idealE` | the old name is keyed to `kim_biased_cert`, which is the spectral certificate (`instances/kim2025/five_card_rows.v:579`, `:608`) | `pgl27_word_proximity_cert_idealE`, `p5_pgl27_word_proximity.v:169` | no (stage B is live) |
| `five_card_sqrt5_le3` | `sqrt5_le3` | same defect as the two `pow2_40` facts | `pow2_split` | no (stage B is live) |

Verified, not argued, for the two compiled rows. A copy of the probe was built at
`<scratchpad>/extC_naming/ren`, the stage A and B `.vo` taken from the live
directory and the stage C `.v` taken from the frozen export, with the two names
substituted by exact token. `p5_pgl27_word_proximity.v` rc=0 5 s,
`p5_mutations.v` rc=0 4 s with all three `Fail` still failing, since the file
compiles, `assumptions_report_stageC.v` rc=0 26 s with 24 `Axioms:` blocks, zero
`Closed under the global context`, and exactly `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`. Neither
new name occurs as a token in any of the 230 `.v` files scanned.

## What passed

- **Barred vocabulary.** No `apex`, no `gate`/`gates`/`gated`/`gating`, no
  `posit`/`posits`/`posited`/`positing`, and no capital-L-digit-one token, in any
  of the four stage C files or in `STATUS-stageC.md`. Scanned by case-insensitive
  regular expression with substrings in other words excluded.
  `p5_mutations.v:76` writes "one apart in the sum of absolute differences",
  which is the tree's phrase and the right one.
- **No name collisions.** Of the 24 declarations stage C writes, none collides
  with any of the 4835 declaration names in the 198 production `.v` files, none
  collides with a stage A or stage B probe name, and there are no duplicates
  within stage C.
- **Headers and layout.** No line over 80 bytes in any of the four `.v` files.
  Every banner box line is exactly 80 bytes. Section banners match the file's
  own structure. Header index glosses that are present all match their
  declarations; the omissions are S5.
- **`_CoqProject` is a dependency order.** Twenty entries; every
  `From tableau_ext_probe Require Import` in every file names a module strictly
  earlier in the list. The four new entries are appended after
  `assumptions_report_stageB.v` as `STATUS-stageC.md:9-10` says. Sixteen entries
  precede them, which is the "sixteen files of stages A and B" of `:305`.
- **No permanent file imports the probe.** No file under `lib`, `protocol`,
  `groups`, `security`, `smc`, `reconstruct`, `instances`, `manifest` or `legacy`
  mentions `tableau_ext_probe`.
- **Parallelism with p4, beyond S1 to S5.** Certificate, close lemma, `_epsE`,
  halving lemma, `_le`, `_eps_lt2`, proximity row, `_rowE`, `_armE`, `_arm_neq`
  and the closing `Theorem` are all present on both sides in the same order and
  under the same section banners ("The distance between the two models' joint
  laws", "The certificate, and its ideal", "The number", "One model, two claims,
  two rows", "What the proximity row states at this instance"). The comment
  wording on the certificate, the halving lemma, the `_le` obligation and the
  proximity row's `_armE` is the same sentence with the instance's nouns
  substituted. Three deliberate divergences, all justified in
  `STATUS-stageC.md:377-391`: `_arm_neq` is proved by assuming the arm equation
  first rather than by `by []`; the `Sampled` equation is on `ab_f` and not
  `ab_obs`; and the ideal row is new here where p4 reused the manifest's uniform
  row. p5 also correctly omits a proximity-row `_publishedE`, since it states the
  three coordinates on the ideal row instead, which is the row that has no
  manifest counterpart.
- **One word per concept.** "proximity" throughout, never "closeness";
  "distance" only for `var_dist` values; "the number" for `ipc_eps` and
  `cert_eps`, "the constant" for the published `2^-39`, "the walk's marginal
  number" for `sw_bound_eps (pgl27_word_marginal_bound R)`, which keeps stage B's
  S3 collision out of stage C; "reading", "run argument", "prior", "arm",
  "ideal", "actual", "model" as stages A and B settled them; "coalition of fewer
  than four seats" at the instance against "coalition below the threshold" in the
  framework, which is the restatement and not a drift. One one-off:
  `p5_mutations.v:8` writes "the discrimination that rejects each" where the same
  sentence and the rest of the file write "rejection" (7 uses of `reject`, 4 of
  `rejection`). Below the SHOULD line; "the failure that rejects each" would fix
  it.
- **Statement comments.** No status marker, no effort estimate, no "key lemma",
  no "headline", no "used by", no `[identifier]` bracket, no fix-pass or audit
  narration, no restated type signature, in any stage C statement comment. Proof
  strategy is in non-rendered `(* *)` comments at `p5_pgl27_word_proximity.v:108-111`
  and `:294-303`, except for S1. The carrier convention matches production: the
  instance-level files use `(** *)` as `instances/kim2025/five_card_rows.v` does,
  and `assumptions_report_stageC.v` uses `(* *)` as its two siblings do. Each
  statement comment states the fact and its domain position: the static coalition
  below the threshold reading its seats, the average over the run argument under
  the prior, and which number is unconditional. The ideal's header at `:19-24`
  does the load-bearing work, saying why a unit-indexed ideal cannot serve and
  what the prior-indexed one buys.
- **`STATUS-stageC.md` as a record, apart from C2.** Every back-quoted Rocq
  identifier exists: checked mechanically, dots split, against the token sets of
  the frozen probe and all 198 production `.v` files. The only non-matches are
  file names (`_CoqProject`, `assumptions_report*.v`, `MEMORY.md`) and the suffix
  fragments `_armE` and `_arm_neq`, none of which is an identifier claim. All
  eleven fenced statements occur verbatim, modulo whitespace, in the two program
  files. No self line-number citation. The `Fail` list is complete: three `Fail`
  sentences in stage C, all three in `p5_mutations.v`, none in the other three
  files. The "argued, not compiled" claim is marked at `:19` and `:274-275` in the
  note, and the missing marking in the file is C1.
- **The two numbers.** `2^-40 = 9.094947017729282379...e-13`, and `:35` gives
  0.00000000000090949470177292824, correct to the digit shown.
  `2^-39 = 1.818989403545856475...e-12`, and `:36-38` give
  0.0000000000018189894035458565, correct. `:47-48` "about 0.00000000000045 of
  the ceiling" is `2^-41 = 4.547e-13`, correct. `:281-282` "above `2^-40` by a
  factor of about 1.1e12" is `2^40 = 1.0995e12`, correct. The halving is what
  `pgl27_word_proximity_eps_halfE` proves and the note does not confuse the two
  currencies: the certificate's `2^-40` and the row's `2^-39` are both
  assumption-conditional on `pgl27_word_mixing`, and the note says so at `:41-45`.
- **The compile table is plausible.** My own independent compile of the three
  affected files in the renamed copy, under the same lock, gave 5 s, 4 s and 26 s
  against the note's 5.0, 4.3 and 26.7 at `:200-203`. The main session's figures
  quoted in the brief, 4.4 to 5.1 s and 27.8 s, bracket the first three and sit
  1.1 s above the note's 26.7 for the assumptions report; that spread is lock
  contention and changes nothing. The assumptions claim at `:232-244` is
  independently confirmed: 24 `Axioms:` blocks, zero `Closed under the global
  context`, exactly the three `boolp` constants and no fourth.
- **D1 recomputed.** My own Python over the `Require` lines of all 198 production
  `.v` files gives reverse closures of size 11 for `pgl27_exec`, 10 for
  `pgl27_models` and 0 for `pgl27_rows`, matching `:319-321` exactly, and the ten
  names listed at `:325-327` are exactly the ten. `psl211_endpoints` is in none of
  the three reverse closures, and its own forward closure of 34 modules holds none
  of the three homes, so no proposed home forces it to rebuild. The rejection of
  `instances/pgl27/pgl27_word_privacy.v` at `:329-334` holds: that file mentions
  none of `static_coalition_obs`, `sa_arg`, `sa_cut`, `sa_sampleP`.
- **D2 spot-checked at five sites, all accurate.**
  `manifest/pgg_analysis_manifest.v:773-791`, where `apr_model` is documented at
  `:781-785` as "an AnalysisModelFamily over the row's own observed execution" and
  the record's docstring at `:770` says "It stores no theorem", which is both of
  D2's claims about `AnalysisPathRow`; `:800-802`, `pgl27_row_exact` over
  `PGL27Analysis.exact_family` at `AnalysisBridged`, `StaticExecutedOnly`,
  `BaselineClassicalOnly`; `:811-813`, `pgl27_row_word` over
  `PGL27Analysis.word_family` at `IdealFinite`;
  `instances/pgl27/pgl27_exec.v:521`, `Variable secretP : R.-fdist bool`, with
  `pgl27_sample` at `:439` and `pgl27_word_sample` at `:548`, which is D1's "inside
  the section that already binds secretP"; `instances/pgl27/pgl27_rows.v:187` and
  `:248`, `pgl27_exact_witness` and `pgl27_word_cert`. **D2 item 1 is right**: a
  landing must add one manifest row, because `apr_model` pins the family,
  `pgl27_row_exact` names `PGL27Analysis.exact_family`, and
  `pgl27_prior_exact_family` is not it. D2 item 2 is right for the same reason in
  the other direction: the word family is unchanged, so
  `pgl27_row_word_proximity_rowE` closes against `pgl27_row_word`, and the
  transfer status `IdealFinite` that `p5_pgl27_word_proximity.v:240` claims "the
  spectral row earns" is the one `pgl27_rows.v:420` and
  `t0_sampled_branch_pgl27.v:149` publish.
- **The grading claim is not repeated.** A regex for `grade`, `graded`,
  `grading`, `monad`, `parameterised` and its spellings returns nothing in
  `STATUS-stageC.md` or in any of the four stage C `.v` files. The hand-back's
  "parameterised monad indexed by completion level, graded by the accumulated
  real" survives nowhere in the artifact, so the spec's "There is no grading by
  the bound" is not contradicted by anything stage C writes.

## Verdict

**GO**, conditional on C1 and C2.

The names, the file layout, the index conventions and the record may be carried
forward as they stand once the two blocking items are fixed. Both are prose: C1
is a mathematical claim asserted in a rendered comment that the record itself
marks as argued and not compiled, and C2 is a false statement about the probe's
own tactic discipline that appears both in the note and in a source comment, in
a campaign where that discipline is the reason a rule exists. Neither needs a
recompile. S1 to S6 should be applied in the same pass; S4 and the last row of
the rename table touch stage B and belong to whoever holds that file. N1 to N4
may ride with them.

The rename table's first two rows are compiled and may be taken as they are.

## What I did not check

- The mathematics of the proofs. Whether `pgl27_word_proximity_close`,
  `pgl27_prior_exact_witness` and `pgl27_word_view_proximity` prove what their
  statements say is the soundness audit's question, not this one. I checked only
  that each comment describes the statement it sits above.
- The recorded `Fail` error lines. I confirmed the list is complete and that all
  three failures are in `p5_mutations.v` and still fail, since the file compiles.
  I did not recompile any of the three with its `Fail` removed to reproduce the
  decisive error text quoted at `STATUS-stageC.md:255-298`.
- Stage B's live state. The audit object is the frozen export; a prover was
  editing stage B in the live directory. S4 and `five_card_sqrt5_le3` are stated
  against the frozen `p4_kim_biased_proximity.v` and were not compiled.
- `instances/psl211/psl211_endpoints.v`, per the brief. Its dependency closure was
  computed from source text without opening it.
- The stage A and B files' own names beyond what stage C touches, and the
  `IdealProximity*` / `ipc_*` naming, which the coordinator settled after stage B.
- `p5_pgl27_prior_ideal.v` in the renamed copy: the two renamed facts are not in
  it, so it was not recompiled. The three files that mention them were.
