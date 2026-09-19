# Adversarial soundness audit of landing 4 (PSL(2,11)) of the Tableau extensions

Date: 2026-09-20. Repository `rocq-pgg-smc` at `833acaf`, branch
`feat/tableau-extensions-probe`. Audited object: the frozen export of
`notes/probes/2026-09-20-tableau-extensions-landing4/`, the six landed files.
No repository file other than this report was edited. All compiles ran in
`/private/tmp/.../scratchpad/land4_sound/` through the `rocq1` lock, against a
copy of the staged tree and its `.vo` objects; `instances/psl211/psl211_endpoints.v`
was never compiled.

## VERDICT: NO-GO on one MUST

One landed sentence is false after the landing and is the same sentence the
landing corrected three lines below it: the section banner of
`psl211_reading_constancy.v` still says this tree carries no sample adapter for
the word model. It is a one-line fix (S1). Everything else below is SHOULD or
NOTE. No code finding: the twenty-two staged files' code, the row, the
certificate and the numbers check out, the three `Fail` guards fail for the
reasons stated, the fidelity ascriptions are not vacuous, the closure is
covered and there is no cycle.

## Findings

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| S1 | MUST | `staged/instances/psl211/psl211_reading_constancy.v:742` | `(*     The word model, which this tree carries no sample adapter for          *)` | False after landing 4, and it is the claim passage (b) of the landing removes from the docstring at `:772-779`, three lines below this banner. `psl211_word_sample (R : realType) : SampleAdapter R (instance_exec psl211_alldecks_params)` is a weighted-word adapter for this instance (`staged/instances/psl211/psl211_word_model.v:96-101`), and its cut is this very law: `psl211_word_cut_distE` gives `sa_cut_dist (psl211_word_sample R) = psl211_word_cutP R` and `psl211_word_cutP R := @rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R)`, the term the lemma under this banner is stated on (`:782`). The landing's own `landing_fidelity.v:103-106` states that identity and closes it by `exact: erefl`. | `(*     The word model, whose sample adapter is psl211_word_model.v            *)` (80 columns, checked) |
| S2 | SHOULD | `staged/instances/psl211/psl211_reading_constancy.v:42-45` (new passage (c)) | "The exclusion covers the input-indistinguishability arm alone: a proximity certificate carries no shuffle bound and no constancy field, and the row of instances/psl211/psl211_word_proximity.v publishes 2^-40 over the word model through that arm." | The nearest antecedent of "that arm" is "the input-indistinguishability arm", and read that way the sentence is false: `psl211_row_word_proximity_armE : security_arm_of psl211_row_word_proximity R idx = IdealProximityArm` (`staged/instances/psl211/psl211_word_proximity.v:293-296`). The intended referent is the proximity arm, which the sentence never names. | "...and the row of instances/psl211/psl211_word_proximity.v publishes 2^-40 over the word model through the proximity arm." |
| S3 | SHOULD | `staged/instances/psl211/psl211_reading_constancy.v:772-774` (new passage (b)) | "because it quantifies over every law within eps of that cut, so it covers the ideal of every certificate at once and needs no adapter to name one" | Overstated in two ways the lemma's own statement fixes. `psl211_alldecks_constancy_false_word584 (R) (ideal : R.-fdist cutT) (eps : R) : var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R)) ideal <= eps -> (2%:R^-40 + eps) + (2%:R^-40 + eps) < (#|pgg_G psl211_M|%:R)^-1 -> ~ coalition_reading_constancy psl211_alldecks_params ideal`. (i) It reaches a certificate's ideal only when that certificate's shuffle law is this cut, through `ic_close` read with `ic_Hd : sw_rho_dist ic_b = sa_cut_dist sa`; a certificate over an adapter drawing some other cut is not covered. (ii) The second hypothesis restricts eps, so certificates with a large shuffle bound are not covered either. `indistinguishability_cert_reading_constancy` (`:208-217`) states the coverage correctly for the group-uniform case: "refuting the proposition at a law refutes every certificate whose ideal cut is that law". | "because it quantifies over every law within eps of that cut, so a certificate whose adapter draws this cut is covered at its own shuffle bound, through ic_close read with ic_Hd, and no adapter has to be named here." (The eps restriction is already stated in the sentence before it.) |
| S4 | NOTE | `staged/instances/psl211/psl211_reading_constancy.v:776-779` (new passage (b)) | "so that row and this refutation are two propositions and neither bears on the other" | True of the two propositions: the refutation denies `coalition_reading_constancy` at a law on cuts, and `IdealProximityCert` has the five fields `ipc_ideal`, `ipc_witness`, `ipc_secret`, `ipc_eps`, `ipc_close` and no constancy field, so neither implies or contradicts the other. It is too strong about the instance: this file's own header at `:71-75` relates them, the refutation being why no input-indistinguishability row over this cut is available at a small eps. | "so that row's certificate has no field this refutation touches, and this refutation rules out no proximity row." |
| S5 | SHOULD | `staged/manifest/pgg_analysis_manifest.v:843` (Row 11 level justification) | "the two rows differ in the law of the cut alone and carry different statements, Row 9 exact independence and this row a distance to that independent model" | Read as a statement about rows it is false, and it is the claim this landing corrected in two other places. `psl211_row_alldecks := @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged PSL211Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly` (`:1061-1063`) against `psl211_row_word := @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged PSL211Analysis.word_family IdealFinite BaselineClassicalOnly` (`:1091-1093`): two coordinates differ, `apr_model` and `apr_transfer`. Row 11's own typed-row docstring at `:1088-1089` and `psl211_row_word_proximity_rowE`'s docstring say exactly that. | "the two models differ in the law of the cut alone, and the two rows differ in the model family and in the transfer status and carry different statements, Row 9 exact independence and this row a distance to that independent model" |
| S6 | SHOULD | `staged/manifest/pgg_analysis_manifest.v:845-847` (Row 11 level justification) | "The constancy propositions refuted in instances/psl211/psl211_reading_constancy.v are fields of an input-indistinguishability certificate and stay true beside this row." | Two slips. Literally it says that propositions which are refuted stay true; what stays true is the three refutations. And the propositions are instances of `coalition_reading_constancy E ideal`, a standalone `Definition` (`psl211_reading_constancy.v:198-206`); `indistinguishability_cert_reading_constancy` is what identifies it with the certificate's fifth field `ic_const`, so the propositions are not themselves fields. | "The three refutations of instances/psl211/psl211_reading_constancy.v deny the fifth field ic_const of an input-indistinguishability certificate, which a proximity certificate has no counterpart of, and all three stay true beside this row." |
| S7 | SHOULD | `staged/instances/psl211/psl211_word_proximity.v:24-27` (header) | "Six is the privacy threshold the derived profile declares, so every statement below is about a static coalition of at most five of the twelve seats reading its own endpoints." | False of eight of the file's fourteen statements: `psl211_pow2_40_ge1`, `psl211_pow2_40_gt0`, `psl211_word_law_le2`, `psl211_word_proximity_cert_epsE`, `psl211_word_proximity_cert_eps_lt2`, `psl211_word_proximity_cert_secretTE`, `psl211_row_word_proximity_armE` and `psl211_row_word_proximity_rowE` quantify over no coalition. It is also in tension with the file's own honest docstring at `:119-120`, "The bound holds at every coalition and not only below the threshold", `psl211_word_proximity_close`'s proof discarding the threshold premise with `move=> _` at `:141`. (The six is right: `profile_k_psl211_algebra : profile_k (instance_profile psl211_algebra) = 6`, `instances/psl211/psl211_exec.v:132-134`.) | "Six is the privacy threshold the derived profile declares, so every security statement below is about a static coalition of at most five of the twelve seats reading its own endpoints." |
| S8 | SHOULD | `staged/instances/psl211/psl211_word_proximity.v:236-237` (the `psl211_word_law_tauto` guard) | "So the number psl211_word_lawE proves is carried by psl211_word_mixing and by nothing that holds of an arbitrary pair of laws." | A `Fail` rejects one written term. Compiled here: an un-`Fail`ed copy of the guard gives `The term "var_dist_le2 ?P ?Q" has type "is_true (var_dist ?P ?Q <= 2)" while it is expected to have type "is_true (var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2 ^- 40)"`, matching the quoted error in the comment verbatim. That establishes that `var_dist_le2 _ _` does not have the type, not that no universally valid fact does. | "So the number psl211_word_lawE proves is not the one var_dist_le2 gives: the term that proves the distance at two is rejected at 2^-40." |
| S9 | NOTE | `staged/instances/psl211/psl211_word_proximity.v:364` (the `psl211_word_proximity_cert_ideal_self` guard) | "The certificate's ideal is not the word model it is about." | What the `Fail` establishes is that `erefl` does not typecheck at that equation, that is, the two adapters are not convertible; propositional inequality is not established. The rest of the comment names the mechanism correctly ("The rejection is a failure to unify the two models"), so only the headline sentence overstates. | "The certificate's ideal is not convertible with the word model it is about." |
| S10 | NOTE | `staged/instances/psl211/psl211_word_proximity.v:193-197` (`psl211_word_proximity_cert_secretTE`) | "At a one-point carrier the arm's proposition compares two readings and mentions no secret at all, the second factor of the product being a point mass, so the number would bound nothing about what a coalition learns of the bit." | The argument is sound for the carrier but does not close the vacuity shape it is aimed at: a constant function into `bool` leaves the second factor a point mass exactly as a one-point carrier does, so `ew_secretT … = bool` alone does not make the secret non-constant. What does close it is `psl211_alldecks_secret_expectedE` of `instances/psl211/psl211_models.v:449-453`, `psl211_alldecks_secret R u = ex_expected psl211_alldecks_params ((psl211_alldecks_sample R).(sa_arg) u)`: the secret is the value the run recovers, at every sample point, and `psl211_alldecks_secret R := fun u => u.1.1` is the chirality coordinate of a description drawn uniformly over all 136857600 of them, that count being `psl211_alldecks_cardE`, two times 132 times 6 factorial squared. Row 11's capabilities table names `secret_expectedE`; this file cites it nowhere. | Add one sentence: "The bit is not a constant either: psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v reads it as the value the run recovers at every sample point." |
| S11 | NOTE | `staged/manifest/pgg_analysis_manifest.v:792-795` (Row 11, `distribution-to-observer bridges`) | "psl211_word_sampleP_E and psl211_word_cut_distE of instances/psl211/psl211_word_model.v, which name the adapter's own law and its cut law" | Both are distribution-to-distribution equations; neither relates a distribution to an observer, which is what this manifest's own Sampled criterion at `:37-38` asks for. Row 9's cell names `exact_coalition_distE` and Row 10's names `pgl27_prior_viewE`, both of which do. Nothing false is stated: the row's reader is the framework's own `sa_coalition_view` at `word_sample`, which needs no facade bridge because the word adapter carries the all-decks sample carrier with `fst` and `snd` (`psl211_word_model.v:96-101` against `psl211_models.v:222-227`), and `psl211_word_view_proximity` compiles at that reader. The cell is filed under a heading it does not meet. | Add to the cell: "the row's reading is the framework's own sa_coalition_view at word_sample, which the adapter's projections make the all-decks reading, so no facade-level reading bridge is named" |
| S12 | NOTE | `staged/manifest/pgg_analysis_client.v:7` | `(* eleven typed rows. The file has EXACTLY ONE Require of any kind, and      *)` | 79 columns where every other comment box in the file is 80; the substitution of "eleven" for "nine" removed one space too many. | `(* eleven typed rows. The file has EXACTLY ONE Require of any kind, and       *)` (80 columns, checked) |
| S13 | NOTE | `STATUS.md`, "The reverse closures" | "A Python walk over the Require lines gives instances/psl211/psl211_analysis.v the nine reverse-dependants the design's section 3 computes" | A `Require` walk over the tree at `833acaf` with the landing's staged text gives twelve, not nine: the nine listed plus `five_card_proximity` and `pgg_tableau_arm_relations` (landings 2 and 3) and `psl211_word_proximity` (this landing). All twelve are among the twenty-two staged files, so the conclusion the number supports is unaffected and only the count is stale. The same walk confirms empty reverse closures for `psl211_word_proximity`, `psl211_reading_constancy` and `pgg_analysis_client`, and no cycle anywhere in the graph. | "the twelve reverse-dependants: the nine of the design's section 3, plus five_card_proximity and pgg_tableau_arm_relations from landings 2 and 3 and psl211_word_proximity from this one, all twelve staged" |
| S14 | NOTE | `instances/psl211/psl211_endpoints.vo` | STATUS.md, R3: "the `.vo` is dated 2026-09-17 and the `.v` 2026-09-18, and a single-file `coqc` does not compare timestamps" | Confirmed and benign, and worth stating as a limit of the evidence rather than only as a recorded state. The `.vo` is 2026-09-17 16:32, the `.v` 2026-09-18 16:10 at commit `c9634fd`, whose whole diff to that file adds `Optimize Proof` and `Optimize Heap` inside the proof of `psl211_profile_endpoints` ("Statement and proof unchanged"). So nothing the landing measured moves. The landing's compiles and its twenty-four assumption reports are nonetheless not reproducible from the committed sources until that file is rebuilt. Three files load it: `psl211_analysis`, `psl211_models`, `psl211_reading_constancy`, exactly as R3 records, and none of them needs it recompiled. | State it in STATUS.md as: "the landing never recompiles psl211_endpoints.v; its .vo predates its .v by one commit, c9634fd, which adds Optimize Proof and Optimize Heap inside one proof and changes neither statement nor proof term" |

## Coverage

### 1. The four rewritten passages of `psl211_reading_constancy.v`

- **(a) header, `:71-75`.** Correct. `IdealProximityCert` has `ipc_ideal`,
  `ipc_witness`, `ipc_secret`, `ipc_eps`, `ipc_close` and no constancy field;
  `ic_const` is the fifth field of `IndistinguishabilityCert`, which
  `indistinguishability_cert_reading_constancy` reads as
  `coalition_reading_constancy`. The row is published over
  `psl211_word_family`, whose adapter is `psl211_word_sample`. The eps figure
  `1/1320 - 2^-40` is the lemma's second hypothesis solved for eps:
  `(2^-40 + eps) + (2^-40 + eps) < 1/660`.
- **(b) `psl211_alldecks_constancy_false_word584`, `:766-779`.** The lemma
  refutes `coalition_reading_constancy psl211_alldecks_params ideal`, that is
  the proposition quantified over all coalitions `C` with
  `#|C| < profile_k (instance_profile psl211_algebra)` (six) and over all pairs
  of run arguments `x x' : ex_inputT E`, at every `ideal : R.-fdist cutT`
  within eps of the 584-letter word cut and under the eps restriction. The
  witness coalition inside the proof is `psl211_perdeck_coalition`, the three
  seats 0, 1 and 2. "The weighted-word adapter psl211_word_sample … draws this
  cut" is exact, by `psl211_word_cut_distE` and the `exact: erefl` identity in
  `landing_fidelity.v:103-106`. "Covers the ideal of every certificate at once"
  is S3; "neither bears on the other" is S4.
- **(c) `:42-45`.** The exclusion it scopes is
  `psl211_alldecks_no_small_eps_cert (R) (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) : sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#|pgg_G psl211_M|%:R)^-1 -> False`,
  which quantifies over a certificate type and a shuffle bound a proximity
  certificate has neither of. Correct apart from S2.
- **(d) header `:14-16`.** Correct.
  `security_arm_of psl211_row_alldecks_tableau R idx = ExactIndependenceArm`
  (`psl211_rows.v:215`) and
  `security_arm_of psl211_row_word_proximity R idx = IdealProximityArm`.
- **Unchanged sentences re-read.** Every line of the file mentioning an
  adapter, a row, an arm, a publication or a non-existence was read against
  the word model. One is now false: S1. The rest hold, in particular the
  "Not claimed" paragraph at `:58-70` (about the all-decks model and larger
  eps), the dealt-mode sentence "this tree carrying no dealt-mode sample
  adapter" at `:55-56` and `:962-963` (the word adapter is an all-decks-mode
  adapter, `SampleAdapter R (instance_exec psl211_alldecks_params)`, so the
  dealt-mode claim stands), and `psl211_alldecks_no_small_eps_cert`'s own
  docstring at `:690-702`, which already scopes itself to the
  input-indistinguishability arm at this model.

### 2. The two new files as permanent text

- **`psl211_word_model.v`.** The header's central claim is exact:
  `psl211_alldecksP R = (`U psl211_alldecks_gt0) `x (`U psl211_G_pos)`
  (`psl211_models.v:200-202`) against
  `psl211_wordP R = (`U psl211_alldecks_gt0) `x (psl211_word_cutP R)`, so the
  two models share the sample space, the deck-description factor and its law,
  and differ in the cut factor alone. Both laws are written as products, so
  the independence claim is by construction and is correctly called a premise
  about the dealer and not a theorem. `psl211_word_sample` carries the same
  carrier and the same `fst`/`snd` projections as `psl211_alldecks_sample`, so
  "the chirality is one random variable for the two models" holds as a term
  identity, which `psl211_word_proximity_cert_secretE` then proves. 136857600
  = 2·132·6!·6! (`psl211_alldecks_cardE`). 2^-40 = 9.094947017729282e-13.
  `psl211_word_family`'s index type is `fun _ => unit`, the one
  `psl211_exact_family` carries. Seven declarations, and the `Definitions:`
  and `Key results:` blocks index four and three of them, all seven, no `Fail`.
- **`psl211_word_proximity.v`.** The certificate's five fields are real terms:
  ideal `amf_sample psl211_exact_family R idx`, witness
  `psl211_exact_witness R idx`, secret `psl211_alldecks_secret R`, eps
  `2%:R^-40`, distance `psl211_word_proximity_close`. Published plainly:
  the program is `psl211_alldecks_prefix sample … certify IdealProximity … |> publish IdealFinite BaselineClassicalOnly`,
  no `conclude`, and `landing_fidelity.v:213` ascribes it at `PublishedRow`
  and not `PublishedRowAt`. "Advantage at most half of 2^-40" is 2^-41 and is
  stated as the advantage, with `var_dist` correctly named the sum of absolute
  differences and twice the literature's total variation, in the file header,
  in the row docstring, in the theorem docstring and in Row 11's level
  justification; no sentence in the landed text calls a bound "the distance".
  The threshold: `#|C| < profile_k (instance_profile psl211_algebra)` with
  `profile_k … = 6` on the distance lemma, `#|C| <= 5` on the theorem, both
  satisfiable by non-empty coalitions; the header's "every statement" is S7.
  The three-refutation paragraph checks out: all three lemmas exist in
  `psl211_reading_constancy.v` with the stated content, all three are
  witnessed at `psl211_perdeck_coalition`, the three seats 0, 1 and 2, the
  word584 eps condition is quoted correctly, and no sentence of the paragraph
  suggests the proximity row says anything about the fixed-deck executions.
  "The third carrier of that arm" is right: `certify IdealProximity` occurs at
  `pgl27_proximity.v`, `five_card_proximity.v` (the biased, one-cut model) and
  here, and nowhere else in the staged tree. An index type is described as
  separating two families, never two models, in both new files and in the
  facade. Fourteen non-`Fail` declarations, indexed two and twelve by the two
  header blocks, no `Fail` indexed. `Fail` honesty is S8 and S9.

### 3. The probe claim the landing corrected

Verified and correct in both places. `psl211_row_alldecks` is
`StaticExecutedOnly` and `psl211_row_word` is `IdealFinite`
(`pgg_analysis_manifest.v:1061-1063`, `:1091-1093`), so the model family is not
the only separating coordinate. The corrected sentence appears at
`psl211_word_proximity.v:303-306` and at `pgg_analysis_manifest.v:1088-1089`,
worded the same way in both. Row 11's level justification did not get the
correction: S5.

### 4. Manifest Row 11, R12, and the blocks STATUS.md judged unchanged

Every field of Row 11's block was read against the declaration it names.
Completion level `AnalysisBridged`, justified by `psl211_word_view_proximity`
being stated at `sa_sampleP (amf_sample psl211_word_family R tt)` and at
`sa_coalition_view` of that same adapter: correct.
`IdealFinite` and its stated reason: correct, and the constructor is the row
equation's and not a manifest choice, `psl211_row_word_proximity_rowE` closing
by `exact: erefl`. `BaselineClassicalOnly`: `landing_fidelity.out` holds 24
`Axioms:` blocks and no axiom name outside
`constructive_indefinite_description`, `functional_extensionality_dep` and
`propositional_extensionality` appears anywhere in the run. The bound and its
distance field: `ipc_eps` is `2%:R^-40` by
`psl211_word_proximity_cert_epsE` and `ipc_close` is
`psl211_word_proximity_close`. "Missing premise: none": correct, the
certificate carries its own distance field. Five `Check` pins for Row 11
(`:2186-2192`), and eleven `Check (… : AnalysisPathRow)` lines in the checker,
so "the eleven typed rows" is right in both the manifest banner and the client.
Row 9's added clause is correct: `psl211_row_alldecks`'s model is
`PSL211Analysis.exact_family` and `ipc_ideal` is `amf_sample psl211_exact_family R idx`,
which `psl211_word_proximity_cert_idealE` identifies with the model
`psl211_row_alldecks_tableau` publishes. The header sentence added at `:18-21`
is true: `AnalysisPathRow` has the five fields `apr_observed`,
`apr_completion`, `apr_model`, `apr_transfer`, `apr_assumptions` and no arm
field, and `security_arm_of (c : Reprice) (r : PublishedRowAt c)` is defined at
`manifest/pgg_tableau.v:983`, applied to a program.

On the four blocks STATUS.md judged to stay true with no edit, I agree with
three and split on one:

- Row 9's capability table (four lines at `exact_view_indep`, `static_indep`,
  `observed_recovers`, `secret_expectedE`): agree, nothing in Row 11 touches
  them.
- Row 9's level justification: agree that the coalition and threshold
  sentences stay true. It is Row 11's level justification, not Row 9's, that
  carries S5.
- "Aliases carrying no capability yet", the `PSL211Analysis` line: agree, and
  for the reason STATUS gives. The table lists observers and bridges no row
  attaches a notion to; sample aliases and family witnesses are not in it for
  any facade, `exact_sample` and `exact_family` included, so `word_sample` and
  `word_family` do not belong in it either.
- "Absent capabilities": agree it stays true. The first sentence constrains
  `NoModelComparison` and `StaticExecutedOnly` rows and Row 11 is
  `IdealFinite`; the second names row 8 specifically, and rows 2, 4 and 5 are
  already `IdealFinite` without being named there.

### 5. Vacuity of the certificate

Not vacuous. Five fields filled by real terms, none of them a placeholder; the
ideal is the all-decks exact model and its witness is production's, both pinned
by `psl211_word_proximity_cert_idealE` against
`published_at psl211_row_alldecks_tableau`, which the fidelity file restates.
`ipc_secret` is `psl211_alldecks_secret R = fun u => u.1.1`, the chirality
coordinate of the deck description, at carrier `bool`;
`psl211_word_proximity_cert_secretE` pins both the certificate's secret and its
witness's secret to that one term, and `_secretTE` pins the carrier. That the
bit is non-constant is not stated in this file; see S10. The threshold premise
`#|C| < 6` is satisfiable by every coalition of one to five seats. The number
is not the universal bound: `psl211_word_law_le2` proves the distance at two
with no fact about the instance, and the same term is rejected at 2^-40,
re-checked here by compiling an un-`Fail`ed copy.

### 6. Closure and cycles

A `Require` walk over the production tree with the landing's staged text
substituted for the six landed files:

- reverse closure of `psl211_analysis.v`: twelve modules, all twelve among the
  twenty-two staged files (S13 on the count STATUS.md reports);
- reverse closure of `pgg_analysis_manifest.v`: eleven, all staged;
- reverse closure of `psl211_word_model.v`: thirteen, all staged, the facade
  included, which is R2's accepted state;
- reverse closures of `psl211_word_proximity.v`, `psl211_reading_constancy.v`
  and `pgg_analysis_client.v`: empty;
- forward closure of `psl211_endpoints.v`: 34 modules besides itself, and its
  intersection with the twenty-two staged files is empty;
- the three files that `Require psl211_endpoints` are `psl211_analysis`,
  `psl211_models` and `psl211_reading_constancy`, so the landing loads its
  `.vo` by digest and never needs it recompiled (S14 on the stale object);
- a depth-first search over the whole graph reports no cycle, so
  `psl211_word_model.v` before the facade and `psl211_word_proximity.v` after
  `psl211_rows.v` introduce none.

### 7. `landing_fidelity.v`

Ascriptions are at the probe's statements, and both forms of the row equation
are present, the landed one closed by `psl211_row_word_proximity_rowE` and the
probe's raw-family one by `exact: erefl`. The five provenance `Check`s would
each fail against production: `grep` over production's
`instances/psl211/psl211_analysis.v` finds no `word_sample` or `word_family`,
over `manifest/pgg_analysis_manifest.v` no `psl211_row_word`, and production
has no `psl211_word_model.v` or `psl211_word_proximity.v` at all, so those two
`Require`s could not resolve outside the staged roots.

The argument for the two files with no provenance witness is sound.
`psl211_reading_constancy.v` changes in comments alone, so its `.vo` from
production and from the staged text are the same object and there is nothing a
`Check` could discriminate; what the landing risks in that file is the text of
a comment, which is what this audit covers and what S1 found.
`pgg_analysis_client.v` declares nothing, so again nothing to discriminate;
its own added `Check PSL211Analysis.word_family.` would fail against
production's facade, which makes the client's compile a witness for the facade
rather than for itself, and the claim that stands for the client is the chain
compile, not the fidelity file. Worth saying plainly, since the fidelity file
does not `Require` the client at all.

Mutation check, compiled: `f_psl211_word_proximity_cert_epsE` restated at
`2%:R^-41` instead of `2%:R^-40` is rejected,
`Error: Cannot apply lemma psl211_word_proximity_cert_epsE`, so that ascription
pins the published number and is not vacuous.

`Fail` re-check, compiled: an un-`Fail`ed `psl211_word_law_tauto` gives
`The term "var_dist_le2 ?P ?Q" has type "is_true (var_dist ?P ?Q <= 2)" while it
is expected to have type "is_true (var_dist (psl211_wordP R) (psl211_alldecksP R)
<= 2 ^- 40)"`, character for character the error the comment quotes.

### Scans

The report was checked against the project's banned vocabulary list and
contains none of its entries; the sum of absolute differences is written in
full throughout and no finding id spells its barred short name.
