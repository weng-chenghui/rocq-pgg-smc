# Adversarial audit of fix pass 1 of landing 2 of the Tableau extensions

Read-only. Nothing was compiled here, no repository file was edited but this
one. Range `b5c4094` to `da53033`. Every sentence the pass wrote or changed was
walked hunk by hunk against the declaration it describes in the frozen tree.

## Verdict: GO

The five staged files may be copied into production as they stand. No MUST.
The pass applied every MUST, SHOULD and NOTE of the two audit reports or
declined it with a reason, the six identifier-level facts of the rewritten
`five_card_proximity.v` header are true, the fourteen new header entries all
name real declarations and describe them correctly, and no changed passage maps
to no finding. Two SHOULDs below are precision regressions the pass introduced
while fixing something else; both are comment-only and neither makes a false
claim about a published number, a row or a certificate. Nine NOTEs follow.

## Findings

| id | class | file:line | quoted text | problem, with the declaration's type quoted | replacement |
|---|---|---|---|---|---|
| F1 | SHOULD | `staged/instances/kim2025/five_card_proximity.v:23-25` | "The input-indistinguishability arm doubles whatever marginal bound its certificate carries and the proximity arm spends the distance once" | The second half is not type-honest, and the pass introduced it: the text it replaced spent a number ("the input-indistinguishability arm spends it once … and the proximity arm spends it once", the antecedent being the one fiftieth). `kim_biased_cut_mixing_exact` (`staged/instances/kim2025/five_card_mixing.v:532-535`) is `var_dist (sw_rho_dist (kim_biased_marginal_bound_exact R)) (sa_cut_dist (five_card_sample R)) <= sw_bound_eps (kim_biased_marginal_bound_exact R)`, and that epsilon is `1 / 50` by `kim_biased_marginal_bound_exact` (`:522-527`, `@MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50) …`). One fiftieth is an upper bound on the cut-group distance, not that distance, so what the proximity certificate carries once is the bound. The first half is sound: `cert_eps cert = sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` by definition (`staged/manifest/pgg_tableau.v:470-474`). | "The input-indistinguishability arm doubles whatever marginal bound its certificate carries and the proximity certificate carries that bound once, so the proximity row publishes one fiftieth where …" |
| F2 | SHOULD | `staged/instances/kim2025/five_card_proximity.v:271-273` | "so the ideal a biased row is measured against is the model the manifest's uniform row publishes and not a second description of it" | The manifest's uniform row is `five_card_row_uniform : AnalysisPathRow` (`staged/manifest/pgg_analysis_manifest.v:827`), and this same file states at `:365-368` that "An AnalysisPathRow holds descriptive metadata and no Prop", so it publishes no model. The term the lemma names is `amf_sample (ab_f (published_at five_card_row_uniform_tableau)) R idx`, the model of the published uniform row program `five_card_row_uniform_tableau : PublishedRow` (`staged/instances/kim2025/five_card_rows.v:400`). The file already has the right phrase eighteen lines above, at `:252-253`, "the terms the published uniform row carries", so the new wording also splits one concept across two words inside one file. | "so the ideal a biased row is measured against is the model the published uniform row carries and not a second description of it." |
| F3 | NOTE | `staged/manifest/pgg_tableau_arm_relations.v:116-119` | "An implication from this proposition to the proximity proposition is not empty for all that: idealproximity_prop_at2 gives the proximity proposition at two whatever the premise." | "not empty" reads as "not vacuous", and that implication is exactly vacuous: `idealproximity_prop_at2` is proved `by move=> C _; exact: var_dist_le2` (`:97`) and never looks at a premise. `five_card_proximity.v:584-586` says of the same shape at the instance "The implication holds and carries no information". The N15 rewrite fixed the missing antecedent and kept the word. | "An implication from this proposition to the proximity proposition does hold for all that, its premise discarded: idealproximity_prop_at2 gives the proximity proposition at two whatever the premise." |
| F4 | NOTE | `staged/manifest/pgg_tableau_arm_relations.v:33-36` | "One recorded failure below says where the arm's mathematics is spent: the ideal witness's independence is what turns the ideal joint law into the product of its marginals, and the arm's proposition compares the actual joint law with exactly that product." | The content after the colon is true and checkable without the failure, from `IdealProximityPropAt` (`pgg_tableau.v:491-506`), whose right side is `(fdistmap (sa_coalition_view …) …) `x (fdistmap (ew_secret (ipc_witness cert)) …)`, against `ipc_close` (`:219-231`), which compares with the ideal's joint law. The failure itself rejects one written term and establishes no necessity. Three paragraphs above, the same header now says of two other failures that they "record what a written term does with that", which is the soundness N1 fix; this paragraph keeps the older attribution. | "The arm's mathematics is spent on the ideal witness's independence: it turns the ideal joint law into the product of its marginals, and the arm's proposition compares the actual joint law with exactly that product. One recorded failure below is a written term that omits it." |
| F5 | NOTE | `staged/manifest/pgg_tableau_arm_relations.v:40-43` | "Refuting it needs a model whose reading law is the same at every run argument, which is what the input-indistinguishability proposition asks" | `IndistinguishabilityPropAt cert c` (`pgg_tableau.v:456-465`) asks `var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa)) (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)) <= c`, which is sameness only at `c = 0`. The S5 rewrite corrected "Settling" to "Refuting" and left the clause. | "Refuting it needs a model whose coalition readings at any two run arguments stay within the constant the input-indistinguishability proposition names, and whose distance to the ideal exceeds the constant the proximity conclusion is stated at." |
| F6 | NOTE | `staged/manifest/pgg_tableau_arm_relations.v:29-31` | "idealproximity_prop_at2 fixes the scale a published number is read against." | The naming N4 cut removed "Every proximity certificate satisfies the arm's proposition at two, so a row publishing two rules nothing out" from the header prose. The fact survives in the `Lemmas:` entry at `:52-53` and in the declaration comment at `:88-92`, and the `Not claimed.` paragraph's "at a constant below two" leans on it. The compiled half of the partial verdict is therefore still stated in the header, in its index rather than in its prose. | No change. Restoring the sentence would recreate the duplication N4 removed. Recorded so the reading is deliberate. |
| F7 | NOTE | `staged/instances/kim2025/five_card_proximity.v:562-564` | "so the proximity arm adds no new way for two models of one instance to be confused" | Two `Fail`s reject two written terms, `kim_centi_proximity_from_biased` (`:549`) and `kim_biased_indistinguishability_from_centi` (`:565`); they quantify over no ways. The clause predates the pass and the N11 rewrite of the sentence before it kept it. | Optional: "so a certificate of either arm is rejected where the other model's is required." |
| F8 | NOTE | `staged/instances/kim2025/five_card_proximity.v:72-73` | "five_card_arg_cut_prodE == that pair's joint law is the uniform pair tensored with the model's cut law" | The statement is `fdistmap (fun u => (u.1, five_card_sample_cut u)) ((fdist_uniform five_card_card_bool2) `x W) = (fdist_uniform five_card_card_bool2) `x (fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) W)`, so it holds of a sample law written as that product. The entry drops the hypothesis; the declaration comment at `:192-195` carries it. Index-line terseness, and the two neighbours are equally terse. | Optional: "== at a sample law written as a product, that pair's joint law is the uniform pair tensored with the model's cut law". |
| F9 | NOTE | `staged/instances/kim2025/five_card_proximity.v:76-78` | "kim_biased_proximity_cert_idealE == the certificate's ideal and witness are the uniform row's model and port" | The second conjunct is `ExactIndependence (ipc_witness (kim_biased_proximity_cert R idx)) = ab_port (published_at five_card_row_uniform_tableau) R idx` (`:277-278`), and `ExactIndependence` is a `SecurityPort` constructor taking an `ExactWitness` (`pgg_tableau.v:239-243`). A witness is not a port; what is equal to the row's port is the port built from the witness. Constructor injectivity makes the intended claim equivalent, and the entry as written is the naming N28 proposal verbatim. | "== the certificate's ideal is the uniform row's model, and the port built from its witness is that row's port". |
| F10 | NOTE | `staged/security/var_dist_joint_law.v:26-29` | "The two variation-distance lemmas this file applies, var_dist_fdistmap and var_dist_triangle, are stated in security/pgg_collusion_bound.v" | Both are stated there, `var_dist_triangle` at `security/pgg_collusion_bound.v:43` and `var_dist_fdistmap` at `:126`, and no file under `lib/` requires anything from `security/`, so the layering claim holds. The count is exact only for lemmas taken from this tree: the file also applies infotheo's `symmetric_var_dist` (`infotheo/probability/variation_dist.v:37`) twice, at `:157` and `:160`. | "The two variation-distance lemmas this file takes from the tree, var_dist_fdistmap and var_dist_triangle, are stated in security/pgg_collusion_bound.v, …" |
| F11 | NOTE | `landing_fidelity.v:330-331` | "Check (five_card_biased_proximity_at_singleton : forall (R : realType) (i : 'I_5), _)." | Applied exactly as soundness N5 proposed, and it narrows the gap without closing it: the telescope is pinned and the conclusion is `_`, so the declaration's proposition is still not written out in the fidelity file. Both components of its body, `five_card_biased_view_proximity` and `five_card_singleton_below_threshold`, are ascribed at `:269` and `:326`. Every other landed declaration is ascribed: 5 of 5 in `var_dist_joint_law.v`, the moved `card_tnth_count`, 3 of 3 lemmas in `pgg_tableau_arm_relations.v`, and all 26 non-`Fail` declarations of `five_card_proximity.v`. | Optional, needs a compile: write the conclusion out in place of `_`. |

## What was checked and found correct

### 1a. The rewritten `five_card_proximity.v` header, soundness S1

Every identifier-level claim of the three-number paragraph holds.

- "the row built on kim_biased_cert_exact, five_card_row_biased_inv25 of
  five_card_rows.v, publishes one twenty-fifth": `five_card_row_biased_inv25 :
  PublishedRowAt five_card_reprice_inv25` (`five_card_rows.v:860-867`),
  continuing `kim_biased_cert_exact` (`:833`), with `five_card_reprice_inv25 :=
  fun R => Some (1 / 25 : R)` (`:850`).
- "The input-indistinguishability row continued below carries kim_biased_cert
  instead": `five_card_row_biased_branch_indistinguishability` (`:329-332`) is
  `five_card_row_biased_tableau certify InputIndistinguishability
  kim_biased_cert |> publish …`.
- "whose marginal bound is the one-cut bundle's spectral number, and publishes
  sqrt 5 over forty": `ic_b (kim_biased_cert R idx) = kim_biased_marginal_bound
  R` (`five_card_rows.v:602-610`), `kim_biased_epsE : sw_bound_eps
  (kim_biased_marginal_bound R) = Num.sqrt 5%:R * (1 / 80)` (`:555`),
  `kim_biased_cert_epsE : cert_eps (kim_biased_cert R idx) = Num.sqrt 5%:R *
  (1 / 80) + Num.sqrt 5%:R * (1 / 80)` (`:748`). The row carries `no_reprice`,
  and `no_reprice` is the coordinate that names nothing, so the row publishes
  the accumulated bound (`pgg_tableau.v:510-514`, `:932`).
- "the proximity row publishes one fiftieth": `kim_biased_proximity_cert_epsE :
  ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50` (`:291-293`), and
  `five_card_row_biased_proximity : PublishedRow` has no `conclude`.
- "That number bounds a sum of absolute differences, twice the total variation
  distance, so a distinguisher's advantage against this row is at most one
  hundredth": half of one fiftieth.
- The deviation "sqrt 5 over forty" for the audit's "the square root of five
  over forty" is right and improves consistency: the same spelling is at
  `five_card_proximity.v:302`, `five_card_rows.v:552` and `:871`.

The one type-honesty regression in this paragraph is F1.

### 1b. The fourteen new header entries

All 26 `Key results:` and `Definitions:` entry names spell a declaration of the
file exactly; the six unindexed declarations are the six `Fail`s, which is the
N22 ruling. Checked each description against its statement, including:
`five_card_uniform_pairE` (`fdist_uniform card_bool2 = fdist_uniform
five_card_card_bool2`), `kim_biased_proximity_cert_epsE` (`= 1 / 50`),
`kim_biased_proximity_eps_halfE` (`cert_eps (kim_biased_cert_exact R idx) =
ipc_eps … + ipc_eps …`, so "twice" is right and the doubling form matches the
statement), `kim_biased_proximity_cert_eps_lt2` (`ipc_eps … < 2%:R`, so "below"
is the strict relation the type has), the two `_rowE` sharing one entry because
both conclude `= five_card_row_biased`, `_publishedE` naming three coordinates
against a three-way conjunction, the two `_armE` against
`InputIndistinguishabilityArm` and `IdealProximityArm`,
`five_card_singleton_below_threshold` (`#|[set i]| < profile_k …`),
`five_card_biased_proximity_prop_holds` (`IdealProximityPropAt
(kim_biased_proximity_cert R tt) (1 / 50)`, the number the row publishes), and
`five_card_biased_indistinguishability_implies_proximity` (premise discarded by
`move=> _`). F8 and F9 are the two entries worth a second look.

### 1c. The certificate paragraph, soundness S2 and naming N8

Field by field against `@MkIdealProximityCert R five_card_algebra
five_card_params (amf_sample kim_biased_family R idx) (amf_sample
five_card_uniform_family R idx) (five_card_exact_witness R idx)
(five_card_leakage.Secret R) (1 / 50) (fun C _ => @kim_biased_proximity_close R
C)` (`:259-267`):

- ideal and witness: `kim_biased_proximity_cert_idealE` states both halves
  (with F9's caveat on the second).
- secret: `five_card_exact_witness R idx = @MkExactWitness R five_card_algebra
  five_card_params (amf_sample five_card_uniform_family R idx) bool (Secret R)
  (@five_card_static_obs_indep R idx)` (`five_card_rows.v:383-386`), and
  `five_card_rows.v:210` requires `five_card_leakage`, so `Secret R` there and
  `five_card_leakage.Secret R` here are one term. The clause the naming audit
  was unsure of is correct.
- number: `kim_biased_cut_mixing_exact`'s bound is `sw_bound_eps
  (kim_biased_marginal_bound_exact R)`, and that field is `1 / 50`.
- last field: `kim_biased_proximity_close` (`:216-229`), `var_dist … <= 1 / 50`,
  with the threshold argument discarded by the `fun C _ =>`, which the lemma's
  own comment at `:213-215` says is sound.

### 1d. The singleton paragraph, soundness S3

`static_coalition_obs` (`protocol/pgg_instance.v:481-489`) is `[ffun i => if i
\in C then ex_content_obs E x (g, tnth (pi_starts (mp_PI (instance_profile A)))
i) else ord0]`. At `[set i]` it is the seat's own content observation at `i`
and `ord0` elsewhere, and at the empty coalition it is `ord0` at every seat.
The replacement text says exactly this, and the unprovable non-constancy claim
the audit flagged is gone.

### 1e. The prose that replaced one word in the five landed files

Zero occurrences of that word remain in the five. Each replacement is true of
`var_dist_le2 : var_dist P Q <= 2%:R` (`lib/var_dist_supp.v:49-50`): "the bound
two on a variation distance" (banner), "the bound two that var_dist_le2 gives"
(`five_card_mixing.v:479`, `five_card_proximity.v:36-37`), "the bound
var_dist_le2 gives for a variation distance" (`five_card_proximity.v:310-311`),
"the scale a published variation distance is read against"
(`var_dist_supp.v:13`, matching the declaration comment at `:46`), "The scale
the proximity number is read against" (`pgg_tableau_arm_relations.v:85`). The
percentages check: one fiftieth is one percent of two, `Num.sqrt 5%:R * (1 /
80) + Num.sqrt 5%:R * (1 / 80)` is about 2.8 percent of two ("about three
percent"), one twenty-fifth is two percent of two.

The renamed lemma: `idealproximity_prop_at2 … : IdealProximityPropAt cert 2%:R`
at arbitrary `R`, `A`, `E`, `sa` and `cert`. Header entry "every proximity
certificate satisfies the arm's proposition at two" and docstring "Every
proximity certificate satisfies the arm's proposition at two, whatever its
model, its ideal and its own number" both match the universal quantification
and the number, and the name states the proposition rather than a metaphor.

### 1f. The `pgg_tableau_arm_relations.v` header after the cuts

The partial verdict is still stated, and completely. Compiled: the
input-indistinguishability proposition does not mention its certificate (prose
`:13-16` plus the entry `:54-57`); the proximity proposition holds at two of any
certificate (entry `:52-53`, see F6); the proximity proposition does mention its
certificate (`:16-18`); at five-card the implication holds because its
conclusion is a theorem and its premise is discarded (`:46-49`). Not compiled: a
countermodel below two (`:38-44`) and a derivation from an
input-indistinguishability certificate's own fields (`:44-46`). No cut removed a
scope condition: the three sentences naming N4 deleted survive at the
declarations, `:114-116`, `:145-148` and `:91-92`, and the `Not claimed.`
paragraph gained content rather than losing it. The `Recorded failures:` index
block was removed per the N22 ruling, and the prose that says what the three
failures record is kept.

### 1g. The N19 sentence

Both named lemmas are in `security/pgg_collusion_bound.v`, at `:43` and `:126`,
both stated on `var_dist`, so the deviation from "data-processing lemmas" is
right: `var_dist_triangle` is a triangle inequality. No file under `lib/`
requires anything from `security/`, checked over all six `lib/` files. F10 is
the one qualification.

### 2. The deviations and the decline

Five passages are labelled `Deviation` in STATUS.md, not six; the remit's count
is one high. All five reasons are right and all five resulting texts are true:
S1's "sqrt 5 over forty" (matches `:302` and `five_card_rows.v:552`, `:871`);
the `kim_biased_proximity_cert_eps_lt2` entry (strict `<` against `2%:R`, and
the wording follows the N12 ruling); N13's "as is kim_biased_cert_exact at one
twenty-fifth" (`cert_eps (kim_biased_cert_exact R idx) = 1 / 50 + 1 / 50`, and
`five_card_inv50_split` gives one twenty-fifth); the N12 prose half widening
the comment changes of `lib/var_dist_supp.v` and `five_card_mixing.v`; N19's
"variation-distance lemmas".

Deviation 4, read in full: `var_dist_supp.v`'s header paragraph is rewrapped
and carries two edits, the one-word change at `:13` and the N7 rewrite at
`:15-16`, "security/var_dist_joint_law.v carries the distance between two joint
laws of a reading and a secret", which no longer equates a real number with a
path; every other word of that paragraph is unchanged. The banner at `:40` is
"The bound two on a variation distance". `five_card_mixing.v:478-480` reads
"Its number is about three percent of the bound two that var_dist_le2 gives, so
it is a weak separation bound and not a cryptographic one", true of
`kim_biased_static_obs_indistinguishability`, whose bound is `sw_bound_eps
kim_biased_marginal_bound + sw_bound_eps kim_biased_marginal_bound` (`:491-492`).
Both files stay comment-only.

Two further texts differ from both audits' proposals without being labelled:
the S2 and N8 merge on the certificate and the S4 and N14 merge on
`idealproximity_reading_le`. Both merges satisfy both findings and both are
true of their declarations.

The decline, naming N31, is reasonable as stated: the finding itself records
the current placement as reading fine and the rule as already satisfied, since
the comment is a plain comment and not part of the docstring.

### 3. Completeness

Nothing vanished silently. Soundness S1-S6 and soundness N1, N2, N3, N5, N6 are
applied; soundness N4 proposed no change and the distinction is recorded.
Naming N1-N19, N21, N22, N24-N28 are applied; N20, N23, N29, N30 were recorded
by the audit with no action; N31 is declined with a reason.

### 4. Unrequested changes

None. All 26 changed passages map to a finding: `landing_fidelity.v` to S6, N12
and soundness N5; `five_card_mixing.v` to the N12 prose half; `var_dist_supp.v`
to N7 and the N12 prose half; `var_dist_joint_law.v` to soundness N2 and N3 and
naming N2, N5, N6, N17, N18 and soundness N6, and N19; `pgg_tableau_arm_relations.v`
to N24, soundness N1, naming N3 and N4, S5, N12, N15, S4 and N14, N22;
`five_card_proximity.v` to S1, S2 and N8, S3, N1, N9, N10, N11, N12 prose, N13,
N16, N21, N25, N26, N27, N28.

### 5. Discipline in the five landed files

No line over 80 bytes. Every box-comment row closes at column 80; the four
lines my scan flagged are one-line docstrings and the in-proof comment, which
carry no column. Zero hits for the project's banned vocabulary list. No
abbreviation of "indistinguishability"; every hit on a shortened form is inside
the full word. The word "view" appears in the five files only inside
identifiers, and "reading" carries the prose. "percent" is spelled one way in
both places. The meta words the rule names are absent; the only hits are the
ordinary verb "fixes" and "fixed", including `pgg_tableau_arm_relations.v:29`,
which means "determines". Proof strategy moved out of both docstrings and into
plain comments inside the proofs at `var_dist_joint_law.v:77` and `:150-152`.

### 6. `landing_fidelity.v`

The three provenance probes are `Check var_dist_supp.var_dist_le2.`, `Fail
Check var_dist_supp.card_tnth_count.` and `Check
five_card_mixing.card_tnth_count.` (`:65-67`), in the spelling the soundness
audit reported, and the header at `:14-15` already asserted the fact they now
test. The rename lands at exactly three sites: the restatement's own name
(`:114`), its `exact:` (`:118`) and its `Print Assumptions` (`:363`). Ascription
coverage is complete except for the `_` of F11.
