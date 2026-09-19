# Soundness audit of landing 2 of the Tableau extensions

Date: 2026-09-20. Repository `rocq-pgg-smc` at `b5c4094`, branch
`feat/tableau-extensions-probe`. Audited object: the frozen export of
`notes/probes/2026-09-20-tableau-extensions-landing2/`, the four files that
are copied into production and the one removal-only edit.

## Verdict: NO-GO, one MUST

The mathematics is sound and every machine-checked claim holds. All fifteen
staged files and the fidelity file recompile from source in the audit's own
directory with the audit's own flags, the fidelity restatements are the
staged statements with nothing weakened, the thirty-five `Print Assumptions`
blocks show the classical trio or nothing, a mutation of one ascription is
rejected, and two of the nine recorded `Fail`s re-fail for the reasons
`STATUS.md` records. The one MUST is a sentence of a landed file header that
states a published number that is not the number the row defined in that same
file publishes. Everything else is a SHOULD or a NOTE.

Fix S1 and the landing is a GO on soundness.

## Findings

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| S1 | MUST | `staged/instances/kim2025/five_card_proximity.v:22-27` | "Both numbers come from one distance on the cut group, the one fiftieth of kim_biased_cut_mixing_exact. The input-indistinguishability arm spends it once for each of the two committed pairs it compares and the proximity arm spends it once, so the proximity row publishes one fiftieth where the input-indistinguishability row of the same model publishes one twenty-fifth." | The one-cut model carries two input-indistinguishability rows and they publish different numbers, so "the input-indistinguishability row of the same model" has no referent that makes the sentence true. The row this file defines at `:281`, `five_card_row_biased_branch_indistinguishability`, continues `kim_biased_cert`, whose number is `cert_eps (kim_biased_cert R idx) = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80)` (`staged/instances/kim2025/five_card_rows.v:748`, `kim_biased_cert_epsE`), which is the square root of five over forty and not one twenty-fifth. The row that does publish one twenty-fifth is `five_card_row_biased_inv25 : PublishedRowAt five_card_reprice_inv25` (`five_card_rows.v:860`), which continues `kim_biased_cert_exact` and is not in this file. The file's own later comment at `:247-255` states the honest version, that the relation is between two certificates and not between two arms, and contradicts this header sentence. | "Both numbers come from one distance on the cut group, the one fiftieth of kim_biased_cut_mixing_exact. The input-indistinguishability arm doubles whatever marginal bound its certificate carries and the proximity arm spends the distance once, so the proximity row publishes one fiftieth where the row built on kim_biased_cert_exact, five_card_row_biased_inv25 of five_card_rows.v, publishes one twenty-fifth. The input-indistinguishability row continued below carries kim_biased_cert instead, whose marginal bound is the one-cut bundle's spectral number, and publishes the square root of five over forty." |
| S2 | SHOULD | `staged/instances/kim2025/five_card_proximity.v:208-211` | "Every field is a term the uniform row already publishes except the number, which is the bound kim_biased_cut_mixing_exact proves on the cut group's own distance, and the distance between the two joint laws is at most it." | Two of the five fields are outside the stated exception. The fifth field of `kim_biased_proximity_cert` is `(fun C _ => @kim_biased_proximity_close R C)`, and `kim_biased_proximity_close` is proved in this file at `:172`, not published by the uniform row. The ideal and the witness are the uniform row's terms, and `kim_biased_proximity_cert_idealE` proves exactly that. The secret `five_card_leakage.Secret R` is the same term `five_card_exact_witness` is built on (`five_card_rows.v:383-386`, `@MkExactWitness R five_card_algebra five_card_params (amf_sample five_card_uniform_family R idx) bool (Secret R) ...`), which is a stronger and checkable statement than "the uniform row publishes it". | "The ideal and the witness are the terms the published uniform row carries, and the secret is the same conjunction that row's witness is stated at. The number is the bound kim_biased_cut_mixing_exact proves on the cut group's own distance, and the last field is kim_biased_proximity_close of this file, which says the distance between the two joint laws is at most that number." |
| S3 | SHOULD | `staged/instances/kim2025/five_card_proximity.v:451-452` | "The coalition is not empty, so the reading it bounds is not the constant finfun and the statement is about a seat that sees a card." | Nothing in the landing establishes that the reading at a singleton is non-constant as a function of the sample point. What is true by the definition of `static_coalition_obs` (`protocol/pgg_instance.v:481`, `[ffun i => if i \in C then ex_content_obs E x (g, tnth (pi_starts ...) i) else ord0]`) is the weaker and checkable statement that at the empty coalition the reading is `ord0` at every seat and at `[set i]` it is the seat's own content observation at `i`. The declaration `five_card_singleton_below_threshold` at `:444` does discharge the threshold premise, so the first half of the comment is sound. | "Kim's one-cut row's claim with every hypothesis discharged: one real field, one coalition of one named seat, and the threshold condition proved rather than assumed. The coalition is not empty, so the reading the bound is stated on is the seat's own content observation at that seat, where the empty coalition's reading is ord0 at every seat." |
| S4 | SHOULD | `staged/manifest/pgg_tableau_arm_relations.v:170-173` | "and it is the sharpest comparison of the input-indistinguishability arm with the proximity arm that does not need a model of one to be a model of the other" | A superlative over all comparisons that no declaration establishes and that no reader can falsify. The rest of the comment is checkable against the statement and the proof, which are the data-processing step along the first projection and `fdist_prod1` for the ideal's first marginal. | Delete the clause and end the sentence at "This is the arm's number read on the carrier the input-indistinguishability arm states its bound on." |
| S5 | SHOULD | `staged/manifest/pgg_tableau_arm_relations.v:50-54` | "Settling it needs a model whose reading law is the same at every run argument, which is what the input-indistinguishability proposition asks, and far from the ideal's, which is what the proximity conclusion forbids; no such model is built here." | "Settling it needs a model" presupposes that the implication is false, which is the thing the paragraph says is not claimed. Only a refutation needs a countermodel. The spec's P8 entry records the same thing as "argued; it needs a countermodel", so the honest form is conditional. | "Refuting it needs a model whose reading law is the same at every run argument, which is what the input-indistinguishability proposition asks, and far from the ideal's, which is what the proximity conclusion forbids. No such model is built here, and no proof of the implication is given either." |
| S6 | SHOULD | `landing_fidelity.v:57-64` | "Check card_tnth_count." (and the four `Fail Check`s beside it) | The provenance block detects a production `five_card_mixing.vo` and a production `five_card_rows.vo`, because `kim_centi_marginal_bound40` and `kim_centi_cut_mixing40` exist at `instances/kim2025/five_card_mixing.v:507,517` and `kim_centi_cert40`, `kim_centi_cert40_epsE` at `instances/kim2025/five_card_rows.v:737,749`. It detects nothing about `lib/var_dist_supp.v`: `Check card_tnth_count` succeeds whether the staged or the production `var_dist_supp` is loaded, since the staged `five_card_mixing` declares the name too. D5's removal is therefore the one landed change with no provenance test. Compiled in the audit's directory (`land2_sound/mut1.v`): `Check var_dist_supp.var_dist_le2.` prints `forall (R : realType) (A : finType) (P Q : {fdist A}), var_dist P Q <= 2`, `Fail Check var_dist_supp.card_tnth_count.` is satisfied, and `Check five_card_mixing.card_tnth_count.` prints the moved lemma's type. | Add the three qualified probes beside the existing block: `Check var_dist_supp.var_dist_le2.`, `Fail Check var_dist_supp.card_tnth_count.`, `Check five_card_mixing.card_tnth_count.` The middle one errors if production's `lib/var_dist_supp.v` is loaded. |
| N1 | NOTE | `staged/manifest/pgg_tableau_arm_relations.v:21-24` | "and the two recorded failures beside it say so from both sides: the equality of the proposition at two certificates is not closed by conversion, and the proposition cannot be stated at an input-indistinguishability certificate at all" | The two readings after the colon are each accurate, but "say so" attaches them to the preceding claim that the proposition mentions its certificate, and a rejected `by []` does not establish an occurrence. The claim itself is verifiable without the failures, from `IdealProximityPropAt` (`pgg_tableau.v:487-500`), which names `ipc_secret cert`, `ipc_ideal cert` and `ipc_witness cert`. The declaration-level comment at `:146-151` is correctly scoped and says "and no more". | "…and the actual model's secret, as its definition shows. The two recorded failures beside it record what a written term does with that: the equality of the proposition at two certificates is not closed by conversion, and the proposition cannot be stated at an input-indistinguishability certificate at all." |
| N2 | NOTE | `staged/security/var_dist_joint_law.v:34-35` | "var_dist_own_marginals == a joint law close to a product law is close to the product of its own marginals" | The table entry drops the factor three, which is the whole content of the lemma. Its type is `var_dist J (Mr \`x Ms) <= d -> var_dist J ((fdistmap fst J) \`x (fdistmap snd J)) <= 3%:R * d`. The prose above the table has the factor. | "var_dist_own_marginals == a joint law within a number of a product law is within three times that number of the product of its own marginals" |
| N3 | NOTE | `staged/security/var_dist_joint_law.v:29-30` | "var_dist_prodR == two products with one left factor are as far apart as their right factors" | "with one left factor" reads as a property of each product rather than as the shared factor the statement needs. The type is `var_dist (P \`x Q1) (P \`x Q2) = var_dist Q1 Q2`, one `P` on both sides. | "var_dist_prodR == two products with a common left factor are exactly as far apart as their right factors" |
| N4 | NOTE | `staged/manifest/pgg_tableau_arm_relations.v:56-58` | "The implication that does hold at the five-card one-cut model, in instances/kim2025/five_card_proximity.v, holds because its conclusion is a theorem there and its premise is discarded." | True, and the right thing to say. It sits beside the landing's own ruling for the same file, which removed the pointer to `p4_kim_biased_proximity.v` from `idealproximity_ceiling` on the principle that a framework-level statement does not cite where an instance exhibits it. The two decisions are defensible together, the header being exposition and the declaration comment being the statement, but the difference is worth recording so it is not read as an oversight. | No change proposed. Record the distinction in the landing note. |
| N5 | NOTE | `landing_fidelity.v:388` | "Print Assumptions five_card_biased_proximity_at_singleton." | This is the only landed declaration whose statement the fidelity file does not ascribe. Q5's ruling removed the probe's bare `Check`, and a `Print Assumptions` forces elaboration but pins no proposition. Its type is determined by its body, `@five_card_biased_view_proximity R [set i] (five_card_singleton_below_threshold i)`, both of whose components are ascribed, so the gap is small. | Optional: add `Check (five_card_biased_proximity_at_singleton : forall (R : realType) (i : 'I_5), _).` Not verified by compilation in this audit, so treat it as a suggestion and check it before use. |
| N6 | NOTE | `staged/security/var_dist_joint_law.v:131-135` | "Each marginal of the joint law is within d of the corresponding factor by data processing, and replacing the two factors one at a time costs d each, so the number is spent three times." | The sentences are true of the proof, which is one `var_dist_triangle` to `Mr \`x Ms`, one to `Mr \`x (fdistmap snd J)`, then `var_dist_prodR` and `var_dist_prodL`. They are proof strategy in a rendered comment rather than in a source comment. Soundness is unaffected. This belongs to the naming pass, not this one. | No change proposed here. |

## Coverage

**Remit 1, the three new files as permanent text.**

`security/var_dist_joint_law.v`. The header's two flagged phrases are sound.
"bounds twice a distinguisher's advantage" is type-honest: `var_dist` is the
sum of absolute differences, which is twice the total variation distance, and
an advantage is at most the total variation distance, so the sum bounds twice
the advantage. "tensoring with a common factor neither creates nor destroys
the sum" describes `var_dist_prodR` and `var_dist_prodL`, and both are
equalities, `var_dist (P \`x Q1) (P \`x Q2) = var_dist Q1 Q2` and
`var_dist (P1 \`x Q) (P2 \`x Q) = var_dist P1 P2`. "within three times that
number" matches `var_dist_own_marginals` exactly: hypothesis
`var_dist J (Mr \`x Ms) <= d`, conclusion
`var_dist J ((fdistmap fst J) \`x (fdistmap snd J)) <= 3%:R * d`.
`fdist_prod_snd`'s comment claims infotheo has no counterpart, and that is
right: `infotheo/probability/fdist.v:1040` proves `fdist_prod1 : fdist_prod\`1 = P`
for `fdist_prod P W` with `W : A -> fdist R B`, the notation `P \`x P2` is
`P \`X (fun _ => P2)` at `:1074`, and no `fdist_prod2` exists, only
`fdist_prod2_conv`, a different statement. The R5 sentence appended to
`var_dist_prodR` is accurate: `Local Lemma var_dist_prodR` at
`instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577`,
used once each at `:1100` and `:601`, and `Local`, so invisible outside their
files. `var_dist_prodL` occurs nowhere else in the tree. Findings N2, N3, N6.

`manifest/pgg_tableau_arm_relations.v`. The header states P8's partial verdict
correctly against the spec's "Results of the probe" section. Compiled and
claimed: the input-indistinguishability proposition does not mention its
certificate, which `IndistinguishabilityPropAt` (`pgg_tableau.v:453-461`)
confirms by not naming `cert` at all. The implication holds at the ceiling
two, which `idealproximity_ceiling : IdealProximityPropAt cert 2%:R` gives at
every certificate. And it holds at the five-card instance for a stated
reason. Not claimed and correctly labelled: a countermodel below two,
and the proximity proposition derived from an input-indistinguishability
certificate's own fields. No sentence claims a refutation or a non-implication
that is not compiled. The header's claim that the proximity proposition does
mention its certificate is verifiable from `IdealProximityPropAt`
(`pgg_tableau.v:487-500`), which names `ipc_secret cert`, `ipc_ideal cert` and
`ipc_witness cert`. The claim that an input-indistinguishability certificate
carries no secret and no ideal model is verifiable from
`IndistinguishabilityCert` (`pgg_tableau.v:186-197`), whose `ic_ideal` is a
bare law `R.-fdist (pgg_gT (mp_M (instance_profile A)))`. Every one of the six
declarations is stated at arbitrary `A`, `E` and `sa`, so none names an
instance, including `idealproximity_tail_without_independence`. Findings S4,
S5, N1, N4.

`instances/kim2025/five_card_proximity.v`. The added clause "the advantage a
distinguisher gets from it is at most three hundredths" is attached to
`five_card_biased_view_own_marginals`, whose bound is `3%:R * (1 / 50)`, three
fiftieths. Half of three fiftieths is three hundredths, so the arithmetic is
right and the halving is the right operation, since the sum of absolute
differences is twice the total variation distance. The same reading in the
header, "a distinguisher's advantage against this row is at most one
hundredth", is read off `kim_biased_proximity_cert_epsE : ipc_eps ... = 1 / 50`
and is right. "one per cent of what a pair of laws on a finite carrier can
reach" is right against `var_dist_le2 : var_dist P Q <= 2`. Findings S1, S2,
S3.

**Remit 2, the removals and rewordings.** All six removals and the three other
comment changes were compared against the probe's original sentence in
`notes/probes/2026-09-19-tableau-extensions/`. No removal takes a mathematical
clause, a scope condition or a vacuity boundary with the narration.
`idealproximity_ceiling` loses only the pointer to where an instance exhibits
the ceiling, and the instance's own comment at
`five_card_proximity.v:262-265` keeps the content.
`indistinguishability_prop_cert_free` loses only the pointer to the two
five-card lemmas, and keeps the non-vacuity boundary, "the implication is not
empty for all that". The `_atE` source comment loses the `STATUS.md` pointer
and keeps the fact about `done`. `kim_biased_conclude_below_false` changes
"what the probe could prove" to "what could be proved" and keeps "is false,
and not merely beyond" together with the arithmetic reason.
`five_card_biased_proximity_prop_holds` and
`five_card_biased_indistinguishability_implies_proximity` lose the spec
reference and keep the scope boundary, that a derivation reading the
certificate's fields is a different statement.
`five_card_biased_view_own_marginals` is restated with the same quantifier,
the same number and the same reading, plus the new advantage clause checked
above.

**Remit 3, dependencies.** No cycle. `staged/lib/var_dist_supp.v` requires no
project module. `security/pgg_collusion_bound.v` requires `perm_uniform` and
`pgg_interface` only. Nothing in the tree outside `notes/` names
`var_dist_joint_law`, `pgg_tableau_arm_relations` or `five_card_proximity`, so
no file the new ones depend on can import them back, and
`five_card_proximity.v` imports nothing that imports it. Against production's
`_CoqProject` and the three insertion points `STATUS.md` names, every project
module the three new files require already appears earlier: 2 modules for
`var_dist_joint_law` at the `pgg_collusion_bound` slot, 12 for
`pgg_tableau_arm_relations` at the `pgg_tableau_syntax` slot, 27 for
`five_card_proximity` at the `s5_rows` slot, with zero late or missing in each
case. `card_tnth_count` has exactly one user in the tree outside `notes/`,
`docs/` and `.claude/`, namely `instances/kim2025/five_card_mixing.v:279`, so
its removal from `lib/var_dist_supp.v` breaks no other production file.
`kim_centi_marginal_bound40` and `kim_centi_cut_mixing40` have one user each,
`instances/kim2025/five_card_rows.v:741,744`, which landing 1 replaces. The
staged `five_card_rows.v` has zero hits for either name.

**Remit 4, `landing_fidelity.v`.** Every one of the thirty-one restated
declarations was compared token by token against the staged declaration, and
the staged text is token-identical to the probe's by the landing's own script,
which this audit did not redo. The only differences are the binders that were
section `Variable`s in the staged file and are explicit arguments in the
restatement: `(R : realType) (A B : finType)` for the three product lemmas,
`(R : realType) (A : PGGAlgebraic) (E : ExecutionParams A) (sa : ...)` for the
two section lemmas of the arm relations, `(R : realType)` for the five-card
section lemmas. Nothing is weakened, no bound is loosened and no hypothesis is
added. The fidelity file compiles rc 0 in the audit's directory at 27.5 s, with
no unsatisfied `Fail`, thirty-three `Axioms:` blocks naming only
`constructive_indefinite_description`, `functional_extensionality_dep` and
`propositional_extensionality`, and two "Closed under the global context",
which is the 35 of `STATUS.md`. Every landed lemma, both rows and the
certificate appear under `Print Assumptions`. Provenance is one-sided for
`five_card_mixing` and `five_card_rows` and absent for `var_dist_supp`, which
is finding S6. Mutation check: `land2_sound/mut1.v` restates
`five_card_biased_view_own_marginals` at `2%:R * (1 / 50)` instead of
`3%:R * (1 / 50)` and is rejected, `rc=1`, `Error: Cannot apply lemma
five_card_biased_view_own_marginals`, so the ascription's constant is
load-bearing.

**Remit 5, vacuity.** The certificate's five fields are all real terms. The
ideal is `amf_sample five_card_uniform_family R idx`, a published model. The
witness is `five_card_exact_witness R idx`, whose independence field is
`@five_card_static_obs_indep R idx`. The secret is `five_card_leakage.Secret R`,
which is `fun w => let: (a, b, _) := w in a && b` at
`instances/denboer1989/five_card_leakage.v:76`, a real secret bit and not a
unit. The number is `1 / 50`. The last field is
`fun C _ => @kim_biased_proximity_close R C`, a proved distance. `ipc_close`'s premise is `#|C| < profile_k (instance_profile A)`.
At five-card `profile_k` is 2: `five_card_biased_view_proximity` states its
hypothesis as `(#|C| < 2)%N` and is proved by `view_proximity_of`, which
consumes the premise at `profile_k`, so the two are convertible. The premise
is therefore satisfied by the empty coalition and by every singleton, and
`five_card_singleton_below_threshold : (#|[set i]| < profile_k
(instance_profile five_card_algebra))%N` exhibits a non-empty one. The
certificate's own bound `kim_biased_proximity_close` holds at every coalition,
so the threshold enters only through the arm's proposition, as its comment
says.

**Remit 6, the recorded `Fail`s.** Two were re-checked by compiling an
un-`Fail`ed copy in the audit's directory. `idealproximity_prop_cert_free`
(`land2_sound/unfail_a.v`) gives `rc=1`, `Error: No applicable tactic.`, which
is the `by []` not closing the equality, as its comment says and no more.
`kim_centi_proximity_from_biased` (`land2_sound/unfail_b.v`) gives `rc=1`,
`The term "kim_biased_proximity_cert R idx" has type "IdealProximityCert
(amf_sample kim_biased_family R idx)" while it is expected to have type
"IdealProximityCert (amf_sample kim_centi_family R idx)"`, which is the
recorded reason. Its comment adds that the two adapters differ in their sample
space as well as in their law, and that is true and checkable:
`kim_single_sample` is built on `five_card_leakage.Omega`, the pair of
committed bits with one rotation (`instances/kim2025/five_card_models.v:139`),
and `kim_centi_repeated_sample` on `kim_repeated_sampleT`, the pair with a
seven-letter word (`:146`, `:382`). All nine comments were read. None claims
more than that a written term is rejected except where the extra claim is
independently checkable, and the two that come closest state their own limit:
`idealproximity_prop_cert_free` says "and no more: two logically equivalent
propositions would still be equal under propositional extensionality", and
`five_card_biased_proximity_by_computation` gives the reason, that a variation
distance over an abstract real field is not a Boolean the kernel reduces,
rather than generalising from one tactic.

**Scans.** The report was checked against the project's banned vocabulary list
and contains none of its words, and writes "the sum of absolute differences"
in full.

## Method

Experiment directory
`/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/land2_sound/`.
No repository file was edited except this one. Every compile went through the
machine-wide `rocq1` lock, one Rocq process at a time, with `rocq compile` and
never `make`. `instances/psl211/psl211_endpoints.v` was never compiled. The
load-path flags are written in `cc.py` with absolute paths: production roots
first, `-Q . tableau_ext_landing2` next, the seven staged roots last, which is
the order `STATUS.md` records.

| File compiled by this audit | rc | wall |
|---|---|---|
| `staged/lib/var_dist_supp.v` | 0 | 6.4 s |
| `staged/security/var_dist_joint_law.v` | 0 | 6.9 s |
| `staged/instances/kim2025/five_card_mixing.v` | 0 | 7.4 s |
| `staged/instances/kim2025/five_card_analysis.v` | 0 | 4.0 s |
| `staged/manifest/pgg_analysis_manifest.v` | 0 | 5.9 s |
| `staged/manifest/pgg_tableau.v` | 0 | 13.1 s |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.4 s |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.3 s |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.5 s |
| `staged/instances/s5/s5_rows.v` | 0 | 4.0 s |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.1 s |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.4 s |
| `staged/manifest/pgg_analysis_client.v` | 0 | 3.8 s |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.7 s |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.6 s |
| `landing_fidelity.v` | 0 | 27.5 s |
| `mut1.v`, the mutation and the three qualified provenance probes | 1 | 4.1 s |
| `unfail_a.v`, `idealproximity_prop_cert_free` without its `Fail` | 1 | 4.1 s |
| `unfail_b.v`, `kim_centi_proximity_from_biased` without its `Fail` | 1 | 4.1 s |

The three `rc=1` runs are the intended failures and their error lines are
quoted in the coverage above.
