# P8 arm-relations probe: naming and style audit (2026-09-20)

Read-only audit of `notes/probes/2026-09-20-p8-arm-relations/`
(`p8a_degenerate_certificate.v`, `p8b_proximity_from_indistinguishability.v`,
`p8b_instances.v`, `LEDGER.md`) against the landing homes
`manifest/pgg_tableau_arm_relations.v`, `manifest/pgg_tableau.v`,
`lib/var_dist_supp.v`, `lib/proba_entropy_ext.v`,
`security/var_dist_joint_law.v` and the two instance trees.

Nothing was compiled and no repository file other than this one was written.

## Verdict

**NO-GO for landing under these names.**

The mathematics is not at issue here. Eleven MUST items stand between the probe
and production, and three of them are not local renames:

- one live name collision with a compiled tree lemma (V1);
- a word used as a value judgement across a file name, a section name and three
  declarations (V7);
- the landing home's own header states as *not claimed* two things this probe
  proves, and its account of what a refutation would need is superseded (V34).

Two further MUSTs are statements, not spellings: a headline carries a parameter
that is discharged inside its own proof (V10), and a definition's docstring
claims two properties that the definition alone does not have (V17, V26). Fix
those before the names are cited anywhere else.

Every finding below was checked against the statement it sits on.

## Declarations the probe introduces

Thirty-eight declarations plus three sections.

`p8a_degenerate_certificate.v`: `var_dist_self`, `var_dist_self_le0`,
`fdistmap_notin_codom0`, `var_dist_disjoint_supp_eq2`, `inde_RV_cst`,
section `degenerate_certificate_over_any_model`, `const_true_witness`,
`degenerate_proximity_cert`, `degenerate_proximity_prop_below2_false`,
`proximity_below2_uniform_in_cert_false`,
`indistinguishability_prop_proximity_below2_false`,
`same_secret_proximity_cert`, `proximity_at0_with_equal_constant_secrets`,
`same_secret_proximity_prop_at0`,
`proximity_below2_false_needs_distinct_secrets`.

`p8b_proximity_from_indistinguishability.v`: section
`reading_with_a_constant_conditional_law`, `sum_reading_fibreE`,
`fdistmap_pair_arg_condE`, `fdistmap_reading_mixtureE`,
`fdistmap_pair_arg_prodE`, section `proximity_from_indistinguishability`
(variables `argT`, `arg_decode`, `arg_read`, `Parg`, `rho`, `rho0`, hypotheses
`Harg`, `Hprod`, `Hconst`), `sa_cut_dist_of_prodE`, `ideal_product_adapter`,
`ideal_product_sampleP`, `ideal_product_joint_prodE`,
`ideal_product_reading_indep`, `ideal_product_witness`,
`joint_reading_arg_var_dist_le`, `proximity_close_of_indistinguishability`,
`proximity_cert_of_indistinguishability`,
`proximity_prop_of_indistinguishability`, the recorded rejection
`proximity_prop_of_indistinguishability_by_conversion`,
`proximity_eps_halves_cert_epsE`.

`p8b_instances.v`: `pgl27_word_arg_cut_prod`, `pgl27_word_arg_readE`,
`pgl27_word_proximity_eps_genericE`, `kim_biased_arg_cut_prod`,
`kim_biased_arg_readE`, `kim_biased_proximity_epsE`,
`kim_biased_indistinguishability_epsE`,
`kim_biased_proximity_eps_generic_le`.

Clean: no term from the project's barred vocabulary appears in any of the three
files or in the ledger, and no token of a capital letter followed by a digit
appears as a distance name. "The sum of absolute differences" is written in
full wherever the concept is named in prose.

## Findings

| id | class | file:line | name or sentence | rule and problem | replacement |
|---|---|---|---|---|---|
| V1 | MUST | p8a:47 | `var_dist_self` | Collision. `legacy/security/pgg_uniform_security.v:86` already declares `Lemma var_dist_self (P : R.-fdist A) : var_dist P P = 0`, in the same `pgg_smc` namespace, and that file is compiled (`_CoqProject:98`). Landing a second copy in `lib/var_dist_supp.v` puts two identical lemmas of one name in one namespace. | Move the legacy lemma down into `lib/var_dist_supp.v` and have `pgg_uniform_security.v` import it; do not restate. If the legacy file must be left untouched, land under `var_dist_xx` and record the duplicate. |
| V2 | SHOULD | p8a:47 | `var_dist_self` | MathComp's published fragment for an operation at one argument twice is `xx` (`eqxx`, `lexx`, `ltxx`) or `rr` (`subrr`, `divrr`). `_self` is not published. infotheo's own file is prefix-style (`pos_var_dist`, `def_var_dist`, `symmetric_var_dist`, `leq_var_dist`); the landing home is suffix-style, so suffix wins. | `var_dist_xx` |
| V3 | NOTE | p8a:51 | `var_dist_self_le0` | A wrapper handing `<= 0` where the equation gives `= 0`. Its only two uses are in the mutation block (V16). `_le0` is published, so the name is fine if the block lands. | keep the name; land only with the block |
| V4 | SHOULD | p8a:55-57 | "It is the contrapositive of `fdistmap_neq0_codom`, in the form a support argument consumes." | Statement comment rule: the second clause is meta about how the lemma is consumed. The contrapositive claim itself checks out against `lib/var_dist_supp.v:147`. | "A pushforward gives no mass to a point outside the image of its map. It is the contrapositive of `fdistmap_neq0_codom`; together with `var_dist_supp_disjoint_eq2` it turns a constant map into a law that misses every value the constant does not take." |
| V5 | SHOULD | p8a:72 | `var_dist_disjoint_supp_eq2` | One word per concept with the home: `lib/var_dist_supp.v` already writes the qualifier as `var_dist_fdistmap_supp_inj`, `supp` before the property. | `var_dist_supp_disjoint_eq2` |
| V6 | SHOULD | p8a:66-71 | "Each law contributes its whole mass to the sum, and each law has mass one." | Proof strategy in a docstring. The sentence is true of the proof, not of the statement. | move to a `(* ... *)` beside the proof; keep the first and last sentences, and write "a single draw" for "a single observation" (V28) |
| V7 | MUST | p8a: file name, :12, :118, :139, :150, and 12 prose occurrences | "degenerate" | Metaphor and value judgement, not a defined term: nothing in the tree defines it, and it is used to mean "legal but says nothing", which is a judgement about the certificate rather than a property it has. The property is that the certificate's two secrets are constants that differ. | write the relation: `idealproximity_cert_cst_secrets_true_false`, `idealproximity_prop_cst_secrets_lt2_false`, section `idealproximity_cert_over_any_model` |
| V8 | MUST | p8a:139,150,180,195,214,221,239,246; p8b:265,290,304,322,330 | bare `proximity_` prefix | One word per concept with the target. `manifest/pgg_tableau_arm_relations.v` writes `idealproximity_` for every lemma of this arm (`idealproximity_prop_at2`, `idealproximity_reading_le`, `idealproximity_tail`, `idealproximity_prop_cert_free`, `idealproximity_tail_without_independence`), matching `IdealProximityCert` and `IdealProximityPropAt`. Bare `proximity` is the tree's word at instance level only, where the instance prefix disambiguates (`pgl27_word_proximity_cert`, `kim_biased_proximity_cert`), so `p8b_instances.v` is exempt. | rename every manifest-bound declaration to `idealproximity_`; leave the instance names alone |
| V9 | MUST | p8a:150,180,195 | `below2` | Not a published fragment. MathComp spells it `lt2` (`ltxx`, `lt0n`), and the landing home already spells "at two" as `at2` in `idealproximity_prop_at2`. | `lt2` throughout |
| V10 | MUST | p8a:180-183 | `proximity_below2_uniform_in_cert_false (Hk) (Q : Prop) (c : R) : Q -> c < 2 -> ~ (Q -> forall cert, IdealProximityPropAt cert c)` | The statement carries a parameter its own proof discharges. With `HQ : Q` in hand, `Q -> S` is equivalent to `S`, so the lemma is the `Q`-free `~ forall cert, IdealProximityPropAt cert c` dressed in a premise. The docstring already says "the strength of the premise plays no part"; the statement should say it by not having the premise. | land `idealproximity_prop_lt2_uniform_in_cert_false (Hk) (c : R) : c < 2%:R -> ~ forall cert : IdealProximityCert sa, IdealProximityPropAt cert c`, and keep the corollary at the input-indistinguishability premise (V11) as the one premise-shaped statement |
| V11 | MUST | p8a:177-179 | "The premise is discharged by the degenerate certificate alone, so the strength of the premise plays no part." | False as written: the premise `Q` is discharged by the hypothesis `HQ`, and the certificate refutes the *conclusion*. Checked against the proof term at :184-188. | "The conclusion is refuted by one certificate available over every model, so no premise can rescue it." |
| V12 | NOTE | p8a:195 | `Corollary indistinguishability_prop_proximity_below2_false` | The landing home declares only `Lemma` and recorded `Fail Definition`. MathComp uses `Lemma` throughout. Also V8 and V9 apply. | `Lemma indistinguishability_prop_idealproximity_lt2_false` |
| V13 | MUST | p8b:102, and every lemma of the landed section | implicit arguments after discharge | The ledger records that in `fdistmap_pair_arg_prodE` the discharged section variables `Q` and `f` became implicit under `Set Implicit Arguments` with `Unset Strict Implicit`, so a positional application silently misaligned and reported only "Cannot apply lemma"; `Check` did not reveal it. `manifest/pgg_tableau_arm_relations.v:75-77` carries the same two lines and has zero `Arguments` declarations, while `manifest/pgg_tableau.v` carries 46. | add one `Arguments` line per landed lemma of the new section, following `Arguments IdealProximityPropAt {R A E sa} cert c` |
| V14 | SHOULD | p8b:175 | `ideal_product_sampleP` | A trailing `P` is MathComp's reflection marker; this is an equation closed by `erefl`. It is also unused in the file. | drop it, or `ideal_prod_samplePE` if a later proof needs it |
| V15 | SHOULD | p8b:170,175,182,199,229 vs :102,144,151 | `ideal_product_*` beside `*_prodE` and `Hprod` | One word per concept inside one file: `product` and `prod` for the same thing. The tree writes `prod` (`var_dist_prodR`, `var_dist_prodL`, `fdist_prod_snd`, `fdistmap_prodr`). `indep` needs no change: the tree writes `indep` 60 times against infotheo's `inde` 15, so `indep` is the project's word. | `ideal_prod_adapter`, `ideal_prod_reading_arg_prodE`, `ideal_prod_reading_indep_arg`, `exact_witness_ideal_prod` |
| V16 | SHOULD | p8a:214-252 | the mutation block | "Keep only claimed or premise": three of the four declarations are mutation apparatus. The one with independent content is `same_secret_proximity_prop_at0`, the mirror of `idealproximity_prop_at2`: a certificate can publish zero over any model whatever. | land `idealproximity_prop_at0_cst_secrets_true_true` and its certificate; leave `proximity_at0_with_equal_constant_secrets` and the negated wrapper in the probe |
| V17 | MUST | p8a:246 | `proximity_below2_false_needs_distinct_secrets` | "needs" asserts a proof dependency, which is meta, and the statement does not make it: the statement is the double negation of `same_secret_proximity_prop_at0` with `0 < 2`. | do not land it (V16); the dependency belongs in the probe record |
| V18 | MUST | p8b:330-334 | `proximity_eps_halves_cert_epsE` | Two problems. (a) `cert_eps cert := sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` at `manifest/pgg_tableau.v:475-478`, and `ipc_eps (proximity_cert_of_indistinguishability Hic)` is `sw_bound_eps (ic_b ic)` by construction, so the lemma restates `cert_eps`'s own definition. Stated inside the section it drags in nine parameters the equation does not use. (b) "halves" names a relation the statement does not write: the statement is an addition. | land `cert_eps_dbl (cert : IndistinguishabilityCert sa) : cert_eps cert = sw_bound_eps (ic_b cert) *+ 2` beside `cert_eps` in `manifest/pgg_tableau.v`; drop the section version |
| V19 | MUST | p8b:298-303 | "so the proximity reading of one certificate is the sharper of the two numbers by a factor of two" | Type-honest phrasing and domain frame. The two numbers bound two different quantities: `IndistinguishabilityPropAt` bounds the distance between one model's coalition readings at two run arguments, `IdealProximityPropAt` bounds the distance between two models' joint laws of a reading and the secret. Neither refines the other, so neither is the sharper. | "B5. The proximity arm's proposition at that certificate, at the input-indistinguishability certificate's marginal bound once. That certificate's own number for the other arm, `cert_eps`, is the same bound added to itself, one term for each of the two run arguments that arm compares. The two numbers bound different quantities and neither refines the other. The bound here is conditional on the model drawing its cut apart from its run argument and on the endpoint statement, and unconditional in the coalition, at every coalition below the threshold." |
| V20 | MUST | p8b:170-173 with :167-169 | "draws the run argument from the actual model's own prior … It leaks nothing about the argument by construction" | The docstring claims two things the definition alone does not have. `ideal_product_adapter` uses only the section variables `Parg`, `rho0`, `arg_decode`; the identification of `Parg` with the actual model's prior follows from `Hprod`, and the independence follows from `Hconst`, and neither hypothesis is discharged onto the definition. | "B2. The ideal model: the program's own execution run on the product of a law on the finite reading of the run argument with the ideal cut law, so its cut is drawn apart from its argument. Under the constancy the input-indistinguishability certificate carries, its coalition readings are independent of its run argument at every coalition below the threshold, and that independence is what makes it a model whose privacy is proved and not a bare law." |
| V21 | MUST | p8b_instances:46,79 | `pgl27_word_arg_cut_prod`, `kim_biased_arg_cut_prod` | Both are existential (`exists Parg rho, …`) and proved with `do 2 eexists`, so neither statement names its two factors. The landed section is parameterised by `Parg` and `rho`, and `rho` is later tied to `ic_ideal ic`; an existential cannot instantiate it, and B6's comparison of numbers needs the same `rho` the certificate's distance field is about. | state with named factors. Both are determined by the model: take the first marginal of `Hprod` to get `Parg = fdistmap arg_read (sa_sampleP sa)` and `rho = sa_cut_dist sa`. Name them and drop the `exists`; then rename `pgl27_word_arg_cut_prodE`, `kim_biased_arg_cut_prodE` |
| V22 | MUST | p8b_instances:65, :111 | `pgl27_word_proximity_eps_genericE`, `kim_biased_proximity_eps_generic_le` | "generic" is a word about how a construction was obtained; neither statement mentions any construction. Both compare the instance's hand-built proximity certificate's `ipc_eps` with the input-indistinguishability certificate's `sw_bound_eps (ic_b …)`. In the second the word points at the wrong side: the left of the `<=` is the hand-built number (one fiftieth), the right is the marginal bound (the square root of five over eighty), so the name reads as a bound on the second when it is a bound by it. | `pgl27_word_proximity_eps_sw_boundE`, `kim_biased_proximity_eps_le_sw_bound` |
| V23 | MUST | p8a:40 | `Search "dist_of_RV".` | A live query left in the source; it prints on every compile. Zero tracked non-`notes/` `.v` files contain a bare `Search`. | delete |
| V24 | MUST | p8a:256-258, p8b:338 | `Print Assumptions …` | Zero tracked non-`notes/` `.v` files contain `Print Assumptions`. The assumption evidence belongs in the ledger. | delete on landing; keep the output in `LEDGER.md` |
| V25 | MUST | manifest/pgg_tableau_arm_relations.v:38-49 and :51-59 | the "Not claimed." paragraph and the `Lemmas:` index | The header states as not claimed two things this probe proves. "Nor is the proximity proposition derived from an input-indistinguishability certificate's own fields at a stated constant" is falsified by B4 and B5. Its account of what a refutation of the uniform implication needs ("a model whose coalition readings … stay within the constant … and whose distance to the ideal exceeds the constant") is superseded: A5 refutes the version whose premise is at the certificate's own number, using only a certificate, because `indistinguishability_tail` discharges that premise unconditionally. Both versions can stand, and the header must say which is which or a reader sees a contradiction. Every landed declaration also needs an index row, names never touching `==`. | rewrite the paragraph to distinguish the implication at an arbitrary named constant (still open, still needs a model) from the implication at the certificate's own number (refuted, A5), and extend the index |
| V26 | SHOULD | p8b:17-24 | "Departure from the spec's B1 and B2. … Neither typechecks: …" | History and plan narration in a file header. Correct for the ledger, barred from the landed file. | keep in `LEDGER.md`; in the landed header keep only the reason the run argument is read through a finite reading, which is the statement at p8b:128-130 and should survive verbatim |
| V27 | SHOULD | p8a:125,137,147,178,190; p8b:60,148,168,180,227,236,260,285,298,320 | `A3.`, `A4.`, `A5.`, `B1.` … opening every docstring | Plan-task tokens in statement comments. | strip on landing; the ledger keeps the mapping |
| V28 | SHOULD | p8a:190 | "A5 at the premise the parent statement had in view" | Reference to a plan document in a statement comment, plus a ledger token. | "The same refutation with the premise a reader is most likely to bring: the input-indistinguishability proposition at the certificate's own number, which `indistinguishability_tail` gives unconditionally." Checked: `indistinguishability_tail ic : IndistinguishabilityPropAt ic (cert_eps ic)`, applied with one argument at :204. |
| V29 | SHOULD | p8a:147-149 | "Below a positive threshold the degenerate certificate's proximity proposition fails at every number below two. … The two secrets disagree by construction, and that disagreement is the whole of the argument." | "Below a positive threshold" misreads the hypothesis, which is that the threshold is positive. The last sentence is proof strategy. The vacuity boundary is unstated: at threshold zero no coalition is below it and the refutation is empty. | "When the instance's privacy threshold is positive the empty coalition is below it, and there the certificate's proposition compares a joint law carrying all its mass at the secret value false with a product whose secret factor is the point mass at true. The two are two apart, so the proposition fails at every number below two. A published proximity number therefore says something only against a certificate an instance builds, and nothing against a certificate a reader may choose." Checked against :150-173: `cards0` gives the empty coalition, the actual secret is the constant false, the ideal witness's secret is the constant true. |
| V30 | SHOULD | p8a:123-125 | "Its independence field is A2, so no property of the model is used." | Ledger token and a statement about the proof rather than the object. | "A constant random variable is independent of every random variable, so this witness's independence field holds at an arbitrary model, and the exact arm's record alone therefore does not say that a model hides anything." |
| V31 | SHOULD | p8b:53 | section `reading_with_a_constant_conditional_law` | Article in a section name; every other section in the landing homes is terse (`proximity_against_indistinguishability`, `var_dist_supp_inj`, `var_dist_product_factor`). | `fdist_prod_cst_cond` |
| V32 | SHOULD | p8b:61,84 and :73 | `sum_reading_fibreE`, `fdistmap_reading_mixtureE`, `fdistmap_pair_arg_condE` | "reading" and "arg" are the framework's domain words used for an arbitrary `f : T -> G -> V` and an arbitrary first coordinate, in a section that names no coalition and no model. If these land in `lib/` (V35 says they should), the domain word does not belong in the identifier. | `sum_prod_fibreE`, `fdistmap_prod_mixtureE`, `fdistmap_pair_fst_condE`, `fdistmap_pair_fst_prodE` |
| V33 | SHOULD | p8b:238 | `joint_reading_arg_var_dist_le` | Main symbol last. Both homes put it first: `var_dist_fdistmap_pair`, `var_dist_prodR`, `var_dist_own_marginals`, `var_dist_fdistmap_supp_inj`. | `var_dist_joint_reading_arg_le` |
| V34 | SHOULD | p8b:233-237 | "The two models share the prior on the run argument and read one function of the pair, so the distance on the cut group transfers by data processing." | Proof strategy in a docstring. | move to a `(* ... *)` beside the proof; the first sentence already states the fact and earns a position sentence instead |
| V35 | NOTE | p8a:95 | `inde_RV_cst` | No collision anywhere. infotheo has `inde_RV_unit` and `inde_unit_RV` in `smc/smc_proba.v` and `du2002/spp_proba.v` but no constant version, so the new lemma is justified and the name parallels the published one; `cst` is MathComp's fragment for a constant function. Two observations: the lemma follows from `inde_RV_unit` with `inde_RV_comp` at `f := idfun`, `g := fun _ : unit => c`, if `smc_proba` may be imported; and if the mirrored orientation is ever needed, name it `inde_cst_RV` after infotheo's pair. |
| V36 | NOTE | p8a:66-71 | "so two here is the distance between two laws that a single observation tells apart with certainty" | One word per concept: the tree's word for what a coalition sees is "reading"; "observation" appears once, here, where the frame is a distinguisher and not a coalition. | "a single draw tells apart with certainty" |
| V37 | NOTE | p8b:149 | `sa_cut_dist_of_prodE` | The `sa_` prefix marks record fields in `security/pgg_sample_adapter.v`, but `sa_coalition_viewE` is existing precedent for an `sa_`-prefixed lemma with the `E` suffix. Consistent as it stands. | keep |
| V38 | NOTE | p8b:265-283 | `proximity_close_of_indistinguishability` | The coalition-size hypothesis is taken and discarded (`move=> _`), so the bound holds at every coalition, not only below the threshold. Keeping the hypothesis is right, because the statement must be the `ipc_close` field's shape, but the docstring should say what it omits: the threshold plays no part in this step. | add "The coalition bound holds at every coalition; the threshold hypothesis is the field's shape and is not used here." |
| V39 | NOTE | p8b_instances:106-108 | `kim_biased_indistinguishability_epsE` | Duplicates `kim_biased_epsE` (`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:582`) up to the conversion `ic_b (kim_biased_cert R idx) = kim_biased_marginal_bound R`; the proof is `exact: kim_biased_epsE`. | land only if a later statement needs the `ic_b` form; otherwise use `kim_biased_epsE` |
| V40 | NOTE | p8b_instances:92-95 | `kim_biased_arg_readE` | The only declaration in the three files with no statement comment, beside three siblings that have one. | add one |
| V41 | NOTE | p8a:12 | header box line 79 bytes where the box is 80 | Layout: the closing `*)` does not line up with the rest of the box. | pad by one space |
| V42 | NOTE | p8b_instances:49,50 | 81 and 82 bytes | Layout: at most 80 bytes per line. Both are the `@sa_arg` / `@sa_cut` application inside the existential. | breaking the `exists` into named factors (V21) removes both lines |

## Proposed final name list

### `lib/var_dist_supp.v`

| probe name | final name |
|---|---|
| `var_dist_self` | `var_dist_xx` (or reuse the legacy lemma, V1) |
| `var_dist_self_le0` | `var_dist_xx_le0`, only with the mutation block |
| `fdistmap_notin_codom0` | unchanged |
| `var_dist_disjoint_supp_eq2` | `var_dist_supp_disjoint_eq2` |

### `lib/proba_entropy_ext.v`

| probe name | final name |
|---|---|
| `inde_RV_cst` | unchanged |

### `lib/` product-law section (new file, or appended to `lib/var_dist_supp.v`)

| probe name | final name |
|---|---|
| section `reading_with_a_constant_conditional_law` | section `fdist_prod_cst_cond` |
| `sum_reading_fibreE` | `sum_prod_fibreE` |
| `fdistmap_pair_arg_condE` | `fdistmap_pair_fst_condE` |
| `fdistmap_reading_mixtureE` | `fdistmap_prod_mixtureE` |
| `fdistmap_pair_arg_prodE` | `fdistmap_pair_fst_prodE` |

### `security/var_dist_joint_law.v`

| probe name | final name |
|---|---|
| (extracted from `joint_reading_arg_var_dist_le`) | `var_dist_fdistmap_prodR_le : var_dist (fdistmap h (P \`x Q1)) (fdistmap h (P \`x Q2)) <= var_dist Q1 Q2` |

### `manifest/pgg_tableau.v`

| probe name | final name |
|---|---|
| (extracted from `proximity_eps_halves_cert_epsE`) | `cert_eps_dbl` |

### `manifest/pgg_tableau_arm_relations.v`

| probe name | final name |
|---|---|
| section `degenerate_certificate_over_any_model` | section `idealproximity_cert_over_any_model` |
| `const_true_witness` | `exact_witness_cst_true` |
| `degenerate_proximity_cert` | `idealproximity_cert_cst_secrets_true_false` |
| `degenerate_proximity_prop_below2_false` | `idealproximity_prop_cst_secrets_lt2_false` |
| `proximity_below2_uniform_in_cert_false` | `idealproximity_prop_lt2_uniform_in_cert_false`, restated without the `Q` parameter |
| `indistinguishability_prop_proximity_below2_false` | `indistinguishability_prop_idealproximity_lt2_false`, as a `Lemma` |
| `same_secret_proximity_cert` | `idealproximity_cert_cst_secrets_true_true` |
| `same_secret_proximity_prop_at0` | `idealproximity_prop_at0_cst_secrets_true_true` |
| `proximity_at0_with_equal_constant_secrets` | not landed |
| `proximity_below2_false_needs_distinct_secrets` | not landed |
| `sa_cut_dist_of_prodE` | unchanged |
| `ideal_product_adapter` | `ideal_prod_adapter` |
| `ideal_product_sampleP` | not landed |
| `ideal_product_joint_prodE` | `ideal_prod_reading_arg_prodE` |
| `ideal_product_reading_indep` | `ideal_prod_reading_indep_arg` |
| `ideal_product_witness` | `exact_witness_ideal_prod` |
| `joint_reading_arg_var_dist_le` | `var_dist_joint_reading_arg_le` |
| `proximity_close_of_indistinguishability` | `idealproximity_close_of_indistinguishability` |
| `proximity_cert_of_indistinguishability` | `idealproximity_cert_of_indistinguishability` |
| `proximity_prop_of_indistinguishability` | `idealproximity_prop_of_indistinguishability` |
| `proximity_prop_of_indistinguishability_by_conversion` | `idealproximity_prop_of_indistinguishability_by_conversion` |
| `proximity_eps_halves_cert_epsE` | not landed; see `cert_eps_dbl` |

### Instances

`proximity` stays bare here: the tree already writes `pgl27_word_proximity_cert`
and `kim_biased_proximity_cert`, and the instance prefix disambiguates.

| probe name | final name |
|---|---|
| `pgl27_word_arg_cut_prod` | `pgl27_word_arg_cut_prodE`, factors named |
| `pgl27_word_arg_readE` | unchanged |
| `pgl27_word_proximity_eps_genericE` | `pgl27_word_proximity_eps_sw_boundE` |
| `kim_biased_arg_cut_prod` | `kim_biased_arg_cut_prodE`, factors named |
| `kim_biased_arg_readE` | unchanged, plus a statement comment |
| `kim_biased_proximity_epsE` | unchanged |
| `kim_biased_indistinguishability_epsE` | unchanged, or dropped (V39) |
| `kim_biased_proximity_eps_generic_le` | `kim_biased_proximity_eps_le_sw_bound` |

## Placement

Load order in `_CoqProject`: `lib/` 30-35, `security/pgg_collusion_bound.v` 87,
`security/var_dist_joint_law.v` 88, `security/pgg_sample_adapter.v` 110,
`instances/pgl27/pgl27_models.v` 203, `instances/kim2025/five_card_models.v` 76,
`manifest/pgg_tableau.v` 221, `manifest/pgg_tableau_arm_relations.v` 223, the
two `tableau/*_analysis_bridged.v` at 229 and 242.

| declaration | file | why the arrows stay upward |
|---|---|---|
| `var_dist_xx`, `var_dist_xx_le0`, `fdistmap_notin_codom0`, `var_dist_supp_disjoint_eq2` | `lib/var_dist_supp.v` | mathcomp and infotheo only; `fdistmap_notin_codom0` sits beside its contrapositive `fdistmap_neq0_codom`, and the disjointness lemma beside `var_dist_le2`, the bound it meets |
| `inde_RV_cst` | `lib/proba_entropy_ext.v` | the tree's home for infotheo extensions; it mentions no `var_dist`, so `var_dist_supp.v` would be topically wrong |
| `sum_prod_fibreE`, `fdistmap_pair_fst_condE`, `fdistmap_prod_mixtureE`, `fdistmap_pair_fst_prodE` | `lib/` | all four are pure `fdist` and `fdistmap` statements with no `var_dist` and nothing from `security/`. Putting them in `security/var_dist_joint_law.v` would place them above `pgg_collusion_bound.v` for no reason. A new `lib/fdist_prod_cond.v` after `lib/var_dist_supp.v`, or a section appended to it |
| `var_dist_fdistmap_prodR_le` | `security/var_dist_joint_law.v` | the general core of B3: one map applied to two products with a common left factor. Its two steps, `var_dist_fdistmap` and `var_dist_prodR`, are at or below that file (`pgg_collusion_bound.v` 87 and the file itself) |
| `cert_eps_dbl` | `manifest/pgg_tableau.v` | it is `cert_eps`'s own arithmetic and belongs beside the definition at :475, not in a section about two arms |
| everything else of A3 to A5 and B1 to B5 | `manifest/pgg_tableau_arm_relations.v` | they name `IdealProximityCert`, `ExactWitness`, `IndistinguishabilityCert`, `static_coalition_obs`, `sa_coalition_view`, `idealproximity_tail`, all from `manifest/pgg_tableau.v` (221), which that file already imports; nothing below the manifest layer is touched |
| `pgl27_word_arg_cut_prodE`, `pgl27_word_arg_readE` | `instances/pgl27/pgl27_models.v` | `pgl27_word_family` is defined there (:424), `fdistmap_prodr` comes from `security/pgg_sample_adapter.v`, which the file already imports, and the file imports no tableau, framework or manifest module. `instances/pgl27/pgl27_proximity.v` stays untouched |
| `kim_biased_arg_cut_prodE`, `kim_biased_arg_readE` | `instances/kim2025/five_card_models.v` | `kim_biased_family` is defined there (:435), `five_card_sample_arg` in `five_card_exec.v`, which it imports; same import profile as above. `instances/kim2025/five_card_proximity.v` stays untouched |
| `pgl27_word_proximity_eps_sw_boundE` | `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | both certificates it names are defined there, `pgl27_word_cert` at :341 and `pgl27_word_proximity_cert` at :825 |
| `kim_biased_proximity_epsE`, `kim_biased_proximity_eps_le_sw_bound` | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | `kim_biased_cert` at :628 and `kim_biased_proximity_cert` at :971, and `kim_biased_epsE` at :582 is the step the comparison rewrites with |

Not `*_tableau_checks.v` for the instance facts: that file's header declares it
holds terms the kernel refuses, with one positive statement marked as the
exception. Four more positive statements would change what the file is.

## Section structure for the landed manifest sections

Read against `Section proximity_against_indistinguishability`
(`manifest/pgg_tableau_arm_relations.v:103-182`), which declares four variables
and no hypothesis:

```
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
```

**Section one, A3 to A5.** The same four variables and nothing else. The
threshold hypothesis stays an explicit argument on the two lemmas that use it,
as the probe has it. A section-wide `Hypothesis Hk` would also be sound, since
Rocq discharges only the variables a declaration uses and the two certificates
do not use it, but carrying it as an argument matches the existing section's
style of holding no hypothesis, and keeps the two `Definition`s free of a proof
argument. After discharge `R`, `A`, `E` and `sa` are all inferable from `cert`
or from the certificate the lemma names, so they become implicit exactly as
they do for `idealproximity_reading_le`.

**Section two, B1 to B5.** The probe declares four variables and one hypothesis
more than it needs.

- `Parg` and `rho` are determined by `Hprod`: the first marginal of both sides
  gives `Parg = fdistmap arg_read (sa_sampleP sa)` by `fdist_prod1` and
  `fdistmap_comp`, and `rho = sa_cut_dist sa` is exactly what
  `sa_cut_dist_of_prodE` proves. State the hypothesis with the two marginals in
  place of the two variables and both disappear.
- `rho0` and `Hic : ic_ideal ic = rho0` collapse if the certificate itself is a
  section variable. Declare `Variable ic : IndistinguishabilityCert sa` before
  the constancy hypothesis and set the ideal law to `ic_ideal ic`; then `Hic`
  vanishes and each of the last four declarations loses an argument. The
  instances instantiate `ic` with `pgl27_word_cert secretP` and
  `kim_biased_cert R idx`, which is how the section will be used.

What remains:

```
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Variable argT : finType.
Variable arg_decode : argT -> ex_inputT E.
Variable arg_read : sa_sampleT sa -> argT.
Hypothesis Harg : forall u, sa.(sa_arg) u = arg_decode (arg_read u).
Hypothesis Hprod : fdistmap (fun u => (arg_read u, sa.(sa_cut) u))
                     (sa_sampleP sa)
                   = fdistmap arg_read (sa_sampleP sa) `x sa_cut_dist sa.
Variable ic : IndistinguishabilityCert sa.
Hypothesis Hconst : (* the constancy of the ideal reading, at ic_ideal ic *)
```

`Hconst` is `ic_const ic` and can be dropped as a hypothesis, read off the
certificate instead.

**Implicit arguments after discharge.** This is where the prover lost time, and
the landed file has no defence yet: `manifest/pgg_tableau_arm_relations.v`
carries `Set Implicit Arguments` with `Unset Strict Implicit` and zero
`Arguments` declarations, while `manifest/pgg_tableau.v` carries 46. After
discharge, `argT` is inferable from `arg_read`, but `arg_decode` is inferable
from nothing in a conclusion such as `sa_cut_dist sa = rho`, and the finTypes
are implicit, so the argument list of each lemma is an order Rocq chooses by
first use. Write one `Arguments` line per landed lemma, in the home's own
idiom, for example

```
Arguments fdistmap_pair_fst_prodE {R T G V} PT Q f.
Arguments idealproximity_cert_of_indistinguishability
  {R A E sa argT} arg_decode arg_read Harg Hprod ic.
```

and check each against the elaboration error rather than against `Check`, which
the ledger records as not showing which arguments are implicit.
