# Adversarial soundness audit of the P8 landing (2026-09-20)

Working tree on top of `ef190d4`; the landing is uncommitted (`git diff HEAD`
plus the new `lib/fdist_prod_cond.v`). Read-only audit: no repository file was
edited except this report. Scratch files and two probe compiles under
`…/scratchpad/p8_landing_audit/`.

## Verdict

**NO-GO as it stands. GO after W1, W3 and W4 are fixed** (three comment edits,
in three files, one recompile each).

The kernel-checked content is clean. No false theorem, no new axiom, no
`Admitted`, no `Abort`, no existing statement or proof changed, no unused
hypothesis beyond the one the record shape forces. Every defect below is in a
comment or in a bridge that was not landed. W1 is a sentence in two production
docstrings that is false as written, which is why the verdict is NO-GO rather
than GO-with-notes.

## What was confirmed

1. **Pure addition (Q1).** `git diff HEAD -U0` removes exactly ten lines, all
   of them consecutive lines of the "Not claimed." comment paragraph of
   `manifest/pgg_tableau_security_property_relations.v`. Everything else is an
   addition: the header index blocks, two import lines
   (`From pgg_smc Require Import fdist_prod_cond var_dist_joint_law.` and
   `From pgg_reconstruct Require Import pgg_sharing_framework.`), and one
   `_CoqProject` line (`lib/fdist_prod_cond.v`, directly after
   `lib/var_dist_supp.v`). No existing statement, proof or name changed.
   Nothing else was found.

2. **Statements against the spec's results section (Q2).** Headline A is
   premise-free and parameter-free (`c < 2` is its only hypothesis; the
   threshold positivity is proved inside by `profile_k_gt0`). The
   parameter-free universal and exactly one premise-shaped corollary are
   landed; the `Q`-parametrised form is not. Section B has `Harg`, `Hprod`
   with both factors named (`fdistmap arg_read (sa_sampleP sa)` and
   `sa_cut_dist sa`), and `ic` as a variable. Headline B carries
   `instance_endpoints_stmt E` as an explicit hypothesis. This matches
   changes 1 to 7 of the spec's results section.

3. **`arg_read_distE` is a real fact, not conversion** (departure 2 stands).
   Probe `probe1.v`: `Fail Definition arg_read_distE_by_conversion … := erefl.`
   was accepted, so the term is rejected and the lemma is a genuine use of
   `fdist_prod1`.

4. **The corollary is honest about its premise** (Q2e). Its docstring says the
   premise is "a proposition `indistinguishability_tail` proves with no
   hypothesis" and that "the premise holds over every model, so what fails is
   not its strength but the quantifier over certificates in the conclusion".
   Checked against `manifest/pgg_tableau.v:757-760`:
   `indistinguishability_tail cert : IndistinguishabilityPropAt cert (cert_eps cert)`
   with no hypothesis.

5. **Section B is not vacuous** (Q3). With both factors named as the model's
   own marginals, `Hprod` says exactly that the joint law of the finite
   reading and the cut is the product of its two marginals, which is exact
   independence. It is satisfiable non-trivially: probe `probe2.v` compiled
   `hprod27_left : fdistmap fst (sa_sampleP (amf_sample pgl27_word_family R
   secretP)) = secretP`, and the matching right factor is the existing
   `pgl27_word_cut_distE` (`instances/pgl27/pgl27_exec.v:604`). The headline's
   docstring does state what happens at a constant reading: "at a one-point
   `argT` the run argument read is constant, the statement is true and it says
   nothing."

6. **The three comparisons of numbers are right (Q5).**
   `ipc_eps (pgl27_word_proximity_cert secretP) = sw_bound_eps (ic_b
   (pgl27_word_cert secretP))` is `2^-40` (`pgl27_word_proximity_cert` carries
   `sw_bound_eps (pgl27_word_marginal_bound R)` and
   `pgl27_word_proximity_cert_epsE` gives `2%:R^-40`), and the docstring says
   `2^-40`. At five-card, `kim_biased_marginal_bound_exact` carries `1 / 50`
   and `kim_biased_proximity_cert` carries `1 / 50`, so the `erefl` equality
   and its "one fiftieth, the exact one-cut distance" are right;
   `kim_biased_epsE` gives `sw_bound_eps (kim_biased_marginal_bound R) =
   Num.sqrt 5%:R * (1 / 80)`, and `1/50 = 0.02 <= sqrt 5 / 80 ≈ 0.02795`, so
   the `<=` direction is right. The claim "the two certificates stand over one
   model and name one ideal cut law" checks out: both `kim_biased_cert` and
   `kim_biased_cert_exact` take `amf_sample kim_biased_family R idx` and
   `sa_cut_dist (five_card_sample R)`.

7. **`Arguments` and the fidelity file (Q6).** Nine `Arguments` lines, each
   exercised by an application at `landing_fidelity.v:147-158` (elaborated
   `Definition chk_*`, not `Check`, as decision 7 asks). The file carries 31
   `Check`s against 31 landed declarations. `landing_fidelity.out` contains no
   error and no warning, and all four `Print Assumptions` report exactly
   `propositional_extensionality`, `functional_extensionality_dep` and
   `constructive_indefinite_description`.

8. **Proof hygiene (Q7).** `Harg` and `Hprod` are both used in
   `var_dist_joint_reading_arg_le`. The four `exact: erefl` lemmas are honest:
   each pins a definitional coincidence between two differently named terms
   that a reader cannot see, and none is presented as more. The
   `Set Implicit Arguments` discharge hazard is handled and demonstrated.

## Findings

| id | class | file:line | finding | what to change |
|---|---|---|---|---|
| W1 | MUST | `instances/pgl27/pgl27_models.v:445-448`; `instances/kim2025/five_card_models.v:457-460` | Both docstrings say of the landed product equation: "It is the hypothesis a construction of ideal-proximity evidence from an input-indistinguishability certificate places on a model, so this model is one such a construction applies to." False as written. The hypothesis section B places is `Hprod`, whose factors are `fdistmap arg_read (sa_sampleP sa)` and `sa_cut_dist sa`; the landed lemmas name `secretP` and `rho_word R` (pgl27) and `fdist_uniform card_bool2` and `fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (kim_weight_dist …)` (five-card). Evidence: probe `probe1.v`, `Fail Definition hprod27_by_landed : hprod27_stmt := @pgl27_word_arg_cut_prodE R secretP.` was accepted, so the two statements are not even convertible; and `pgl27_word_cut_distE` (`instances/pgl27/pgl27_exec.v:604`) is a `rewrite`-proved lemma, not `erefl`. | Replace the second sentence with what the lemma is: "The construction of ideal-proximity evidence from an input-indistinguishability certificate asks for that joint law as the product of its own two marginals; the first marginal of this product is the prior by `fdist_prod1` and the second is the cut law by `pgl27_word_cut_distE`." (five-card: name its own cut-law lemma.) Or land the bridge of W2 and point the sentence at it. |
| W2 | SHOULD | `notes/probes/2026-09-20-p8-arm-relations/LANDING.md:370-372`; spec rows B1, B6 | LANDING says "the four instance facts discharge the product hypothesis and the run-argument reading there". The reading half is discharged (`sa_arg u ≡ u.1` and `sa_arg u ≡ five_card_sample_arg u` by `erefl`), the product half is not. Spec row B1's passing criterion includes "Under it `sa_cut_dist sa = rho`", and that derivation is not landed. Departure 1 drops `sa_cut_dist_of_prodE` because it is a tautology inside section B, which is correct there, but it is exactly the step the instances need, so dropping it left B6 half open. | Either land one lemma per instance at `Hprod`'s exact shape (probe `probe2.v` shows the pgl27 one is four tactic lines over `fdistmap_comp`, `fdist_prod1` and `pgl27_word_cut_distE`), or strike the sentence from LANDING and say the bridge is the two named marginal steps and is not landed. |
| W3 | SHOULD | `lib/var_dist_supp.v:72-75` | `var_dist_xx`'s docstring says "a number a certificate publishes lies between this value and two". False: a certificate's published number is a field of type `R`; its closeness field forces only `0 <= ipc_eps`, and nothing bounds it above by two. What lies in `[0, 2]` is the distance, by `var_dist_xx` below and `var_dist_le2` above. Type-honest phrasing: a number is not a distance. | "It is the zero end of the scale `var_dist_le2` closes above: the distance a certificate's closeness field bounds lies between this value and two, and a number at or above two constrains no coalition." (The second clause is checked against `idealproximity_prop_at2`, which holds of every proximity certificate at two.) |
| W4 | SHOULD | `lib/fdist_prod_cond.v:7-9` | The file header states a biconditional: a model "tells an observer nothing about the first coordinate **exactly when** the reading's conditional law does not move with that coordinate." Only one direction is proved, and the converse is false at the file's own constancy, which is `forall x x'` and so also constrains points the first coordinate's law gives no mass; a product joint law constrains the conditional law only on the support. | Drop "exactly": "…tells an observer nothing about the first coordinate when the reading's conditional law does not move with that coordinate." The following sentence, "states the direction a privacy argument uses", then reads correctly. |
| W5 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:63-70` | The rewritten "Not claimed." paragraph is true sentence by sentence and does keep both exclusions the plan's decision 10 asks for (no implication at a given, instance-chosen certificate; nothing for a model whose cut depends on its run argument). What it no longer says, and what a reader now needs, is that the construction is not run end to end at any production model, while the two instance docstrings say "this model is one such a construction applies to". LANDING states the omission ("The generic construction is not instantiated end to end at either production instance"); the production header does not. | Add one sentence: "No instance of the construction at a production model: the instance files record the product form of a model's joint law and the number a construction would carry, not a built certificate." |
| W6 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:54-61` | Header paragraph two states only the independence hypothesis. It omits `Harg`, which requires the model's run argument to factor through a finite reading, and omits that the strength of the conclusion is the fineness of that reading. The declaration docstring at :542-550 says both; the header, which is what a reader meets first, says neither. | Add after "…and not a theorem about it": "The construction reads the run argument through a finite reading of the sample point, and the strength of the conclusion is the fineness of that reading." |
| W7 | NOTE | `manifest/pgg_tableau_security_property_relations.v:507-521` | `idealproximity_close_of_indistinguishability` takes `(#|C| < profile_k (instance_profile A))%N` and opens with `move=> _`. The premise is unused; it is there because the certificate's closeness field has that shape. The sibling `var_dist_joint_reading_arg_le` docstring does say "The threshold plays no part here"; this one does not, so the two neighbouring statements read as if one used the threshold and the other did not. | Add: "The threshold premise is the shape the certificate's closeness field asks for; the bound does not use it." |
| W8 | NOTE | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1282-1292` | `kim_biased_proximity_eps_le_sw_bound` reproves from scratch (a fresh `2%:R <= Num.sqrt 5%:R` step and `lra`) a fact the same file already carries at :605-606 as `kim_biased_exact_le_eps : 1 / 50 <= sw_bound_eps (kim_biased_marginal_bound R)`. Both sides are convertible: `ipc_eps (kim_biased_proximity_cert R idx)` is `1 / 50` by `erefl` (:1018-1020) and `ic_b (kim_biased_cert R idx)` is `kim_biased_marginal_bound R` by the definition at :642-650. | Try `Proof. exact: kim_biased_exact_le_eps. Qed.` and, if it closes, say in the docstring that the number relation is that lemma read at the two certificates. Verify before applying. |
| W9 | NOTE | `notes/probes/2026-09-20-p8-arm-relations/LANDING.md:312-313` | "all thirty-two landed declarations". The count is 31: 3 in `var_dist_supp.v`, 5 in `fdist_prod_cond.v`, 1 in `var_dist_joint_law.v`, 6 in section A, 9 in section B, 7 at the instances. `landing_fidelity.v` has exactly 31 `Check`s, so the file is right and the sentence is off by one (the `Fail Definition` is not a declaration). | Write thirty-one. |
| W10 | NOTE | `notes/probes/2026-09-20-p8-arm-relations/landing_fidelity.v:103, 105, 162, 188, 221` | Five landed `Definition`s are ascribed only at their record type (`ExactWitness sa`, `IdealProximityCert sa`, `SampleAdapter R (instance_exec E)`). Their field values are what the docstrings claim and what a reader would want pinned: the two constant secrets and the number two for `idealproximity_cert_cst_secrets_true_false`, the product law for `ideal_prod_adapter`, and `sw_bound_eps (ic_b ic)` for `idealproximity_cert_of_indistinguishability`. `IdealProximityPropAt` takes its number as a parameter, so headline B does not pin the built certificate's own `ipc_eps` either. | Add projection checks, for instance `Check (erefl : ipc_eps (@idealproximity_cert_cst_secrets_true_false R A E sa) = 2%:R)` and `Check (erefl : ipc_eps (idealproximity_cert_of_indistinguishability Harg Hprod ic) = sw_bound_eps (ic_b ic))`. |
| W11 | NOTE | `lib/var_dist_supp.v:76-78` | `var_dist_xx` has no consumer anywhere in production (it appears only in its own file and in notes). What it was landed to serve, `var_dist_xx_le0` and the second constant-secret certificate, was deliberately not landed (LANDING departure 3). `legacy/security/pgg_uniform_security.v:86` also declares `var_dist_self : var_dist P P = 0` in the same `pgg_smc` namespace, so the tree now proves the same fact twice; the plan's decision 2 accepted that, so this is recorded and not raised as a defect. | Under "keep only claimed or premise", either land the consumer or drop `var_dist_xx` and let `var_dist_self` serve. Owner's call. |
| W12 | NOTE | `manifest/pgg_tableau_security_property_relations.v:471-474` | `arg_read_distE`'s docstring says "the number below measures the coupling of that secret with a coalition's reading alone". The statement below is a `<=`, so it bounds rather than measures. Separately, "the actual model's secret" names no field of `sa`; it is the secret this landing's certificate gives `sa`. | "…and the number below bounds the coupling of that secret with a coalition's reading." For the second point, "the secret the certificate below gives the actual model" is accurate. |
| W13 | NOTE | `manifest/pgg_tableau_security_property_relations.v:73-85, 95-113` | The header indexes 3 of the 5 new definitions and 6 of the 10 new lemmas. `exact_witness_cst_true`, `exact_witness_ideal_prod`, `ideal_prod_reading_arg_prodE`, `ideal_prod_reading_indep_arg`, `var_dist_joint_reading_arg_le` and `idealproximity_close_of_indistinguishability` have no entry, while the other eight landed files index every new declaration. | Add the six entries, or say in the header that the index lists the results and not every step. |

## Probe record

`/private/tmp/…/scratchpad/p8_landing_audit/`:

- `probe1.v` — compiled to the first deliberate failure. Two `Fail` commands
  were accepted, establishing (a) `arg_read_distE` is not closed by `erefl`,
  and (b) `pgl27_word_arg_cut_prodE` does not have `Hprod`'s type.
- `probe2.v` — `hprod27_left` compiled, establishing that `Hprod`'s left
  factor at the pgl27 word model is `secretP` and needs `fdistmap_comp` and
  `fdist_prod1` beyond the landed lemma. `hprod27_right` was left unfinished
  on a wrong library name of mine (`fdist_prod2`); the production lemma
  `pgl27_word_cut_distE` already gives it.

No production file was compiled, edited or deleted by this audit.
