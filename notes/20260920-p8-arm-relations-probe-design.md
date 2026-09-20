# P8, the two parts left uncompiled: spec for a probe (2026-09-20)

Tracker step 3.4. Parent spec: `notes/20260919-tableau-three-extensions-probe-design.md`,
section "What the probe found", item 3. Production home of what is already
compiled: `manifest/pgg_tableau_arm_relations.v` (`idealproximity_prop_at2`,
`indistinguishability_prop_cert_free`, `idealproximity_reading_le`).

## The problem

A reader of two published programs over one model, one through the
input-indistinguishability arm and one through the proximity arm, asks how the
two numbers relate. Two things were argued in the parent spec and never
compiled.

A. That no implication into the proximity proposition holds uniformly in the
   proximity certificate at a number below two. The proximity proposition
   mentions its certificate (the ideal adapter, the ideal's witness, the actual
   model's secret), and those are terms an instance chooses.
B. The statement the parent spec intended by "the relation to the other arm":
   the proximity proposition derived from an input-indistinguishability
   certificate's own fields, when the model draws its cut independently of its
   run argument.

## Pinned carrier

`R : realType`, `A : PGGAlgebraic`, `E : ExecutionParams A`,
`sa : SampleAdapter R (instance_exec E)`: the weakest structure the framework's
own arm definitions quantify over (`manifest/pgg_tableau.v`,
`IdealProximityCert`, `IdealProximityPropAt`, `IndistinguishabilityCert`). No
instance is fixed; the vacuity probes instantiate at instances.

## Claim ledger

| id | Claim | Passing means |
|---|---|---|
| A1 | Two laws on a finite carrier with disjoint supports are at `var_dist` exactly two (the sum of absolute differences; the literature's total variation would be one). | A `Qed`'d lemma over an arbitrary `finType`, stated with a disjointness hypothesis of the form `forall a, P a = 0 \/ Q a = 0` or by a separating predicate; mutation: drop the hypothesis, the proof must fail. |
| A2 | A constant random variable is independent of every random variable. | Found in infotheo or proved; used at the carrier of `ew_indep`. |
| A3 | Over every model `sa` there is a proximity certificate `pc` (ideal `sa` itself, witness secret the constant `true`, the actual model's secret the constant `false`, number two, closeness by `var_dist_le2`). | A `Definition` that typechecks at the pinned carrier with no hypothesis on `sa`. |
| A4 | Headline A: if some coalition is below the threshold (`0 < profile_k (instance_profile A)`), then `forall c, c < 2 -> ~ IdealProximityPropAt pc c`. | `Qed`, `Print Assumptions` classical axioms only. Mutation: with both secrets the same constant the statement must fail to prove (the distance is then zero). |
| A5 | Consequence, as a statement and not only prose: for every proposition `Q` that holds of `sa` (in particular `IndistinguishabilityPropAt ic c0` at any `ic`, `c0`), `Q -> forall pc', IdealProximityPropAt pc' c` is false for every `c < 2`. | One corollary, from A4. |
| B1 | Hypothesis of independence, stated on the model and not on its sample space: `fdistmap (fun u => (sa_arg sa u, sa_cut sa u)) (sa_sampleP sa) = P \`x rho`. Under it `sa_cut_dist sa = rho`. | `Qed`. |
| B2 | The ideal adapter: sample space `ex_inputT E * pgg_gT _`, law ``P `x rho0``, argument `fst`, cut `snd`. Its exact witness with secret `fst`, from the constancy `forall C below the threshold, forall x x', fdistmap (static_coalition_obs C x) rho0 = fdistmap (static_coalition_obs C x') rho0`. | A `Definition` of an `ExactWitness`; the independence proof `Qed`. Check that `ep_inputT (instance_exec E)` and `ex_inputT E` agree by conversion at the pinned carrier; if not, state which one the adapter takes. |
| B3 | Closeness by data processing: the joint law of (static reading, run argument) under the model and under the ideal adapter differ by at most `var_dist rho rho0`. | `Qed`, from B1, `var_dist_prodR`, `var_dist_fdistmap` (or the lemmas of `security/var_dist_joint_law.v`). |
| B4 | The certificate: from `ic : IndistinguishabilityCert sa` and B1's hypothesis, an `IdealProximityCert sa` with `ipc_eps := sw_bound_eps (ic_b ic)`, ideal from `ic_ideal ic`, witness from `ic_const ic`. | A `Definition`; `ic_Hd` and `ic_close` are what give `var_dist rho (ic_ideal ic) <= sw_bound_eps (ic_b ic)` once `sa_cut_dist sa = rho`. |
| B5 | Headline B: `IdealProximityPropAt (that certificate) (sw_bound_eps (ic_b ic))`, by the framework's own tail (`idealproximity_tail` or what `certify_idealproximity` uses). The proximity number is the certificate's epsilon once; the input-indistinguishability proposition of the same certificate is at the epsilon added to itself. | `Qed`, `Print Assumptions` classical axioms only. |
| B6 | Vacuity: B1's hypothesis is satisfiable at production models. | The hypothesis proved at the PGL(2,7) word model and at the five-card one-cut model (where the landed proximity certificates were built by hand), and the numbers compared with the landed ones (2^-40; one fiftieth against `kim_biased_cert`'s own epsilon). If an instance's adapter is not of that form, say which and why. |
| B7 | Tautology probe: B5 is not closed by conversion (`Fail` with the error read). | recorded. |

## Soundness invariants

- No new axiom and no assumed constant. `Print Assumptions` of A4, A5, B5: the
  three classical axioms the tree already uses, nothing else.
- Scope, to be written in the statement comments. A4 refutes a universal over
  certificates; it says nothing about a given, meaningful certificate. B5 is
  about static readings only through what the tail already does; it is
  average-case over the prior `P`, single run. `var_dist` is the sum of
  absolute differences: an advantage is at most half of any number here.
- B1 is a hypothesis on the model. A model whose cut depends on its run
  argument is outside B.
- Cited library objects, each to be USED at the pinned carrier by the probe:
  `var_dist_le2`, `var_dist_prodR`, `var_dist_fdistmap`, `fdistmap_comp`,
  infotheo's independence `_|_` and its product characterisation,
  `idealproximity_tail`.

## Procedure

Probe directory `notes/probes/2026-09-20-p8-arm-relations/`, files
`p8a_degenerate_certificate.v`, `p8b_proximity_from_indistinguishability.v`,
`p8_decomposition.v` (headlines from `Admitted` supporting statements, the one
place `Admitted` may appear), compiled single-file with the production load
path. Two audits (soundness, naming) before anything is landed. Landing home:
`manifest/pgg_tableau_arm_relations.v` for A3 to A5 and B1 to B5, a `lib/` or
`security/` file for A1 (decided by what A1's proof imports).
