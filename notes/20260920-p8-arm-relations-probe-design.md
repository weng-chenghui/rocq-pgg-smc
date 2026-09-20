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

## Results of the probe and of the two audits (2026-09-20)

Probe: `notes/probes/2026-09-20-p8-arm-relations/` (`LEDGER.md`), all twelve rows
compiled, recompiled from source by the main session, three classical axioms.
Audits: `audit-soundness.md` (NO-GO, no false statement, no new axiom; two wrong
conclusions in the ledger and four over-claiming sentences) and
`audit-naming.md` (NO-GO under the probe's names, eleven MUST). Every finding
below is ACCEPTED and changes this spec; the landing follows this section, not
the ledger rows above.

Changes to the claims.

1. B1's hypothesis as first written does not typecheck (`ex_inputT E` is a bare
   `Type`). It is stated on a finite reading of the sample point:
   `argT : finType`, `arg_read : sa_sampleT sa -> argT`,
   `arg_decode : argT -> ex_inputT E`, `Harg : sa_arg u = arg_decode (arg_read u)`,
   and the product hypothesis with its two factors NAMED, not quantified:
   `fdistmap (fun u => (arg_read u, sa_cut u)) (sa_sampleP sa)
    = fdistmap arg_read (sa_sampleP sa) \`x sa_cut_dist sa`. `Parg` and `rho` stop
   being variables (naming audit, section structure; soundness U8).
2. The construction takes the certificate `ic` itself; the ideal law is
   `ic_ideal ic` and the constancy is `ic_const ic` (soundness U4). The
   threshold premise that the closeness field discards is dropped (U9).
3. A4 needs no premise: `profile_k` is a successor at every algebra
   (`reconstruct/pgg_sharing_framework.v`), so `0 < profile_k` is proved inside
   (U2). Two is attained by the same certificate; the landing states it (U3).
4. A5 with a parameter `Q` and a proof of `Q` is A4 restated (U1, naming V10).
   Landed: the parameter-free `~ forall cert, IdealProximityPropAt cert c` for
   `c < 2`, and the one premise-shaped corollary whose premise is the
   input-indistinguishability proposition.
5. B5's strength is the fineness of `arg_read`: at `argT := unit` with a constant
   run argument it is true and says nothing. The statement comment says so, and
   the law-level fact `fdistmap arg_read (sa_sampleP sa)` is the secret's law on
   both sides is landed beside it (U6, U7).
6. Departure 6 of the ledger is withdrawn (U5b): at the five-card one-cut model
   the number is whichever epsilon the chosen input-indistinguishability
   certificate carries; over `kim_biased_cert_exact` it is one fiftieth, equal
   to the landed proximity certificate's, and over `kim_biased_cert` it is
   sqrt 5 / 80. The header of the instance file says what the file proves (U5a).
7. Not landed: the lemma restating `cert_eps`'s definition under a name that
   says "halves" (V18; if wanted, `cert_eps_dbl` beside `cert_eps`), the
   double-negation mutation (V17), `Search` and `Print Assumptions` commands
   (V23, V24), the unused `erefl` lemma.
8. Sentences that must not land as written: "any premise whatever" (U10), "the
   premise is discharged by the certificate" (U11, V11), a recorded `Fail` read
   as an impossibility (U12), "the sharper of the two numbers" (U13, V19: the
   two numbers bound different quantities), the ideal adapter "leaks nothing by
   construction" (V20).

Names and placement: the final name list and the placement table of
`audit-naming.md`, with two amendments. First, no name and no sentence uses the
word the owner barred on 2026-09-20 for a constructor of `SecurityPort`; the
home file is `manifest/pgg_tableau_port_relations.v` after the rename of
tracker step 2.6f, and P8 lands after that rename. Second, the value judgement
"degenerate" is replaced by what the certificate is: its two secrets are the
constants true and false (V7). `var_dist_self` exists in
`legacy/security/pgg_uniform_security.v` in the same namespace (V1): the landing
moves that lemma to `lib/var_dist_supp.v` and does not restate it, if the
legacy file's importers allow; otherwise it lands under `var_dist_xx` and the
collision is reported.
