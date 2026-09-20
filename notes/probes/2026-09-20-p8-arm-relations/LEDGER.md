# P8 arm relations: probe ledger (2026-09-20)

Spec: `notes/20260920-p8-arm-relations-probe-design.md`. Probe directory
`notes/probes/2026-09-20-p8-arm-relations/`, compiled single-file with the
production load path plus `-Q notes/probes/2026-09-20-p8-arm-relations p8probe`
first, through the single-Rocq lock wrapper. No production file was edited.

Every row is GO. Two of the spec's statements did not typecheck as written and
were reformulated; one of the spec's numeric expectations was wrong. Both are
recorded below.

## The flow, as a program

```
-- Arm A (refutation). Objects: laws on {ffun ..} * bool.
start   sa , cert := degenerate_proximity_cert sa            // distance: 0
step    ideal := sa                    (object, no hypothesis) // 0
step    ideal secret := const true  by inde_RV_cst  (A2)       // 0
step    model secret := const false    (object, the disagreement) // 0
eval    C := set0                   by cards0 < profile_k       // 0
obs     supports disjoint           by fdistmap_neq0_codom      // 0
term    var_dist = 2                by var_dist_disjoint_supp_eq2 (A1) // 2
concl   ~ (.. <= c), c < 2           by le_lt_trans, ltxx        // 2, refutes
-- Arm B (construction). Objects: joint laws of (reading, run argument).
start   sa , ic : IndistinguishabilityCert sa                  // loss: 0
obs     cut law = rho               by fdist_prod_snd (B1)     // 0
step    ideal := (Parg `x rho0)     by MkSampleAdapter (B2)    // 0
step    ideal witness               by ic_const, fdistmap_pair_arg_prodE (B2) // 0
hop     (Parg`x rho) -> (Parg`x rho0) by var_dist_prodR (B3)   // var_dist rho rho0
obs     read as (reading, argument) by var_dist_fdistmap (B3)  // var_dist rho rho0
eval    var_dist rho rho0 <= eps    by ic_Hd, ic_close (B4)    // sw_bound_eps (ic_b ic)
term    IdealProximityPropAt        by idealproximity_tail (B5) // sw_bound_eps (ic_b ic)
```

Outside the flow: A1 and `var_dist_le2` (unconditional facts about the scale);
the endpoint equation `instance_endpoints_stmt E`, which enters B5 by
pre-composition through the interface `sa_coalition_viewE`; the instance rows
B6, which enter through `fdistmap_prodr`.

Monad verdict: a category, not a monad. The connecting operation is
transitivity of `var_dist` under a common reading, and the accumulated value is
a monoid `(R, +, 0)` with the triangle inequality, but there is no unit and
bind over a bound-carrying value here, only composable hops whose endpoints
must agree. A DSL would not remove an expressiveness problem at this size: the
arm-B flow is four hops long and the existing `idealproximity_tail` already
packages its terminal.

## Ledger

| id | verdict | file : name | compile |
|---|---|---|---|
| A1 | GO | `p8a_degenerate_certificate.v : var_dist_disjoint_supp_eq2` | 4.4 s |
| A2 | GO | `p8a_degenerate_certificate.v : inde_RV_cst` | (same file) |
| A3 | GO | `p8a_degenerate_certificate.v : const_true_witness`, `degenerate_proximity_cert` | (same file) |
| A4 | GO | `p8a_degenerate_certificate.v : degenerate_proximity_prop_below2_false` | (same file) |
| A5 | GO | `p8a_degenerate_certificate.v : proximity_below2_uniform_in_cert_false`, `indistinguishability_prop_proximity_below2_false` | (same file) |
| B1 | GO, reformulated | `p8b_proximity_from_indistinguishability.v : sa_cut_dist_of_prodE` | 3.9 s |
| B2 | GO, reformulated | same file : `ideal_product_adapter`, `ideal_product_joint_prodE`, `ideal_product_reading_indep`, `ideal_product_witness` | (same file) |
| B3 | GO | same file : `joint_reading_arg_var_dist_le` | (same file) |
| B4 | GO | same file : `proximity_close_of_indistinguishability`, `proximity_cert_of_indistinguishability` | (same file) |
| B5 | GO | same file : `proximity_prop_of_indistinguishability` | (same file) |
| B6 | GO, one number differs | `p8b_instances.v` | 4.7 s |
| B7 | GO | same file as B5 : the `Fail Definition ..._by_conversion` | (same file) |

Mutation checks, all GO:

| what | file : name | compile |
|---|---|---|
| A1 without disjointness | `p8a_mut_disjointness_needed.v : var_dist_eq2_unconditional_false` | 3.6 s |
| A4 with both secrets one constant | `p8a_degenerate_certificate.v : proximity_below2_false_needs_distinct_secrets` | in A's file |
| B3 without B1's product hypothesis | `p8b_mut_product_needed.v : joint_le_cut_without_product_false` | 3.6 s |

Decomposition: `p8_decomposition.v`, 3.7 s, three `Admitted` supports and two
`Qed` headlines. Name probes: `p8_names.v` 4.5 s, `p8_names2.v` 4.0 s.

## Statements, verbatim

**A1.**
```coq
Lemma var_dist_disjoint_supp_eq2 (R : realType) (A : finType)
    (P Q : R.-fdist A) :
  (forall a : A, P a = 0 \/ Q a = 0) -> var_dist P Q = 2%:R.
```

**A2.** Not found in infotheo. `Search "inde_RV" inside proba.` returns only
`inde_RV`, `cinde_RV`, `inde_RV_sym`, so it is proved here.
```coq
Lemma inde_RV_cst (R : realType) (U : finType) (P : R.-fdist U)
    (TA TB : finType) (X : {RV P -> TA}) (c : TB) :
  P |= X _|_ ((fun=> c) : {RV P -> TB}).
```

**A3.** Section variables `R : realType`, `A : PGGAlgebraic`,
`E : ExecutionParams A`, `sa : SampleAdapter R (instance_exec E)`.
```coq
Definition const_true_witness : ExactWitness sa :=
  @MkExactWitness R A E sa bool ((fun=> true) : {RV (sa_sampleP sa) -> bool})
    (fun C _ =>
       @inde_RV_cst R (sa_sampleT sa) (sa_sampleP sa) _ bool
         (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))
         true).

Definition degenerate_proximity_cert : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa sa const_true_witness
    ((fun=> false) : {RV (sa_sampleP sa) -> bool}) 2%:R
    (fun C _ => var_dist_le2 _ _).
```

**A4.**
```coq
Lemma degenerate_proximity_prop_below2_false
    (Hk : (0 < profile_k (instance_profile A))%N) (c : R) :
  c < 2%:R -> ~ IdealProximityPropAt degenerate_proximity_cert c.
```

**A5.**
```coq
Lemma proximity_below2_uniform_in_cert_false
    (Hk : (0 < profile_k (instance_profile A))%N) (Q : Prop) (c : R) :
  Q -> c < 2%:R ->
  ~ (Q -> forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).

Corollary indistinguishability_prop_proximity_below2_false
    (Hk : (0 < profile_k (instance_profile A))%N)
    (ic : IndistinguishabilityCert sa) (c : R) :
  c < 2%:R ->
  ~ (IndistinguishabilityPropAt ic (cert_eps ic) ->
     forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
```

**B1.** Section context, added to A's four variables:
```coq
Variable argT : finType.
Variable arg_decode : argT -> ex_inputT E.
Variable arg_read : sa_sampleT sa -> argT.
Hypothesis Harg : forall u : sa_sampleT sa,
  sa.(sa_arg) u = arg_decode (arg_read u).
Variable Parg : R.-fdist argT.
Variable rho : R.-fdist (pgg_gT (mp_M (instance_profile A))).
Hypothesis Hprod :
  fdistmap (fun u => (arg_read u, sa.(sa_cut) u)) (sa_sampleP sa)
  = Parg `x rho.

Lemma sa_cut_dist_of_prodE : sa_cut_dist sa = rho.
```

**B2.**
```coq
Variable rho0 : R.-fdist (pgg_gT (mp_M (instance_profile A))).
Hypothesis Hconst :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (static_coalition_obs C x) rho0
      = fdistmap (static_coalition_obs C x') rho0.

Definition ideal_product_adapter : SampleAdapter R (instance_exec E) :=
  @MkSampleAdapter R (instance_profile A) (instance_exec E)
    [the finType of (argT * pgg_gT (mp_M (instance_profile A)))%type]
    (Parg `x rho0) (fun z => arg_decode z.1) (fun z => z.2).

Lemma ideal_product_reading_indep
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  sa_sampleP ideal_product_adapter
  |= ((fun z => static_coalition_obs C (ideal_product_adapter.(sa_arg) z)
                  (ideal_product_adapter.(sa_cut) z))
      : {RV (sa_sampleP ideal_product_adapter)
           -> {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                 -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}})
     _|_ ((fun z => z.1)
          : {RV (sa_sampleP ideal_product_adapter) -> argT}).

Definition ideal_product_witness : ExactWitness ideal_product_adapter :=
  @MkExactWitness R A E ideal_product_adapter argT
    ((fun z => z.1) : {RV (sa_sampleP ideal_product_adapter) -> argT})
    ideal_product_reading_indep.
```

The general fact behind the independence, proved in the same file over an
arbitrary product law, is
```coq
Lemma fdistmap_pair_arg_prodE :
  (forall x x' : T, fdistmap (f x) Q = fdistmap (f x') Q) ->
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q)
  = (fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q)) `x PT.
```

**B3.** `Hconst` is not used here; only B2's witness needs it.
```coq
Lemma joint_reading_arg_var_dist_le
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 (static_coalition_obs C (arg_decode z.1) z.2, z.1))
       (Parg `x rho0))
  <= var_dist rho rho0.
```

**B4.**
```coq
Lemma proximity_close_of_indistinguishability
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z => (static_coalition_obs C
                           (ideal_product_adapter.(sa_arg) z)
                           (ideal_product_adapter.(sa_cut) z),
                         ew_secret ideal_product_witness z))
       (sa_sampleP ideal_product_adapter))
  <= sw_bound_eps (ic_b ic).

Definition proximity_cert_of_indistinguishability
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
  : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa ideal_product_adapter ideal_product_witness
    (arg_read : {RV (sa_sampleP sa) -> argT})
    (sw_bound_eps (ic_b ic))
    (proximity_close_of_indistinguishability Hic).
```

**B5.**
```coq
Lemma proximity_prop_of_indistinguishability
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
    (Hendp : instance_endpoints_stmt E) :
  IdealProximityPropAt (proximity_cert_of_indistinguishability Hic)
    (sw_bound_eps (ic_b ic)).
```
and the two numbers over one certificate:
```coq
Lemma proximity_eps_halves_cert_epsE (ic : IndistinguishabilityCert sa)
    (Hic : ic_ideal ic = rho0) :
  cert_eps ic = ipc_eps (proximity_cert_of_indistinguishability Hic)
                + ipc_eps (proximity_cert_of_indistinguishability Hic).
Proof. exact: erefl. Qed.
```

**B6.** `p8b_instances.v`.
```coq
Lemma pgl27_word_arg_cut_prod (R : realType) (secretP : R.-fdist bool) :
  exists (Parg : R.-fdist bool)
         (rho : R.-fdist (pgg_gT (mp_M (instance_profile pgl27_algebra)))),
    fdistmap (fun u => (@sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u,
                        @sa_cut _ _ _ (amf_sample pgl27_word_family R secretP) u))
      (sa_sampleP (amf_sample pgl27_word_family R secretP))
    = Parg `x rho.
Proof. by do 2 eexists; exact: fdistmap_prodr. Qed.

Lemma kim_biased_arg_cut_prod (R : realType) (idx : unit) :
  exists (Parg : R.-fdist (bool * bool))
         (rho : R.-fdist (pgg_gT (mp_M (instance_profile five_card_algebra)))),
    fdistmap (fun u => (@sa_arg _ _ _ (amf_sample kim_biased_family R idx) u,
                        @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
      (sa_sampleP (amf_sample kim_biased_family R idx))
    = Parg `x rho.
```
with the decoding checks `pgl27_word_arg_readE` (`sa_arg` is `fst`) and
`kim_biased_arg_readE` (`sa_arg` is `five_card_sample_arg`), both `exact: erefl`.

Numbers:
```coq
Lemma pgl27_word_proximity_eps_genericE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP)
  = sw_bound_eps (ic_b (pgl27_word_cert secretP)).
Proof. exact: erefl. Qed.

Lemma kim_biased_proximity_epsE (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50 :> R.
Lemma kim_biased_indistinguishability_epsE (R : realType) (idx : unit) :
  sw_bound_eps (ic_b (kim_biased_cert R idx)) = Num.sqrt 5%:R * (1 / 80) :> R.
Lemma kim_biased_proximity_eps_generic_le (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx)
  <= sw_bound_eps (ic_b (kim_biased_cert R idx)).
```

**B7.** The guard, and the error read with the guard removed:
```coq
Fail Definition proximity_prop_of_indistinguishability_by_conversion
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
  : IdealProximityPropAt (proximity_cert_of_indistinguishability Hic)
      (sw_bound_eps (ic_b ic))
  := ltac:(by []).
```
`rocq compile` prints nothing for a passing `Fail`, so the guard was deleted
for one compile and the message read directly:

> File "./notes/probes/2026-09-20-p8-arm-relations/p8b_proximity_from_indistinguishability.v", line 325, characters 11-16:
> Error: No applicable tactic.

Characters 11 to 16 are `by []`. This is the ssreflect closing tactic failing
on the inequality, not an unknown reference and not a parse error.

## Mutation checks, verbatim

```coq
Lemma var_dist_eq2_unconditional_false (R : realType) :
  ~ (forall (A : finType) (P Q : R.-fdist A), var_dist P Q = 2%:R).

Lemma proximity_below2_false_needs_distinct_secrets :
  ~ (forall c : R, c < 2%:R ->
       ~ IdealProximityPropAt same_secret_proximity_cert c).

Lemma joint_le_cut_without_product_false :
  ~ (forall (T G : finType) (P Q : R.-fdist (T * G)),
       fdistmap fst P = fdistmap fst Q ->
       fdistmap snd P = fdistmap snd Q ->
       var_dist P Q <= var_dist (fdistmap snd P) (fdistmap snd Q)).
```
The third is witnessed by the diagonal and the antidiagonal law on the two
booleans: one pair of marginals, disjoint supports, so the left side is two by
A1 and the right side is zero.

## Print Assumptions

`degenerate_proximity_prop_below2_false` (A4),
`proximity_below2_uniform_in_cert_false` and
`indistinguishability_prop_proximity_below2_false` (A5), and
`proximity_prop_of_indistinguishability` (B5) each print exactly:

```
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

These are the three classical axioms `boolp` already puts on every statement of
this tree. No new axiom, no assumed constant.

## Departures from the spec

1. **B1's hypothesis does not typecheck as written.** The spec writes
   `fdistmap (fun u => (sa_arg sa u, sa_cut sa u)) (sa_sampleP sa) = P `x rho`.
   `ex_inputT E : Type` is a bare Type (`protocol/pgg_instance.v:284`), and
   `fdistmap` requires a finite codomain, so the pair has no law. The
   hypothesis is stated instead on a finite reading `arg_read` of the sample
   point together with a decoding `arg_decode` into `ex_inputT E` that agrees
   with `sa_arg`. This is weaker for a user of the lemma than any form that
   would demand `ex_inputT E` be finite, and both production models satisfy it
   with `arg_decode` the identity.
2. **B2's ideal adapter's sample space does not typecheck as written.** The
   spec asks for `ex_inputT E * pgg_gT _`; `sa_sampleT : finType`, so the
   adapter's space is `argT * pgg_gT _`.
3. **The conversion B2 asked to check holds.** `ex_inputT E` and
   `ep_inputT (instance_exec E)` agree by `erefl`, verified in `p8_names.v`.
4. **B5 needs the endpoint equation.** `idealproximity_tail` takes two link
   hypotheses, and at an arbitrary adapter they are not automatic. B5 therefore
   takes `instance_endpoints_stmt E` and derives both by `sa_coalition_viewE`,
   exactly as `certify_idealproximity` does inside the framework. The spec did
   not name this premise.
5. **B3 does not use the constancy field.** Only B2's witness does. The spec
   grouped them.
6. **B6's five-card number is not the one the spec expected.** The spec says to
   compare "one fiftieth against `kim_biased_cert`'s own epsilon". Those two are
   different numbers: `kim_biased_cert`'s `sw_bound_eps` is
   `Num.sqrt 5%:R * (1 / 80)`, about 0.02795, while the hand-built proximity
   certificate carries `1 / 50`, exactly 0.02. The hand-built certificate is the
   sharper of the two, because `kim_biased_proximity_close` rests on
   `kim_biased_cut_mixing_exact` and not on the spectral marginal bound. The
   equality holds at PGL(2,7), where both numbers are
   `sw_bound_eps (pgl27_word_marginal_bound R)`, two to the minus fortieth.
7. **A5 takes the premise and a proof of it.** `Q : Prop` together with `Q`,
   which is what "every proposition that holds of `sa`" means as a statement.

## Library objects used, with their file

From this tree:

- `var_dist_le2`, `fdistmap_neq0_codom`, `fdistmap_inj_uniform_id` —
  `lib/var_dist_supp.v`
- `var_dist_prodR`, `fdist_prod_snd` — `security/var_dist_joint_law.v`
- `var_dist_fdistmap` — `security/pgg_collusion_bound.v`
- `fdistmap_prodr`, `sa_coalition_viewE`, `MkSampleAdapter`, `sa_cut_dist`,
  `sa_sampleP`, `sa_sampleT`, `sa_arg`, `sa_cut` — `security/pgg_sample_adapter.v`
- `MkExactWitness`, `MkIdealProximityCert`, `IdealProximityPropAt`,
  `IndistinguishabilityPropAt`, `cert_eps`, `ic_b`, `ic_Hd`, `ic_close`,
  `ic_ideal`, `ic_const`, `ipc_eps`, `ew_secret`, `idealproximity_tail`,
  `indistinguishability_tail` — `manifest/pgg_tableau.v`
- `static_coalition_obs`, `instance_exec`, `ex_inputT`, `ex_content_obs`,
  `instance_endpoints_stmt`, `profile_k`, `instance_profile` —
  `protocol/pgg_instance.v`
- `amf_sample` — `manifest/pgg_analysis_manifest.v`
- `pgl27_algebra`, `pgl27_word_family`, `pgl27_word_cert`,
  `pgl27_word_proximity_cert`, `five_card_algebra`, `five_card_sample_arg`,
  `kim_biased_family`, `kim_biased_cert`, `kim_biased_proximity_cert`,
  `kim_biased_epsE`, `five_card_group.fc_sigma` — the two instance directories

From infotheo:

- `var_dist` (`variation_dist.v`)
- `fdistmap`, `fdistmapE`, `fdistmap_comp`, `fdist_prod1`, `fdist_prodE`,
  `fdist_ext`, `fdist_uniform`, `fdist_uniformE`, `fdist1`, `FDist.f1`,
  `FDist.ge0`, `card_bool` (`fdist.v`)
- `inde_RV`, `inde_dist_of_RV2`, `dist_of_RVE`, `pfwd1E`, `Pr_set0`, `Pr_setT`
  (`proba.v`)

From mathcomp: `reindex_onto`, `partition_big`, `big_distrr`, `big_distrl`,
`big_split`, `big1`, `eq_big`, `eq_bigl`, `eq_bigr`, `under eq_bigr`,
`xpair_eqE`, `eqVneq`, `negb_inj`, `cards0`, `set0`, `setP`, `funext`,
`ger0_norm`, `mulr2n`, `pnatr_eq0`, `ltr0n`, `sqr_sqrtr`, `sqrtr_ge0`,
`ler_pXn2r`, `ler_nat`, `natrX`, `lra`, `Order.POrderTheory.le_trans`,
`Order.POrderTheory.le_lt_trans`, `Order.POrderTheory.ltxx`.

Cited in the spec and **not** needed: `var_dist_fdistmap_pair` and
`var_dist_triangle` (`var_dist_fdistmap` with `le_trans` was enough) and
`var_dist_own_marginals`.

Proved here because no library name was found: `var_dist_self`,
`var_dist_self_le0`, `fdistmap_notin_codom0`, `inde_RV_cst`,
`var_dist_disjoint_supp_eq2`, `sum_reading_fibreE`,
`fdistmap_pair_arg_condE`, `fdistmap_reading_mixtureE`,
`fdistmap_pair_arg_prodE`. Before landing, check `var_dist_self` against
infotheo under another name.

## What misled, and will mislead the landing

- **`sa_arg` and `sa_cut` take the adapter implicitly**, because the adapter
  appears in their domain type; `sa_sampleP` and `sa_sampleT` take it
  explicitly, because it appears only in their result type. Writing
  `sa_arg M u` parses `M` as the sample point. Use `M.(sa_arg) u` or
  `@sa_arg _ _ _ M u`.
- **Section discharge under `Set Implicit Arguments` and
  `Unset Strict Implicit` makes later section variables implicit.** In
  `fdistmap_pair_arg_prodE` the discharged `Q` and `f` became implicit, so
  `lemma Parg rho0 f Hc` silently passed `rho0` where the hypothesis was
  expected and reported only "Cannot apply lemma". The `@` form with `_` for
  the finTypes fixed it. `Check @name` shows all seven arguments and hides
  which are implicit, so it does not reveal the problem; the elaboration error
  does.
- **`rocq compile` prints nothing for a passing `Fail`.** To read the message,
  delete the guard for one compile.
- **`reindex_onto`'s side condition is stated before simplification**, so the
  pair projection appears as `(a, g).1` and `/eqP ->` has nothing to rewrite.
  A `/=` in the intro pattern before the view fixes it.
- **`congr (_ * _)` closes convertible branches silently**, so the tactic after
  it can address a different goal than intended and fail with
  "No applicable tactic".
- **infotheo has no converse of `inde_dist_of_RV2`.** `dist_of_RVE`
  (`` `p_ X a = `Pr[X = a] ``) is the bridge that turns a product-of-marginals
  equation into `inde_RV`.
- **`pgl27_word_cert` has `R` implicit** (inferable from `secretP`), while
  `kim_biased_cert` has it explicit (its other argument is `unit`).
- **`pgl27_algebra` lives in `pgl27_exec.v`**, not in `pgl27_models.v`; Import
  is not transitive.

## Left open

- The generic B4 and B5 construction is not instantiated end to end at either
  production instance. B6 proves B1's hypothesis there and compares the
  numbers; wiring `rho0 := ic_ideal ic`, `Harg` and the endpoint statement at
  each instance was not attempted inside the probe's budget. Nothing found
  suggests it would fail.
- A1's landing home: its proof imports only `variation_dist`, `fdist` and
  mathcomp, so `lib/var_dist_supp.v`, beside `var_dist_le2`, is the file the
  spec's rule selects.
- Naming for the landing: `var_dist_disjoint_supp_eq2` has five lowercase
  components. `var_dist_fdistmap_supp_inj` in the same file has five as well,
  so the threshold is already exceeded in that file; the landing may prefer a
  shorter name.
