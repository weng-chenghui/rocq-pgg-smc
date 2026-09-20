# P8 landing: the relations between two security properties' propositions

Landed 2026-09-20 on `feat/tableau-extensions-probe` from
`notes/2026-09-20-221500-p8-landing-plan.md`. Every file below compiles
single-file through the lock wrapper. No `make`, no frozen module, no git
write, nothing deleted under `notes/probes/`.

## Flow program

```
A                                                              // loss (bits of slack)
  inde_RV_cst                                    lib           // 0   exact independence
  exact_witness_cst_true      <- inde_RV_cst                   // 0   witness over any model
  var_dist_le2                                   lib           // 2   the field eps := 2
  idealproximity_cert_cst_secrets_true_false                   // 2   certificate over any model
  fdistmap_notin_codom0       -> disjoint supports at C = set0 // 2
  var_dist_supp_disjoint_eq2  -> the two laws are 2 apart      // 2   attained, not bounded
  profile_k_gt0               -> set0 is below the threshold   // 2
  idealproximity_prop_cst_secrets_lt2_false                    // refutes every c < 2
  idealproximity_prop_lt2_uniform_in_cert_false                // refutes the universal
  indistinguishability_prop_idealproximity_lt2_false           // premise costs nothing

B
  Hprod                       (hypothesis on the model)        // 0
  ic_const ic                 -> fdistmap_pair_fst_prodE       // 0   ideal reading independent
  ideal_prod_reading_arg_prodE                                 // 0
  ideal_prod_reading_indep_arg -> exact_witness_ideal_prod     // 0
  arg_read_distE              <- fdist_prod1                   // 0   one secret, both sides
  Harg, Hprod                 -> one map on two products       // 0
  var_dist_fdistmap_prodR_le  -> var_dist_joint_reading_arg_le // <= var_dist cut ideal
  ic_Hd ic, ic_close ic                                        // <= sw_bound_eps (ic_b ic)
  idealproximity_close_of_indistinguishability                 // = sw_bound_eps (ic_b ic)
  idealproximity_cert_of_indistinguishability                  // eps field := that number
  idealproximity_tail + instance_endpoints_stmt E              // unchanged
  idealproximity_prop_of_indistinguishability                  // sw_bound_eps (ic_b ic), ONCE
                                                               // cert_eps is that number TWICE
```

Monad verdict: a category, not a monad. The landed lemmas compose as arrows
between laws ordered by `<=` on `var_dist`, with `var_dist_fdistmap` as the
functorial action; there is no unit/bind pair, because a certificate's number
is a field it carries and not a value a bind threads.

Interfaces every existing result enters through:

| result | file it enters from |
|---|---|
| `var_dist_le2`, `fdistmap_neq0_codom` | `lib/var_dist_supp.v` |
| `fdist_prod1`, `fdistmapE`, `fdist_prodE`, `FDist.f1` | infotheo `fdist` |
| `dist_of_RVE`, `Pr_setT`, `Pr_set0`, `pfwd1E` | infotheo `proba` |
| `var_dist_fdistmap` | `security/pgg_collusion_bound.v` |
| `var_dist_prodR` | `security/var_dist_joint_law.v` |
| `ic_b`, `ic_Hd`, `ic_ideal`, `ic_close`, `ic_const`, `cert_eps` | `manifest/pgg_tableau.v` |
| `indistinguishability_tail`, `idealproximity_tail`, `sa_coalition_viewE` | `manifest/pgg_tableau.v` |
| `profile_k`, `ts_k` | `reconstruct/pgg_sharing_framework.v` |
| `fdistmap_prodr` | `security/pgg_sample_adapter.v` |

## What landed, per file

### `lib/var_dist_supp.v` (4.1 s), three lemmas and three index entries

```coq
Lemma var_dist_xx (R : realType) (A : finType) (P : R.-fdist A) :
  var_dist P P = 0.

Lemma fdistmap_notin_codom0 (R : realType) (U B : finType) (g : U -> B)
    (P : R.-fdist U) (b : B) :
  (forall u : U, g u != b) -> fdistmap g P b = 0.

Lemma var_dist_supp_disjoint_eq2 (R : realType) (A : finType)
    (P Q : R.-fdist A) :
  (forall a : A, P a = 0 \/ Q a = 0) -> var_dist P Q = 2%:R.
```

### `lib/fdist_prod_cst_cond.v` (3.9 s), NEW, plus its `_CoqProject` line

The `_CoqProject` line `lib/fdist_prod_cst_cond.v` sits directly after
`lib/var_dist_supp.v`; nothing else in `_CoqProject` changed.

```coq
Lemma inde_RV_cst (R : realType) (U : finType) (P : R.-fdist U)
    (TA TB : finType) (X : {RV P -> TA}) (c : TB) :
  P |= X _|_ ((fun=> c) : {RV P -> TB}).

Section fdist_prod_cst_cond.
Variable R : realType.
Variables T G V : finType.
Variables (PT : R.-fdist T) (Q : R.-fdist G) (f : T -> G -> V).

Lemma sum_prod_fibreE (v : V) (x : T) :
  \sum_(z : T * G | (f z.1 z.2 == v) && (z.1 == x)) PT z.1 * Q z.2
  = PT x * fdistmap (f x) Q v.

Lemma fdistmap_pair_fst_condE (v : V) (x : T) :
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q) (v, x)
  = PT x * fdistmap (f x) Q v.

Lemma fdistmap_prod_mixtureE (v : V) :
  fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q) v
  = \sum_(x : T) PT x * fdistmap (f x) Q v.

Lemma fdistmap_pair_fst_prodE :
  (forall x x' : T, fdistmap (f x) Q = fdistmap (f x') Q) ->
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q)
  = (fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q)) `x PT.
End fdist_prod_cst_cond.
```

### `security/var_dist_joint_law.v` (4.3 s), one lemma and one index entry

```coq
Lemma var_dist_fdistmap_prodR_le (R : realType) (A B C : finType)
    (P : R.-fdist A) (Q1 Q2 : R.-fdist B) (h : A * B -> C) :
  var_dist (fdistmap h (P `x Q1)) (fdistmap h (P `x Q2)) <= var_dist Q1 Q2.
```

### `manifest/pgg_tableau_security_property_relations.v` (3.8 s)

Two import lines added (`fdist_prod_cst_cond var_dist_joint_law` from
`pgg_smc`,
`pgg_sharing_framework` from `pgg_reconstruct`); the header's index gained a
`Definitions:` block and six `Lemmas:` entries; the three paragraphs from
"Not claimed." down were rewritten per decision 10. No existing statement,
proof or name changed.

```coq
Lemma profile_k_gt0 (A : PGGAlgebraic) :
  (0 < profile_k (instance_profile A))%N.

Section idealproximity_cert_over_any_model.
Variable R : realType.  Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Definition exact_witness_cst_true : ExactWitness sa := ...
Definition idealproximity_cert_cst_secrets_true_false
  : IdealProximityCert sa := ...

Lemma idealproximity_prop_cst_secrets_lt2_false (c : R) :
  c < 2%:R ->
  ~ IdealProximityPropAt idealproximity_cert_cst_secrets_true_false c.

Lemma idealproximity_prop_lt2_uniform_in_cert_false (c : R) :
  c < 2%:R ->
  ~ (forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).

Lemma indistinguishability_prop_idealproximity_lt2_false
    (ic : IndistinguishabilityCert sa) (c : R) :
  c < 2%:R ->
  ~ (IndistinguishabilityPropAt ic (cert_eps ic) ->
     forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
End idealproximity_cert_over_any_model.
```

Section B's variables and hypotheses, exactly decision 5:

```coq
Section idealproximity_from_indistinguishability.
Variable R : realType.  Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Variable argT : finType.
Variable arg_decode : argT -> ex_inputT E.
Variable arg_read : sa_sampleT sa -> argT.
Hypothesis Harg : forall u : sa_sampleT sa,
  sa.(sa_arg) u = arg_decode (arg_read u).
Hypothesis Hprod :
  fdistmap (fun u => (arg_read u, sa.(sa_cut) u)) (sa_sampleP sa)
  = (fdistmap arg_read (sa_sampleP sa)) `x (sa_cut_dist sa).
Variable ic : IndistinguishabilityCert sa.
```

and its declarations:

```coq
Definition ideal_prod_adapter : SampleAdapter R (instance_exec E) :=
  @MkSampleAdapter R (instance_profile A) (instance_exec E)
    [the finType of (argT * pgg_gT (mp_M (instance_profile A)))%type]
    ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic))
    (fun z => arg_decode z.1) (fun z => z.2).

Lemma ideal_prod_reading_arg_prodE
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
              (static_coalition_obs C (arg_decode z.1) z.2, z.1))
    ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic))
  = (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 static_coalition_obs C (arg_decode z.1) z.2)
       ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
    `x (fdistmap arg_read (sa_sampleP sa)).

Lemma ideal_prod_reading_indep_arg
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  sa_sampleP ideal_prod_adapter
  |= ((fun z => static_coalition_obs C (ideal_prod_adapter.(sa_arg) z)
                  (ideal_prod_adapter.(sa_cut) z))
      : {RV (sa_sampleP ideal_prod_adapter)
           -> {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                 -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}})
     _|_ ((fun z => z.1)
          : {RV (sa_sampleP ideal_prod_adapter) -> argT}).

Definition exact_witness_ideal_prod : ExactWitness ideal_prod_adapter := ...

Lemma arg_read_distE :
  fdistmap (ew_secret exact_witness_ideal_prod)
    (sa_sampleP ideal_prod_adapter)
  = fdistmap arg_read (sa_sampleP sa).

Lemma var_dist_joint_reading_arg_le
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 (static_coalition_obs C (arg_decode z.1) z.2, z.1))
       ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
  <= var_dist (sa_cut_dist sa) (ic_ideal ic).

Lemma idealproximity_close_of_indistinguishability
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z => (static_coalition_obs C
                           (ideal_prod_adapter.(sa_arg) z)
                           (ideal_prod_adapter.(sa_cut) z),
                         ew_secret exact_witness_ideal_prod z))
       (sa_sampleP ideal_prod_adapter))
  <= sw_bound_eps (ic_b ic).

Definition idealproximity_cert_of_indistinguishability
  : IdealProximityCert sa := ...

Lemma idealproximity_prop_of_indistinguishability
    (Hendp : instance_endpoints_stmt E) :
  IdealProximityPropAt idealproximity_cert_of_indistinguishability
    (sw_bound_eps (ic_b ic)).

Fail Definition idealproximity_prop_of_indistinguishability_by_conversion
  : IdealProximityPropAt idealproximity_cert_of_indistinguishability
      (sw_bound_eps (ic_b ic))
  := ltac:(by []).
End idealproximity_from_indistinguishability.
```

Nine `Arguments` lines follow the section, one per landed declaration of
section B, with `{R A E sa argT}` implicit and the data and hypothesis
arguments explicit. Each is exercised by an application in the fidelity file.

### `instances/pgl27/pgl27_models.v` (3.9 s) and `instances/kim2025/five_card_models.v` (3.8 s)

Neither file gained an import; both still import no tableau, framework or
manifest module, and everything the two lemmas name was already in scope.

```coq
Lemma pgl27_word_arg_cut_prodE (R : realType) (secretP : R.-fdist bool) :
  fdistmap (fun u => (@sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u,
                      @sa_cut _ _ _ (amf_sample pgl27_word_family R secretP) u))
    (sa_sampleP (amf_sample pgl27_word_family R secretP))
  = secretP `x (rho_word R).

Lemma pgl27_word_arg_readE (R : realType) (secretP : R.-fdist bool)
    (u : bool * (200.-tuple 'I_5)) :
  @sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u = u.1.

Lemma kim_biased_arg_cut_prodE (R : realType) (idx : unit) :
  fdistmap (fun u => (@sa_arg _ _ _ (amf_sample kim_biased_family R idx) u,
                      @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
    (sa_sampleP (amf_sample kim_biased_family R idx))
  = (fdist_uniform card_bool2)
    `x (fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g)
          (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))).

Lemma kim_biased_arg_readE (R : realType) (idx : unit)
    (u : five_card_leakage.Omega) :
  @sa_arg _ _ _ (amf_sample kim_biased_family R idx) u = five_card_sample_arg u.
```

### The comparisons of numbers

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` (6.9 s):

```coq
Lemma pgl27_word_proximity_eps_sw_boundE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP)
  = sw_bound_eps (ic_b (pgl27_word_cert secretP)).
Proof. exact: erefl. Qed.
```

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` (5.9 s):

```coq
Lemma kim_biased_proximity_eps_sw_bound_exactE (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx)
  = sw_bound_eps (ic_b (kim_biased_cert_exact R idx)).
Proof. exact: erefl. Qed.

Lemma kim_biased_proximity_eps_le_sw_bound (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx)
  <= sw_bound_eps (ic_b (kim_biased_cert R idx)).
```

Each carries a header index entry.

## Fidelity check

`notes/probes/2026-09-20-p8-arm-relations/landing_fidelity.v` (4.5 s) requires
production only. It ascribes all thirty-one landed declarations at their
statements written out in full, applies each of the nine `Arguments` lines,
and prints the assumptions. Output saved as `landing_fidelity.out`.

`Print Assumptions` for `idealproximity_prop_cst_secrets_lt2_false`,
`idealproximity_prop_lt2_uniform_in_cert_false`,
`indistinguishability_prop_idealproximity_lt2_false` and
`idealproximity_prop_of_indistinguishability` each report exactly:

```
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

The same three classical axioms the probe reported. No new axiom, no
`Admitted`, no `Abort`.

## Departures from the plan, with the reason

1. **`sa_cut_dist_of_prodE` not landed.** Under decision 5 the product
   hypothesis already names `sa_cut_dist sa` as its right factor, so the
   lemma would read `sa_cut_dist sa = sa_cut_dist sa`. The order of work for
   section B does not list it.
2. **`arg_read_distE` restated.** The audit's U-J form,
   `fdistmap arg_read (sa_sampleP sa) = Parg`, is likewise vacuous once
   `Parg` is that very pushforward. It is landed as the fact decision 6
   names: the ideal model's own secret has the law the actual model's secret
   has, closed by `fdist_prod1`.
3. **The second constant-secret certificate is not landed**
   (`idealproximity_cert_cst_secrets_true_true` and its proposition at zero),
   nor `var_dist_xx_le0`, which exists only to serve it. The order of work
   for section 3 lists section A as the headline, the universal and the one
   corollary. `var_dist_xx` is landed, as the order of work for step 1 asks.
4. **The five-card equality is named `kim_biased_proximity_eps_sw_bound_exactE`**,
   not the naming audit's `kim_biased_proximity_epsE`. The tree already
   carries `kim_biased_proximity_cert_epsE : ipc_eps (kim_biased_proximity_cert
   R idx) = 1 / 50` at `five_card_tableau_analysis_bridged.v:1012`; restating
   one fiftieth would duplicate it. What the tree lacked, and what landed, is
   the identification of that number with `kim_biased_cert_exact`'s marginal
   bound.
5. **The pgl27 product factors are `secretP` and `rho_word R`**, not the raw
   `word_weighted`/`word_eval` pair `fdistmap_prodr` produces. `rho_word` is
   the law the word walk's marginal bound is stated at, the two are
   convertible, and `exact: fdistmap_prodr` closes the lemma unchanged.
6. **`inde_RV_cst` is in `lib/fdist_prod_cst_cond.v`**, not
   `lib/proba_entropy_ext.v`. This follows decision 1 of the plan, which
   overrides the naming audit's placement table on that row.

## Not landed, and why

Everything decision 9 excludes: the lemma restating `cert_eps`, the
double-negation mutation, the `Search` and `Print Assumptions` commands
inside production, the unused `erefl` lemma, and the decomposition file,
which stays a probe. The generic construction is not instantiated end to end
at either production instance; the six instance facts discharge the product
hypothesis and the run-argument reading there, and the comparisons say what
number the construction would carry, which is what decision 8 asks for.

## Traps met

- **`` `x `` rejects an application on either slot.** Both
  `fdistmap arg_read (sa_sampleP sa) `x (sa_cut_dist sa)` readings are wrong:
  the right slot took `sa_cut_dist` alone and applied the result to `sa`, and
  once that was parenthesized the left slot swallowed `(sa_sampleP sa) `x
  (sa_cut_dist sa)` as `fdistmap`'s second argument. Both sides need
  parentheses whenever either is an application.
- **Header anchors differ file to file.** `pgl27_tableau_analysis_bridged.v`
  opens at `From mathcomp Require Import ssreflect`,
  `five_card_tableau_analysis_bridged.v` at `Require Import Lia.`, neither at
  `From HB Require`. An insertion keyed to the wrong anchor fails silently in
  the sense that the guard fires before the write, so check the write landed.
- **Recompiling `lib/var_dist_supp.v` stales its importers**, and the
  rebuild must follow a topological order, not `_CoqProject` order:
  `pgl27_analysis` and `five_card_analysis` sit below `pgg_analysis_manifest`,
  which sits below `pgg_tableau`.

## Unedited production files recompiled (single-file, through the lock)

In this order, all clean:

```
instances/kim2025/five_card_mixing.v          4.2 s
instances/kim2025/five_card_analysis.v        3.8 s
instances/psl211/psl211_word_model.v          3.7 s
instances/psl211/psl211_analysis.v            3.7 s
instances/pgl27/pgl27_analysis.v              3.7 s
manifest/pgg_analysis_manifest.v              5.9 s
manifest/pgg_tableau.v                       13.1 s
manifest/pgg_tableau_syntax.v                 4.4 s
instances/pgl27/pgl27_proximity.v             3.9 s
instances/pgl27/tableau/pgl27_tableau_algebraic.v    3.7 s
instances/pgl27/tableau/pgl27_tableau_executable.v   3.7 s
instances/pgl27/tableau/pgl27_tableau_observed.v     3.9 s
instances/pgl27/tableau/pgl27_tableau_sampled.v      3.7 s
instances/kim2025/five_card_proximity.v              3.8 s
instances/kim2025/tableau/five_card_tableau_algebraic.v   3.7 s
instances/kim2025/tableau/five_card_tableau_executable.v  3.7 s
instances/kim2025/tableau/five_card_tableau_observed.v    3.7 s
instances/kim2025/tableau/five_card_tableau_sampled.v     4.0 s
```

No frozen module was touched. The main session still owes the rest of the
reverse closure of `lib/var_dist_supp.v` and of the two model files.

## Fix pass

Applied 2026-09-20 against `landing_rulings.md`, `audit-landing-soundness.md`
(W1 to W13) and `audit-landing-naming.md` (X1 to X28). No statement or proof
of a declaration that existed before the landing changed. One git write, the
`git mv` of ruling X18. Nothing deleted under `notes/probes/`.

### Code items

**X18, file rename.** `lib/fdist_prod_cond.v` -> `lib/fdist_prod_cst_cond.v`
by `git mv`; `lib/fdist_prod_cond.{vo,vok,vos,glob}` and the dot-`aux` file
removed. Header line:

```coq
(* fdist_prod_cst_cond: constant conditional laws and constant random         *)
(* variables                                                                  *)
```

`_CoqProject:36` is now `lib/fdist_prod_cst_cond.v`; the import at
`manifest/pgg_tableau_security_property_relations.v` reads
`From pgg_smc Require Import fdist_prod_cst_cond var_dist_joint_law.`

**W11, X7, `var_dist_xx` dropped.** The lemma, its docstring and its index
entry are gone from `lib/var_dist_supp.v`. `grep -rn var_dist_xx` over
`*.v` returns nothing outside `notes/`; `landing_fidelity.v` lost its check.
W3 and X8, which were about that docstring, are therefore moot.

**X15, two renames** in
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`:

```coq
Lemma kim_biased_proximity_eps_cert_exact_sw_boundE (R : realType)
    (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx)
  = sw_bound_eps (ic_b (kim_biased_cert_exact R idx)).
Proof. exact: erefl. Qed.

Lemma kim_biased_proximity_eps_le_cert_sw_bound (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx)
  <= sw_bound_eps (ic_b (kim_biased_cert R idx)).
Proof. exact: kim_biased_exact_le_eps. Qed.
```

Both index entries now open "the proximity certificate's number" and name
`kim_biased_cert_exact` and `kim_biased_cert`.

**W8.** `exact: kim_biased_exact_le_eps` closes the inequality at the first
try, so the fresh `2%:R <= Num.sqrt 5%:R` step and the `lra` call are gone.
The docstring says the number relation is that lemma read at the two
certificates.

**W1, W2, X4, the two bridges.** Both names were free tree-wide. Neither
model file gained an import: `sa_cut_dist` and `fdistmap_prodr` come from
`security/pgg_sample_adapter.v`, `pgl27_word_cut_distE` from
`instances/pgl27/pgl27_exec.v` and `kim_single_cut_distE` from the same
model file, all already in scope. `instances/pgl27/pgl27_models.v`:

```coq
Lemma pgl27_word_arg_cut_marginals_prodE (R : realType)
    (secretP : R.-fdist bool) :
  fdistmap (fun u : bool * (200.-tuple 'I_5) =>
              (u.1, @sa_cut _ _ _ (amf_sample pgl27_word_family R secretP) u))
    (sa_sampleP (amf_sample pgl27_word_family R secretP))
  = (fdistmap (fun u : bool * (200.-tuple 'I_5) => u.1)
       (sa_sampleP (amf_sample pgl27_word_family R secretP)))
    `x (sa_cut_dist (amf_sample pgl27_word_family R secretP)).
```

`instances/kim2025/five_card_models.v`:

```coq
Lemma kim_biased_arg_cut_marginals_prodE (R : realType) (idx : unit) :
  fdistmap (fun u : five_card_leakage.Omega =>
              (five_card_sample_arg u,
               @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
    (sa_sampleP (amf_sample kim_biased_family R idx))
  = (fdistmap (fun u : five_card_leakage.Omega => five_card_sample_arg u)
       (sa_sampleP (amf_sample kim_biased_family R idx)))
    `x (sa_cut_dist (amf_sample kim_biased_family R idx)).
```

Each is proved from its `_arg_cut_prodE` sibling, `fdistmap_comp` and
`fdist_prod1` for the first marginal and the model's cut-law lemma for the
second. The two `_arg_cut_prodE` docstrings point at the new lemma for the
shape a construction asks a model for, so X4's fallback rewording was not
needed. Both carry a header index entry.

### Comment items, old line then new line

| id | old | new |
|---|---|---|
| W3, X8 | `var_dist_xx`'s "a number a certificate publishes lies between this value and two" | declaration dropped, so no replacement |
| W4 | "tells an observer nothing about the first coordinate exactly when the reading's conditional law does not move with that coordinate." | "tells an observer nothing about the first coordinate when the reading's conditional law does not move with that coordinate." |
| W5 | (absent) | "No instance of the construction at a production model: the instance files record the product form of a model's joint law and the number a construction would carry, not a built certificate." |
| W6, X14 | paragraph two ended at "at one run." | "…at one run. The construction reads the run argument through a finite coordinate of the sample point, and the strength of the conclusion is the fineness of that coordinate. Two further hypotheses are carried, not proved: the run argument factors through that coordinate, and the model's executed coalition reading is its static one, which every program at Sampled holds. At a one-point carrier the statement is true and says nothing." |
| W7, X20 | (absent) | "The threshold hypothesis is the field's shape; the bound holds at every coalition." |
| W9 | "all thirty-two landed declarations" | "all thirty-one landed declarations"; the landing now introduces thirty-two, one dropped and two added, and `landing_fidelity.v` carries thirty-two declaration checks |
| W10 | (absent) | eight projection checks, closed by `erefl`: the constant witness's secret, the constant certificate's ideal, witness secret, own secret and number two, the ideal adapter's sample law, the ideal witness's secret, and the built certificate's `ipc_eps` |
| W12, X12 | "The ideal model's secret has the law the actual model's secret has. … and the number below measures the coupling of that secret with a coalition's reading alone." | "The ideal model's secret is distributed as the finite coordinate arg_read takes off the actual model's sample point. … and idealproximity_close_of_indistinguishability then bounds the distance between the two joint laws of that secret with a coalition's reading." |
| W13, X1 | nine index entries | six added: `exact_witness_cst_true`, `exact_witness_ideal_prod`, `ideal_prod_reading_arg_prodE`, `ideal_prod_reading_indep_arg`, `var_dist_joint_reading_arg_le`, `idealproximity_close_of_indistinguishability`, each at the block's `==` column 33 and continuation column 36 |
| X2 | "inde_RV_cst is the same conclusion in the case where the reading is one value." | "inde_RV_cst is the same conclusion in the case where the coordinate the reading is compared against is one value." |
| X3 | "The two models draw the run argument from one law and read one function of the pair, so a distance on the cut group transfers unchanged." | "Both models draw that coordinate from one law and read one function of the pair, so the only quantity the two sides can differ in is the cut law." plus, above `have HL`, `(* Rewrite the actual side as one map on a product with the same left factor, then var_dist_fdistmap_prodR_le. *)` |
| X5 | the two 79-byte index lines of the five-card equality | replaced by the X15 entry, both lines 80 bytes |
| X6 | `kim_biased_arg_cut_prodE == …` with `==` at column 31 against the file's 29 | the long name alone on its line, `==` at column 29, continuation at column 32, matching the sibling entry |
| X9 | "the contrapositive of fdistmap_neq0_codom in the form a support argument consumes" | "the contrapositive of fdistmap_neq0_codom: a reading that never returns a value leaves that value with mass zero" |
| X10 | "Each law contributes its whole mass of one, so the value meets the bound var_dist_le2 gives." in the docstring | moved to `(* On a disjoint support the absolute difference splits into the two masses, and each sums to one. *)` above the proof |
| X11 | "so holding exact-independence evidence is by itself no statement" | "so holding an exact witness is by itself no statement" |
| X13 | "a finite reading of the sample point", "here the reading is the run argument itself", "the run argument read is constant", "the joint laws of the reading and the run argument" | "a finite coordinate of the sample point", "here that coordinate is the run argument itself", "that coordinate is constant", "the joint laws of the reading and the finite coordinate"; "reading" now names only the coalition's static reading |
| X16 | "…would carry that same number, so at this model the built number is the number the hand-built certificate publishes." | "…would carry that same number." |
| X17 | "the spectral square root of five over eighty" | "the square root of five over eighty, the number the spectral bound carries" |
| X19 | four `Require Import` lines alternating namespaces | `pgg_smc` twice, then `pgg_reconstruct algebraic_rigidity pgg_sharing_framework`, then `pgg_smc pgg_tableau` |
| X24 | "fails of some certificate over a model" | "does not hold of every certificate over a model" |
| X25 | "The disagreement between the two secrets is the whole of the argument; no property of the model enters." | "No property of the model enters." |
| X26 | "The two joint laws the proposition compares are two laws and its number is read off neither" | "Neither of the two joint laws the proposition compares reduces to the other, and its number is read off neither" |

X21, X23, X27 and X28 are no change by ruling; X22 is not landed by ruling.

### Compiles, in dependency order, single-file through the lock

All clean. The files this pass edited are marked; the rest are unedited
production files a stale-library error named, recompiled in topological
order.

```
lib/var_dist_supp.v                                       edited    4.0 s
lib/fdist_prod_cst_cond.v                                 edited    3.9 s
instances/pgl27/pgl27_models.v                            edited    4.0 s
instances/kim2025/five_card_models.v                      edited    4.3 s
security/var_dist_joint_law.v                                       3.9 s
instances/kim2025/five_card_mixing.v                                4.1 s
instances/kim2025/five_card_analysis.v                              3.9 s
instances/pgl27/pgl27_analysis.v                                    3.7 s
instances/psl211/psl211_mixing.v                                  159.8 s
instances/psl211/psl211_word_model.v                                4.1 s
instances/psl211/psl211_analysis.v                                  3.9 s
manifest/pgg_analysis_manifest.v                                    6.0 s
manifest/pgg_tableau.v                                             13.5 s
manifest/pgg_tableau_syntax.v                                       4.4 s
manifest/pgg_tableau_security_property_relations.v        edited    4.0 s
instances/pgl27/pgl27_proximity.v                                   3.8 s
instances/pgl27/tableau/pgl27_tableau_algebraic.v                   4.0 s
instances/pgl27/tableau/pgl27_tableau_executable.v                  3.8 s
instances/pgl27/tableau/pgl27_tableau_observed.v                    3.8 s
instances/pgl27/tableau/pgl27_tableau_sampled.v                     3.8 s
instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v  edited    6.4 s
instances/kim2025/five_card_proximity.v                             3.8 s
instances/kim2025/tableau/five_card_tableau_algebraic.v             3.7 s
instances/kim2025/tableau/five_card_tableau_executable.v            3.7 s
instances/kim2025/tableau/five_card_tableau_observed.v              3.7 s
instances/kim2025/tableau/five_card_tableau_sampled.v               4.0 s
instances/kim2025/tableau/five_card_tableau_analysis_bridged.v
                                                          edited    5.9 s
notes/probes/…/landing_fidelity.v                         edited    4.7 s
```

`instances/psl211/psl211_endpoints.v` was neither compiled nor edited, and
nothing it requires was. `psl211_mixing.v`, `psl211_word_model.v` and
`psl211_analysis.v` require it and were recompiled because
`manifest/pgg_analysis_manifest.v` refused to load
`pgl27_analysis` beside a `psl211_analysis` built against the earlier
`var_dist_supp`; each loads `psl211_endpoints.vo` unchanged. No `legacy/`
file was touched.

### Fidelity

`landing_fidelity.v` requires production only. It carries thirty-two
declaration checks, one per landed declaration, eight projection checks and
the nine `Arguments` applications. Output in `landing_fidelity.out`: no
error, the one pre-existing `notation-incompatible-prefix` warning, and four
`Print Assumptions` blocks each reporting exactly
`propositional_extensionality`, `functional_extensionality_dep` and
`constructive_indefinite_description`.

### Finishing checks

`git status --short` over tracked sources: `_CoqProject`,
`instances/kim2025/five_card_models.v`,
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`,
`instances/pgl27/pgl27_models.v`,
`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`,
`lib/fdist_prod_cst_cond.v`, `lib/var_dist_supp.v`,
`manifest/pgg_tableau_security_property_relations.v`,
`security/var_dist_joint_law.v`. No `legacy/` file, no frozen file, no
`instances/psl211/` source. Every added line is at most 80 bytes and every
boxed line is exactly 80 with a space before the closing delimiter. A scan
of the added lines for the two barred nouns, the owner's barred list, a
capital letter followed by a digit, an abbreviation of
"indistinguishability", and status or history words returns nothing.
