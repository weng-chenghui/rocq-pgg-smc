(* P8 arm-relations probe, ledger rows A1 to A5.                              *)
(*                                                                            *)
(* No implication into the proximity proposition holds at a number below two  *)
(* uniformly in the proximity certificate. Over an arbitrary model there is a *)
(* certificate whose ideal is the model itself, whose ideal secret is the     *)
(* constant true and whose own secret is the constant false. The two joint    *)
(* laws the arm's proposition compares are then supported on disjoint sets of *)
(* the second coordinate, so their sum of absolute differences is exactly     *)
(* two, the largest value that sum can take. Any premise whatever, an         *)
(* input-indistinguishability proposition among them, therefore fails to give *)
(* the proximity proposition at any number below two once the conclusion is   *)
(* quantified over certificates.                                             *)
(*                                                                            *)
(* Scope. This refutes a universal over certificates. It says nothing about a *)
(* given certificate an instance builds, whose ideal is a model of its own    *)
(* and whose secret is the one the execution computes.                        *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Search "dist_of_RV".

(******************************************************************************)
(*     A1: two laws with disjoint supports are two apart                      *)
(******************************************************************************)

(** A law is at no distance from itself. *)
Lemma var_dist_self (R : realType) (A : finType) (P : R.-fdist A) :
  var_dist P P = 0.
Proof. by rewrite /var_dist big1 // => a _; rewrite subrr normr0. Qed.

Lemma var_dist_self_le0 (R : realType) (A : finType) (P : R.-fdist A) :
  var_dist P P <= 0.
Proof. by rewrite var_dist_self. Qed.

(** A pushforward gives no mass to a point outside the image of its map. It is
    the contrapositive of fdistmap_neq0_codom, in the form a support argument
    consumes. *)
Lemma fdistmap_notin_codom0 (R : realType) (U B : finType) (g : U -> B)
    (P : R.-fdist U) (b : B) :
  (forall u : U, g u != b) -> fdistmap g P b = 0.
Proof.
move=> Hno; apply/eqP; apply: contraT => /fdistmap_neq0_codom[u Hu].
by move: (Hno u); rewrite Hu eqxx.
Qed.

(** Two laws on a finite carrier no point of which carries mass under both are
    exactly two apart in the sum of absolute differences, which is the largest
    value var_dist_le2 allows. Each law contributes its whole mass to the sum,
    and each law has mass one. The literature's total variation distance is
    half of this, so two here is the distance between two laws that a single
    observation tells apart with certainty. *)
Lemma var_dist_disjoint_supp_eq2 (R : realType) (A : finType)
    (P Q : R.-fdist A) :
  (forall a : A, P a = 0 \/ Q a = 0) -> var_dist P Q = 2%:R.
Proof.
move=> Hdisj.
have Hf1 : forall d : R.-fdist A, \sum_(a : A) d a = 1.
  by move=> d; rewrite -(FDist.f1 d); apply: eq_bigl => a; rewrite inE.
rewrite /var_dist.
have -> : \sum_(a : A) `|P a - Q a| = \sum_(a : A) (P a + Q a).
  apply: eq_bigr => a _; case: (Hdisj a) => ->.
  - by rewrite sub0r normrN (ger0_norm (FDist.ge0 Q a)) add0r.
  - by rewrite subr0 addr0 (ger0_norm (FDist.ge0 P a)).
by rewrite big_split /= !Hf1 mulr2n.
Qed.

(******************************************************************************)
(*     A2: a constant random variable is independent of every other           *)
(******************************************************************************)

(** A random variable with one value is independent of every random variable
    on the same space. It is what makes a constant secret a legal field of an
    ExactWitness over any model at all, so the exact arm's record alone does
    not say that a model hides anything. *)
Lemma inde_RV_cst (R : realType) (U : finType) (P : R.-fdist U)
    (TA TB : finType) (X : {RV P -> TA}) (c : TB) :
  P |= X _|_ ((fun=> c) : {RV P -> TB}).
Proof.
move=> x y; rewrite !pfwd1E.
case: (eqVneq y c) => [->|Hne].
- have -> : finset (preim ((fun=> c) : U -> TB) (pred1 c)) = setT.
    by apply/setP => u; rewrite !inE eqxx.
  rewrite Pr_setT mulr1; congr (Pr P _).
  by apply/setP => u; rewrite !inE /= xpair_eqE eqxx andbT.
- have -> : finset (preim ((fun=> c) : U -> TB) (pred1 y)) = set0.
    by apply/setP => u; rewrite !inE /= eq_sym (negbTE Hne).
  have -> : finset (preim [% X, ((fun=> c) : {RV P -> TB})] (pred1 (x, y)))
            = set0.
    apply/setP => u; rewrite !inE /= xpair_eqE.
    by rewrite [c == y]eq_sym (negbTE Hne) andbF.
  by rewrite !Pr_set0 mulr0.
Qed.

(******************************************************************************)
(*     A3 to A5: the certificate no premise rules out                         *)
(******************************************************************************)

Section degenerate_certificate_over_any_model.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(** A3. The witness whose secret is the constant true, over any model. Its
    independence field is A2, so no property of the model is used. *)
Definition const_true_witness : ExactWitness sa :=
  @MkExactWitness R A E sa bool ((fun=> true) : {RV (sa_sampleP sa) -> bool})
    (fun C _ =>
       @inde_RV_cst R (sa_sampleT sa) (sa_sampleP sa) _ bool
         (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))
         true).

(** A3. The proximity certificate over any model at all: its ideal is the
    model itself, its ideal secret is the constant true, its own secret the
    constant false, and its number two, which var_dist_le2 proves without any
    hypothesis. Every field is available at an arbitrary algebra, arbitrary
    execution parameters and an arbitrary sample adapter, so the proximity
    arm's record can be built over a model about which nothing is known. *)
Definition degenerate_proximity_cert : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa sa const_true_witness
    ((fun=> false) : {RV (sa_sampleP sa) -> bool}) 2%:R
    (fun C _ => var_dist_le2 _ _).

(** A4. Below a positive threshold the degenerate certificate's proximity
    proposition fails at every number below two. The empty coalition is below
    the threshold, and there the two laws the proposition compares put all
    their mass on opposite values of the secret coordinate, so they are two
    apart. The two secrets disagree by construction, and that disagreement is
    the whole of the argument. *)
Lemma degenerate_proximity_prop_below2_false
    (Hk : (0 < profile_k (instance_profile A))%N) (c : R) :
  c < 2%:R -> ~ IdealProximityPropAt degenerate_proximity_cert c.
Proof.
move=> Hc H.
have Hcard : (#|@set0 'I_(pi_T' (mp_PI (instance_profile A))).+1|
              < profile_k (instance_profile A))%N by rewrite cards0.
have Hcst : fdistmap ((fun=> true) : sa_sampleT sa -> bool) (sa_sampleP sa)
              false = 0 :> R by apply: fdistmap_notin_codom0.
have H2 : var_dist
    (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                           (instance_exec E) sa 0 set0 u, false))
       (sa_sampleP sa))
    ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                  sa 0 set0) (sa_sampleP sa))
     `x (fdistmap ((fun=> true) : sa_sampleT sa -> bool) (sa_sampleP sa)))
  = 2%:R.
  apply: var_dist_disjoint_supp_eq2 => -[v []].
  - by left; apply: fdistmap_notin_codom0 => u; rewrite xpair_eqE andbF.
  - by right; rewrite fdist_prodE /= Hcst mulr0.
have H2c : (2%:R : R) <= c by rewrite -H2; exact: (H set0 Hcard).
move: (Order.POrderTheory.le_lt_trans H2c Hc).
by rewrite Order.POrderTheory.ltxx.
Qed.

(** A5. The consequence as a statement: whatever proposition a model is known
    to satisfy, that proposition does not give the proximity proposition at a
    number below two when the conclusion is quantified over certificates. The
    premise is discharged by the degenerate certificate alone, so the strength
    of the premise plays no part. *)
Lemma proximity_below2_uniform_in_cert_false
    (Hk : (0 < profile_k (instance_profile A))%N) (Q : Prop) (c : R) :
  Q -> c < 2%:R ->
  ~ (Q -> forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
Proof.
move=> HQ Hc Himp.
exact: (degenerate_proximity_prop_below2_false Hk Hc
          (Himp HQ degenerate_proximity_cert)).
Qed.

(** A5 at the premise the parent statement had in view: the
    input-indistinguishability proposition at the certificate's own number,
    which indistinguishability_tail proves unconditionally, does not give the
    proximity proposition at any number below two uniformly in the proximity
    certificate. *)
Corollary indistinguishability_prop_proximity_below2_false
    (Hk : (0 < profile_k (instance_profile A))%N)
    (ic : IndistinguishabilityCert sa) (c : R) :
  c < 2%:R ->
  ~ (IndistinguishabilityPropAt ic (cert_eps ic) ->
     forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
Proof.
move=> Hc Himp.
exact: (degenerate_proximity_prop_below2_false Hk Hc
          (Himp (indistinguishability_tail ic) degenerate_proximity_cert)).
Qed.

(******************************************************************************)
(*     Mutation of A4: the two secrets made one constant                      *)
(******************************************************************************)

(** The same certificate with its own secret changed to the ideal witness's
    constant. The two laws the arm's proposition compares at the direct
    computation are then one law, so the number zero is a legal field. *)
Definition same_secret_proximity_cert : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa sa const_true_witness
    ((fun=> true) : {RV (sa_sampleP sa) -> bool}) 0
    (fun C _ => var_dist_self_le0 _).

(** With both secrets the constant true the arm compares a joint law with the
    product of its own two marginals, and A2 says the two coincide. *)
Lemma proximity_at0_with_equal_constant_secrets
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                           (instance_exec E) sa 0 C u, true))
       (sa_sampleP sa))
    ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                  sa 0 C) (sa_sampleP sa))
     `x (fdistmap ((fun=> true) : sa_sampleT sa -> bool) (sa_sampleP sa)))
  <= 0.
Proof.
rewrite -(inde_dist_of_RV2
  (@inde_RV_cst R (sa_sampleT sa) (sa_sampleP sa) _ bool
     (@sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C)
     true)).
exact: var_dist_self_le0.
Qed.

Lemma same_secret_proximity_prop_at0 :
  IdealProximityPropAt same_secret_proximity_cert 0.
Proof. by move=> C _; exact: proximity_at0_with_equal_constant_secrets. Qed.

(** The mutation check for A4: with both secrets the same constant, A4's
    conclusion is false. The disagreement between the two secrets is therefore
    what the refutation rests on and not the shape of the certificate. *)
Lemma proximity_below2_false_needs_distinct_secrets :
  ~ (forall c : R, c < 2%:R ->
       ~ IdealProximityPropAt same_secret_proximity_cert c).
Proof.
move=> H; apply: (H (0 : R) _ same_secret_proximity_prop_at0).
by rewrite ltr0n.
Qed.

End degenerate_certificate_over_any_model.

Print Assumptions degenerate_proximity_prop_below2_false.
Print Assumptions proximity_below2_uniform_in_cert_false.
Print Assumptions indistinguishability_prop_proximity_below2_false.
