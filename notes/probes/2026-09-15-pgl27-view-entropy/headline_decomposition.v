From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset fingroup ssralg ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import proba_entropy_ext pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_secrecy.
From pgg_smc Require Import pgl27_leakage_census.
From pgl27_view_entropy_probe Require Import probe_view_definitions.
From pgl27_view_entropy_probe Require Import ambiguous_probability.
From pgl27_view_entropy_probe Require Import headline_connection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(** The secret marginal of the actual protocol distribution is uniform on
    the two orbit classes. It therefore has one bit of prior entropy. *)
Lemma pgl27_secret_uniform (R : realType) :
  `p_(pgl27_secret R) = fdist_uniform card_bool.
Admitted.

(** Under a uniform Boolean secret, a posterior entropy indicator makes the
    information in a coalition view equal to one bit minus the probability
    that the view remains compatible with both secrets. *)
Local Lemma pgl27_mutual_info_ambiguity_of_posteriorE
    (R : realType) (S : seq nat)
    (Hposterior : forall v : {ffun 'I_8 -> 'I_8},
      pfwd1 (pgl27_view R (pgl27_code_coalition S)) v != 0 ->
      centropy1_RV (pgl27_view R (pgl27_code_coalition S))
        (pgl27_secret R) v = (v \in pgl27_ambiguous_views R S)%:R) :
  mutual_info_RV (pgl27_secret R)
    (pgl27_view R (pgl27_code_coalition S)) =
  1 - pr_in (pgl27_view R (pgl27_code_coalition S))
    (pgl27_ambiguous_views R S).
Proof.
apply: mutual_info_binary_ambiguityE.
- exact: pgl27_secret_uniform R.
- exact: Hposterior.
Qed.

(** The harmonic four-position view reveals one bit minus its census
    collision ratio. This combines its exact posterior entropy with its
    actual ambiguous-view probability. *)
Lemma pgl27_mutual_info_ambiguity_harmonicE (R : realType) :
  mutual_info_RV (pgl27_secret R)
    (pgl27_view R (pgl27_code_coalition rep_harmonic)) =
  1 - (pgl27_collisions rep_harmonic)%:R / 336%:R.
Proof.
by rewrite (pgl27_mutual_info_ambiguity_of_posteriorE
  (pgl27_reachable_view_entropy_harmonic_memE (R:=R)))
  pgl27_ambiguous_probability_harmonicE.
Qed.

(** The equianharmonic four-position view reveals one bit minus its census
    collision ratio. This combines its exact posterior entropy with its
    actual ambiguous-view probability. *)
Lemma pgl27_mutual_info_ambiguity_equianharmonicE (R : realType) :
  mutual_info_RV (pgl27_secret R)
    (pgl27_view R (pgl27_code_coalition rep_equianharmonic)) =
  1 - (pgl27_collisions rep_equianharmonic)%:R / 336%:R.
Proof.
by rewrite (pgl27_mutual_info_ambiguity_of_posteriorE
  (pgl27_reachable_view_entropy_equianharmonic_memE (R:=R)))
  pgl27_ambiguous_probability_equianharmonicE.
Qed.

(** The five-position view reveals one bit minus its census collision ratio.
    This combines its exact posterior entropy with its actual ambiguous-view
    probability. *)
Lemma pgl27_mutual_info_ambiguity_fiveE (R : realType) :
  mutual_info_RV (pgl27_secret R)
    (pgl27_view R (pgl27_code_coalition rep_five)) =
  1 - (pgl27_collisions rep_five)%:R / 336%:R.
Proof.
by rewrite (pgl27_mutual_info_ambiguity_of_posteriorE
  (pgl27_reachable_view_entropy_five_memE (R:=R)))
  pgl27_ambiguous_probability_fiveE.
Qed.

(** The six-position view reveals one bit minus its census collision ratio.
    This combines its exact posterior entropy with its actual ambiguous-view
    probability. *)
Lemma pgl27_mutual_info_ambiguity_sixE (R : realType) :
  mutual_info_RV (pgl27_secret R)
    (pgl27_view R (pgl27_code_coalition rep_six)) =
  1 - (pgl27_collisions rep_six)%:R / 336%:R.
Proof.
by rewrite (pgl27_mutual_info_ambiguity_of_posteriorE
  (pgl27_reachable_view_entropy_six_memE (R:=R)))
  pgl27_ambiguous_probability_sixE.
Qed.

Print Assumptions pgl27_mutual_info_ambiguity_harmonicE.
Print Assumptions pgl27_mutual_info_ambiguity_equianharmonicE.
Print Assumptions pgl27_mutual_info_ambiguity_fiveE.
Print Assumptions pgl27_mutual_info_ambiguity_sixE.
