From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp boolp ring lra reals.
From infotheo Require Import realType_ext fdist proba entropy.

From pgg_smc Require Import pgg_interface pgl27_group pgl27_profile.
From pgg_smc Require Import pgl27_secrecy pgl27_leakage_census.
From pgl27_view_entropy_probe Require Import probe_view_definitions.
From pgl27_view_entropy_probe Require Import ambiguous_probability.
From pgl27_view_entropy_probe Require Import posterior_entropy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(** At every reachable harmonic representative view, posterior entropy is
    the indicator of the same ambiguous-view event counted by the census. *)
Lemma pgl27_reachable_view_entropy_harmonic_memE
    (R : realType) (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1
      (pgl27_view R
        (pgl27_code_coalition rep_harmonic)) v != 0 ->
  centropy1_RV
      (pgl27_view R
        (pgl27_code_coalition rep_harmonic))
      (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_harmonic)%:R.
Proof.
exact: posterior_entropy.pgl27_reachable_view_entropy_harmonicE.
Qed.

(** At every reachable equianharmonic representative view, posterior entropy
    is the indicator of the same ambiguous-view event counted by the census. *)
Lemma pgl27_reachable_view_entropy_equianharmonic_memE
    (R : realType) (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1
      (pgl27_view R
        (pgl27_code_coalition rep_equianharmonic)) v != 0 ->
  centropy1_RV
      (pgl27_view R
        (pgl27_code_coalition rep_equianharmonic))
      (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_equianharmonic)%:R.
Proof.
exact: posterior_entropy.pgl27_reachable_view_entropy_equianharmonicE.
Qed.

(** At every reachable five-position representative view, posterior entropy
    is the indicator of the same ambiguous-view event counted by the census. *)
Lemma pgl27_reachable_view_entropy_five_memE
    (R : realType) (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1
      (pgl27_view R
        (pgl27_code_coalition rep_five)) v != 0 ->
  centropy1_RV
      (pgl27_view R
        (pgl27_code_coalition rep_five))
      (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_five)%:R.
Proof.
exact: posterior_entropy.pgl27_reachable_view_entropy_fiveE.
Qed.

(** At every reachable six-position representative view, posterior entropy
    is the indicator of the same ambiguous-view event counted by the census. *)
Lemma pgl27_reachable_view_entropy_six_memE
    (R : realType) (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1
      (pgl27_view R
        (pgl27_code_coalition rep_six)) v != 0 ->
  centropy1_RV
      (pgl27_view R
        (pgl27_code_coalition rep_six))
      (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_six)%:R.
Proof.
exact: posterior_entropy.pgl27_reachable_view_entropy_sixE.
Qed.

Print Assumptions pgl27_reachable_view_entropy_harmonic_memE.
Print Assumptions pgl27_reachable_view_entropy_equianharmonic_memE.
Print Assumptions pgl27_reachable_view_entropy_five_memE.
Print Assumptions pgl27_reachable_view_entropy_six_memE.
