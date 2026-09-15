From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp boolp ring lra reals Rstruct.
From infotheo Require Import realType_ext fdist proba entropy.

From pgg_smc Require Import pgg_interface pgl27_group pgl27_profile.
From pgg_smc Require Import pgl27_secrecy pgl27_leakage_census.
From pgl27_view_entropy_probe Require Import probe_view_definitions.
From pgl27_view_entropy_probe Require Import ambiguous_probability.
From pgl27_view_entropy_probe Require Import headline_connection.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(** Over the standard real carrier, the harmonic ambiguous-view probability
    equals its census collision ratio. This gives the probability statement
    its concrete numerical interpretation. *)
Lemma pgl27_ambiguous_probability_harmonic_realE :
  `Pr[(pgl27_view Rdefinitions.R
        (pgl27_code_coalition rep_harmonic))
      \in pgl27_ambiguous_views
        Rdefinitions.R rep_harmonic] =
  (pgl27_collisions rep_harmonic)%:R / 336%:R :> Rdefinitions.R.
Proof.
exact: (@ambiguous_probability.pgl27_ambiguous_probability_harmonicE
  Rdefinitions.R).
Qed.

(** Every reachable harmonic view over the standard real carrier has
    posterior entropy zero or one according to whether both secrets produce
    it. This gives the information value a concrete real-number carrier. *)
Lemma pgl27_reachable_view_entropy_harmonic_realE
    (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1
      (pgl27_view Rdefinitions.R
        (pgl27_code_coalition rep_harmonic)) v != 0 ->
  centropy1_RV
      (pgl27_view Rdefinitions.R
        (pgl27_code_coalition rep_harmonic))
      (pgl27_secret Rdefinitions.R) v =
  (v \in pgl27_ambiguous_views Rdefinitions.R rep_harmonic)%:R.
Proof.
exact:
  (@headline_connection.pgl27_reachable_view_entropy_harmonic_memE
    Rdefinitions.R v).
Qed.

Print Assumptions pgl27_ambiguous_probability_harmonic_realE.
Print Assumptions pgl27_reachable_view_entropy_harmonic_realE.
