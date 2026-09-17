From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_secrecy pgl27_leakage_census pgl27_recovery.
From pgg_smc Require Import proba_entropy_ext.
From aud Require Import q1_transport q345 q2_local.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Section q7.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(* pgl27_secret_uniform: the load-bearing uniform-secret lemma *)
Lemma q7_secret_uniform : `p_(pgl27_secret R) = fdist_uniform card_bool.
Proof.
rewrite -[RHS](@fdist_prod1 R bool (pgg_gT pgl27_M) (fdist_uniform card_bool)
  (fun _ : bool => (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)))).
by [].
Qed.

(* size-4 orbit split: every four-coalition is an image of one of the two reps *)
Lemma q7_four_split (C : {set 'I_8}) : #|C| = 4 ->
  (exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M
     & C = g @: pgl27_code_coalition rep_harmonic)
  \/ (exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M
     & C = g @: pgl27_code_coalition rep_equianharmonic).
Proof.
move=> HC.
case HcC: (subset_class C).
  right.
  have [g [gG Hg]] := iffLR (subset_class_orbit
    (pgl27_code_coalition rep_equianharmonic) C q3_card_equi HC)
    (etrans q3_class_equi (esym HcC)).
  by exists g.
left.
have [g [gG Hg]] := iffLR (subset_class_orbit
  (pgl27_code_coalition rep_harmonic) C q3_card_harmonic HC)
  (etrans q3_class_harmonic (esym HcC)).
by exists g.
Qed.

(* size-7: transport from the seven representative *)
Lemma q7_seven (C : {set 'I_8}) : #|C| = 7 ->
  `I(pgl27_secret R ; pgl27_view R C)
  = `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition rep_seven)).
Proof.
move=> HC.
have [g gG ->] := q2_seven_subset_orbit q3_card_seven HC.
exact: pgl27_view_transport.
Qed.

End q7.

(* seven-subset orbit, re-proved here from the Local helpers *)
Print Assumptions coalition_view_transport.
Print Assumptions q2_seven_subset_orbit.
