From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface pgl27_group pgl27_orbit.
From pgg_smc Require Import pgl27_leakage_census pgl27_recovery.

Set Implicit Arguments.

(* short name of a Local lemma is NOT imported *)
Fail Check ntransitive_subset_orbit.
(* but the fully qualified name IS reachable *)
Check pgl27_leakage_census.ntransitive_subset_orbit.
Check pgl27_leakage_census.perm_imsetC.
Check pgl27_leakage_census.cardsC8.

Check pgl27_five_subset_orbit.
Check pgl27_six_subset_orbit.
Check subset_class_orbit.
Check subset_class_invariant.
Check pgl27_2transitive.

Lemma q2_1transitive :
  ntransitive 1 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.
Proof. exact: ntransitive_weak (isT : (1 <= 3)%N) pgl27_3transitive. Qed.

(* the size-seven orbit lemma, same pattern as pgl27_six_subset_orbit *)
Lemma q2_seven_subset_orbit (S T : {set 'I_8}) :
  #|S| = 7 -> #|T| = 7 ->
  exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & T = g @: S.
Proof.
move=> HS HT.
have Hc (C : {set 'I_8}) : #|C| = 7 -> #|~: C| = 1.
  by move=> HC; apply: (@addnI 7); rewrite -{1}HC pgl27_leakage_census.cardsC8.
have [g gG Hg] :=
  pgl27_leakage_census.ntransitive_subset_orbit q2_1transitive (Hc S HS) (Hc T HT).
by exists g => //; rewrite -[T]setCK Hg pgl27_leakage_census.perm_imsetC setCK.
Qed.

(* rho is the identity morphism on the pgl27 instance *)
Lemma q2_rho_id (g : pgg_gT pgl27_M) (C : {set 'I_8}) :
  (@pgg_rho pgl27_M g) @: C = g @: C.
Proof. by []. Qed.

Lemma q2_rho_id_pt (g : pgg_gT pgl27_M) (i : 'I_8) :
  (@pgg_rho pgl27_M g) i = g i.
Proof. by []. Qed.
