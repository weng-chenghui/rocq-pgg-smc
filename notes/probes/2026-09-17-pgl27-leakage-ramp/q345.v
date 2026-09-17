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
From pgg_smc Require Import pgl27_secrecy pgl27_leakage_census.
From pgg_smc Require Import proba_entropy_ext.
From aud Require Import q1_transport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Definition pgl27_code_coalition (S : seq nat) : {set 'I_8} :=
  [set i | val i \in S].

Definition rep_seven : seq nat := [:: 0; 1; 2; 3; 4; 5; 6].

(* ---------- Q3 ---------- *)
Lemma q3_card_five : #|pgl27_code_coalition rep_five| = 5.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

Lemma q3_card_harmonic : #|pgl27_code_coalition rep_harmonic| = 4.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

Lemma q3_card_equi : #|pgl27_code_coalition rep_equianharmonic| = 4.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

Lemma q3_card_six : #|pgl27_code_coalition rep_six| = 6.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

Lemma q3_card_seven : #|pgl27_code_coalition rep_seven| = 7.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

Lemma q3_leakE : pgl27_code_coalition rep_harmonic = pgl27_leak_coalition.
Proof.
apply/setP => x; rewrite /pgl27_code_coalition /pgl27_leak_coalition !inE.
by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

Lemma q3_class_harmonic : subset_class (pgl27_code_coalition rep_harmonic) = false.
Proof.
have Hhs : heart_set (orbit_encode false) = pgl27_code_coalition rep_harmonic.
  apply/setP => x; rewrite /heart_set /pgl27_code_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
by rewrite -Hhs; exact: (orbit_encodeK false).
Qed.

Lemma q3_class_equi : subset_class (pgl27_code_coalition rep_equianharmonic) = true.
Proof.
have Hhs : heart_set (orbit_encode true) = pgl27_code_coalition rep_equianharmonic.
  apply/setP => x; rewrite /heart_set /pgl27_code_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
by rewrite -Hhs; exact: (orbit_encodeK true).
Qed.

(* does vm_compute work directly on subset_class of a set? *)
Goal subset_class (pgl27_code_coalition rep_harmonic) = false.
Proof. Fail by vm_compute. Fail by native_compute. Abort.

(* ---------- instance-level transport ---------- *)
Section instance.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

Lemma pgl27_view_transport (g : pgg_gT pgl27_M) (C : {set 'I_8}) :
  g \in pgg_G pgl27_M ->
  `I(pgl27_secret R ; pgl27_view R (g @: C))
  = `I(pgl27_secret R ; pgl27_view R C).
Proof.
exact: (@coalition_view_transport (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool)
  pgl27_G_pos orbit_encode g C).
Qed.

(* ---------- Q4 ---------- *)
Lemma q4_zero (C : {set 'I_8}) : (#|C| <= 3)%N ->
  `I(pgl27_secret R ; pgl27_view R C) = 0.
Proof.
move=> HC.
by rewrite mutual_info_RVE (inde_cond_entropy (pgl27_view_indep R HC)) subrr.
Qed.

(* ---------- Q5 ---------- *)
Lemma q5_le_entropy (U TS TV : finType) (Q : R.-fdist U)
    (S : {RV Q -> TS}) (V : {RV Q -> TV}) : `I(S ; V) <= `H `p_S.
Proof.
by rewrite mutual_info_RVE lerBlDr lerDl; exact: centropy_RV_ge0.
Qed.

Lemma q5_entropy_bool (U : finType) (Q : R.-fdist U) (S : {RV Q -> bool}) :
  `p_S = fdist_uniform card_bool -> `H `p_S = 1.
Proof. by move=> ->; rewrite entropy_uniform card_bool realType_ln.log2. Qed.

End instance.

(* subset of prescribed size *)
Lemma q5_seven_sub (C : {set 'I_8}) : (7 <= #|C|)%N ->
  exists2 D : {set 'I_8}, D \subset C & #|D| = 7.
Proof.
move=> HC.
have [s [Us Ss subsC]] := card_geqP HC.
exists [set x in s]; first by apply/subsetP => x; rewrite inE; exact: subsC.
by rewrite cardsE (card_uniqP Us).
Qed.
