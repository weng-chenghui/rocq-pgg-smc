From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
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
From aud Require Import q1_transport q345 q2_local q7.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Section final.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(* the four+one representative values, as delivered by T4 and T6 *)
Hypothesis Iharmonic :
  `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition rep_harmonic))
  = 5%:R / 7%:R.
Hypothesis Iequi :
  `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition rep_equianharmonic))
  = 11%:R / 14%:R.
Hypothesis Ifive :
  `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition rep_five))
  = 25%:R / 28%:R.
Hypothesis Isix :
  `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition rep_six))
  = 27%:R / 28%:R.
Hypothesis Iseven :
  `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition rep_seven)) = 1.

Lemma fin4_harmonic (C : {set 'I_8}) :
  #|C| = 4 -> subset_class C = false ->
  `I(pgl27_secret R ; pgl27_view R C) = 5%:R / 7%:R.
Proof.
move=> HC HcC.
have [g [gG ->]] := iffLR (subset_class_orbit
  (pgl27_code_coalition rep_harmonic) C q3_card_harmonic HC)
  (etrans q3_class_harmonic (esym HcC)).
by rewrite pgl27_view_transport.
Qed.

Lemma fin4_equi (C : {set 'I_8}) :
  #|C| = 4 -> subset_class C = true ->
  `I(pgl27_secret R ; pgl27_view R C) = 11%:R / 14%:R.
Proof.
move=> HC HcC.
have [g [gG ->]] := iffLR (subset_class_orbit
  (pgl27_code_coalition rep_equianharmonic) C q3_card_equi HC)
  (etrans q3_class_equi (esym HcC)).
by rewrite pgl27_view_transport.
Qed.

Lemma fin5 (C : {set 'I_8}) :
  #|C| = 5 -> `I(pgl27_secret R ; pgl27_view R C) = 25%:R / 28%:R.
Proof.
move=> HC.
have [g gG ->] := pgl27_five_subset_orbit q3_card_five HC.
by rewrite pgl27_view_transport.
Qed.

Lemma fin6 (C : {set 'I_8}) :
  #|C| = 6 -> `I(pgl27_secret R ; pgl27_view R C) = 27%:R / 28%:R.
Proof.
move=> HC.
have [g gG ->] := pgl27_six_subset_orbit q3_card_six HC.
by rewrite pgl27_view_transport.
Qed.

Lemma fin7 (C : {set 'I_8}) :
  #|C| = 7 -> `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC.
have [g gG ->] := q2_seven_subset_orbit q3_card_seven HC.
by rewrite pgl27_view_transport.
Qed.

(* the |C| = 8 join *)
Lemma fin8 (C : {set 'I_8}) :
  #|C| = 8 -> `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC.
have HCT : C = [set: 'I_8].
  by apply/eqP; rewrite eqEcard subsetT /= cardsT card_ord HC.
have H1 : `H `p_(pgl27_secret R) = 1.
  by rewrite (@q7_secret_uniform R) entropy_uniform card_bool realType_ln.log2.
apply: le_anti; apply/andP; split.
  by rewrite -H1 mutual_info_RVE lerBlDr lerDl; exact: centropy_RV_ge0.
rewrite -Iseven; apply: pgl27_view_leakage_le.
by rewrite HCT subsetT.
Qed.

(* every C with 7 <= #|C| gives I = 1 *)
Lemma fin_ge7 (C : {set 'I_8}) :
  (7 <= #|C|)%N -> `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC.
have H8 : (#|C| <= 8)%N by have := max_card (mem C); rewrite card_ord.
have [E7|E7] := eqVneq #|C| 7; first exact: fin7.
apply: fin8; apply/eqP; rewrite eqn_leq H8 /=.
by move: HC; rewrite leq_eqVlt eq_sym (negbTE E7) /=.
Qed.

(* the post line: I = 0 exactly below the threshold *)
Lemma fin_zero_iff (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_view R C) = 0) <-> (#|C| <= 3)%N.
Proof.
split; last exact: q4_zero.
move=> HI; rewrite leqNgt; apply/negP => H4.
have H4' : (4 <= #|C|)%N by [].
have Hsub : exists2 D : {set 'I_8}, D \subset C & #|D| = 4.
  have [s [Us Ss subsC]] := card_geqP H4'.
  exists [set x in s]; first by apply/subsetP => x; rewrite inE; exact: subsC.
  by rewrite cardsE (card_uniqP Us).
have [D DC HD] := Hsub.
have Hpos : 0 < `I(pgl27_secret R ; pgl27_view R D).
  case HcD: (subset_class D).
    by rewrite (fin4_equi HD HcD) divr_gt0 // ltr0n.
  by rewrite (fin4_harmonic HD HcD) divr_gt0 // ltr0n.
have := pgl27_view_leakage_le R DC.
rewrite HI => Hle.
by move: (lt_le_trans Hpos Hle); rewrite ltxx.
Qed.

(* the headline assembly *)
Theorem pgl27_view_mutual_infoE (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_view R C) =
    if (#|C| <= 3)%N then 0
    else if #|C| == 4 then (if subset_class C then 11%:R / 14%:R else 5%:R / 7%:R)
    else if #|C| == 5 then 25%:R / 28%:R
    else if #|C| == 6 then 27%:R / 28%:R
    else 1.
Proof.
have step : forall n, (n <= #|C|)%N -> (#|C| == n) = false -> (n.+1 <= #|C|)%N.
  by move=> n Hn Hne; rewrite ltn_neqAle Hn andbT eq_sym Hne.
case H3 : (#|C| <= 3)%N; first exact: q4_zero.
have H4 : (4 <= #|C|)%N by rewrite ltnNge H3.
case E4 : (#|C| == 4).
  by case Hc : (subset_class C);
     [exact: (fin4_equi (eqP E4) Hc)|exact: (fin4_harmonic (eqP E4) Hc)].
have H5 := step 4 H4 E4.
case E5 : (#|C| == 5); first exact: (fin5 (eqP E5)).
have H6 := step 5 H5 E5.
case E6 : (#|C| == 6); first exact: (fin6 (eqP E6)).
exact: fin_ge7 (step 6 H6 E6).
Qed.

End final.
