(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_leakage_ramp: the leakage of the eight-card orbit scheme as a        *)
(*                     function of coalition size                             *)
(*                                                                            *)
(* For every coalition of the eight positions, the mutual information between *)
(* the orbit secret and the coalition view is a function of the coalition     *)
(* size alone, except at size four, where it also depends on the cross-ratio  *)
(* class of the four positions. It is zero up to the privacy threshold three, *)
(* eleven fourteenths at four on an equianharmonic quadruple and five         *)
(* sevenths on a harmonic one, twenty-five twenty-eighths at five,            *)
(* twenty-seven twenty-eighths at six, and the full bit from seven positions  *)
(* on. Every value is exact and unconditional on any computational            *)
(* assumption.                                                                *)
(*                                                                            *)
(* Scope. One pre-reveal view, a uniform Boolean orbit secret, a uniform      *)
(* shuffle drawn from pgg_G pgl27_M, and for each secret the fixed            *)
(* representative deal orbit_encode of its class. The all-decks dealer of     *)
(* pgl27_view_indep_alldecks, which deals a uniform valid deck of the         *)
(* secret's class, is not covered by any value of this file.                  *)
(*                                                                            *)
(* The file joins three statements of pgl27_secrecy.v. The independence of a  *)
(* coalition view of at most three positions from the orbit secret            *)
(* (pgl27_view_indep) becomes the value zero; the monotonicity of the mutual  *)
(* information under coalition inclusion (pgl27_view_leakage_le) carries the  *)
(* seven-position value to the whole deck and the four-position values up to  *)
(* every larger coalition; and the single four-position coalition of strictly *)
(* positive mutual information (pgl27_view_dep_k4, pgl27_view_leak_k4)        *)
(* becomes the exact value five sevenths there, and an equivalence between    *)
(* vanishing mutual information and coalition size at most three for every    *)
(* coalition.                                                                 *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_subset_class_harmonicE, pgl27_subset_class_equianharmonicE == the  *)
(*     cross-ratio class of the two four-position representatives             *)
(*   pgl27_leak_coalitionE == the four heart positions of the identity deal   *)
(*     are the positions listed by the harmonic representative                *)
(*   pgl27_view_mutual_info_imset == relabelling the positions of a coalition *)
(*     by a shuffle leaves its mutual information with the orbit secret       *)
(*     unchanged                                                              *)
(*   pgl27_secret_entropy == the prior entropy of the orbit secret is one bit *)
(*   pgl27_view_mutual_info_le1 == no coalition shares more than one bit with *)
(*     the orbit secret                                                       *)
(*   pgl27_view_mutual_info_le3E, pgl27_view_mutual_info_k4E,                 *)
(*   pgl27_view_mutual_info_k5E, pgl27_view_mutual_info_k6E,                  *)
(*   pgl27_view_mutual_info_k7E, pgl27_view_mutual_info_ge7E == the value at  *)
(*     every coalition of the given size                                      *)
(*   pgl27_view_mutual_infoE == the value at every coalition of the eight     *)
(*     positions                                                              *)
(*   pgl27_view_mutual_info_eq0 == a coalition shares no information with the *)
(*     orbit secret exactly when it holds at most three positions             *)
(*   pgl27_view_mutual_info_leak_coalitionE == the four heart positions of    *)
(*     the identity deal share five sevenths of a bit with the orbit secret   *)
(*   pgl27_view_mutual_info_ge4 == every coalition above the privacy          *)
(*     threshold shares at least five sevenths of a bit with the orbit secret *)
(*                                                                            *)
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design.                                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp lra reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_reconstruct Require Import coalition_view_transport.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_secrecy pgl27_leakage_census.
From pgg_smc Require Import pgl27_view_census pgl27_mutual_info.
From pgg_smc Require Import proba_entropy_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Section pgl27_leakage_ramp.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(** The harmonic representative lists four of the eight positions. At size
    four the shuffle group has two orbits, so a representative's size
    selects the coalitions its value governs only together with the
    cross-ratio class of its positions. *)
Local Lemma pgl27_card_harmonic : #|pgl27_code_coalition rep_harmonic| = 4.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** The equianharmonic representative lists four of the eight positions. It
    is the second of the two four-position orbit classes, and carries the
    other of the two leakage values at that size. *)
Local Lemma pgl27_card_equianharmonic :
  #|pgl27_code_coalition rep_equianharmonic| = 4.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** The five-position representative lists five of the eight positions. The
    five-position coalitions form one shuffle orbit, so its value is the
    value of every coalition of five positions. *)
Local Lemma pgl27_card_five : #|pgl27_code_coalition rep_five| = 5.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** The six-position representative lists six of the eight positions. The
    six-position coalitions form one shuffle orbit, so its value is the value
    of every coalition of six positions. *)
Local Lemma pgl27_card_six : #|pgl27_code_coalition rep_six| = 6.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** The seven-position representative lists seven of the eight positions. It
    is the smallest size at which the coalition view determines the orbit
    secret before the reveal. *)
Local Lemma pgl27_card_seven : #|pgl27_code_coalition rep_seven| = 7.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** The four positions of the harmonic representative form a quadruple of
    cross-ratio class false. A four-position coalition of this class shares
    five sevenths of a bit with the orbit secret, the smaller of the two
    values at that size. *)
Lemma pgl27_subset_class_harmonicE :
  subset_class (pgl27_code_coalition rep_harmonic) = false.
Proof.
have Hhs : heart_set (orbit_encode false) = pgl27_code_coalition rep_harmonic.
  apply/setP => x; rewrite /heart_set /pgl27_code_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
by rewrite -Hhs; exact: (orbit_encodeK false).
Qed.

(** The four positions of the equianharmonic representative form a quadruple
    of cross-ratio class true. A four-position coalition of this class shares
    eleven fourteenths of a bit with the orbit secret, the larger of the two
    values at that size. *)
Lemma pgl27_subset_class_equianharmonicE :
  subset_class (pgl27_code_coalition rep_equianharmonic) = true.
Proof.
have Hhs : heart_set (orbit_encode true)
         = pgl27_code_coalition rep_equianharmonic.
  apply/setP => x; rewrite /heart_set /pgl27_code_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
by rewrite -Hhs; exact: (orbit_encodeK true).
Qed.

(** The four heart positions of the identity deal are the positions listed by
    the harmonic representative. The coalition that witnesses sharpness of
    the privacy threshold three therefore lies in the harmonic orbit class,
    and its exact leakage is the harmonic value. *)
Lemma pgl27_leak_coalitionE :
  pgl27_leak_coalition = pgl27_code_coalition rep_harmonic.
Proof.
apply/setP => x; rewrite /pgl27_code_coalition /pgl27_leak_coalition !inE.
by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

(** Moving a coalition from the positions C to the positions g C, for a
    shuffle g of the group, leaves the mutual information between the orbit
    secret and the coalition view unchanged. What a coalition learns depends
    on its positions only through their orbit under the shuffle group, so one
    representative of each orbit fixes the leakage of every coalition in it. *)
Lemma pgl27_view_mutual_info_imset (g : pgg_gT pgl27_M) (C : {set 'I_8}) :
  g \in pgg_G pgl27_M ->
  `I(pgl27_secret R ; pgl27_view R (g @: C))
  = `I(pgl27_secret R ; pgl27_view R C).
Proof.
exact: (@coalition_view_mutual_info_imset (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool)
  pgl27_G_pos orbit_encode g C).
Qed.

(** The prior entropy of the orbit secret is one bit. It is the whole of what
    any coalition can learn about the orbit secret, and the unit in which
    every leakage value of this file is measured. *)
Lemma pgl27_secret_entropy : `H `p_(pgl27_secret R) = 1.
Proof.
by rewrite pgl27_secret_uniform entropy_uniform card_bool realType_ln.log2.
Qed.

(** The mutual information between two random variables is at most the
    entropy of the first. It bounds the leakage of a coalition by the prior
    entropy of the orbit secret, which is what makes the value at seven
    positions the largest value the scheme reaches. *)
Local Lemma mutual_info_RV_le_entropy (U TS TV : finType) (Q : R.-fdist U)
    (S : {RV Q -> TS}) (V : {RV Q -> TV}) : `I(S ; V) <= `H `p_S.
Proof.
by rewrite mutual_info_RVE lerBlDr lerDl; exact: centropy_RV_ge0.
Qed.

(** A coalition of at most three positions shares zero bits with the orbit
    secret. Below the privacy threshold a coalition learns nothing at all
    about the orbit secret from one pre-reveal view. *)
Lemma pgl27_view_mutual_info_le3E (C : {set 'I_8}) : (#|C| <= 3)%N ->
  `I(pgl27_secret R ; pgl27_view R C) = 0.
Proof.
move=> HC.
by rewrite mutual_info_RVE (inde_cond_entropy (pgl27_view_indep R HC)) subrr.
Qed.

(** A coalition of four positions shares eleven fourteenths of a bit with the
    orbit secret when its positions are an equianharmonic quadruple, and five
    sevenths of a bit otherwise. The first size above the privacy threshold
    already leaks, by an amount that depends on the cross-ratio class of the
    four positions and not only on their number. *)
Lemma pgl27_view_mutual_info_k4E (C : {set 'I_8}) : #|C| = 4 ->
  `I(pgl27_secret R ; pgl27_view R C) =
  (if subset_class C then 11%:R / 14%:R else 5%:R / 7%:R).
Proof.
move=> HC.
(* the two four-position orbits are the fibers of subset_class, and the
   representative of each is transported onto C by a shuffle *)
case HcC : (subset_class C).
  have [g [gG ->]] := iffLR (subset_class_orbit
    (pgl27_code_coalition rep_equianharmonic) C pgl27_card_equianharmonic HC)
    (etrans pgl27_subset_class_equianharmonicE (esym HcC)).
  by rewrite (pgl27_view_mutual_info_imset _ gG)
     pgl27_view_mutual_info_equianharmonicE.
have [g [gG ->]] := iffLR (subset_class_orbit
  (pgl27_code_coalition rep_harmonic) C pgl27_card_harmonic HC)
  (etrans pgl27_subset_class_harmonicE (esym HcC)).
by rewrite (pgl27_view_mutual_info_imset _ gG) pgl27_view_mutual_info_harmonicE.
Qed.

(** A coalition of five positions shares twenty-five twenty-eighths of a bit
    with the orbit secret. The five-position coalitions form one shuffle
    orbit, so no choice of five positions leaks more than another. *)
Lemma pgl27_view_mutual_info_k5E (C : {set 'I_8}) : #|C| = 5 ->
  `I(pgl27_secret R ; pgl27_view R C) = 25%:R / 28%:R.
Proof.
move=> HC.
have [g gG ->] := pgl27_five_subset_orbit pgl27_card_five HC.
by rewrite (pgl27_view_mutual_info_imset _ gG) pgl27_view_mutual_info_fiveE.
Qed.

(** A coalition of six positions shares twenty-seven twenty-eighths of a bit
    with the orbit secret. The value is still below one bit, so six of the
    eight positions leave the orbit secret undetermined on some
    executions. *)
Lemma pgl27_view_mutual_info_k6E (C : {set 'I_8}) : #|C| = 6 ->
  `I(pgl27_secret R ; pgl27_view R C) = 27%:R / 28%:R.
Proof.
move=> HC.
have [g gG ->] := pgl27_six_subset_orbit pgl27_card_six HC.
by rewrite (pgl27_view_mutual_info_imset _ gG) pgl27_view_mutual_info_sixE.
Qed.

(** A coalition of seven positions shares one bit with the orbit secret, the
    whole of its prior entropy. Seven of the eight positions determine the
    orbit secret before the reveal, so the scheme keeps nothing from a
    coalition of that size. *)
Lemma pgl27_view_mutual_info_k7E (C : {set 'I_8}) : #|C| = 7 ->
  `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC.
have [g gG ->] := pgl27_seven_subset_orbit pgl27_card_seven HC.
by rewrite (pgl27_view_mutual_info_imset _ gG) pgl27_view_mutual_info_sevenE.
Qed.

(** No coalition shares more than one bit with the orbit secret. One
    pre-reveal view never tells a coalition more than the orbit secret
    itself carries, whatever its positions. *)
Lemma pgl27_view_mutual_info_le1 (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_view R C) <= 1.
Proof.
by rewrite -pgl27_secret_entropy; exact: mutual_info_RV_le_entropy.
Qed.

(** The coalition of all eight positions shares one bit with the orbit
    secret. Every player together learns the orbit secret before the reveal,
    which is the boundary case of the seven-position value. *)
Local Lemma pgl27_view_mutual_info_k8E (C : {set 'I_8}) : #|C| = 8 ->
  `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC.
have HCT : C = [set: 'I_8].
  by apply/eqP; rewrite eqEcard subsetT /= cardsT card_ord HC.
(* one bit from above by the prior entropy of the secret, one bit from below
   by monotonicity along a seven-position subcoalition *)
apply: le_anti; apply/andP; split; first exact: pgl27_view_mutual_info_le1.
rewrite -(pgl27_view_mutual_info_sevenE R); apply: pgl27_view_leakage_le.
by rewrite HCT subsetT.
Qed.

(** A coalition of seven or eight positions shares one bit with the orbit
    secret. From seven positions on the coalition view determines the orbit
    secret before the reveal, and no larger coalition can learn more. *)
Lemma pgl27_view_mutual_info_ge7E (C : {set 'I_8}) : (7 <= #|C|)%N ->
  `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC.
have H8 : (#|C| <= 8)%N by have := max_card (mem C); rewrite card_ord.
have [E7|E7] := eqVneq #|C| 7; first exact: pgl27_view_mutual_info_k7E.
apply: pgl27_view_mutual_info_k8E; apply/eqP; rewrite eqn_leq H8 /=.
by move: HC; rewrite leq_eqVlt eq_sym (negbTE E7) /=.
Qed.

(** The mutual information between the orbit secret and the view of a
    coalition of the eight positions is zero up to size three, eleven
    fourteenths at size four on the twenty-eight equianharmonic quadruples
    and five sevenths on the forty-two harmonic ones, twenty-five
    twenty-eighths at five, twenty-seven twenty-eighths at six, and one bit
    from seven positions on. The scheme hides the orbit secret completely
    below the privacy threshold three and reveals it completely from seven
    positions on, and between those two sizes it leaks a known exact
    amount rather than an amount bounded only from above. *)
Theorem pgl27_view_mutual_infoE (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_view R C) =
    if (#|C| <= 3)%N then 0
    else if #|C| == 4 then
      (if subset_class C then 11%:R / 14%:R else 5%:R / 7%:R)
    else if #|C| == 5 then 25%:R / 28%:R
    else if #|C| == 6 then 27%:R / 28%:R
    else 1.
Proof.
have step : forall n, (n <= #|C|)%N -> (#|C| == n) = false -> (n.+1 <= #|C|)%N.
  by move=> n Hn Hne; rewrite ltn_neqAle Hn andbT eq_sym Hne.
case H3 : (#|C| <= 3)%N; first exact: pgl27_view_mutual_info_le3E.
have H4 : (4 <= #|C|)%N by rewrite ltnNge H3.
case E4 : (#|C| == 4); first exact: (pgl27_view_mutual_info_k4E (eqP E4)).
have H5 := step 4 H4 E4.
case E5 : (#|C| == 5); first exact: (pgl27_view_mutual_info_k5E (eqP E5)).
have H6 := step 5 H5 E5.
case E6 : (#|C| == 6); first exact: (pgl27_view_mutual_info_k6E (eqP E6)).
exact: (pgl27_view_mutual_info_ge7E (step 6 H6 E6)).
Qed.

(** A coalition shares no information with the orbit secret exactly when it
    holds at most three positions. The privacy threshold three is sharp at
    every coalition of four or more positions and not only at one witness
    coalition, so no four of the eight positions are information-free. *)
Lemma pgl27_view_mutual_info_eq0 (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_view R C) == 0) = (#|C| <= 3)%N.
Proof.
apply/idP/idP; last by move=> HC; rewrite (pgl27_view_mutual_info_le3E HC) eqxx.
move=> /eqP HI; rewrite leqNgt; apply/negP => H4.
(* a coalition of four or more positions contains a four-position one, whose
   value is strictly positive in either cross-ratio class *)
have [D DC HD] : exists2 D : {set 'I_8}, D \subset C & #|D| = 4.
  have [s [Us Ss subsC]] := card_geqP H4.
  exists [set x in s]; first by apply/subsetP => x; rewrite inE; exact: subsC.
  by rewrite cardsE (card_uniqP Us).
have Hpos : 0 < `I(pgl27_secret R ; pgl27_view R D).
  rewrite (pgl27_view_mutual_info_k4E HD).
  by case: (subset_class D); rewrite divr_gt0 // ltr0n.
have := pgl27_view_leakage_le R DC.
rewrite HI => Hle.
by move: (lt_le_trans Hpos Hle); rewrite ltxx.
Qed.

(** The four heart positions of the identity deal share five sevenths of a
    bit with the orbit secret. This is the exact value at the coalition
    that witnesses sharpness of the privacy threshold three, where the
    threshold statements give only strict positivity. *)
Lemma pgl27_view_mutual_info_leak_coalitionE :
  `I(pgl27_secret R ; pgl27_view R pgl27_leak_coalition) = 5%:R / 7%:R.
Proof.
by rewrite pgl27_leak_coalitionE pgl27_view_mutual_info_harmonicE.
Qed.

(** A coalition of four or more positions shares at least five sevenths of a
    bit with the orbit secret. Once the privacy threshold is passed the
    leakage never falls back towards zero, so the smallest value above the
    threshold is a lower bound for every larger coalition. *)
Lemma pgl27_view_mutual_info_ge4 (C : {set 'I_8}) : (4 <= #|C|)%N ->
  5%:R / 7%:R <= `I(pgl27_secret R ; pgl27_view R C).
Proof.
move=> H4; rewrite pgl27_view_mutual_infoE.
have -> : (#|C| <= 3)%N = false by apply/negbTE; rewrite -ltnNge.
case: ifP => _; first by case: (subset_class C); lra.
case: ifP => _; first by lra.
by case: ifP => _; lra.
Qed.

End pgl27_leakage_ramp.
