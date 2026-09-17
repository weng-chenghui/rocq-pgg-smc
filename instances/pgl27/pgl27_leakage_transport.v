(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_leakage_transport: carrying a leakage value from one coalition to    *)
(*                          every coalition of the same shape                 *)
(*                                                                            *)
(* The exact leakage identity of pgl27_mutual_info.v computes a number at one *)
(* reveal set at a time, from a collision count. This file turns each such    *)
(* number into a statement about every coalition of the eight positions, and  *)
(* it does so once for all deck pairs: relabelling the positions of a         *)
(* coalition by a shuffle leaves its leakage unchanged, so a value proved at  *)
(* one coalition is the value of its whole orbit under the shuffle group. The *)
(* orbits are known from pgl27_leakage_census.v: one orbit at each of the     *)
(* sizes five, six and seven, and two at size four, separated by the          *)
(* cross-ratio class.                                                         *)
(*                                                                            *)
(* The transport lemmas take the value at a representative as a premise, so   *)
(* an instance file supplies its own census numbers and obtains its closed    *)
(* form. No statement here names a deck pair. Two proofs below use            *)
(* orbit_encode of pgl27_orbit.v as a witness for a fact about the eight      *)
(* positions alone.                                                           *)
(*                                                                            *)
(* Scope. One pre-reveal view, a uniform Boolean orbit secret, a uniform      *)
(* shuffle drawn from pgg_G pgl27_M, and for each secret the deck the pair    *)
(* assigns to it. The all-decks dealer of pgl27_view_indep_alldecks, which    *)
(* deals a uniform valid deck of the secret's class, is not covered.          *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_subset_class_harmonicE, pgl27_subset_class_equianharmonicE == the  *)
(*     cross-ratio class of the two four-position representatives             *)
(*   pgl27_leak_coalitionE == the coalition witnessing sharpness of the       *)
(*     privacy threshold is the harmonic four-position representative         *)
(*   pgl27_enc_view_mutual_info_imset == relabelling the positions of a       *)
(*     coalition by a shuffle leaves its leakage unchanged                    *)
(*   pgl27_secret_entropy == the prior entropy of the orbit secret is one bit *)
(*   pgl27_enc_view_mutual_info_le1 == no coalition shares more than one bit  *)
(*     with the orbit secret                                                  *)
(*   pgl27_enc_view_mutual_info_le3E == a coalition of at most three          *)
(*     positions shares zero bits with the orbit secret                       *)
(*   pgl27_enc_view_mutual_info_k4E, _k5E, _k6E, _k7E == the value at a       *)
(*     representative is the value at every coalition of that size, and of    *)
(*     that cross-ratio class at size four                                    *)
(*   pgl27_enc_view_mutual_info1_card_ge == one bit at every coalition of     *)
(*     some size k is one bit at every coalition of at least k positions      *)
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
From pgg_smc Require Import pgl27_secrecy pgl27_leakage_census pgl27_encoding.
From pgg_smc Require Import pgl27_view_census pgl27_mutual_info.
From pgg_smc Require Import proba_entropy_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

(* The block below is about the eight positions and the shuffle group alone.
   No statement and no proof in it mentions a carrier or a deck pair. *)
Section pgl27_leakage_positions.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(** pgl27_card_harmonic — the harmonic representative lists four of the eight
    positions. At size four the shuffle group has two orbits, so a
    representative's size selects the coalitions its value governs only
    together with the cross-ratio class of its positions. *)
Local Lemma pgl27_card_harmonic : #|pgl27_code_coalition rep_harmonic| = 4.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** pgl27_card_equianharmonic — the equianharmonic representative lists four
    of the eight positions. It is the second of the two four-position orbit
    classes, and carries the other of the two leakage values at that size. *)
Local Lemma pgl27_card_equianharmonic :
  #|pgl27_code_coalition rep_equianharmonic| = 4.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** pgl27_card_five — the five-position representative lists five of the eight
    positions. The five-position coalitions form one shuffle orbit, so its
    value is the value of every coalition of five positions. *)
Local Lemma pgl27_card_five : #|pgl27_code_coalition rep_five| = 5.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** pgl27_card_six — the six-position representative lists six of the eight
    positions. The six-position coalitions form one shuffle orbit, so its
    value is the value of every coalition of six positions. *)
Local Lemma pgl27_card_six : #|pgl27_code_coalition rep_six| = 6.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** pgl27_card_seven — the seven-position representative lists seven of the
    eight positions. The seven-position coalitions form one shuffle orbit, so
    its value is the value of every coalition of seven positions. *)
Local Lemma pgl27_card_seven : #|pgl27_code_coalition rep_seven| = 7.
Proof.
rewrite /pgl27_code_coalition -sum1dep_card big_mkcond /=.
by do 8 rewrite big_ord_recl; rewrite big_ord0.
Qed.

(** pgl27_subset_class_harmonicE — the four positions of the harmonic
    representative form a quadruple of cross-ratio class false. It is one of
    the two classes a four-position coalition can occupy, and which class a
    coalition occupies is the only thing besides its size that its leakage
    depends on. *)
Lemma pgl27_subset_class_harmonicE :
  subset_class (pgl27_code_coalition rep_harmonic) = false.
Proof.
have Hhs : heart_set (orbit_encode false) = pgl27_code_coalition rep_harmonic.
  apply/setP => x; rewrite /heart_set /pgl27_code_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
by rewrite -Hhs; exact: (orbit_encodeK false).
Qed.

(** pgl27_subset_class_equianharmonicE — the four positions of the
    equianharmonic representative form a quadruple of cross-ratio class true.
    It is the other of the two classes a four-position coalition can
    occupy. *)
Lemma pgl27_subset_class_equianharmonicE :
  subset_class (pgl27_code_coalition rep_equianharmonic) = true.
Proof.
have Hhs : heart_set (orbit_encode true)
         = pgl27_code_coalition rep_equianharmonic.
  apply/setP => x; rewrite /heart_set /pgl27_code_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
by rewrite -Hhs; exact: (orbit_encodeK true).
Qed.

(** pgl27_leak_coalitionE — the coalition witnessing sharpness of the privacy
    threshold is the harmonic four-position representative. The witness
    therefore lies in the cross-ratio class of orbit size 42, so its exact
    leakage is whichever of the two four-position values a deck pair gives
    that class. *)
Lemma pgl27_leak_coalitionE :
  pgl27_leak_coalition = pgl27_code_coalition rep_harmonic.
Proof.
apply/setP => x; rewrite /pgl27_code_coalition /pgl27_leak_coalition !inE.
by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

End pgl27_leakage_positions.

Section pgl27_leakage_transport.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(** pgl27_secret_entropy — the prior entropy of the orbit secret is one bit.
    It is the whole of what any coalition can learn about the orbit secret,
    and the unit in which every leakage value is measured. *)
Lemma pgl27_secret_entropy : `H `p_(pgl27_secret R) = 1.
Proof.
by rewrite pgl27_secret_uniform entropy_uniform card_bool realType_ln.log2.
Qed.

(** mutual_info_RV_le_entropy — the mutual information between two random
    variables is at most the entropy of the first. It bounds the leakage of a
    coalition by the prior entropy of the orbit secret, which is what makes
    one bit the largest value the scheme can reach. *)
Local Lemma mutual_info_RV_le_entropy (U TS TV : finType) (Q : R.-fdist U)
    (S : {RV Q -> TS}) (V : {RV Q -> TV}) : `I(S ; V) <= `H `p_S.
Proof.
by rewrite mutual_info_RVE lerBlDr lerDl; exact: centropy_RV_ge0.
Qed.

Variable e : pgl27_encoding.

(** pgl27_enc_view_mutual_info_imset — moving a coalition from the positions C
    to the positions g C, for a shuffle g of the group, leaves the mutual
    information between the orbit secret and the coalition view unchanged.
    What a coalition learns depends on its positions only through their orbit
    under the shuffle group, so one representative of each orbit fixes the
    leakage of every coalition in it. *)
Lemma pgl27_enc_view_mutual_info_imset (g : pgg_gT pgl27_M) (C : {set 'I_8}) :
  g \in pgg_G pgl27_M ->
  `I(pgl27_secret R ; pgl27_enc_view R e (g @: C))
  = `I(pgl27_secret R ; pgl27_enc_view R e C).
Proof.
exact: (@coalition_view_mutual_info_imset (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool)
  pgl27_G_pos (enc_deck e) g C).
Qed.

(** pgl27_enc_view_mutual_info_le1 — no coalition shares more than one bit
    with the orbit secret. One pre-reveal view never tells a coalition more
    than the orbit secret itself carries, whatever its positions and whatever
    the deck pair. *)
Lemma pgl27_enc_view_mutual_info_le1 (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_enc_view R e C) <= 1.
Proof.
by rewrite -pgl27_secret_entropy; exact: mutual_info_RV_le_entropy.
Qed.

(** pgl27_enc_view_mutual_info_le3E — a coalition of at most three positions
    shares zero bits with the orbit secret. Below the privacy threshold a
    coalition learns nothing at all about the orbit secret from one pre-reveal
    view, at every deck pair. *)
Lemma pgl27_enc_view_mutual_info_le3E (C : {set 'I_8}) : (#|C| <= 3)%N ->
  `I(pgl27_secret R ; pgl27_enc_view R e C) = 0.
Proof.
move=> HC.
rewrite mutual_info_RVE.
by rewrite (inde_cond_entropy (pgl27_enc_view_indep R e HC)) subrr.
Qed.

(** pgl27_enc_view_mutual_info_k4E — the two values at the four-position
    representatives are the values at every four-position coalition, according
    to its cross-ratio class. The first coalition size above the privacy
    threshold already leaks, by an amount that depends on the class of the
    four positions and not only on their number. *)
Lemma pgl27_enc_view_mutual_info_k4E (C : {set 'I_8}) (v0 v1 : R) :
  `I(pgl27_secret R ;
     pgl27_enc_view R e (pgl27_code_coalition rep_harmonic)) = v0 ->
  `I(pgl27_secret R ;
     pgl27_enc_view R e (pgl27_code_coalition rep_equianharmonic)) = v1 ->
  #|C| = 4 ->
  `I(pgl27_secret R ; pgl27_enc_view R e C) =
  (if subset_class C then v1 else v0).
Proof.
move=> H0 H1 HC.
(* the two four-position orbits are the fibers of subset_class, and the
   representative of each is transported onto C by a shuffle *)
case HcC : (subset_class C).
  have [g [gG ->]] := iffLR (subset_class_orbit
    (pgl27_code_coalition rep_equianharmonic) C pgl27_card_equianharmonic HC)
    (etrans pgl27_subset_class_equianharmonicE (esym HcC)).
  rewrite (pgl27_enc_view_mutual_info_imset _ gG); exact: H1.
have [g [gG ->]] := iffLR (subset_class_orbit
  (pgl27_code_coalition rep_harmonic) C pgl27_card_harmonic HC)
  (etrans pgl27_subset_class_harmonicE (esym HcC)).
rewrite (pgl27_enc_view_mutual_info_imset _ gG); exact: H0.
Qed.

(** pgl27_enc_view_mutual_info_k5E — the value at the five-position
    representative is the value at every five-position coalition. The
    five-position coalitions form one shuffle orbit, so no choice of five
    positions leaks more than another. *)
Lemma pgl27_enc_view_mutual_info_k5E (C : {set 'I_8}) (v : R) :
  `I(pgl27_secret R ;
     pgl27_enc_view R e (pgl27_code_coalition rep_five)) = v ->
  #|C| = 5 -> `I(pgl27_secret R ; pgl27_enc_view R e C) = v.
Proof.
move=> Hv HC.
have [g gG ->] := pgl27_five_subset_orbit pgl27_card_five HC.
rewrite (pgl27_enc_view_mutual_info_imset _ gG); exact: Hv.
Qed.

(** pgl27_enc_view_mutual_info_k6E — the value at the six-position
    representative is the value at every six-position coalition. The
    six-position coalitions form one shuffle orbit. *)
Lemma pgl27_enc_view_mutual_info_k6E (C : {set 'I_8}) (v : R) :
  `I(pgl27_secret R ;
     pgl27_enc_view R e (pgl27_code_coalition rep_six)) = v ->
  #|C| = 6 -> `I(pgl27_secret R ; pgl27_enc_view R e C) = v.
Proof.
move=> Hv HC.
have [g gG ->] := pgl27_six_subset_orbit pgl27_card_six HC.
rewrite (pgl27_enc_view_mutual_info_imset _ gG); exact: Hv.
Qed.

(** pgl27_enc_view_mutual_info_k7E — the value at the seven-position
    representative is the value at every seven-position coalition. The
    seven-position coalitions form one shuffle orbit. *)
Lemma pgl27_enc_view_mutual_info_k7E (C : {set 'I_8}) (v : R) :
  `I(pgl27_secret R ;
     pgl27_enc_view R e (pgl27_code_coalition rep_seven)) = v ->
  #|C| = 7 -> `I(pgl27_secret R ; pgl27_enc_view R e C) = v.
Proof.
move=> Hv HC.
have [g gG ->] := pgl27_seven_subset_orbit pgl27_card_seven HC.
rewrite (pgl27_enc_view_mutual_info_imset _ gG); exact: Hv.
Qed.

(** pgl27_enc_view_mutual_info1_card_ge — if every coalition of k positions
    determines the orbit secret, so does every coalition of at least k
    positions. It is the one step of the argument where a lower bound and an
    upper bound meet: monotonicity along a k-position subcoalition gives one
    bit from below, and the prior entropy of the secret gives one bit from
    above. *)
Lemma pgl27_enc_view_mutual_info1_card_ge (k : nat) (C : {set 'I_8}) :
  (forall D : {set 'I_8}, #|D| = k ->
     `I(pgl27_secret R ; pgl27_enc_view R e D) = 1) ->
  (k <= #|C|)%N -> `I(pgl27_secret R ; pgl27_enc_view R e C) = 1.
Proof.
move=> Hk HC.
have [D DC HD] : exists2 D : {set 'I_8}, D \subset C & #|D| = k.
  have [s [Us Ss subsC]] := card_geqP HC.
  exists [set x in s]; first by apply/subsetP => x; rewrite inE; exact: subsC.
  by rewrite cardsE (card_uniqP Us).
apply: le_anti; apply/andP; split; first exact: pgl27_enc_view_mutual_info_le1.
rewrite -(Hk D HD).
exact: pgl27_enc_view_leakage_le.
Qed.

End pgl27_leakage_transport.
