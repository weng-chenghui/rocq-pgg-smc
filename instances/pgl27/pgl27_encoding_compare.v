(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_encoding_compare: the two deck pairs of the eight-card scheme side   *)
(*                         by side                                            *)
(*                                                                            *)
(* The shuffle group, the decoder and the privacy threshold of the eight-card *)
(* scheme are fixed by the geometry of PGL(2,7). The deck pair is not, and    *)
(* pgl27_leakage_r7.v and pgl27_leakage_r5.v compute the exact leakage at two *)
(* choices of it. This file puts the two closed forms next to each other and  *)
(* reads off what the geometry fixes and what the choice of decks fixes.      *)
(*                                                                            *)
(* The two pairs deal the same deck to the secret false and differ in the     *)
(* deck they deal to the secret true, by the transposition of the cards 6 and *)
(* 7. Both true decks hold their hearts at the positions 0, 1, 2 and 4, so    *)
(* the decoder, which reads the cross-ratio class of the heart four-subset,   *)
(* returns the same secret on both pairs. The two pairs are therefore two     *)
(* encodings of one secret, and a difference between their leakage values is  *)
(* a property of the encoding alone.                                          *)
(*                                                                            *)
(* They agree below the privacy threshold, where both leak nothing, and at    *)
(* the equianharmonic four-position coalitions, where both leak eleven        *)
(* fourteenths of a bit. They separate at the harmonic four-position          *)
(* coalitions, five sevenths against six sevenths, and at five and six        *)
(* positions, where one pair leaks twenty-five and twenty-seven               *)
(* twenty-eighths of a bit and the other already leaks the whole bit.         *)
(*                                                                            *)
(* Recovery threshold. At a fixed deck pair the coalition view determines the *)
(* secret exactly when no shuffle produces that view under both decks, which  *)
(* the census counts as a collision count of zero, and which is one full bit  *)
(* of mutual information. The recovery threshold of a fixed pair is therefore *)
(* the smallest coalition size at which the mutual information is one full    *)
(* bit: seven for the pair of pgl27_encoding_r7.v and five for the pair of    *)
(* pgl27_encoding_r5.v. The statement pgl27_seven_reveal_class of             *)
(* pgl27_recovery.v is a different claim: it quantifies over every valid deck *)
(* the dealer might use, holds independently of the deck pair, and is cited   *)
(* here rather than reproved or attributed to either pair.                    *)
(*                                                                            *)
(* Every value below is a value of the running protocol as well as of the     *)
(* coalition view, by pgl27_r7_trace_mutual_infoE and                         *)
(* pgl27_r5_trace_mutual_infoE.                                               *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_compare_heart_setE, pgl27_compare_classE == the two pairs put      *)
(*     their hearts at the same positions and decode to the same secret       *)
(*   pgl27_compare_le3E == both pairs leak nothing up to three positions      *)
(*   pgl27_compare_equianharmonicE == both pairs leak eleven fourteenths of a *)
(*     bit at an equianharmonic four-position coalition                       *)
(*   pgl27_compare_harmonicE == the pairs leak five sevenths and six sevenths *)
(*     of a bit at a harmonic four-position coalition                         *)
(*   pgl27_compare_k5E, pgl27_compare_k6E == at five and at six positions one *)
(*     pair leaks part of the bit and the other leaks all of it               *)
(*   pgl27_compare_recovery_thresholdE == the recovery thresholds of the two  *)
(*     pairs are seven and five                                               *)
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
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_secrecy.
From pgg_smc Require Import pgl27_encoding pgl27_encoding_r7 pgl27_encoding_r5.
From pgg_smc Require Import pgl27_leakage_r7 pgl27_leakage_r5.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

(* -------------------------------------------------------------------------- *)
(* The two pairs encode the same secret.                                      *)
(* -------------------------------------------------------------------------- *)

(** pgl27_compare_heart_setE — the two deck pairs hold their hearts at the
    same positions for each secret value. The decoder reads only the heart
    four-subset, so this is what makes the two pairs two encodings of one
    secret rather than two secrets. *)
Lemma pgl27_compare_heart_setE (s : bool) :
  heart_set (enc_deck pgl27_encoding_r5 s)
  = heart_set (enc_deck pgl27_encoding_r7 s).
Proof. exact: pgl27_r5_hearts. Qed.

(** pgl27_compare_classE — the two deck pairs decode to the same secret. A
    decoder that reads the heart positions returns the dealt secret on either
    pair, so a coalition holding enough positions recovers the same bit
    whichever pair the dealer uses, and the leakage values below compare like
    with like. *)
Lemma pgl27_compare_classE (s : bool) :
  orbit_class (enc_deck pgl27_encoding_r5 s)
  = orbit_class (enc_deck pgl27_encoding_r7 s).
Proof. by rewrite !enc_classK. Qed.

Section pgl27_encoding_compare.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(* -------------------------------------------------------------------------- *)
(* Where the two pairs agree.                                                 *)
(* -------------------------------------------------------------------------- *)

(** pgl27_compare_le3E — both pairs leak nothing to a coalition of at most
    three positions. Three is the privacy threshold of the eight-card scheme,
    and it comes from sharp 3-transitivity of the shuffle group together with
    distinctness of the cards, neither of which the choice of decks can
    move. *)
Lemma pgl27_compare_le3E (C : {set 'I_8}) : (#|C| <= 3)%N ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) = 0
  /\ `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 0.
Proof.
move=> HC; split.
- by rewrite pgl27_r7_viewE pgl27_r7_view_mutual_infoE HC.
- by rewrite pgl27_r5_view_mutual_infoE HC.
Qed.

(** pgl27_compare_equianharmonicE — both pairs leak eleven fourteenths of a
    bit to an equianharmonic four-position coalition. The two pairs differ by
    a transposition of two cards, and at the equianharmonic class that
    transposition leaves the number of shuffles producing one view under both
    decks unchanged. *)
Lemma pgl27_compare_equianharmonicE (C : {set 'I_8}) :
  #|C| = 4 -> subset_class C ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) = 11%:R / 14%:R
  /\ `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C)
     = 11%:R / 14%:R.
Proof.
move=> H4 Hsc; split.
- by rewrite pgl27_r7_viewE pgl27_r7_view_mutual_infoE H4 Hsc.
- by rewrite pgl27_r5_view_mutual_infoE H4 Hsc.
Qed.

(* -------------------------------------------------------------------------- *)
(* Where the two pairs separate.                                              *)
(* -------------------------------------------------------------------------- *)

(** pgl27_compare_harmonicE — at a harmonic four-position coalition one pair
    leaks five sevenths of a bit and the other six sevenths. This is the
    smallest coalition size at which the choice of decks is visible at all,
    and it is also where the two pairs put the minimum of their leakage on
    opposite cross-ratio classes. *)
Lemma pgl27_compare_harmonicE (C : {set 'I_8}) :
  #|C| = 4 -> subset_class C = false ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) = 5%:R / 7%:R
  /\ `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 6%:R / 7%:R.
Proof.
move=> H4 Hsc; split.
- by rewrite pgl27_r7_viewE pgl27_r7_view_mutual_infoE H4 Hsc.
- by rewrite pgl27_r5_view_mutual_infoE H4 Hsc.
Qed.

(** pgl27_compare_k5E — at five positions one pair leaks twenty-five
    twenty-eighths of a bit and the other the whole bit. Five positions
    already determine the secret at one pair and leave it undetermined on some
    executions at the other, which is the gap between the two recovery
    thresholds. *)
Lemma pgl27_compare_k5E (C : {set 'I_8}) : #|C| = 5 ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) = 25%:R / 28%:R
  /\ `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 1.
Proof.
move=> H5; split.
- by rewrite pgl27_r7_viewE pgl27_r7_view_mutual_infoE H5.
- by rewrite pgl27_r5_view_mutual_infoE H5.
Qed.

(** pgl27_compare_k6E — at six positions one pair leaks twenty-seven
    twenty-eighths of a bit and the other the whole bit. Six is the second and
    last size inside the gap between the two recovery thresholds. *)
Lemma pgl27_compare_k6E (C : {set 'I_8}) : #|C| = 6 ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) = 27%:R / 28%:R
  /\ `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 1.
Proof.
move=> H6; split.
- by rewrite pgl27_r7_viewE pgl27_r7_view_mutual_infoE H6.
- by rewrite pgl27_r5_view_mutual_infoE H6.
Qed.

(** pgl27_compare_recovery_thresholdE — the recovery thresholds of the two
    pairs are seven and five. Both pairs have the privacy threshold three, so
    the choice of decks moves only the size at which a coalition recovers the
    secret, and moves it by two positions out of eight. *)
Lemma pgl27_compare_recovery_thresholdE (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) == 1)
    = (7 <= #|C|)%N
  /\ (`I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) == 1)
    = (5 <= #|C|)%N.
Proof.
split; last exact: pgl27_r5_view_determines.
by rewrite pgl27_r7_viewE pgl27_r7_view_determines.
Qed.

End pgl27_encoding_compare.
