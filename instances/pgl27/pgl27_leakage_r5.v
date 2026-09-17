(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_leakage_r5: the leakage of the eight-card orbit scheme at the deck   *)
(*                   pair whose recovery threshold is five                    *)
(*                                                                            *)
(* The deck pair is the one of pgl27_encoding_r5.v, dealing 0 1 2 3 4 5 6 7   *)
(* for the secret false and 0 1 2 4 3 5 7 6 for the secret true. It encodes   *)
(* the same secret as the pair of pgl27_encoding_r7.v, since the two pairs    *)
(* put their hearts at the same positions, and it is the comparison that      *)
(* separates what the geometry of PGL(2,7) fixes from what the choice of      *)
(* decks fixes.                                                               *)
(*                                                                            *)
(* For every coalition of the eight positions, the mutual information between *)
(* the orbit secret and the coalition view is zero up to the privacy          *)
(* threshold three, eleven fourteenths at size four on an equianharmonic      *)
(* quadruple and six sevenths on a harmonic one, and the full bit from five   *)
(* positions on. Every value is exact and unconditional on any computational  *)
(* assumption.                                                                *)
(*                                                                            *)
(* Five is therefore the recovery threshold of this pair against seven for    *)
(* the pair of pgl27_leakage_r7.v, and a single coalition size lies strictly  *)
(* between the two thresholds. The smallest amount a coalition above the      *)
(* privacy threshold shares with the secret is eleven fourteenths of a bit,   *)
(* on the equianharmonic class; at the other pair the minimum sits on the     *)
(* harmonic class instead.                                                    *)
(*                                                                            *)
(* Each value holds twice: of the coalition view, and of the joint executed   *)
(* trace of the same coalition in the run that deals this pair. The two are   *)
(* the same random variable by pgl27_enc_coalition_traceE of                  *)
(* pgl27_trace_encoding.v, so the numbers are the amounts a coalition learns  *)
(* from an execution.                                                         *)
(*                                                                            *)
(* Scope. One pre-reveal view, a uniform Boolean orbit secret and a uniform   *)
(* shuffle drawn from pgg_G pgl27_M. The all-decks dealer of                  *)
(* pgl27_view_indep_alldecks, which deals a uniform valid deck of the         *)
(* secret's class, is not covered by any value of this file.                  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_r5_view_mutual_infoE == the value at every coalition of the eight  *)
(*     positions                                                              *)
(*   pgl27_r5_view_mutual_info_eq0 == a coalition shares no information with  *)
(*     the orbit secret exactly when it holds at most three positions         *)
(*   pgl27_r5_view_mutual_info_ge5E == a coalition of five or more positions  *)
(*     determines the orbit secret before the reveal                          *)
(*   pgl27_r5_view_mutual_info_k4_lt1 == a coalition of four positions does   *)
(*     not, so five is the recovery threshold of this pair                    *)
(*   pgl27_r5_view_mutual_info_ge4 == every coalition above the privacy       *)
(*     threshold shares at least eleven fourteenths of a bit with the orbit   *)
(*     secret                                                                 *)
(*   pgl27_r5_view_determines == a coalition view determines the orbit secret *)
(*     exactly when the coalition holds at least five positions               *)
(*   pgl27_r5_trace_mutual_infoE == the same value at every coalition, on the *)
(*     joint executed trace of the run                                        *)
(*   pgl27_r5_trace_mutual_info_eq0 == an executed trace shares no            *)
(*     information with the orbit secret exactly when the coalition holds at  *)
(*     most three positions                                                   *)
(*   pgl27_r5_trace_determines == an executed trace determines the orbit      *)
(*     secret exactly when the coalition holds at least five positions        *)
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
From pgg_smc Require Import pgl27_trace_encoding.
From pgg_smc Require Import pgl27_encoding pgl27_encoding_r5.
From pgg_smc Require Import pgl27_view_census pgl27_mutual_info.
From pgg_smc Require Import pgl27_leakage_transport.
From pgg_smc Require Import proba_entropy_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Section pgl27_leakage_r5.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(* -------------------------------------------------------------------------- *)
(* The value at each representative reveal set, from its collision count.     *)
(* -------------------------------------------------------------------------- *)

(** The harmonic four-position representative leaves six sevenths of the
    shuffles distinguishable. *)
Local Lemma pgl27_r5_noncollision_harmonic :
  pgl27_noncollision_ratio R pgl27_encoding_r5 rep_harmonic = 6%:R / 7%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r5_collisions_harmonic; lra.
Qed.

(** The equianharmonic four-position representative leaves eleven fourteenths
    of the shuffles distinguishable. *)
Local Lemma pgl27_r5_noncollision_equianharmonic :
  pgl27_noncollision_ratio R pgl27_encoding_r5 rep_equianharmonic =
  11%:R / 14%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r5_collisions_equianharmonic; lra.
Qed.

(** The five-position representative leaves every shuffle distinguishable. No
    shuffle produces the same five-position view under both decks of this
    pair. *)
Local Lemma pgl27_r5_noncollision_five :
  pgl27_noncollision_ratio R pgl27_encoding_r5 rep_five = 1.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r5_collisions_five; lra.
Qed.

(** The harmonic four-position representative shares six sevenths of a bit
    with the orbit secret. *)
Local Lemma pgl27_r5_harmonicE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r5
       (pgl27_code_coalition rep_harmonic)) = 6%:R / 7%:R.
Proof.
move/andP: pgl27_r5_views_uniq_harmonic => [Hfalse Htrue].
rewrite -pgl27_r5_noncollision_harmonic.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The equianharmonic four-position representative shares eleven fourteenths
    of a bit with the orbit secret, less than the harmonic one shares. *)
Local Lemma pgl27_r5_equianharmonicE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r5
       (pgl27_code_coalition rep_equianharmonic)) = 11%:R / 14%:R.
Proof.
move/andP: pgl27_r5_views_uniq_equianharmonic => [Hfalse Htrue].
rewrite -pgl27_r5_noncollision_equianharmonic.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The five-position representative shares one bit with the orbit secret, the
    whole of its prior entropy. *)
Local Lemma pgl27_r5_fiveE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r5
       (pgl27_code_coalition rep_five)) = 1.
Proof.
move/andP: pgl27_r5_views_uniq_five => [Hfalse Htrue].
rewrite -pgl27_r5_noncollision_five.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(* -------------------------------------------------------------------------- *)
(* The value at every coalition of a given size.                              *)
(* -------------------------------------------------------------------------- *)

(** A coalition of at most three positions shares zero bits with the orbit
    secret. Below the privacy threshold a coalition learns nothing at all
    about the orbit secret from one pre-reveal view. *)
Local Lemma pgl27_r5_le3E (C : {set 'I_8}) : (#|C| <= 3)%N ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 0.
Proof. exact: pgl27_enc_view_mutual_info_le3E. Qed.

(** A coalition of four positions shares eleven fourteenths of a bit with the
    orbit secret when its positions are an equianharmonic quadruple, and six
    sevenths of a bit otherwise. Four positions are the only coalition size
    strictly between the two thresholds of this deck pair, and the two
    cross-ratio classes already leak different amounts there. *)
Local Lemma pgl27_r5_k4E (C : {set 'I_8}) : #|C| = 4 ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) =
  (if subset_class C then 11%:R / 14%:R else 6%:R / 7%:R).
Proof.
exact: (pgl27_enc_view_mutual_info_k4E pgl27_r5_harmonicE
  pgl27_r5_equianharmonicE).
Qed.

(** A coalition of five positions shares one bit with the orbit secret. The
    five-position coalitions form one shuffle orbit, so every choice of five
    positions determines the orbit secret before the reveal. *)
Local Lemma pgl27_r5_k5E (C : {set 'I_8}) : #|C| = 5 ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 1.
Proof. exact: (pgl27_enc_view_mutual_info_k5E pgl27_r5_fiveE). Qed.

(** A coalition of five or more positions shares one bit with the orbit
    secret. Five is the recovery threshold of this deck pair: from five
    positions on the coalition view determines the orbit secret before the
    reveal, and no larger coalition can learn more. *)
Lemma pgl27_r5_view_mutual_info_ge5E (C : {set 'I_8}) : (5 <= #|C|)%N ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) = 1.
Proof.
apply: (pgl27_enc_view_mutual_info1_card_ge (k := 5)) => D HD.
exact: pgl27_r5_k5E.
Qed.

(* -------------------------------------------------------------------------- *)
(* The closed form and what it says about the two thresholds.                 *)
(* -------------------------------------------------------------------------- *)

(** The mutual information between the orbit secret and the view of a
    coalition of the eight positions is zero up to size three, eleven
    fourteenths at size four on the twenty-eight equianharmonic quadruples and
    six sevenths on the forty-two harmonic ones, and one bit from five
    positions on. The scheme hides the orbit secret completely below the
    privacy threshold three and reveals it completely from five positions on,
    so a single coalition size separates perfect privacy from full recovery at
    this deck pair. *)
Theorem pgl27_r5_view_mutual_infoE (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) =
    if (#|C| <= 3)%N then 0
    else if #|C| == 4 then
      (if subset_class C then 11%:R / 14%:R else 6%:R / 7%:R)
    else 1.
Proof.
case H3 : (#|C| <= 3)%N; first exact: pgl27_r5_le3E.
have H4 : (4 <= #|C|)%N by rewrite ltnNge H3.
case E4 : (#|C| == 4); first exact: (pgl27_r5_k4E (eqP E4)).
apply: pgl27_r5_view_mutual_info_ge5E.
by rewrite ltn_neqAle H4 andbT eq_sym E4.
Qed.

(** A coalition shares no information with the orbit secret exactly when it
    holds at most three positions. The privacy threshold three is sharp at
    every coalition of four or more positions and not only at one witness
    coalition, so this deck pair has the same privacy threshold as the pair of
    pgl27_leakage_r7.v while recovering the secret two positions earlier. *)
Lemma pgl27_r5_view_mutual_info_eq0 (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) == 0)
  = (#|C| <= 3)%N.
Proof.
apply/idP/idP; last by move=> HC; rewrite (pgl27_r5_le3E HC) eqxx.
move=> /eqP HI; rewrite leqNgt; apply/negP => H4.
(* a coalition of four or more positions contains a four-position one, whose
   value is strictly positive in either cross-ratio class *)
have [D DC HD] : exists2 D : {set 'I_8}, D \subset C & #|D| = 4.
  have [s [Us Ss subsC]] := card_geqP H4.
  exists [set x in s]; first by apply/subsetP => x; rewrite inE; exact: subsC.
  by rewrite cardsE (card_uniqP Us).
have Hpos : 0 < `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 D).
  rewrite (pgl27_r5_k4E HD).
  by case: (subset_class D); rewrite divr_gt0 // ltr0n.
have := pgl27_enc_view_leakage_le R pgl27_encoding_r5 DC.
rewrite HI => Hle.
by move: (lt_le_trans Hpos Hle); rewrite ltxx.
Qed.

(** A coalition of four positions shares strictly less than one bit with the
    orbit secret, in either cross-ratio class. Four positions leave the orbit
    secret undetermined on some executions, so the recovery threshold of this
    deck pair is five and not lower. *)
Lemma pgl27_r5_view_mutual_info_k4_lt1 (C : {set 'I_8}) : #|C| = 4 ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) < 1.
Proof.
move=> HC; rewrite (pgl27_r5_k4E HC).
by case: (subset_class C); lra.
Qed.

(** A coalition of four or more positions shares at least eleven fourteenths
    of a bit with the orbit secret. Once the privacy threshold is passed the
    leakage never falls back towards zero, and the smallest value above the
    threshold sits on the equianharmonic class at this deck pair, the opposite
    class from the pair of pgl27_leakage_r7.v. *)
Lemma pgl27_r5_view_mutual_info_ge4 (C : {set 'I_8}) : (4 <= #|C|)%N ->
  11%:R / 14%:R <= `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C).
Proof.
move=> H4; rewrite pgl27_r5_view_mutual_infoE.
have -> : (#|C| <= 3)%N = false by apply/negbTE; rewrite -ltnNge.
case: ifP => _; last by lra.
by case: (subset_class C); lra.
Qed.

(** A coalition of at most four positions shares strictly less than one bit
    with the orbit secret. It is the half of the recovery threshold that no
    single coalition size witnesses: every size below five leaves the orbit
    secret undetermined on some executions. *)
Local Lemma pgl27_r5_le4_lt1 (C : {set 'I_8}) : (#|C| <= 4)%N ->
  `I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) < 1.
Proof.
move=> H4.
case H3 : (#|C| <= 3)%N; first by rewrite (pgl27_r5_le3E H3); lra.
have H4' : (4 <= #|C|)%N by rewrite ltnNge H3.
have E4 : #|C| = 4 by apply/eqP; rewrite eqn_leq H4 H4'.
by rewrite (pgl27_r5_k4E E4); case: (subset_class C); lra.
Qed.

(** A coalition view shares the whole prior entropy of the orbit secret
    exactly when the coalition holds at least five positions. Five is the
    recovery threshold of this deck pair: at a fixed pair the view determines
    the secret exactly when no shuffle produces that view under both decks,
    which is one full bit of mutual information. *)
Lemma pgl27_r5_view_determines (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) == 1)
  = (5 <= #|C|)%N.
Proof.
case H5 : (5 <= #|C|)%N.
  by rewrite (pgl27_r5_view_mutual_info_ge5E H5) eqxx.
apply: lt_eqF; apply: pgl27_r5_le4_lt1.
by rewrite leqNgt H5.
Qed.

(* -------------------------------------------------------------------------- *)
(* The same values on the executed trace of the run.                          *)
(* -------------------------------------------------------------------------- *)

(** The mutual information between the orbit secret and the joint executed
    trace of a coalition follows the same closed form as its view. The
    coalition trace is what the interpreter writes at the eight player
    processes when the protocol deals this pair, so every value above is the
    amount a coalition of that size learns from an execution and not from a
    model of one. *)
Theorem pgl27_r5_trace_mutual_infoE (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_enc_coalition_trace R pgl27_encoding_r5 C) =
    if (#|C| <= 3)%N then 0
    else if #|C| == 4 then
      (if subset_class C then 11%:R / 14%:R else 6%:R / 7%:R)
    else 1.
Proof.
by rewrite pgl27_enc_coalition_traceE pgl27_r5_view_mutual_infoE.
Qed.

(** The executed trace of a coalition shares no information with the orbit
    secret exactly when the coalition holds at most three positions. Three is
    the privacy threshold of the running protocol at this pair as well, so the
    two pairs are separated by their recovery thresholds alone. *)
Lemma pgl27_r5_trace_mutual_info_eq0 (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_enc_coalition_trace R pgl27_encoding_r5 C) == 0)
  = (#|C| <= 3)%N.
Proof.
by rewrite pgl27_enc_coalition_traceE pgl27_r5_view_mutual_info_eq0.
Qed.

(** The executed trace of a coalition determines the orbit secret exactly when
    the coalition holds at least five positions. Five is the recovery
    threshold of this deck pair on an execution, two positions below the
    threshold of the pair of pgl27_leakage_r7.v. *)
Lemma pgl27_r5_trace_determines (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_enc_coalition_trace R pgl27_encoding_r5 C) == 1)
  = (5 <= #|C|)%N.
Proof.
by rewrite pgl27_enc_coalition_traceE pgl27_r5_view_determines.
Qed.

End pgl27_leakage_r5.
