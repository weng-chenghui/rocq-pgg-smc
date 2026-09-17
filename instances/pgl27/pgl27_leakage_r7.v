(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_leakage_r7: the leakage of the eight-card orbit scheme at the deck   *)
(*                   pair whose recovery threshold is seven                   *)
(*                                                                            *)
(* The deck pair is the one of pgl27_encoding_r7.v, dealing 0 1 2 3 4 5 6 7   *)
(* for the secret false and 0 1 2 4 3 5 6 7 for the secret true. It is the    *)
(* pair the rest of the development executes, so the values below are the     *)
(* leakage of the scheme as it stands.                                        *)
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
(* Seven is therefore the recovery threshold of this pair: a coalition of six *)
(* positions still leaves the secret undetermined on some executions, and a   *)
(* coalition of seven never does. Three is the privacy threshold, and the     *)
(* smallest amount a coalition above it shares with the secret is five        *)
(* sevenths of a bit, on the harmonic class.                                  *)
(*                                                                            *)
(* Each value holds twice: of the coalition view, and of the joint executed   *)
(* trace of the same coalition in the run of the protocol. The two are the    *)
(* same random variable by pgl27_coalition_trace_E of pgl27_trace.v, so the   *)
(* numbers are the amounts a coalition learns from an execution.              *)
(*                                                                            *)
(* Scope. One pre-reveal view, a uniform Boolean orbit secret and a uniform   *)
(* shuffle drawn from pgg_G pgl27_M. The all-decks dealer of                  *)
(* pgl27_view_indep_alldecks, which deals a uniform valid deck of the         *)
(* secret's class, is not covered by any value of this file.                  *)
(*                                                                            *)
(* The file joins three statements of pgl27_secrecy.v. The independence of a  *)
(* coalition view of at most three positions from the orbit secret            *)
(* (pgl27_view_indep) becomes the value zero; the monotonicity of the mutual  *)
(* information under coalition inclusion (pgl27_view_leakage_le) carries the  *)
(* seven-position value to the whole deck; and the single four-position       *)
(* coalition of strictly positive mutual information (pgl27_view_dep_k4,      *)
(* pgl27_view_leak_k4) becomes the exact value five sevenths there, and an    *)
(* equivalence between vanishing mutual information and coalition size at     *)
(* most three for every coalition.                                            *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_r7_viewE == the coalition view at this deck pair is the coalition  *)
(*     view of pgl27_secrecy.v                                                *)
(*   pgl27_r7_view_mutual_infoE == the value at every coalition of the eight  *)
(*     positions                                                              *)
(*   pgl27_r7_view_mutual_info_eq0 == a coalition shares no information with  *)
(*     the orbit secret exactly when it holds at most three positions         *)
(*   pgl27_r7_view_mutual_info_ge7E == a coalition of seven or eight          *)
(*     positions determines the orbit secret before the reveal                *)
(*   pgl27_r7_view_mutual_info_k6_lt1 == a coalition of six positions does    *)
(*     not, so seven is the recovery threshold of this pair                   *)
(*   pgl27_r7_view_mutual_info_ge4 == every coalition above the privacy       *)
(*     threshold shares at least five sevenths of a bit with the orbit secret *)
(*   pgl27_r7_view_mutual_info_leak_coalitionE == the four heart positions of *)
(*     the identity deal share five sevenths of a bit with the orbit secret   *)
(*   pgl27_r7_view_determines == a coalition view determines the orbit secret *)
(*     exactly when the coalition holds at least seven positions              *)
(*   pgl27_r7_trace_mutual_infoE == the same value at every coalition, on the *)
(*     joint executed trace of the run                                        *)
(*   pgl27_r7_trace_mutual_info_eq0 == an executed trace shares no            *)
(*     information with the orbit secret exactly when the coalition holds at  *)
(*     most three positions                                                   *)
(*   pgl27_r7_trace_determines == an executed trace determines the orbit      *)
(*     secret exactly when the coalition holds at least seven positions       *)
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
From pgg_smc Require Import pgl27_trace pgl27_trace_encoding.
From pgg_smc Require Import pgl27_encoding pgl27_encoding_r7.
From pgg_smc Require Import pgl27_view_census pgl27_mutual_info.
From pgg_smc Require Import pgl27_leakage_transport.
From pgg_smc Require Import proba_entropy_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Section pgl27_leakage_r7.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(** The coalition view at this deck pair is the coalition view of
    pgl27_secrecy.v. The values below are therefore values of the scheme the
    rest of the development runs, and not of a separate model of it. *)
Lemma pgl27_r7_viewE (C : {set 'I_8}) :
  pgl27_enc_view R pgl27_encoding_r7 C = pgl27_view R C.
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(* The value at each representative reveal set, from its collision count.     *)
(* -------------------------------------------------------------------------- *)

(** The harmonic four-position representative leaves five sevenths of the
    shuffles distinguishable. *)
Local Lemma pgl27_r7_noncollision_harmonic :
  pgl27_noncollision_ratio R pgl27_encoding_r7 rep_harmonic = 5%:R / 7%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r7_collisions_harmonic; lra.
Qed.

(** The equianharmonic four-position representative leaves eleven fourteenths
    of the shuffles distinguishable. *)
Local Lemma pgl27_r7_noncollision_equianharmonic :
  pgl27_noncollision_ratio R pgl27_encoding_r7 rep_equianharmonic =
  11%:R / 14%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r7_collisions_equianharmonic; lra.
Qed.

(** The five-position representative leaves twenty-five twenty-eighths of the
    shuffles distinguishable. *)
Local Lemma pgl27_r7_noncollision_five :
  pgl27_noncollision_ratio R pgl27_encoding_r7 rep_five = 25%:R / 28%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r7_collisions_five; lra.
Qed.

(** The six-position representative leaves twenty-seven twenty-eighths of the
    shuffles distinguishable. *)
Local Lemma pgl27_r7_noncollision_six :
  pgl27_noncollision_ratio R pgl27_encoding_r7 rep_six = 27%:R / 28%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r7_collisions_six; lra.
Qed.

(** The seven-position representative leaves every shuffle distinguishable.
    No shuffle produces the same seven-position view under both decks. *)
Local Lemma pgl27_r7_noncollision_seven :
  pgl27_noncollision_ratio R pgl27_encoding_r7 rep_seven = 1.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_r7_collisions_seven; lra.
Qed.

(** The harmonic four-position representative shares five sevenths of a bit
    with the orbit secret. *)
Local Lemma pgl27_r7_harmonicE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r7
       (pgl27_code_coalition rep_harmonic)) = 5%:R / 7%:R.
Proof.
move/andP: pgl27_r7_views_uniq_harmonic => [Hfalse Htrue].
rewrite -pgl27_r7_noncollision_harmonic.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The equianharmonic four-position representative shares eleven fourteenths
    of a bit with the orbit secret. *)
Local Lemma pgl27_r7_equianharmonicE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r7
       (pgl27_code_coalition rep_equianharmonic)) = 11%:R / 14%:R.
Proof.
move/andP: pgl27_r7_views_uniq_equianharmonic => [Hfalse Htrue].
rewrite -pgl27_r7_noncollision_equianharmonic.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The five-position representative shares twenty-five twenty-eighths of a
    bit with the orbit secret. *)
Local Lemma pgl27_r7_fiveE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r7
       (pgl27_code_coalition rep_five)) = 25%:R / 28%:R.
Proof.
move/andP: pgl27_r7_views_uniq_five => [Hfalse Htrue].
rewrite -pgl27_r7_noncollision_five.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The six-position representative shares twenty-seven twenty-eighths of a
    bit with the orbit secret. *)
Local Lemma pgl27_r7_sixE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r7
       (pgl27_code_coalition rep_six)) = 27%:R / 28%:R.
Proof.
move/andP: pgl27_r7_views_uniq_six => [Hfalse Htrue].
rewrite -pgl27_r7_noncollision_six.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The seven-position representative shares one bit with the orbit secret,
    the whole prior entropy of the secret. *)
Local Lemma pgl27_r7_sevenE :
  `I(pgl27_secret R ;
     pgl27_enc_view R pgl27_encoding_r7
       (pgl27_code_coalition rep_seven)) = 1.
Proof.
move/andP: pgl27_r7_views_uniq_seven => [Hfalse Htrue].
rewrite -pgl27_r7_noncollision_seven.
apply: pgl27_view_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(* -------------------------------------------------------------------------- *)
(* The value at every coalition of a given size.                              *)
(* -------------------------------------------------------------------------- *)

(** A coalition of at most three positions shares zero bits with the orbit
    secret. Below the privacy threshold a coalition learns nothing at all
    about the orbit secret from one pre-reveal view. *)
Local Lemma pgl27_r7_le3E (C : {set 'I_8}) : (#|C| <= 3)%N ->
  `I(pgl27_secret R ; pgl27_view R C) = 0.
Proof.
move=> HC; rewrite -pgl27_r7_viewE.
exact: pgl27_enc_view_mutual_info_le3E.
Qed.

(** A coalition of four positions shares eleven fourteenths of a bit with the
    orbit secret when its positions are an equianharmonic quadruple, and five
    sevenths of a bit otherwise. The first size above the privacy threshold
    already leaks, by an amount that depends on the cross-ratio class of the
    four positions and not only on their number. *)
Local Lemma pgl27_r7_k4E (C : {set 'I_8}) : #|C| = 4 ->
  `I(pgl27_secret R ; pgl27_view R C) =
  (if subset_class C then 11%:R / 14%:R else 5%:R / 7%:R).
Proof.
move=> HC; rewrite -pgl27_r7_viewE.
exact: (pgl27_enc_view_mutual_info_k4E pgl27_r7_harmonicE
  pgl27_r7_equianharmonicE HC).
Qed.

(** A coalition of five positions shares twenty-five twenty-eighths of a bit
    with the orbit secret. The five-position coalitions form one shuffle
    orbit, so no choice of five positions leaks more than another. *)
Local Lemma pgl27_r7_k5E (C : {set 'I_8}) : #|C| = 5 ->
  `I(pgl27_secret R ; pgl27_view R C) = 25%:R / 28%:R.
Proof.
move=> HC; rewrite -pgl27_r7_viewE.
exact: (pgl27_enc_view_mutual_info_k5E pgl27_r7_fiveE HC).
Qed.

(** A coalition of six positions shares twenty-seven twenty-eighths of a bit
    with the orbit secret. The value is still below one bit, so six of the
    eight positions leave the orbit secret undetermined on some
    executions. *)
Local Lemma pgl27_r7_k6E (C : {set 'I_8}) : #|C| = 6 ->
  `I(pgl27_secret R ; pgl27_view R C) = 27%:R / 28%:R.
Proof.
move=> HC; rewrite -pgl27_r7_viewE.
exact: (pgl27_enc_view_mutual_info_k6E pgl27_r7_sixE HC).
Qed.

(** A coalition of seven positions shares one bit with the orbit secret, the
    whole of its prior entropy. Seven of the eight positions determine the
    orbit secret before the reveal. *)
Local Lemma pgl27_r7_k7E (C : {set 'I_8}) : #|C| = 7 ->
  `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC; rewrite -pgl27_r7_viewE.
exact: (pgl27_enc_view_mutual_info_k7E pgl27_r7_sevenE HC).
Qed.

(** A coalition of seven or eight positions shares one bit with the orbit
    secret. Seven is the recovery threshold of this deck pair: from seven
    positions on the coalition view determines the orbit secret before the
    reveal, and no larger coalition can learn more. *)
Lemma pgl27_r7_view_mutual_info_ge7E (C : {set 'I_8}) : (7 <= #|C|)%N ->
  `I(pgl27_secret R ; pgl27_view R C) = 1.
Proof.
move=> HC; rewrite -pgl27_r7_viewE.
apply: (pgl27_enc_view_mutual_info1_card_ge (k := 7)) => // D HD.
by rewrite pgl27_r7_viewE; exact: pgl27_r7_k7E.
Qed.

(* -------------------------------------------------------------------------- *)
(* The closed form and what it says about the two thresholds.                 *)
(* -------------------------------------------------------------------------- *)

(** The mutual information between the orbit secret and the view of a
    coalition of the eight positions is zero up to size three, eleven
    fourteenths at size four on the twenty-eight equianharmonic quadruples
    and five sevenths on the forty-two harmonic ones, twenty-five
    twenty-eighths at five, twenty-seven twenty-eighths at six, and one bit
    from seven positions on. The scheme hides the orbit secret completely
    below the privacy threshold three and reveals it completely from seven
    positions on, and between those two sizes it leaks a known exact amount
    rather than an amount bounded only from above. *)
Theorem pgl27_r7_view_mutual_infoE (C : {set 'I_8}) :
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
case H3 : (#|C| <= 3)%N; first exact: pgl27_r7_le3E.
have H4 : (4 <= #|C|)%N by rewrite ltnNge H3.
case E4 : (#|C| == 4); first exact: (pgl27_r7_k4E (eqP E4)).
have H5 := step 4 H4 E4.
case E5 : (#|C| == 5); first exact: (pgl27_r7_k5E (eqP E5)).
have H6 := step 5 H5 E5.
case E6 : (#|C| == 6); first exact: (pgl27_r7_k6E (eqP E6)).
exact: (pgl27_r7_view_mutual_info_ge7E (step 6 H6 E6)).
Qed.

(** A coalition shares no information with the orbit secret exactly when it
    holds at most three positions. The privacy threshold three is sharp at
    every coalition of four or more positions and not only at one witness
    coalition, so no four of the eight positions are information-free. *)
Lemma pgl27_r7_view_mutual_info_eq0 (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_view R C) == 0) = (#|C| <= 3)%N.
Proof.
apply/idP/idP; last by move=> HC; rewrite (pgl27_r7_le3E HC) eqxx.
move=> /eqP HI; rewrite leqNgt; apply/negP => H4.
(* a coalition of four or more positions contains a four-position one, whose
   value is strictly positive in either cross-ratio class *)
have [D DC HD] : exists2 D : {set 'I_8}, D \subset C & #|D| = 4.
  have [s [Us Ss subsC]] := card_geqP H4.
  exists [set x in s]; first by apply/subsetP => x; rewrite inE; exact: subsC.
  by rewrite cardsE (card_uniqP Us).
have Hpos : 0 < `I(pgl27_secret R ; pgl27_view R D).
  rewrite (pgl27_r7_k4E HD).
  by case: (subset_class D); rewrite divr_gt0 // ltr0n.
have := pgl27_view_leakage_le R DC.
rewrite HI => Hle.
by move: (lt_le_trans Hpos Hle); rewrite ltxx.
Qed.

(** A coalition of six positions shares strictly less than one bit with the
    orbit secret. Six positions leave the orbit secret undetermined on some
    executions, so the recovery threshold of this deck pair is seven and not
    lower. *)
Lemma pgl27_r7_view_mutual_info_k6_lt1 (C : {set 'I_8}) : #|C| = 6 ->
  `I(pgl27_secret R ; pgl27_view R C) < 1.
Proof.
by move=> HC; rewrite (pgl27_r7_k6E HC); lra.
Qed.

(** The four heart positions of the identity deal share five sevenths of a bit
    with the orbit secret. This is the exact value at the coalition that
    witnesses sharpness of the privacy threshold three, where the threshold
    statements give only strict positivity. *)
Lemma pgl27_r7_view_mutual_info_leak_coalitionE :
  `I(pgl27_secret R ; pgl27_view R pgl27_leak_coalition) = 5%:R / 7%:R.
Proof.
rewrite pgl27_leak_coalitionE -pgl27_r7_viewE.
exact: pgl27_r7_harmonicE.
Qed.

(** A coalition of four or more positions shares at least five sevenths of a
    bit with the orbit secret. Once the privacy threshold is passed the
    leakage never falls back towards zero, so the smallest value above the
    threshold, which this pair reaches on the harmonic class, is a lower
    bound for every larger coalition. *)
Lemma pgl27_r7_view_mutual_info_ge4 (C : {set 'I_8}) : (4 <= #|C|)%N ->
  5%:R / 7%:R <= `I(pgl27_secret R ; pgl27_view R C).
Proof.
move=> H4; rewrite pgl27_r7_view_mutual_infoE.
have -> : (#|C| <= 3)%N = false by apply/negbTE; rewrite -ltnNge.
case: ifP => _; first by case: (subset_class C); lra.
case: ifP => _; first by lra.
by case: ifP => _; lra.
Qed.

(** A coalition of at most six positions shares strictly less than one bit
    with the orbit secret. It is the half of the recovery threshold that no
    single coalition size witnesses: every size below seven leaves the orbit
    secret undetermined on some executions. *)
Local Lemma pgl27_r7_le6_lt1 (C : {set 'I_8}) : (#|C| <= 6)%N ->
  `I(pgl27_secret R ; pgl27_view R C) < 1.
Proof.
move=> H6.
case H3 : (#|C| <= 3)%N; first by rewrite (pgl27_r7_le3E H3); lra.
have H4 : (4 <= #|C|)%N by rewrite ltnNge H3.
case E4 : (#|C| == 4).
  by rewrite (pgl27_r7_k4E (eqP E4)); case: (subset_class C); lra.
have H5 : (5 <= #|C|)%N by rewrite ltn_neqAle H4 andbT eq_sym E4.
case E5 : (#|C| == 5); first by rewrite (pgl27_r7_k5E (eqP E5)); lra.
have H6' : (6 <= #|C|)%N by rewrite ltn_neqAle H5 andbT eq_sym E5.
have E6 : #|C| = 6 by apply/eqP; rewrite eqn_leq H6 H6'.
by rewrite (pgl27_r7_k6E E6); lra.
Qed.

(** A coalition view shares the whole prior entropy of the orbit secret
    exactly when the coalition holds at least seven positions. Seven is the
    recovery threshold of this deck pair: at a fixed pair the view determines
    the secret exactly when no shuffle produces that view under both decks,
    which is one full bit of mutual information. *)
Lemma pgl27_r7_view_determines (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_view R C) == 1) = (7 <= #|C|)%N.
Proof.
case H7 : (7 <= #|C|)%N.
  by rewrite (pgl27_r7_view_mutual_info_ge7E H7) eqxx.
apply: lt_eqF; apply: pgl27_r7_le6_lt1.
by rewrite leqNgt H7.
Qed.

(* -------------------------------------------------------------------------- *)
(* The same values on the executed trace of the run.                          *)
(* -------------------------------------------------------------------------- *)

(** The mutual information between the orbit secret and the joint executed
    trace of a coalition follows the same closed form as its view. The
    coalition trace is what the interpreter writes at the eight player
    processes when the protocol runs, so every value above is the amount a
    coalition of that size learns from an execution and not from a model of
    one. *)
Theorem pgl27_r7_trace_mutual_infoE (C : {set 'I_8}) :
  `I(pgl27_secret R ; pgl27_coalition_trace R C) =
    if (#|C| <= 3)%N then 0
    else if #|C| == 4 then
      (if subset_class C then 11%:R / 14%:R else 5%:R / 7%:R)
    else if #|C| == 5 then 25%:R / 28%:R
    else if #|C| == 6 then 27%:R / 28%:R
    else 1.
Proof.
by rewrite pgl27_coalition_trace_E pgl27_r7_view_mutual_infoE.
Qed.

(** The executed trace of a coalition shares no information with the orbit
    secret exactly when the coalition holds at most three positions. Three is
    the privacy threshold of the running protocol, and not only of the view
    the leakage argument is stated about. *)
Lemma pgl27_r7_trace_mutual_info_eq0 (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_coalition_trace R C) == 0) = (#|C| <= 3)%N.
Proof.
by rewrite pgl27_coalition_trace_E pgl27_r7_view_mutual_info_eq0.
Qed.

(** The executed trace of a coalition determines the orbit secret exactly when
    the coalition holds at least seven positions. Seven is the recovery
    threshold of this deck pair on an execution, and six seats of the running
    protocol still leave the orbit secret undetermined. *)
Lemma pgl27_r7_trace_determines (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_coalition_trace R C) == 1) = (7 <= #|C|)%N.
Proof.
by rewrite pgl27_coalition_trace_E pgl27_r7_view_determines.
Qed.

End pgl27_leakage_r7.
