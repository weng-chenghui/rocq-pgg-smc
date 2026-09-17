(* PROBE Q5 (task P0, plan 2026-09-18-pgl27-encoding-parameter).
   Threshold privacy at an arbitrary encoding: the |C| <= 3 independence
   statement, proved by applying the generic ttrans_view_indep_gen.
   Question: what exactly does the generic theorem ask of the encoding? *)

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
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_profile pgl27_secrecy.
From probe Require Import q2_record.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section q5_privacy.
Variable R : realType.

(* Every coalition of at most three positions has a view of the shuffled deal
   independent of the orbit secret, at any encoding.  The only premise on the
   encoding is that each of its two decks has distinct cards, which is the
   record field enc_deck_ok (deck_ok is uniq by definition). *)
Lemma enc_view_indep (e : pgl27_encoding) (C : {set 'I_8}) : (#|C| <= 3)%N ->
  (fdist_uniform card_bool) `x (`U pgl27_G_pos)
  |= coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       (enc_deck e) C
  _|_ @dealt_secret (pgg_gT pgl27_M) (pgg_G pgl27_M) R
        (fdist_uniform card_bool) pgl27_G_pos.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R
  (fdist_uniform card_bool) pgl27_G_pos (enc_deck e) C HC (enc_deck_ok e)).
Qed.

(* Leakage monotonicity in the coalition, at any encoding.  No premise. *)
Local Open Scope ring_scope.
Lemma enc_view_leakage_le (e : pgl27_encoding) (C C' : {set 'I_8}) :
  C' \subset C ->
  `I(@dealt_secret (pgg_gT pgl27_M) (pgg_G pgl27_M) R
       (fdist_uniform card_bool) pgl27_G_pos ;
     coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       (enc_deck e) C')
  <= `I(@dealt_secret (pgg_gT pgl27_M) (pgg_G pgl27_M) R
          (fdist_uniform card_bool) pgl27_G_pos ;
        coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
          pgl27_G_pos (enc_deck e) C).
Proof.
move=> HCC'.
exact: (@coalition_view_mutual_info_le (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool) pgl27_G_pos
  (enc_deck e) C C' HCC').
Qed.

(* The r5 instance of the two statements. *)
Lemma q5_r5_view_indep (C : {set 'I_8}) : (#|C| <= 3)%N ->
  (fdist_uniform card_bool) `x (`U pgl27_G_pos)
  |= coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       (enc_deck enc_r5) C
  _|_ @dealt_secret (pgg_gT pgl27_M) (pgg_G pgl27_M) R
        (fdist_uniform card_bool) pgl27_G_pos.
Proof. exact: enc_view_indep. Qed.

(* The r7 instance is the source statement pgl27_view_indep on the nose. *)
Lemma q5_r7_is_source (C : {set 'I_8}) : (#|C| <= 3)%N ->
  pgl27P R |= pgl27_view R C _|_ pgl27_secret R.
Proof. exact: (enc_view_indep enc_r7). Qed.

End q5_privacy.

Print Assumptions enc_view_indep.
Print Assumptions q5_r5_view_indep.
Print Assumptions q5_r7_is_source.
