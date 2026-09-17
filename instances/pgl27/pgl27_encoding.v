(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_encoding: the deck pair of the eight-card PGL(2,7) scheme as a       *)
(*                 parameter                                                  *)
(*                                                                            *)
(* The scheme deals one of two fixed decks according to a uniform Boolean     *)
(* secret, then shuffles by a uniform element of PGL(2,7). The shuffle group  *)
(* and the decoder are fixed by the geometry, but the two decks are a free    *)
(* choice, and how much a coalition above the privacy threshold learns        *)
(* depends on that choice. This file makes the choice a parameter: a deck     *)
(* pair is a record, and the results below are the part of the leakage        *)
(* argument that holds at every deck pair.                                    *)
(*                                                                            *)
(* The record pgl27_encoding has five fields.                                 *)
(*                                                                            *)
(*   enc_deck : bool -> 8.-tuple 'I_8                                         *)
(*     The deck dealt to each secret value, as the card sitting at each of    *)
(*     the eight positions. This is the arrangement the protocol hands to the *)
(*     shuffle, so it is the only place where the deck pair enters an         *)
(*     execution.                                                             *)
(*                                                                            *)
(*   enc_code : bool -> seq nat                                               *)
(*     The same two decks as lists of card codes. It carries no information   *)
(*     the deck does not already carry, and is a field rather than a derived  *)
(*     definition so that an instance supplies a literal list of numerals:    *)
(*     the collision census runs by vm_compute over 336 rows of such lists,   *)
(*     and a tuple projection inside every row would be evaluated 336 times.  *)
(*                                                                            *)
(*   enc_deck_ok : forall s, deck_ok (enc_deck s)                             *)
(*     Each deck deals eight distinct cards. This is the premise of threshold *)
(*     privacy: a coalition below the threshold learns nothing because the    *)
(*     sharply 3-transitive shuffle sends any three distinct cards anywhere,  *)
(*     which fails as soon as a deck repeats a card.                          *)
(*                                                                            *)
(*   enc_classK : forall s, orbit_class (enc_deck s) = s                      *)
(*     The deck dealt to a secret decodes back to that secret. This is        *)
(*     correctness of the scheme at this deck pair: it fixes what the secret  *)
(*     means, namely the PGL(2,7) orbit class of the four heart positions,    *)
(*     and it is what lets two different deck pairs be compared, since they   *)
(*     encode the same secret.                                                *)
(*                                                                            *)
(*   enc_codeE : forall s, enc_code s = [seq val x | x <- enc_deck s]         *)
(*     The two representations of a deck agree. It is the bridge along which  *)
(*     a count over nat tables becomes a probability over executions, and it  *)
(*     replaces the case analysis over the two fixed decks that the census    *)
(*     bridge used when the pair was fixed.                                   *)
(*                                                                            *)
(* The chain parametrised by this record runs through pgl27_table_bridge.v,  *)
(* pgl27_view_census.v and pgl27_mutual_info.v to the exact leakage of one    *)
(* reveal set, and through pgl27_leakage_transport.v to every coalition of    *)
(* the eight positions. pgl27_trace_encoding.v carries the same values onto   *)
(* the executed trace of the run. The two deck pairs are                      *)
(* pgl27_encoding_r7.v and pgl27_encoding_r5.v, their closed forms            *)
(* pgl27_leakage_r7.v and pgl27_leakage_r5.v, and their comparison            *)
(* pgl27_encoding_compare.v.                                                  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_encoding == a deck pair of the eight-card scheme                   *)
(*   pgl27_enc_view R e C == the cards a coalition C sees before the reveal   *)
(*                           under the deck pair e, and ord0 elsewhere        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   enc_code_nthE == the code list and the deck agree position by position   *)
(*   pgl27_enc_view_indep == a coalition of at most three positions has a     *)
(*     view independent of the secret, at every deck pair                     *)
(*   pgl27_enc_view_leakage_le == leakage is monotone in the coalition, at    *)
(*     every deck pair                                                        *)
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
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_profile pgl27_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

(** pgl27_encoding — a pair of distinct-card decks, one per secret value,
    together with its nat code table and the proof that the decoder returns
    the secret the deck was dealt for. It is the only datum of the eight-card
    scheme that the geometry leaves free, and the leakage above the privacy
    threshold is a function of it. *)
Record pgl27_encoding := PGL27Encoding {
  enc_deck : bool -> 8.-tuple 'I_8;
  enc_code : bool -> seq nat;
  enc_deck_ok : forall s, deck_ok (enc_deck s);
  enc_classK : forall s, orbit_class (enc_deck s) = s;
  enc_codeE : forall s, enc_code s = [seq val x | x <- enc_deck s]
}.

(** enc_code_nthE — the code table and the deck name the same card at every
    position. It is the pointwise form of the agreement field, and the step
    along which a restricted census row becomes a coalition's observation. *)
Lemma enc_code_nthE (e : pgl27_encoding) (s : bool) (i : 'I_8) :
  nth 0 (enc_code e s) i = val (tnth (enc_deck e s) i).
Proof.
rewrite enc_codeE (nth_map ord0); last by rewrite size_tuple.
by rewrite (tnth_nth ord0).
Qed.

Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** pgl27_enc_view — the card values a coalition C observes at a sample of the
    uniform secret and the uniform shuffle, under the deck pair e, and ord0
    outside C. It is the pre-reveal observable of the coalition: it holds the
    cards at the coalition's own positions and refuses to hold the shuffle
    that produced them, which is what makes the leakage question nontrivial. *)
Definition pgl27_enc_view (R : realType) (e : pgl27_encoding)
    (C : {set 'I_8}) : {RV (pgl27P R) -> {ffun 'I_8 -> 'I_8}} :=
  coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
    (enc_deck e) C.

(** pgl27_enc_view_indep — a coalition of at most three positions has a view
    independent of the secret, at every deck pair. Three is the privacy
    threshold of the eight-card scheme, and it is fixed by sharp
    3-transitivity of PGL(2,7) together with distinctness of the cards, so no
    choice of deck pair can move it. *)
Lemma pgl27_enc_view_indep (R : realType) (e : pgl27_encoding)
    (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  pgl27P R |= pgl27_enc_view R e C _|_ pgl27_secret R.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R
  (fdist_uniform card_bool) pgl27_G_pos (enc_deck e) C HC (enc_deck_ok e)).
Qed.

Local Open Scope entropy_scope.

(** pgl27_enc_view_leakage_le — a coalition never shares less with the secret
    than one of its subcoalitions, at every deck pair. Holding more positions
    cannot hide information, so a value proved at one coalition size bounds
    every larger size from below. *)
Lemma pgl27_enc_view_leakage_le (R : realType) (e : pgl27_encoding)
    (C C' : {set 'I_8}) :
  C' \subset C ->
  `I(pgl27_secret R ; pgl27_enc_view R e C')
  <= `I(pgl27_secret R ; pgl27_enc_view R e C).
Proof.
move=> HCC'.
exact: (@coalition_view_mutual_info_le (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool) pgl27_G_pos
  (enc_deck e) C C' HCC').
Qed.
