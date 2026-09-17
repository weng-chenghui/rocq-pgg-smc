(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_encoding_r5: the deck pair whose recovery threshold is five          *)
(*                                                                            *)
(* The deck pair. Written as the card code sitting at position 0, 1, ..., 7:  *)
(*                                                                            *)
(*   secret false: deck 0 1 2 3 4 5 6 7                                       *)
(*   secret true:  deck 0 1 2 4 3 5 7 6                                       *)
(*                                                                            *)
(* The cards 0, 1, 2 and 3 are the hearts (is_heart, pgl27_orbit.v), so the   *)
(* deck of the secret false holds its hearts at the positions {0, 1, 2, 3}    *)
(* and the deck of the secret true holds them at {0, 1, 2, 4}. Those are the  *)
(* same two heart four-subsets as the pair of pgl27_encoding_r7.v, so the two *)
(* pairs encode the same secret and the decoder orbit_class cannot tell them  *)
(* apart. The pairs differ only in where each deck puts the cards 6 and 7,    *)
(* which the decoder never reads and a coalition of enough positions does.    *)
(*                                                                            *)
(* Census. Over the 336 shuffles, the number of restrictions to a reveal set  *)
(* that both decks produce is                                                 *)
(*                                                                            *)
(*   three positions {0,1,2}          336                                     *)
(*   harmonic four {0,1,2,3}           48                                     *)
(*   equianharmonic four {0,1,2,4}     72                                     *)
(*   five positions                     0                                     *)
(*   six positions                      0                                     *)
(*   seven positions                    0                                     *)
(*                                                                            *)
(* The count first vanishes at five positions, so five is the recovery        *)
(* threshold of this pair, against seven for the pair of pgl27_encoding_r7.v. *)
(* The leakage of this pair rises from zero at three positions to one full    *)
(* bit at five, with a single intermediate size. At that one intermediate     *)
(* size the two cross-ratio classes leak different amounts, 48 collisions on  *)
(* the harmonic class against 72 on the equianharmonic.                       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   deck_r5 == the two decks as tuples of cards                              *)
(*   code_table_r5 == the same two decks as nat code tables                   *)
(*   pgl27_encoding_r5 == the deck pair as an encoding                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_r5_hearts == the two decks of this pair hold their hearts at the   *)
(*     same positions as the decks of pgl27_encoding_r7.v                     *)
(*   pgl27_r5_views_uniq_* == at the two four-position representatives and    *)
(*     the five-position one, neither deck's view list repeats an entry, so   *)
(*     its collision count is a set-intersection cardinality                  *)
(*   pgl27_r5_collisions_* == the six collision counts above                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit.
From pgg_smc Require Import pgl27_leakage_census pgl27_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** deck_r5 — the two decks of this pair as arrangements of the eight cards:
    0 1 2 3 4 5 6 7 for the secret false and 0 1 2 4 3 5 7 6 for the secret
    true. It is the arrangement the protocol hands to the shuffle. *)
Definition deck_r5 (b : bool) : 8.-tuple 'I_8 :=
  if b then [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
                   @Ordinal 8 4 isT; @Ordinal 8 3 isT; @Ordinal 8 5 isT;
                   @Ordinal 8 7 isT; @Ordinal 8 6 isT]
  else [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
              @Ordinal 8 3 isT; @Ordinal 8 4 isT; @Ordinal 8 5 isT;
              @Ordinal 8 6 isT; @Ordinal 8 7 isT].

(** code_table_r5 — the same two decks as tables of the eight card codes. It
    is the form in which the collision census evaluates the pair. *)
Definition code_table_r5 (b : bool) : seq nat :=
  if b then [:: 0; 1; 2; 4; 3; 5; 7; 6] else code_id.

(** pgl27_r5_deck_ok — each deck of this pair deals eight distinct cards. It
    is the premise under which a coalition below the privacy threshold learns
    nothing. *)
Local Lemma pgl27_r5_deck_ok (s : bool) : deck_ok (deck_r5 s).
Proof. by case: s; vm_compute. Qed.

(** pgl27_r5_hearts — each deck of this pair holds its hearts at the same
    positions as the deck of pgl27_encoding_r7.v for the same secret. The two
    pairs are therefore interchangeable as far as the decoder is concerned,
    and differ only in what a coalition above the privacy threshold sees. *)
Lemma pgl27_r5_hearts (s : bool) :
  heart_set (deck_r5 s) = heart_set (orbit_encode s).
Proof.
apply/setP => x; rewrite !inE /is_heart.
by case: s; case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

(** pgl27_r5_classK — the deck dealt to a secret decodes back to that secret.
    It is correctness of the scheme at this pair, and it holds because the
    heart positions agree with those of pgl27_encoding_r7.v rather than by any
    computation: the decoder reads the cross-ratio class of the heart
    four-subset through an enumeration that does not reduce. *)
Lemma pgl27_r5_classK (s : bool) : orbit_class (deck_r5 s) = s.
Proof.
by rewrite /orbit_class pgl27_r5_hearts -/(orbit_class (orbit_encode s))
  orbit_encodeK.
Qed.

(** pgl27_r5_codeE — the nat table of this pair is the tuple deck read code by
    code. It is the agreement field of the encoding record, and the step that
    turns a count over nat tables into a count over shuffles. *)
Local Lemma pgl27_r5_codeE (s : bool) :
  code_table_r5 s = [seq val x | x <- deck_r5 s].
Proof. by case: s. Qed.

(** pgl27_encoding_r5 — the deck pair 0 1 2 3 4 5 6 7 against
    0 1 2 4 3 5 7 6, as an encoding. It encodes the same secret as the pair of
    pgl27_encoding_r7.v and leaks differently above the privacy threshold, so
    it separates what the geometry fixes from what the choice of decks fixes. *)
Definition pgl27_encoding_r5 : pgl27_encoding :=
  @PGL27Encoding deck_r5 code_table_r5
    pgl27_r5_deck_ok pgl27_r5_classK pgl27_r5_codeE.

(* -------------------------------------------------------------------------- *)
(* Repetition-freeness of the view lists at the representative reveal sets.   *)
(* -------------------------------------------------------------------------- *)

(** pgl27_r5_views_uniq_harmonic — at {0, 1, 2, 3} neither deck's view list
    repeats an entry. The collision count below is therefore the cardinality
    of an intersection of view sets, which is what makes it a probability
    after division by 336. *)
Lemma pgl27_r5_views_uniq_harmonic :
  uniq (code_views (enc_code pgl27_encoding_r5) false rep_harmonic)
  && uniq (code_views (enc_code pgl27_encoding_r5) true rep_harmonic).
Proof. by vm_compute. Qed.

(** pgl27_r5_views_uniq_equianharmonic — at {0, 1, 2, 4} neither deck's view
    list repeats an entry. The collision count below is a set-intersection
    cardinality. *)
Lemma pgl27_r5_views_uniq_equianharmonic :
  uniq (code_views (enc_code pgl27_encoding_r5) false rep_equianharmonic)
  && uniq (code_views (enc_code pgl27_encoding_r5) true rep_equianharmonic).
Proof. by vm_compute. Qed.

(** pgl27_r5_views_uniq_five — at {0, 1, 2, 3, 4} neither deck's view list
    repeats an entry. The collision count below is a set-intersection
    cardinality. *)
Lemma pgl27_r5_views_uniq_five :
  uniq (code_views (enc_code pgl27_encoding_r5) false rep_five)
  && uniq (code_views (enc_code pgl27_encoding_r5) true rep_five).
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* The collision counts.                                                      *)
(* -------------------------------------------------------------------------- *)

(** pgl27_r5_collisions_harmonic — the four-subset {0, 1, 2, 3} has 48
    collisions. 48 of the 336 shuffles leave a coalition holding those four
    positions unable to tell the two decks apart, half as many as the pair of
    pgl27_encoding_r7.v leaves. *)
Lemma pgl27_r5_collisions_harmonic :
  pgl27_collisions (enc_code pgl27_encoding_r5) rep_harmonic = 48.
Proof. by vm_compute. Qed.

(** pgl27_r5_collisions_equianharmonic — the four-subset {0, 1, 2, 4} has 72
    collisions. 72 of the 336 shuffles leave a coalition holding those four
    positions unable to tell the two decks apart, as many as the pair of
    pgl27_encoding_r7.v leaves at the same class. *)
Lemma pgl27_r5_collisions_equianharmonic :
  pgl27_collisions (enc_code pgl27_encoding_r5) rep_equianharmonic = 72.
Proof. by vm_compute. Qed.

(** pgl27_r5_collisions_five — the five-subset {0, 1, 2, 3, 4} has no
    collision. Five positions determine the deck under every shuffle, which is
    the recovery threshold of this pair. *)
Lemma pgl27_r5_collisions_five :
  pgl27_collisions (enc_code pgl27_encoding_r5) rep_five = 0.
Proof. by vm_compute. Qed.

(* rep_five, rep_six and rep_seven are nested as literal lists, and a
   collision at a larger reveal set restricts to a collision at a smaller one,
   so the two counts below already follow from pgl27_r5_collisions_five. They
   are stated separately because the census table quotes all six rows. *)

(** pgl27_r5_collisions_six — the six-subset {0, 1, 2, 3, 4, 5} has no
    collision. Six positions determine the deck under every shuffle. *)
Lemma pgl27_r5_collisions_six :
  pgl27_collisions (enc_code pgl27_encoding_r5) rep_six = 0.
Proof. by vm_compute. Qed.

(** pgl27_r5_collisions_seven — the seven-subset {0, ..., 6} has no collision.
    Seven positions determine the deck under every shuffle. *)
Lemma pgl27_r5_collisions_seven :
  pgl27_collisions (enc_code pgl27_encoding_r5) rep_seven = 0.
Proof. by vm_compute. Qed.

(** pgl27_r5_collisions_three — the three-subset {0, 1, 2} has 336 collisions.
    Every shuffle leaves a coalition of three positions unable to tell the two
    decks apart, which is the privacy threshold read as a count. *)
Lemma pgl27_r5_collisions_three :
  pgl27_collisions (enc_code pgl27_encoding_r5) [:: 0; 1; 2] = 336.
Proof. by vm_compute. Qed.
