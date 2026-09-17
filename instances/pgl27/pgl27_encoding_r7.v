(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_encoding_r7: the deck pair whose recovery threshold is seven         *)
(*                                                                            *)
(* The deck pair. Written as the card code sitting at position 0, 1, ..., 7:  *)
(*                                                                            *)
(*   secret false: deck 0 1 2 3 4 5 6 7                                       *)
(*   secret true:  deck 0 1 2 4 3 5 6 7                                       *)
(*                                                                            *)
(* The cards 0, 1, 2 and 3 are the hearts (is_heart, pgl27_orbit.v), so the   *)
(* deck of the secret false holds its hearts at the positions {0, 1, 2, 3}    *)
(* and the deck of the secret true holds them at {0, 1, 2, 4}. Those two      *)
(* four-subsets have different cross-ratio classes, which is what makes the   *)
(* pair encode a bit: the secret is the class of the heart positions, and the *)
(* decoder orbit_class reads it back.                                         *)
(*                                                                            *)
(* This is the pair the development started from, orbit_encode of             *)
(* pgl27_orbit.v, and the pair the earlier leakage results were stated at.    *)
(*                                                                            *)
(* Census. Over the 336 shuffles, the number of restrictions to a reveal set  *)
(* that both decks produce is                                                 *)
(*                                                                            *)
(*   three positions {0,1,2}          336                                     *)
(*   harmonic four {0,1,2,3}           96                                     *)
(*   equianharmonic four {0,1,2,4}     72                                     *)
(*   five positions                    36                                     *)
(*   six positions                     12                                     *)
(*   seven positions                    0                                     *)
(*                                                                            *)
(* The count first vanishes at seven positions, so seven is the recovery      *)
(* threshold of this pair: a coalition of seven positions always determines   *)
(* the secret before the reveal, and a coalition of six does not.             *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   code_deal_r7 == the two decks as nat code tables                         *)
(*   pgl27_encoding_r7 == the deck pair as an encoding                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_r7_views_uniq_* == at each representative reveal set, neither      *)
(*     deck's view list repeats an entry, so its collision count is a         *)
(*     set-intersection cardinality                                           *)
(*   pgl27_r7_collisions_* == the six collision counts above                  *)
(*   pgl27_r7_collision_ratio_* == the identities (336 - m) * q = p * 336     *)
(*     giving the non-collision fraction of each representative as a rational *)
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

(** code_deal_r7 — the two decks of this pair as tables of the eight card
    codes: the identity table for the secret false and the transposition of
    the codes 3 and 4 for the secret true. It is the form in which the
    collision census evaluates the pair. *)
Definition code_deal_r7 (b : bool) : seq nat :=
  if b then [:: 0; 1; 2; 4; 3; 5; 6; 7] else code_id.

(** pgl27_r7_codeE — the nat table of this pair is the tuple deck read code by
    code. It is the agreement field of the encoding record, and the step that
    turns a count over nat tables into a count over shuffles. *)
Lemma pgl27_r7_codeE (s : bool) :
  code_deal_r7 s = [seq val x | x <- orbit_encode s].
Proof. by case: s. Qed.

(** pgl27_encoding_r7 — the deck pair 0 1 2 3 4 5 6 7 against
    0 1 2 4 3 5 6 7, as an encoding. Its decks are the orbit encoder of
    pgl27_orbit.v, so every leakage value proved at this encoding is a value
    of the scheme the rest of the development executes. *)
Definition pgl27_encoding_r7 : pgl27_encoding :=
  @PGL27Encoding orbit_encode code_deal_r7
    orbit_encode_deck orbit_encodeK pgl27_r7_codeE.

(* -------------------------------------------------------------------------- *)
(* Repetition-freeness of the view lists at the representative reveal sets.   *)
(* -------------------------------------------------------------------------- *)

(** pgl27_r7_views_uniq_harmonic — at {0, 1, 2, 3} neither deck's view list
    repeats an entry. The collision count below is therefore the cardinality
    of an intersection of view sets, which is what makes it a probability
    after division by 336. *)
Lemma pgl27_r7_views_uniq_harmonic :
  uniq (code_views (enc_code pgl27_encoding_r7) false rep_harmonic)
  && uniq (code_views (enc_code pgl27_encoding_r7) true rep_harmonic).
Proof. by vm_compute. Qed.

(** pgl27_r7_views_uniq_equianharmonic — at {0, 1, 2, 4} neither deck's view
    list repeats an entry. The collision count below is a set-intersection
    cardinality. *)
Lemma pgl27_r7_views_uniq_equianharmonic :
  uniq (code_views (enc_code pgl27_encoding_r7) false rep_equianharmonic)
  && uniq (code_views (enc_code pgl27_encoding_r7) true rep_equianharmonic).
Proof. by vm_compute. Qed.

(** pgl27_r7_views_uniq_five — at {0, 1, 2, 3, 4} neither deck's view list
    repeats an entry. The collision count below is a set-intersection
    cardinality. *)
Lemma pgl27_r7_views_uniq_five :
  uniq (code_views (enc_code pgl27_encoding_r7) false rep_five)
  && uniq (code_views (enc_code pgl27_encoding_r7) true rep_five).
Proof. by vm_compute. Qed.

(** pgl27_r7_views_uniq_six — at {0, 1, 2, 3, 4, 5} neither deck's view list
    repeats an entry. The collision count below is a set-intersection
    cardinality. *)
Lemma pgl27_r7_views_uniq_six :
  uniq (code_views (enc_code pgl27_encoding_r7) false rep_six)
  && uniq (code_views (enc_code pgl27_encoding_r7) true rep_six).
Proof. by vm_compute. Qed.

(** pgl27_r7_views_uniq_seven — at {0, ..., 6} neither deck's view list
    repeats an entry. The collision count below is a set-intersection
    cardinality. *)
Lemma pgl27_r7_views_uniq_seven :
  uniq (code_views (enc_code pgl27_encoding_r7) false rep_seven)
  && uniq (code_views (enc_code pgl27_encoding_r7) true rep_seven).
Proof. by vm_compute. Qed.

(** pgl27_r7_views_uniq_three — at {0, 1, 2} neither deck's view list repeats
    an entry. Sharp 3-transitivity makes a shuffle determined by where it
    sends three positions, so the census route applies at three positions too
    and gives the value zero the privacy threshold already gives. *)
Lemma pgl27_r7_views_uniq_three :
  uniq (code_views (enc_code pgl27_encoding_r7) false [:: 0; 1; 2])
  && uniq (code_views (enc_code pgl27_encoding_r7) true [:: 0; 1; 2]).
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* The collision counts.                                                      *)
(* -------------------------------------------------------------------------- *)

(** pgl27_r7_collisions_harmonic — the four-subset {0, 1, 2, 3} has 96
    collisions. 96 of the 336 shuffles leave a coalition holding those four
    positions unable to tell the two decks apart. *)
Lemma pgl27_r7_collisions_harmonic :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_harmonic = 96.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_equianharmonic — the four-subset {0, 1, 2, 4} has 72
    collisions. 72 of the 336 shuffles leave a coalition holding those four
    positions unable to tell the two decks apart. *)
Lemma pgl27_r7_collisions_equianharmonic :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_equianharmonic = 72.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_five — the five-subset {0, 1, 2, 3, 4} has 36
    collisions. 36 of the 336 shuffles leave a coalition holding five
    positions unable to tell the two decks apart. *)
Lemma pgl27_r7_collisions_five :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_five = 36.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_six — the six-subset {0, 1, 2, 3, 4, 5} has 12
    collisions. 12 of the 336 shuffles leave a coalition holding six positions
    unable to tell the two decks apart. *)
Lemma pgl27_r7_collisions_six :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_six = 12.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_seven — the seven-subset {0, ..., 6} has no collision.
    Seven positions determine the deck under every shuffle, which is the
    recovery threshold of this pair. *)
Lemma pgl27_r7_collisions_seven :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_seven = 0.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_three — the three-subset {0, 1, 2} has 336 collisions.
    Every shuffle leaves a coalition of three positions unable to tell the two
    decks apart, which is the privacy threshold read as a count. *)
Lemma pgl27_r7_collisions_three :
  pgl27_collisions (enc_code pgl27_encoding_r7) [:: 0; 1; 2] = 336.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_harmonic_neq — the four-subset {0, 1, 2, 3} does not
    have 97 collisions. The count of the harmonic class separates 96 from the
    neighbouring value, so the leakage value it gives is not an artefact of a
    rounding. *)
Lemma pgl27_r7_collisions_harmonic_neq :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_harmonic != 97.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_equianharmonic_neq — the four-subset {0, 1, 2, 4} does
    not have 96 collisions. The two four-position classes of this pair have
    different counts, so a coalition of four positions leaks an amount that
    depends on which class it occupies. *)
Lemma pgl27_r7_collisions_equianharmonic_neq :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_equianharmonic != 96.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_five_neq — the five-subset {0, 1, 2, 3, 4} does not
    have 35 collisions. The count at five positions separates 36 from the
    neighbouring value. *)
Lemma pgl27_r7_collisions_five_neq :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_five != 35.
Proof. by vm_compute. Qed.

(** pgl27_r7_collisions_six_neq — the six-subset {0, 1, 2, 3, 4, 5} has a
    collision. Six positions still leave the two decks confusable under some
    shuffle, so the recovery threshold of this pair is above six. *)
Lemma pgl27_r7_collisions_six_neq :
  pgl27_collisions (enc_code pgl27_encoding_r7) rep_six != 0.
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* The collision counts as exact rationals.                                   *)
(* -------------------------------------------------------------------------- *)

(** pgl27_r7_collision_ratio_harmonic — (336 - 96) / 336 = 5 / 7. Five
    sevenths of the shuffles leave a harmonic four-position coalition able to
    tell the two decks apart. *)
Lemma pgl27_r7_collision_ratio_harmonic :
  ((336 - pgl27_collisions (enc_code pgl27_encoding_r7) rep_harmonic)
     * 7)%N = (5 * 336)%N.
Proof. by vm_compute. Qed.

(** pgl27_r7_collision_ratio_equianharmonic — (336 - 72) / 336 = 11 / 14.
    Eleven fourteenths of the shuffles leave an equianharmonic four-position
    coalition able to tell the two decks apart. *)
Lemma pgl27_r7_collision_ratio_equianharmonic :
  ((336 - pgl27_collisions (enc_code pgl27_encoding_r7) rep_equianharmonic)
     * 14)%N = (11 * 336)%N.
Proof. by vm_compute. Qed.

(** pgl27_r7_collision_ratio_five — (336 - 36) / 336 = 25 / 28. Twenty-five
    twenty-eighths of the shuffles leave a five-position coalition able to
    tell the two decks apart. *)
Lemma pgl27_r7_collision_ratio_five :
  ((336 - pgl27_collisions (enc_code pgl27_encoding_r7) rep_five)
     * 28)%N = (25 * 336)%N.
Proof. by vm_compute. Qed.

(** pgl27_r7_collision_ratio_six — (336 - 12) / 336 = 27 / 28. Twenty-seven
    twenty-eighths of the shuffles leave a six-position coalition able to tell
    the two decks apart. *)
Lemma pgl27_r7_collision_ratio_six :
  ((336 - pgl27_collisions (enc_code pgl27_encoding_r7) rep_six)
     * 28)%N = (27 * 336)%N.
Proof. by vm_compute. Qed.
