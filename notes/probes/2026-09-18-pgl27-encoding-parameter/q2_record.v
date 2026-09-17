(* PROBE Q2 (task P0, plan 2026-09-18-pgl27-encoding-parameter).
   The candidate pgl27_encoding record, with both instances built.

   Real names checked against the source:
     deck_ok    : 8.-tuple 'I_8 -> bool      (pgl27_orbit.v:94, = uniq sh)
     orbit_class: 8.-tuple 'I_8 -> bool      (pgl27_orbit.v:112)
     heart_set  : 8.-tuple 'I_8 -> {set 'I_8}(pgl27_orbit.v:98)
     orbit_encode, orbit_encodeK, orbit_encode_deck (pgl27_orbit.v:349-365)
     code_deal, code_id, code_tau            (pgl27_leakage_census.v:405,212,216)
   The agreement shape the bridge needs is pgl27_table_bridge.v:178,
     pgl27_code_deal_orbit_encodeE (b) (i) :
       nth 0 (code_deal b) i = val (tnth (orbit_encode b) i).
*)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_leakage_census.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ------------------------------------------------------------------ *)
(* The candidate record.                                               *)
(* ------------------------------------------------------------------ *)

Record pgl27_encoding := PGL27Encoding {
  enc_deck : bool -> 8.-tuple 'I_8;
  enc_code : bool -> seq nat;
  enc_deck_ok : forall s, deck_ok (enc_deck s);
  enc_classK : forall s, orbit_class (enc_deck s) = s;
  enc_codeE : forall s, enc_code s = [seq val x | x <- enc_deck s]
}.

(* Derived facts the chain needs.  They are consequences of the five
   fields, so they are lemmas and not further fields. *)

Lemma enc_code_size (e : pgl27_encoding) (s : bool) : size (enc_code e s) = 8.
Proof. by rewrite enc_codeE size_map size_tuple. Qed.

Lemma enc_code_uniq (e : pgl27_encoding) (s : bool) : uniq (enc_code e s).
Proof. by rewrite enc_codeE map_inj_uniq //; [exact: enc_deck_ok | exact: val_inj]. Qed.

(* The pointwise form used by pgl27_code_deal_orbit_encodeE. *)
Lemma enc_code_nthE (e : pgl27_encoding) (s : bool) (i : 'I_8) :
  nth 0 (enc_code e s) i = val (tnth (enc_deck e s) i).
Proof.
rewrite enc_codeE (nth_map ord0); last by rewrite size_tuple.
by rewrite (tnth_nth ord0).
Qed.

(* ------------------------------------------------------------------ *)
(* Instance _r7: the repository's pair.                                *)
(* ------------------------------------------------------------------ *)

Lemma r7_codeE (s : bool) : code_deal s = [seq val x | x <- orbit_encode s].
Proof. by case: s. Qed.

Definition enc_r7 : pgl27_encoding :=
  @PGL27Encoding orbit_encode code_deal
    orbit_encode_deck orbit_encodeK r7_codeE.

(* ------------------------------------------------------------------ *)
(* Instance _r5: false 0 1 2 3 4 5 6 7, true 0 1 2 4 3 5 7 6.          *)
(* ------------------------------------------------------------------ *)

Definition deck_r5 (b : bool) : 8.-tuple 'I_8 :=
  if b then [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
                   @Ordinal 8 4 isT; @Ordinal 8 3 isT; @Ordinal 8 5 isT;
                   @Ordinal 8 7 isT; @Ordinal 8 6 isT]
  else [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
              @Ordinal 8 3 isT; @Ordinal 8 4 isT; @Ordinal 8 5 isT;
              @Ordinal 8 6 isT; @Ordinal 8 7 isT].

Definition code_r5 (b : bool) : seq nat :=
  if b then [:: 0; 1; 2; 4; 3; 5; 7; 6] else code_id.

Lemma deck_r5_ok (s : bool) : deck_ok (deck_r5 s).
Proof. by case: s; vm_compute. Qed.

(* The two true decks have the same heart positions {0,1,2,4}, so the
   decoder cannot tell them apart.  This is the route to enc_classK for a
   new pair: pgl27_orbit.v's own orbit_classE is a Local Lemma, hence
   unavailable outside that file, and plain vm_compute on orbit_class does
   not reduce through enum 'I_8. *)
Lemma deck_r5_hearts (s : bool) :
  heart_set (deck_r5 s) = heart_set (orbit_encode s).
Proof.
apply/setP => x; rewrite !inE /is_heart.
by case: s; case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

Lemma deck_r5_classK (s : bool) : orbit_class (deck_r5 s) = s.
Proof. by rewrite /orbit_class deck_r5_hearts -/(orbit_class (orbit_encode s))
  orbit_encodeK. Qed.

Lemma r5_codeE (s : bool) : code_r5 s = [seq val x | x <- deck_r5 s].
Proof. by case: s. Qed.

Definition enc_r5 : pgl27_encoding :=
  @PGL27Encoding deck_r5 code_r5 deck_r5_ok deck_r5_classK r5_codeE.

(* ------------------------------------------------------------------ *)
(* Q2 checks: the two instances behave as the chain needs.             *)
(* ------------------------------------------------------------------ *)

(* The _r7 instance's fields are the source objects on the nose. *)
Lemma q2_r7_deck : enc_deck enc_r7 = orbit_encode.
Proof. by []. Qed.

Lemma q2_r7_code : enc_code enc_r7 = code_deal.
Proof. by []. Qed.

(* The bridge lemma of pgl27_table_bridge.v is the record's derived
   pointwise agreement at _r7. *)
Lemma q2_r7_bridge (b : bool) (i : 'I_8) :
  nth 0 (code_deal b) i = val (tnth (orbit_encode b) i).
Proof. exact: (enc_code_nthE enc_r7). Qed.

(* The _r5 nat table is the one Q1 computes with. *)
Lemma q2_r5_code_true : enc_code enc_r5 true = [:: 0; 1; 2; 4; 3; 5; 7; 6].
Proof. by []. Qed.

Lemma q2_r5_code_false : enc_code enc_r5 false = [:: 0; 1; 2; 3; 4; 5; 6; 7].
Proof. by []. Qed.

(* Decoder equality of the two encodings: the two true decks decode to the
   same class, and so do the two false decks. *)
Lemma q2_decoder_agree (s : bool) :
  orbit_class (enc_deck enc_r5 s) = orbit_class (enc_deck enc_r7 s).
Proof. by rewrite !(enc_classK). Qed.

(* Q2 side question: does orbit_class of the r5 true deck compute?
   It does not: the enum 'I_8 inside heart_set / subset_class blocks
   vm_compute, exactly as pgl27_orbit.v's Local orbit_classE anticipates. *)
Lemma q2_orbit_class_no_vm_compute :
  True.
Proof.
(* Evidence that a direct computation fails; the Fail is the claim. *)
Fail (have : orbit_class (deck_r5 true) = true by vm_compute).
by [].
Qed.

Print Assumptions enc_r5.
Print Assumptions deck_r5_classK.
Print Assumptions enc_code_nthE.
