(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_recovery: the sharp recovery threshold of the twelve-card scheme    *)
(*                                                                            *)
(* A valid deck holds six hearts, so eleven revealed colours leave the        *)
(* twelfth forced by the count: eleven colours determine the heart set and    *)
(* hence the chirality. Ten never do. Each Steiner system covers every        *)
(* five-subset of positions exactly once, so the mirror block through five    *)
(* points of a hexad block is a second block meeting it in exactly those      *)
(* five, and two decks carrying those two heart sets agree in colour off the  *)
(* two positions where the blocks differ; 2-transitivity carries that pair    *)
(* of positions to any other. With the privacy threshold five and the         *)
(* six-position leak (psl211_secrecy.v) the ramp reads: private to five,      *)
(* leak at six, ambiguous through ten, determined at eleven, decoder reads    *)
(* twelve.                                                                    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_eleven_reveal_set    == six-subsets agreeing off one position     *)
(*                                  are equal                                 *)
(*   psl211_eleven_reveal_class  == eleven colours determine the chirality    *)
(*   psl211_ten_reveal_ambiguous == ten colours never determine it            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action div.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import psl211_blocks psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* Eleven colours determine the heart set.                                    *)
(* -------------------------------------------------------------------------- *)

(** psl211_eleven_reveal_set — under a fixed count of hearts the twelfth
    colour is forced by the other eleven. The colour-layer pigeonhole,
    constraining colours alone and never the cards beneath them. *)
Lemma psl211_eleven_reveal_set (H H' : {set 'I_12}) (j : 'I_12) :
  #|H| = 6 -> #|H'| = 6 ->
  (forall i, i != j -> (i \in H') = (i \in H)) -> H' = H.
Proof.
move=> H6 H'6 Hoff.
have Hd : H' :\ j = H :\ j.
  by apply/setP => i; rewrite !in_setD1; case: (eqVneq i j) => //= ij;
     rewrite Hoff.
have Hc : (j \in H') + #|H' :\ j| = (j \in H) + #|H :\ j|.
  by rewrite -!(cardsD1 j) H6 H'6.
have Hj : (j \in H') = (j \in H).
  by move: Hc; rewrite Hd => /addIn /(congr1 odd) /=; case: (j \in H');
     case: (j \in H).
apply/setP => i; have [->|ij] := eqVneq i j; first exact: Hj.
exact: Hoff.
Qed.

(* A block of either Steiner system has six positions, so the heart set of a
   valid deck does. *)
Local Lemma block_card6 (S : {set 'I_12}) : psl211_subset_valid S -> #|S| = 6.
Proof.
have key (tbl : seq (seq nat)) :
    psl211_tbl_ok tbl -> S \in psl211_sets_of tbl -> #|S| = 6.
  move=> Hok; rewrite inE => /hasP[R HR /eqP <-].
  apply: psl211_block_card6; exact: (allP (psl211_tbl_ok_asc6 Hok) _ HR).
case/orP; [exact: key psl211_tbl_ok_mirrorT
         | exact: key psl211_tbl_ok_hexadT].
Qed.

(** psl211_eleven_reveal_class — two valid decks whose cards have the same
    colour off one position carry the same chirality, so a coalition holding
    eleven of the twelve colours reconstructs the secret. *)
Lemma psl211_eleven_reveal_class (s s' : bool) (sh sh' : 12.-tuple 'I_12)
    (j : 'I_12) :
  psl211_orbit_valid s sh -> psl211_orbit_valid s' sh' ->
  (forall i, i != j ->
     psl211_is_heart (tnth sh' i) = psl211_is_heart (tnth sh i)) ->
  s' = s.
Proof.
move=> [_ [Hval Hcl]] [_ [Hval' Hcl']] Hoff.
have E : psl211_heart_set sh' = psl211_heart_set sh.
  apply: (@psl211_eleven_reveal_set _ _ j).
  - exact: block_card6 Hval.
  - exact: block_card6 Hval'.
  - move=> i ij; rewrite !inE; exact: Hoff.
by rewrite -Hcl -Hcl' /psl211_orbit_class E.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ten colours never determine the chirality.                                 *)
(* -------------------------------------------------------------------------- *)

(* vm_compute cannot reduce enum 'I_12, so the ground distinctness check of
   the witness deck goes through the literal enumeration, as psl211_orbit.v
   does for the encoders. *)
Local Definition ord12_enum : seq 'I_12 :=
  [:: @Ordinal 12 0 isT; @Ordinal 12 1 isT; @Ordinal 12 2 isT;
      @Ordinal 12 3 isT; @Ordinal 12 4 isT; @Ordinal 12 5 isT;
      @Ordinal 12 6 isT; @Ordinal 12 7 isT; @Ordinal 12 8 isT;
      @Ordinal 12 9 isT; @Ordinal 12 10 isT; @Ordinal 12 11 isT].

(* The twelve positions in order, as a literal reduction may consume. *)
Local Lemma enum_ord12 : enum 'I_12 = ord12_enum.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(* Position from a natural number, by reduction modulo twelve; restated
   because psl211_orbit.v's copy is Local there. *)
Local Definition Imod (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).

(* The mirror block through the five positions 1, 3, 7, 10, 11 of the hexad
   row psl211_rep_list false = [0; 1; 3; 7; 10; 11]; it is unique by
   psl211_design5_mirrorT. It holds position 2 where the hexad row holds
   position 0, so the two blocks differ at 0 and at 2 only. *)
Local Definition mirror_swap_row : seq nat := [:: 1; 2; 3; 7; 10; 11].

(* Position to card of a deck whose hearts sit on mirror_swap_row: the
   chirality-false encoder deck with the cards at positions 0 and 2
   exchanged. *)
Local Definition mirror_swap_tbl : seq nat :=
  [:: 6; 1; 0; 2; 7; 8; 9; 3; 10; 11; 4; 5].

(* The chirality-true witness deck: its hearts sit on the mirror block. *)
Local Definition mirror_swap_deck : 12.-tuple 'I_12 :=
  [tuple Imod (nth 0 mirror_swap_tbl i) | i < 12].

(* The witness deck deals twelve distinct cards. *)
Local Lemma mirror_swap_deck_ok : psl211_deck_ok mirror_swap_deck.
Proof.
by rewrite /psl211_deck_ok /mirror_swap_deck /= enum_ord12; vm_compute.
Qed.

(* The witness deck's heart positions are exactly the mirror block. *)
Local Lemma mirror_swap_heart_set :
  psl211_heart_set mirror_swap_deck = psl211_list_to_set mirror_swap_row.
Proof.
apply/setP => i; rewrite !inE tnth_mktuple.
by case: i => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(* The mirror block is a block of the mirror system, by its table row. *)
Local Lemma mirror_swap_mem :
  psl211_list_to_set mirror_swap_row \in psl211_mirror_blocks.
Proof.
rewrite inE; apply/hasP; exists mirror_swap_row; last by [].
by vm_compute.
Qed.

(* The witness deck is a valid deal of chirality true. *)
Local Lemma mirror_swap_valid : psl211_orbit_valid true mirror_swap_deck.
Proof.
split; first exact: mirror_swap_deck_ok.
split; first by rewrite /psl211_subset_valid mirror_swap_heart_set
                        mirror_swap_mem.
by rewrite /psl211_orbit_class mirror_swap_heart_set /psl211_subset_class
           mirror_swap_mem.
Qed.

(* The two witness decks hold cards of the same colour away from positions 0
   and 2, the two positions where their heart sets differ. *)
Local Lemma decks_agree_off02 (i : 'I_12) :
  i != @Ordinal 12 0 isT -> i != @Ordinal 12 2 isT ->
  psl211_is_heart (tnth (psl211_orbit_encode false) i)
  = psl211_is_heart (tnth mirror_swap_deck i).
Proof.
rewrite /psl211_orbit_encode /mirror_swap_deck !tnth_mktuple.
by case: i => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(* The card at position i of a re-dealt deck is the card the original deck
   holds at position g i. Stated at an abstract deck because tnth_mktuple
   otherwise unfolds the witness decks, which are themselves tuple
   comprehensions. *)
Local Lemma tnth_act (sh : 12.-tuple 'I_12) (g : pgg_gT psl211_M)
    (i : 'I_12) :
  tnth [tuple tnth sh (@pgg_rho psl211_M g k) | k < 12] i
  = tnth sh (@pgg_rho psl211_M g i).
Proof. by rewrite tnth_mktuple. Qed.

(* A shuffle carries a valid deck to a valid deck of the same chirality. *)
Local Lemma valid_act (s : bool) (sh : 12.-tuple 'I_12)
    (g : pgg_gT psl211_M) :
  g \in pgg_G psl211_M -> psl211_orbit_valid s sh ->
  psl211_orbit_valid s [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12].
Proof.
move=> gG [Hok [Hval Hcl]].
split; first by rewrite (psl211_deck_stable g _ gG).
split; last by rewrite (psl211_orbit_class_invariant g _ gG).
move: Hval; rewrite /psl211_subset_valid psl211_heart_set_act.
by rewrite (psl211_mirror_invariant _ _ (groupVr gG))
           (psl211_hexad_invariant _ _ (groupVr gG)).
Qed.

(** psl211_ten_reveal_ambiguous — for every two hidden positions there are
    valid decks of the two chiralities whose cards have the same colour at
    the other ten. Ten colours leave the secret undetermined, wherever the
    two hidden positions sit. *)
Lemma psl211_ten_reveal_ambiguous (p q : 'I_12) :
  p != q ->
  exists sh sh', psl211_orbit_valid true sh /\ psl211_orbit_valid false sh' /\
    (forall i, i != p -> i != q ->
       psl211_is_heart (tnth sh' i) = psl211_is_heart (tnth sh i)).
Proof.
move=> npq.
pose a0 : 'I_12 := @Ordinal 12 0 isT.
pose a2 : 'I_12 := @Ordinal 12 2 isT.
have Hpq : [tuple p; q] \in 2.-dtuple([set: 'I_12]).
  rewrite inE; apply/andP; split.
    by rewrite /= !inE andbT npq.
  by apply/subsetP => u _; rewrite inE.
have H02 : [tuple a0; a2] \in 2.-dtuple([set: 'I_12]).
  by rewrite inE; apply/andP; split.
have Htr := psl211_2transitive.
rewrite /ntransitive psl211_rho_im in Htr.
have [g gG Hg] := atransP2 Htr Hpq H02.
have Hgp : g p = a0.
  by rewrite -[g p]/(tnth (('P * 2)%act [tuple p; q] g) (@Ordinal 2 0 isT)) -Hg.
have Hgq : g q = a2.
  by rewrite -[g q]/(tnth (('P * 2)%act [tuple p; q] g) (@Ordinal 2 1 isT)) -Hg.
exists [tuple tnth mirror_swap_deck (@pgg_rho psl211_M g i) | i < 12].
exists [tuple tnth (psl211_orbit_encode false) (@pgg_rho psl211_M g i)
       | i < 12].
split; first exact: valid_act gG mirror_swap_valid.
split; first exact: valid_act gG (psl211_orbit_encode_valid false).
move=> i nip niq; rewrite !tnth_act; apply: decks_agree_off02.
  apply: contra nip => /eqP Hgi; apply/eqP; apply: (@perm_inj _ g).
  by rewrite Hgi Hgp.
apply: contra niq => /eqP Hgi; apply/eqP; apply: (@perm_inj _ g).
by rewrite Hgi Hgq.
Qed.
