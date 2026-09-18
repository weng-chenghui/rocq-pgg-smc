(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_recovery: the sharp recovery threshold of the eight-card scheme      *)
(*                                                                            *)
(* A valid deck deals the eight distinct cards, so seven revealed positions   *)
(* leave a unique missing card: seven reveals determine the deck and hence    *)
(* the orbit class. Six reveals never do: for every choice of two hidden      *)
(* positions there are two valid decks of opposite orbit classes agreeing on  *)
(* the six revealed ones. Together with the privacy threshold three and the   *)
(* four-position leak (pgl27_secrecy.v), the scheme is private up to three    *)
(* revealed positions, leaks from four, stays ambiguous through six and is    *)
(* determined at seven.                                                       *)
(* The implemented protocol decoder (pgl27_run.v) reads all eight endpoints.  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_seven_reveal_determines == decks agreeing off one position agree   *)
(*   pgl27_seven_reveal_class      == seven reveals determine the class       *)
(*   pgl27_six_reveal_ambiguous    == six reveals never determine the class   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** pgl27_seven_reveal_determines — two valid decks agreeing everywhere off
    one position are equal: the eight distinct cards leave a unique missing
    card for the hidden position. Seven revealed cards determine the deck. *)
Lemma pgl27_seven_reveal_determines (p : 'I_8) (sh1 sh2 : 8.-tuple 'I_8) :
  deck_ok sh1 -> deck_ok sh2 ->
  (forall i : 'I_8, i != p -> tnth sh1 i = tnth sh2 i) ->
  sh1 = sh2.
Proof.
move=> u1 u2 Hagree.
have inj1 : injective (tnth sh1) by apply/tuple_uniqP.
have inj2 : injective (tnth sh2) by apply/tuple_uniqP.
have Himg : [set tnth sh1 i | i in [set~ p]]
          = [set tnth sh2 i | i in [set~ p]].
  apply: eq_in_imset => i; rewrite inE => nip.
  by move: nip; rewrite !inE => nip; rewrite Hagree.
have Hout : forall sh : 8.-tuple 'I_8, injective (tnth sh) ->
    tnth sh p \notin [set tnth sh i | i in [set~ p]].
  move=> sh injs; apply/imsetP => -[j]; rewrite inE => njp Heq.
  by move: njp; rewrite (injs _ _ Heq) inE eqxx.
have Hcard : #|~: [set tnth sh1 i | i in [set~ p]]| = 1%N.
  by rewrite cardsCs setCK card_imset ?cardsC1 ?card_ord.
move: Hcard => /eqP /cards1P [a Ha].
have E1 : tnth sh1 p = a.
  by move: (Hout _ inj1); rewrite -in_setC Ha inE => /eqP.
have E2 : tnth sh2 p = a.
  by move: (Hout _ inj2); rewrite -Himg -in_setC Ha inE => /eqP.
apply: eq_from_tnth => i.
have [->|nip] := eqVneq i p; first by rewrite E1 E2.
exact: Hagree.
Qed.

(** pgl27_seven_reveal_class — two valid decks agreeing off one position have
    the same orbit class: a seven-position decoder for the secret exists.
    Seven revealed cards determine the orbit class. *)
Lemma pgl27_seven_reveal_class (p : 'I_8) (sh1 sh2 : 8.-tuple 'I_8) :
  deck_ok sh1 -> deck_ok sh2 ->
  (forall i : 'I_8, i != p -> tnth sh1 i = tnth sh2 i) ->
  orbit_class sh1 = orbit_class sh2.
Proof.
by move=> u1 u2 Hag; rewrite (@pgl27_seven_reveal_determines p _ _ u1 u2 Hag).
Qed.

(** pgl27_2transitive — the PGL(2,7) monodromy acts 2-transitively on the
    eight projective points, weakened from sharp 3-transitivity. *)
Lemma pgl27_2transitive :
  ntransitive 2 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.
Proof. exact: ntransitive_weak (isT : (2 <= 3)%N) pgl27_3transitive. Qed.

(* The deck 0 1 2 4 3 5 6 7, the class-false deck with the cards at the
   positions 3 and 4 exchanged. *)
Local Definition deck34 : 8.-tuple 'I_8 :=
  [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
         @Ordinal 8 4 isT; @Ordinal 8 3 isT; @Ordinal 8 5 isT;
         @Ordinal 8 6 isT; @Ordinal 8 7 isT].

(* deck34 deals eight distinct cards. *)
Local Lemma deck34_ok : deck_ok deck34.
Proof. by vm_compute. Qed.

(* deck34 holds its hearts at the positions of the class-true encoded deck. *)
Local Lemma deck34_hearts : heart_set deck34 = heart_set (orbit_encode true).
Proof.
apply/setP => x; rewrite !inE /is_heart.
by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

(* deck34 has orbit class true, read through its heart positions because the
   class of a deck is the class of its heart four-subset. *)
Local Lemma deck34_class : orbit_class deck34 = true.
Proof.
by rewrite /orbit_class deck34_hearts -/(orbit_class (orbit_encode true))
  orbit_encodeK.
Qed.

(* deck34 and the class-false encoded deck agree away from positions 3
   and 4. *)
Local Lemma deck34_agree_off34 (i : 'I_8) :
  i != (@Ordinal 8 3 isT) -> i != (@Ordinal 8 4 isT) ->
  tnth deck34 i = tnth (orbit_encode false) i.
Proof.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt // _ _; apply: val_inj.
Qed.

(** pgl27_six_reveal_ambiguous — for every two hidden positions there are two
    valid decks of opposite orbit classes agreeing on the six revealed
    positions. Six revealed cards never determine the orbit class. *)
Lemma pgl27_six_reveal_ambiguous (p q : 'I_8) : p != q ->
  exists sh1 sh2 : 8.-tuple 'I_8,
    [/\ deck_ok sh1, deck_ok sh2, orbit_class sh1 != orbit_class sh2 &
        forall i : 'I_8, i != p -> i != q -> tnth sh1 i = tnth sh2 i].
Proof.
move=> npq.
pose p3 : 'I_8 := @Ordinal 8 3 isT.
pose p4 : 'I_8 := @Ordinal 8 4 isT.
have Hpq : [tuple p; q] \in 2.-dtuple([set: 'I_8]).
  rewrite inE; apply/andP; split.
    by rewrite /= !inE andbT npq.
  by apply/subsetP => u _; rewrite inE.
have H34 : [tuple p3; p4] \in 2.-dtuple([set: 'I_8]).
  by rewrite inE; apply/andP; split.
have Htr := pgl27_2transitive.
rewrite /ntransitive pgl27_rho_im in Htr.
have [g gG Hg] := atransP2 Htr Hpq H34.
have Hgp : g p = p3.
  by rewrite -[g p]/(tnth (('P * 2)%act [tuple p; q] g) (@Ordinal 2 0 isT)) -Hg.
have Hgq : g q = p4.
  by rewrite -[g q]/(tnth (('P * 2)%act [tuple p; q] g) (@Ordinal 2 1 isT)) -Hg.
exists [tuple tnth deck34 (@pgg_rho pgl27_M g i) | i < 8],
       [tuple tnth (orbit_encode false) (@pgg_rho pgl27_M g i) | i < 8].
split.
- by rewrite (deck_stable g _ gG) deck34_ok.
- by rewrite (deck_stable g _ gG) orbit_encode_deck.
- by rewrite !(orbit_class_invariant g _ gG) deck34_class orbit_encodeK.
- move=> i nip niq; rewrite !tnth_mktuple; apply: deck34_agree_off34.
  + apply: contra nip => /eqP Hgi; apply/eqP; apply: (@perm_inj _ g).
    by rewrite Hgi Hgp.
  + apply: contra niq => /eqP Hgi; apply/eqP; apply: (@perm_inj _ g).
    by rewrite Hgi Hgq.
Qed.

(** pgl27_reveal_ambiguous — for every revealed position set of at most six
    positions there are two valid decks of opposite orbit classes agreeing on
    all revealed positions. At most six revealed cards never determine the
    orbit class, for every choice of the revealed set. *)
Lemma pgl27_reveal_ambiguous (D : {set 'I_8}) : (#|D| <= 6)%N ->
  exists sh1 sh2 : 8.-tuple 'I_8,
    [/\ deck_ok sh1, deck_ok sh2, orbit_class sh1 != orbit_class sh2 &
        {in D, forall i, tnth sh1 i = tnth sh2 i}].
Proof.
move=> HD.
have Hc : (1 < #|~: D|)%N.
  have := cardsC D.
  rewrite card_ord => HDC.
  rewrite -(leq_add2l #|D|) HDC.
  by apply: (leq_trans _ (leq_add HD (leqnn _))).
case/card_gt1P: Hc => p [q [Hp Hq npq]].
have [sh1 [sh2 [Hok1 Hok2 Hcl Hagree]]] := pgl27_six_reveal_ambiguous npq.
exists sh1, sh2; split=> // i iD.
apply: Hagree.
- by apply: contraTneq iD => ->; rewrite -in_setC.
- by apply: contraTneq iD => ->; rewrite -in_setC.
Qed.
