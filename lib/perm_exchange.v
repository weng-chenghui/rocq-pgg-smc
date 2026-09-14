(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* perm_exchange: exchanging two equinumerous subsets of a finite type        *)
(*                                                                            *)
(* Two subsets of the same cardinality are carried onto one another by a      *)
(* permutation supported on their union, so that permutation fixes every      *)
(* point outside both.  A re-deal built from it therefore leaves untouched    *)
(* every card lying outside the two sets being exchanged, which is what a     *)
(* re-deal to a coalition's fixed view requires.                              *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   perm_onS        == perm_on is monotone in its support                    *)
(*   perm_of_eq_card == equinumerous subsets are exchanged by a permutation   *)
(*                      supported on their union                              *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* perm_on is a subset statement, so it is monotone in its support. *)
Lemma perm_onS (T : finType) (S1 S2 : {set T}) (s : {perm T}) :
  S1 \subset S2 -> perm_on S1 s -> perm_on S2 s.
Proof. by move=> H1 H2; exact: subset_trans H2 H1. Qed.

(* Two equinumerous subsets are exchanged by a permutation supported on their
   union, which therefore fixes every point outside both.  The re-deal needs
   exactly this: the cards already on the coalition must not move. *)
Lemma perm_of_eq_card (T : finType) (U V : {set T}) :
  #|U| = #|V| ->
  exists s : {perm T}, perm_on (U :|: V) s /\ [set s x | x in U] = V.
Proof.
have [n] := ubnP #|U :\: V|; elim: n U V => // n IH U V HD Hcard.
case: (set_0Vmem (U :\: V)) => [HU0 | [u Hu]].
  have HUV : U \subset V by rewrite -setD_eq0 HU0.
  have -> : U = V by apply/eqP; rewrite eqEcard HUV Hcard leqnn.
  exists 1%g; split; first exact: perm_on1.
  by apply/setP => x; apply/imsetP/idP => [[y Hy ->]|Hx];
     rewrite ?perm1 //; exists x; rewrite ?perm1.
have HVU : #|V :\: U| = #|U :\: V| by rewrite !cardsD Hcard setIC.
have : (0 < #|V :\: U|)%N by rewrite HVU (cardsD1 u) Hu.
case/card_gt0P => v Hv.
pose t := tperm u v.
have Hvu : v \notin U by move: Hv; rewrite inE => /andP[].
have HuU : u \in U by move: Hu; rewrite inE => /andP[].
have HuV : u \notin V by move: Hu; rewrite inE => /andP[].
have HvV : v \in V by move: Hv; rewrite inE => /andP[].
have Ht (y : T) : y \in U -> t y = (if y == u then v else y).
  move=> Hy; rewrite /t; case: tpermP => [->|Hy'|]; rewrite ?eqxx //.
    by rewrite Hy' (negbTE Hvu) in Hy.
  by move=> /eqP/negbTE-> _.
pose U1 := [set t x | x in U].
have HU1card : #|U1| = #|V| by rewrite card_imset ?Hcard //; exact: perm_inj.
have HU1sub : U1 \subset U :|: V.
  apply/subsetP => x /imsetP[y Hy ->]; rewrite Ht // inE.
  by case: ifP => _; [rewrite HvV orbT | rewrite Hy].
have HU1D : U1 :\: V \subset (U :\: V) :\ u.
  apply/subsetP => x; rewrite !inE => /andP[HxV /imsetP[y Hy Hxy]].
  move: Hxy; rewrite Ht //; case: ifP => [_ Hxv | Hyu Hxy].
    by rewrite Hxv HvV in HxV.
  by rewrite Hxy in HxV *; rewrite Hyu HxV Hy.
have HD1 : (#|U1 :\: V| < n)%N.
  apply: (leq_ltn_trans (subset_leq_card HU1D)).
  have HE := cardsD1 u (U :\: V); rewrite Hu add1n in HE.
  by rewrite -HE.
have [s1 [Hon1 Him1]] := IH U1 V HD1 HU1card.
exists (t * s1)%g; split; last first.
  by rewrite -Him1 /U1 -imset_comp; apply: eq_imset => x; rewrite permM.
apply: perm_onM.
  apply: (perm_onS _ (tperm_on u v)).
  by apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->];
     rewrite ?HuU ?HvV ?orbT.
by apply: (perm_onS _ Hon1); rewrite subUset HU1sub subsetUr.
Qed.
