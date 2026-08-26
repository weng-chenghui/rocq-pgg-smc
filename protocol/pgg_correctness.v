(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.

(******************************************************************************)
(* PGG: Correctness Theorems                                                  *)
(*                                                                            *)
(*   Theorem 1 (Correctness): rho(g*h)(s) = rho(h)(rho(g)(s))               *)
(*     The monodromy representation composes correctly.                       *)
(*                                                                            *)
(*   Theorem 2 (Bijectivity/UPLP): rho(P) is a bijection on card positions.  *)
(*     Trivially true since rho(P) : {perm 'I_N}.                            *)
(*                                                                            *)
(*   Proposition 3 (Distinctness): Endpoints of distinct starting card        *)
(*     positions remain distinct under any monodromy evaluation.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_correctness.

Variable gT : finGroupType.
Variable N' : nat.
Let N := N'.+1.
Variable G : {group gT}.
Variable rho : {morphism G >-> {perm 'I_N}}.

(* rho composes elements of G the same way it composes their images in
   {perm 'I_N}: evaluating the product g*h at a card position agrees with
   evaluating h at the position rho g already moved. This is the action law
   that lets a word of group elements be replayed one generator at a time
   without changing the card position the last generator lands on. *)
Theorem pgg_correctness (g h : gT) (s : 'I_N) :
  g \in G -> h \in G ->
  rho (g * h)%g s = rho h (rho g s).
Proof. by move=> gG hG; rewrite (morphM rho gG hG) permM. Qed.

(* rho sends the group identity to the identity permutation, so a word that
   evaluates to 1 leaves every card position where it started. *)
Lemma pgg_correctness1 (s : 'I_N) : rho 1%g s = s.
Proof. by rewrite morph1 perm1. Qed.

(* rho g^-1 undoes rho g on every card position, so any shuffle applied by
   the protocol can be reversed by evaluating the inverse word. *)
Lemma pgg_correctnessV (g : gT) (s : 'I_N) :
  g \in G -> rho g^-1%g (rho g s) = s.
Proof.
by move=> gG; rewrite -permM (morphV rho gG) mulgV perm1.
Qed.

(* Every group element P acts on the deck as a bijection of card positions,
   since rho P is by construction a member of {perm 'I_N}. Bijectivity is
   what guarantees the shuffle neither collapses nor duplicates a card
   position: every endpoint has exactly one preimage under P. *)
Theorem pgg_bijectivity (P : gT) : bijective (rho P).
Proof. by exists (rho P)^-1%g => x; rewrite ?permK ?permKV. Qed.

(* rho P is injective on card positions: two starting positions that reach
   the same endpoint under P were already equal. Distinctness of the deck
   before a shuffle therefore survives the shuffle, which is what the
   distinctness results below build on. *)
Theorem pgg_injective (P : gT) : injective (rho P).
Proof. exact: perm_inj. Qed.

(* The T starting card positions assigned to the players. *)
Variable T' : nat.
Let T := T'.+1.
Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

(* The T starting card positions, being distinct, remain distinct after any
   monodromy evaluation rho P: this is pgg_injective transported along a uniq
   tuple, and it is what lets the verifier tell the T revealed endpoints
   apart as belonging to T different players rather than to some collapsed
   subset of them. *)
Proposition pgg_distinctness (P : gT) :
  uniq (map (rho P) starts).
Proof. by rewrite map_inj_uniq //; exact: perm_inj. Qed.

(* tnth starts is injective because starts is a uniq tuple: distinct player
   indices name distinct starting card positions. This is the tuple-level
   fact endpoints_card below composes with rho's injectivity to count
   endpoints. *)
Let x0 := tnth starts ord0.

Lemma starts_tnth_inj : injective (tnth starts).
Proof.
move=> i j eq_ij.
have Hi : (i < size starts)%N by rewrite size_tuple.
have Hj : (j < size starts)%N by rewrite size_tuple.
have := @nth_uniq _ x0 starts i j Hi Hj starts_uniq.
have -> : nth x0 starts i = tnth starts i by rewrite (tnth_nth x0).
have -> : nth x0 starts j = tnth starts j by rewrite (tnth_nth x0).
rewrite eq_ij eqxx => /esym/eqP. exact: ord_inj.
Qed.

(* The set of endpoints {rho P (start i) | i} has the same cardinality T as
   the set of starting card positions: rho P is injective (pgg_injective)
   and starts_tnth_inj makes the composite injective, so no two players'
   endpoints coincide under any shuffle P. This is the cardinality form of
   pgg_distinctness that fiber-counting and entropy arguments elsewhere
   build on. *)
Lemma endpoints_card (P : gT) :
  #|[set rho P (tnth starts i) | i : 'I_T]| = T.
Proof.
rewrite card_imset ?card_ord //.
by move=> i j /(perm_inj (s := rho P)) /starts_tnth_inj.
Qed.

End pgg_correctness.
