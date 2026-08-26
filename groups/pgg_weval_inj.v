(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop.
From pgg_smc Require Import pgg_interface.

(******************************************************************************)
(* PGG: Word-Eval Injective Generators and Optimal Search Space               *)
(*                                                                            *)
(* MathComp's finGroupType cannot represent the infinite free group needed    *)
(* for maximal PGG search spaces.  Word evaluation injectivity at length L    *)
(* approximates it on demand: given a word length L, we ask only that         *)
(* word_eval be injective on L-words (i.e., the group "looks free" up to     *)
(* depth L).  This suffices to achieve search_space(L) = Tg^L, matching the  *)
(* free group for all protocol uses.                                          *)
(*                                                                            *)
(* Parameters for a word-eval injective PGG instance:                         *)
(*   L  -- word length (security/search space depth)                          *)
(*   Tg -- number of generators (branching factor), search space = Tg^L      *)
(*   N  -- number of card positions (permutation domain), N! >= Tg^L         *)
(*   sigmas -- Tg permutations in S_N generating a group of order >= Tg^L    *)
(* Example: for L=10 with Tg=2, need 2^10=1024 distinct group elements,     *)
(* so N >= 7 (since 7!=5040 >= 1024). Pick two sigma_i in S_7 generating a   *)
(* subgroup of order >= 1024 with no word collisions at length 10.            *)
(*                                                                            *)
(* Section 1 -- Nat-level computable word-eval injectivity check:             *)
(*   weval_inj_natB N Tg L gens == boolean check via uniq of word fingerprints*)
(*   weval_inj_of_natB == reflection: weval_inj_natB true -> weval_inj L     *)
(*   Usage: define a nat-level gens_nat mirroring the permutations, prove     *)
(*   gens_agree, then discharge weval_inj by vm_compute on weval_inj_natB.   *)
(*                                                                            *)
(* Section 2 -- Parameterized word-eval injective theory:                     *)
(*   Given generators with hypothesis weval_inj L, derives                    *)
(*   search_space = Tg^L.                                                     *)
(*                                                                            *)
(* Section 3 -- Concrete instance: overlapping 3-cycles in S_4:              *)
(*   Intended presentation < s0, s1 | s0^3 = s1^3 = (s0*s1)^2 = 1 >, the     *)
(*   alternating group A_4 of order 12.  Only s0^3 = s1^3 = 1 is discharged  *)
(*   in the kernel below; neither the braid relation nor the order of the    *)
(*   group is.                                                               *)
(*   sigma_0 = (0 1 2), sigma_1 = (1 2 3) -- two 3-cycles sharing (1,2).    *)
(*   Tg=2, N=4, L=2: search_space = 4.  L >= 3 fails (s0^3 = s1^3 = 1      *)
(*   so words [0,0,0] and [1,1,1] both map to the identity).                *)
(*   oc_weval_inj2 == word-eval injectivity at L=2 via weval_inj_of_natB    *)
(*                    + vm_compute                                            *)
(*   oc_search_space_2 == search_space 2 = 4                                 *)
(*   oc_noncommute == the generators do not commute                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Nat-level computable word-eval injectivity check                 *)
(* ========================================================================== *)

(** Every word of length L over the alphabet {0,...,Tg-1}, enumerated by
    recursion on the length.
    The nat-level stand-in for the enumeration of the pgg_word finType, kept
    structural so vm_compute reduces it.  It is the carrier both of the
    injectivity check below and of the Foata trace count in pgg_raag.v, so
    its completeness is what makes a computation on it a statement about all
    words. *)
Fixpoint all_words (Tg L : nat) : seq (seq nat) :=
  match L with
  | 0 => [:: [::]]
  | L'.+1 =>
    flatten [seq map (cons i) (all_words Tg L') | i <- iota 0 Tg]
  end.

(* Nat-level evaluation of a word at a point: apply the generators in reading
   order.  The left fold is chosen to match MathComp's \prod convention for
   permutations,
   foldl f x [a;b;c] = f(f(f(x,a),b),c) = sigma_c(sigma_b(sigma_a(x)))
   = (\prod_(i <- [a;b;c]) sigma_i)%g x,
   which is what lets word_eval_foldl identify the two evaluators. *)
Definition eval_word_nat (gens : nat -> nat -> nat) (w : seq nat) (x : nat) : nat :=
  foldl (fun acc i => gens i acc) x w.

(** The fingerprint of a word: the images of the N card positions under the
    permutation the word evaluates to.
    A permutation of a finite set is determined by its table of values, so two
    words name the same deck permutation exactly when their fingerprints
    agree.  This turns a question about group elements into an equality of
    concrete lists. *)
Definition word_fp (N : nat) (gens : nat -> nat -> nat) (w : seq nat) : seq nat :=
  map (eval_word_nat gens w) (iota 0 N).

(** Boolean test that the length-L words over Tg generators have pairwise
    distinct fingerprints.
    A closed nat-level term, so vm_compute decides it for a concrete
    instance.  weval_inj_of_natB turns a positive verdict into the abstract
    weval_inj, hence into search_space L = Tg^L. *)
Definition weval_inj_natB (N Tg L : nat) (gens : nat -> nat -> nat) : bool :=
  uniq (map (word_fp N gens) (all_words Tg L)).

(** A duplicate-free image list makes f injective on the source list.
    The generic step that converts the uniq verdict into an injectivity
    statement. *)
Lemma map_uniq_injective (T1 T2 : eqType) (f : T1 -> T2) (xs : seq T1) (a b : T1) :
  uniq (map f xs) -> a \in xs -> b \in xs -> f a = f b -> a = b.
Proof.
move=> Huniq Ha Hb Hfab.
set ia := index a xs; set ib := index b xs.
have Hia : ia < size [seq f i | i <- xs] by rewrite size_map index_mem.
have Hib : ib < size [seq f i | i <- xs] by rewrite size_map index_mem.
have Ha' : nth (f a) [seq f i | i <- xs] ia = f a.
  by rewrite (nth_map a) ?index_mem // nth_index.
have Hb' : nth (f a) [seq f i | i <- xs] ib = f a.
  by rewrite (nth_map a) ?index_mem // nth_index // Hfab.
have /eqP Hiab : ia == ib.
  by rewrite -(nth_uniq (f a) Hia Hib Huniq) Ha' Hb' eqxx.
by rewrite -(nth_index a Ha) -(nth_index a Hb) -/ia -/ib Hiab.
Qed.

(** A word of length L whose letters are all below Tg occurs in all_words.
    Completeness of the enumeration: without it a duplicate-free verdict over
    all_words could still miss a colliding pair of words. *)
Lemma mem_all_words Tg L (w : seq nat) :
  size w = L -> all (fun i => i < Tg) w -> w \in all_words Tg L.
Proof.
elim: L w => [|L IH] w /=.
  by move=> /size0nil -> _.
case: w => [// | a w'] /= [Hsz] /andP [Ha Hw'].
apply/flattenP; exists (map (cons a) (all_words Tg L)).
  by apply/mapP; exists a => //; rewrite mem_iota add0n.
by apply/mapP; exists w' => //; exact: IH.
Qed.

(* ========================================================================== *)
(* Reflection for Gen_PGGTypes instances                                      *)
(* ========================================================================== *)

Section weval_inj_gen_reflect.

(* Tg = m+1 generators on N = n+2 card positions, with gens_nat a nat-level
   mirror of the permutations and Hgens the statement that the mirror is
   faithful. *)
Variable m n : nat.
Let Tg := m.+1.
Let N := n.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Variable gens_nat : nat -> nat -> nat.

Hypothesis Hgens : forall (i : 'I_Tg) (x : 'I_N),
  gens_nat (val i) (val x) = val (tnth sigmas i x).

(* The nat-level fold and the ordinal-level fold agree under val: the nat
   generators mirror the permutations one step at a time. *)
Lemma eval_foldl_agree (ws : seq 'I_Tg) (x : 'I_N) :
  foldl (fun acc i => gens_nat i acc) (val x) (map val ws) =
  val (foldl (fun (acc : 'I_N) (i : 'I_Tg) => tnth sigmas i acc) x ws).
Proof.
by elim: ws x => [|j js IH] x //=; rewrite Hgens IH.
Qed.

(* word_eval, defined as a product of generators indexed along the word,
   computes as the left fold that applies them in reading order.  The bridge
   from MathComp's \prod to the shape of the nat-level evaluator. *)
Lemma word_eval_foldl (L : nat) (w : @pgg_word M L) (x : 'I_N) :
  @word_eval M L w x =
  foldl (fun (acc : 'I_N) (j : 'I_Tg) => tnth sigmas j acc) x (tval w).
Proof.
rewrite /word_eval; have -> : @pgg_sigmas M = sigmas by [].
elim: L w x => [|L IH] w x.
  by rewrite big_ord0 perm1; case: w => [[] //].
rewrite big_ord_recl permM.
case Hw: (tval w) => [|a s].
  by move: (size_tuple w); rewrite Hw.
have Ha : a = tnth w ord0 by rewrite (tnth_nth a) Hw.
have Hsz : size s == L by move: (size_tuple w); rewrite Hw /= => [[->]].
set wt : L.-tuple 'I_Tg := Tuple Hsz.
have Hlift : forall i : 'I_L, tnth w (lift ord0 i) = tnth wt i.
  by move=> i; rewrite !(tnth_nth a) Hw.
rewrite (eq_bigr (fun i => tnth sigmas (tnth wt i))); last first.
  by move=> i _; rewrite Hlift.
rewrite -/(word_eval (L:=L) wt) /= Ha.
have -> : s = tval wt by [].
exact: IH.
Qed.

(* The nat-level evaluator and word_eval send every card position to the same
   image: the computable mirror is faithful. *)
Lemma eval_word_agree (L : nat) (w : @pgg_word M L) (x : 'I_N) :
  eval_word_nat gens_nat (map val (tval w)) (val x) =
  val (@word_eval M L w x).
Proof.
by rewrite /eval_word_nat eval_foldl_agree word_eval_foldl.
Qed.

(* Two words with the same sequence of letter values are equal, so nothing is
   lost by reasoning about the nat projection of a word. *)
Lemma map_val_tuple_inj (L : nat) (w1 w2 : @pgg_word M L) :
  map val (tval w1) = map val (tval w2) -> w1 = w2.
Proof. by move/(inj_map val_inj) => /val_inj. Qed.

(** The nat projection of a length-L word is one of the words all_words
    enumerates. *)
Lemma map_val_in_all_words (L : nat) (w : @pgg_word M L) :
  map val (tval w) \in all_words Tg L.
Proof.
apply: mem_all_words.
  by rewrite size_map size_tuple.
by apply/allP => k /mapP [i _ ->]; case: i.
Qed.

(* A positive verdict on the fingerprint check gives word-eval injectivity at
   length L: distinct length-L words then name distinct deck permutations, so
   no two dealer words of that length are confusable.  This is the
   computational route to weval_inj for a concrete instance, and weval_inj is
   the hypothesis under which the search space is as large as the alphabet
   allows. *)
Lemma weval_inj_of_natB (L : nat) :
  weval_inj_natB N Tg L gens_nat -> @weval_inj M L.
Proof.
rewrite /weval_inj_natB /weval_inj => Huniq w1 w2 Heval.
apply: map_val_tuple_inj.
apply: (map_uniq_injective Huniq (map_val_in_all_words w1) (map_val_in_all_words w2)).
rewrite /word_fp.
apply: (@eq_from_nth _ 0); first by rewrite !size_map !size_iota.
move=> j; rewrite size_map size_iota => Hj.
rewrite !(nth_map 0) ?size_iota // !nth_iota // !add0n.
have -> : j = val (Ordinal Hj) by [].
by rewrite (eval_word_agree w1) (eval_word_agree w2) Heval.
Qed.

End weval_inj_gen_reflect.

(* ========================================================================== *)
(* Section 2: Parameterized word-eval injective theory                        *)
(* ========================================================================== *)

Section weval_inj_instance.

(* A deck on m+1 generators and n+2 card positions, assumed word-eval
   injective at the fixed length L. *)
Variable L m n : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n.+2}.
Let M := Gen_PGGTypes sigmas.
Hypothesis Hlfree : @weval_inj M L.

(** For a Gen_PGGTypes on Tg = m+1 generators that is word-eval injective at
    length L, the search space is exactly Tg^L.
    That is the largest a search space over Tg letters can be, matching the
    free group up to depth L.  Injectivity is not merely sufficient but
    exact: every collision at length L would take one element out of the
    count. *)
Lemma weval_inj_inst_search_space : @search_space M L = m.+1 ^ L.
Proof. exact: weval_inj_search_space Hlfree. Qed.

End weval_inj_instance.

(* ========================================================================== *)
(* Section 3: Concrete word-eval injective instance — overlapping 3-cycles    *)
(*            in S_4                                                           *)
(* ========================================================================== *)

Section overlapping_3cycles.

(* Four card positions. *)
Definition oc_N := 4.

(* sigma_0 = (0 1 2): the 3-cycle mapping 0->1->2->0 *)
Definition oc_s0_fun (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 0 => @Ordinal oc_N 1 isT | 1 => @Ordinal oc_N 2 isT
  | 2 => @Ordinal oc_N 0 isT | _ => i end.
(** The inverse 3-cycle (0 2 1), present only to supply the cancel witness
    that raises oc_s0_fun to a permutation. *)
Definition oc_s0_inv (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 0 => @Ordinal oc_N 2 isT | 1 => @Ordinal oc_N 0 isT
  | 2 => @Ordinal oc_N 1 isT | _ => i end.
(** oc_s0_inv cancels oc_s0_fun, so the latter is injective. *)
Lemma oc_s0K : cancel oc_s0_fun oc_s0_inv.
Proof. by move=> x; apply: val_inj; case: x => [[|[|[|[|?]]]] ?]. Qed.
(** The generator sigma_0 = (0 1 2) as a permutation of the four card
    positions. *)
Definition oc_s0 : {perm 'I_oc_N} := perm (can_inj oc_s0K).
(** oc_s0 sends a position to oc_s0_fun of it. *)
Lemma oc_s0E x : oc_s0 x = oc_s0_fun x. Proof. by rewrite permE. Qed.

(* sigma_1 = (1 2 3): the 3-cycle mapping 1->2->3->1 *)
Definition oc_s1_fun (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 1 => @Ordinal oc_N 2 isT | 2 => @Ordinal oc_N 3 isT
  | 3 => @Ordinal oc_N 1 isT | _ => i end.
(** The inverse of the second 3-cycle, companion of oc_s0_inv. *)
Definition oc_s1_inv (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 1 => @Ordinal oc_N 3 isT | 2 => @Ordinal oc_N 1 isT
  | 3 => @Ordinal oc_N 2 isT | _ => i end.
(** oc_s1_inv cancels oc_s1_fun. *)
Lemma oc_s1K : cancel oc_s1_fun oc_s1_inv.
Proof. by move=> x; apply: val_inj; case: x => [[|[|[|[|?]]]] ?]. Qed.
(** The generator sigma_1 = (1 2 3) as a permutation of the four card
    positions.  Its support {1,2,3} overlaps sigma_0's in the two positions
    1 and 2, which is the whole reason the instance is non-abelian. *)
Definition oc_s1 : {perm 'I_oc_N} := perm (can_inj oc_s1K).
(** oc_s1 sends a position to oc_s1_fun of it. *)
Lemma oc_s1E x : oc_s1 x = oc_s1_fun x. Proof. by rewrite permE. Qed.

(* The generator list has the length the tuple type asks for. *)
Lemma oc_sigmas_size : size [:: oc_s0; oc_s1] == 2.
Proof. by []. Qed.

(** The two-letter alphabet of the overlapping-3-cycles instance. *)
Definition oc_sigmas : 2.-tuple {perm 'I_oc_N} := Tuple oc_sigmas_size.

(** Index 0 of the alphabet is oc_s0 and index 1 is oc_s1. *)
Lemma oc_sigmasE (i : 'I_2) : tnth oc_sigmas i =
  match val i with 0 => oc_s0 | _ => oc_s1 end.
Proof.
by rewrite (tnth_nth oc_s0) /=; case: i => [[|[|?]] ?].
Qed.

(** The overlapping-3-cycles deck: two 3-cycles of four card positions as a
    PGG instance, the smallest concrete setting in which the search-space
    theory below is exercised. *)
Definition OC_PGGTypes := Gen_PGGTypes oc_sigmas.

(* The two generators as nat functions on {0,1,2,3}, the form vm_compute can
   reduce. *)
Definition oc_gens_nat (i x : nat) : nat :=
  match i with
  | 0 => match x with 0 => 1 | 1 => 2 | 2 => 0 | _ => x end
  | _ => match x with 1 => 2 | 2 => 3 | 3 => 1 | _ => x end
  end.

(** The nat generators agree with the permutations at every card position.
    This is the faithfulness hypothesis weval_inj_of_natB needs: without it a
    computation on the nat mirror would say nothing about the group. *)
Lemma oc_gens_agree (i : 'I_2) (x : 'I_oc_N) :
  oc_gens_nat (val i) (val x) = val (tnth oc_sigmas i x).
Proof.
by case: i => [[|[|?]] ?]; case: x => [[|[|[|[|?]]]] ?];
  rewrite oc_sigmasE /= permE.
Qed.

(** sigma_0 cubed is the identity.
    Together with oc_s1_order3 this is the collision that bounds the
    instance: the length-3 words 000 and 111 both evaluate to the identity,
    so word-eval injectivity can hold at length 2 and must fail from length 3
    on. *)
Lemma oc_s0_order3 : (oc_s0 ^+ 3 = 1 :> {perm 'I_oc_N})%g.
Proof.
apply/permP => x; rewrite perm1 expgS permM expgS permM expg1 !oc_s0E.
by apply: val_inj; case: x => [[|[|[|[|?]]]] ?].
Qed.

(** sigma_1 cubed is the identity, the second half of the length-3
    collision. *)
Lemma oc_s1_order3 : (oc_s1 ^+ 3 = 1 :> {perm 'I_oc_N})%g.
Proof.
apply/permP => x; rewrite perm1 expgS permM expgS permM expg1 !oc_s1E.
by apply: val_inj; case: x => [[|[|[|[|?]]]] ?].
Qed.

(* The two generators do not commute, their supports sharing positions 1 and
   2.  The deck group is therefore non-abelian, so its search space is not
   the polynomial count an abelian instance would give. *)
Lemma oc_noncommute : (oc_s0 * oc_s1 != oc_s1 * oc_s0)%g.
Proof.
apply/negP => /eqP/permP /(_ (Ordinal (isT : 0 < oc_N))).
by rewrite !permM !oc_s0E !oc_s1E.
Qed.

(* Word-eval injectivity at length 2, decided by vm_compute on the
   fingerprint check. *)
Lemma oc_weval_inj2 : @weval_inj OC_PGGTypes 2.
Proof.
apply: (weval_inj_of_natB oc_gens_agree).
by vm_compute.
Qed.

(* Length-2 words reach exactly 4 = 2^2 distinct deck permutations, the
   maximum for two generators at that length.  By the order-3 relations above
   the same cannot hold at length 3. *)
Lemma oc_search_space_2 : @search_space OC_PGGTypes 2 = 4.
Proof. exact: weval_inj_inst_search_space oc_weval_inj2. Qed.

End overlapping_3cycles.
