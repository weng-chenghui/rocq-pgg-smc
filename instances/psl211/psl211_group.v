(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_group: the PSL(2,11) monodromy on the twelve card positions         *)
(*                                                                            *)
(* The twelve card positions are identified with 'I_12. Two shuffle letters   *)
(* generate the monodromy group, each given as an explicit permutation table  *)
(* of 'I_12 read off psl211_blocks.v:                                         *)
(*                                                                            *)
(*   psl211_r4_perm == reverse each of the three four-card blocks           *)
(*                     0..3, 4..7, 8..11                                      *)
(*                     (psl211_r4_tbl    = [3;2;1;0;7;6;5;4;11;10;9;8])       *)
(*   psl211_m6_perm == Monge-shuffle each of the two halves 0..5, 6..11       *)
(*                     (psl211_m6_tbl    = [3;2;4;1;5;0;9;8;10;7;11;6]),      *)
(*                     inverted by the milk table                             *)
(*                     (psl211_milk6_tbl = [5;3;1;0;2;4;11;9;7;6;8;10])       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_gens == the two letters as a 2.-tuple {perm 'I_12}                *)
(*   psl211_M    == the MonodromyReprType [@Gen_PGGTypes 1 10 psl211_gens]    *)
(*                  (a Notation, so HB keeps the hasGenerators structure)     *)
(*   psl211_word_perm w == a word w over the two letter indices, folded      *)
(*                          into the composite shuffle permutation it names   *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_N'          == the deck has twelve positions                      *)
(*   psl211_G_pos       == the shuffle group is nonempty                      *)
(*   psl211_rho_im      == rho's image is the generated group itself          *)
(*   psl211_2transitive == the group acts 2-transitively on the twelve        *)
(*                         positions                                          *)
(*                                                                            *)
(* 2-transitivity carries the ten-reveal ambiguity transport and the          *)
(* single-card uniformity of the profile (psl211_2transitive). The            *)
(* privacy threshold does not rest on it: that bound comes from the equal     *)
(* pattern counts of the two Steiner tables in psl211_blocks.v.               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finset fingroup perm.
From mathcomp Require Import morphism action div.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface psl211_blocks.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* The two letters as permutations of 'I_12.                                  *)
(* -------------------------------------------------------------------------- *)

(* Ordinal in 'I_12 from a natural number, by reduction modulo 12. *)
Local Definition Imod (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).

(* The 'I_12 -> 'I_12 function read off a table by position. *)
Local Definition tbl_fun (tbl : seq nat) (i : 'I_12) : 'I_12 :=
  Imod (nth 0 tbl i).

(** psl211_r4_inj — the block-reversal table is an involution, hence
    injective. *)
Lemma psl211_r4_inj : injective (tbl_fun psl211_r4_tbl).
Proof.
apply: (can_inj (g := tbl_fun psl211_r4_tbl)).
by move=> x; apply: val_inj;
   case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_m6_inj — the half-Monge table is cancelled by the half-milk
    table, hence injective. *)
Lemma psl211_m6_inj : injective (tbl_fun psl211_m6_tbl).
Proof.
apply: (can_inj (g := tbl_fun psl211_milk6_tbl)).
by move=> x; apply: val_inj;
   case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_r4_perm — the block-reversal letter as a permutation of the
    twelve positions. *)
Definition psl211_r4_perm : {perm 'I_12} := perm psl211_r4_inj.

(** psl211_m6_perm — the half-Monge letter as a permutation of the twelve
    positions. *)
Definition psl211_m6_perm : {perm 'I_12} := perm psl211_m6_inj.

(** psl211_gens — reverse each four-card block, Monge-shuffle each half. The
    generator tuple driving psl211_M. *)
Definition psl211_gens : 2.-tuple {perm 'I_12} :=
  [tuple psl211_r4_perm; psl211_m6_perm].

(* A Notation, as pgl27_M: an ascription would seal the hasGenerators
   structure that ShuffleMarginalBound needs downstream. *)
Notation psl211_M := (@Gen_PGGTypes 1 10 psl211_gens).

(* The two numerals are pinned by the generator tuple's type: 1 gives the
   two-letter generator count, 10 the twelve-card deck. Neither moves. *)
Fail Definition bad_N := (@Gen_PGGTypes 1 9 psl211_gens).
Fail Definition bad_T := (@Gen_PGGTypes 2 10 psl211_gens).

(** psl211_N' — the deck has twelve positions. *)
Lemma psl211_N' : pgg_N' psl211_M = 11.
Proof. by []. Qed.

(** psl211_gens_in_G — each of the two letters lies in the shuffle group it
    generates. *)
Lemma psl211_gens_in_G (i : 'I_2) : tnth psl211_gens i \in pgg_G psl211_M.
Proof. by apply: mem_gen; apply/imsetP; exists i. Qed.

(** psl211_r4_permE — the block-reversal permutation acts on a position by
    table lookup. *)
Lemma psl211_r4_permE (x : 'I_12) :
  val (psl211_r4_perm x) = nth 0 psl211_r4_tbl (val x).
Proof.
rewrite permE /tbl_fun /Imod /=.
by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_m6_permE — the half-Monge permutation acts on a position by table
    lookup. *)
Lemma psl211_m6_permE (x : 'I_12) :
  val (psl211_m6_perm x) = nth 0 psl211_m6_tbl (val x).
Proof.
rewrite permE /tbl_fun /Imod /=.
by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_m6_permVE — the inverse of the half-Monge letter acts on a
    position by the half-milk table. *)
Lemma psl211_m6_permVE (x : 'I_12) :
  val ((psl211_m6_perm^-1)%g x) = nth 0 psl211_milk6_tbl (val x).
Proof.
have K : cancel (tbl_fun psl211_milk6_tbl) (tbl_fun psl211_m6_tbl).
  by move=> y; apply: val_inj;
     case: y => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
have -> : (psl211_m6_perm^-1)%g x = tbl_fun psl211_milk6_tbl x.
  by apply: (perm_inj (s := psl211_m6_perm)); rewrite permKV permE K.
by rewrite /tbl_fun /Imod /=;
   case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_G_pos — the shuffle group has positive order, so the uniform
    distribution on it is well defined. *)
Lemma psl211_G_pos : (0 < #|pgg_G psl211_M|)%N.
Proof. exact: cardG_gt0. Qed.

(** psl211_rho_im — the permutation image of the monodromy morphism is the
    generated shuffle group itself, so an orbit computed in the group
    transports to the image. *)
Lemma psl211_rho_im :
  (@pgg_rho psl211_M @* pgg_G psl211_M)%g = pgg_G psl211_M.
Proof. by rewrite morphimEdom imset_id. Qed.

(* -------------------------------------------------------------------------- *)
(* In-kernel pair-word certificate: nat-level word search.                    *)
(* A word is a seq of letter indices (0 = block reversal, 1 = half Monge).  *)
(* A fueled BFS from the base pair [:: 0; 1] finds, for each of the 132       *)
(* ordered distinct position pairs, a word carrying the base pair to it; the  *)
(* checker re-verifies every entry by computation.                            *)
(* -------------------------------------------------------------------------- *)

(** psl211_wgenn i — the nat-level action of letter i on a card position,
    read off
    the block-reversal table for i = 0 and the half-Monge table otherwise. *)
Definition psl211_wgenn (i : nat) : nat -> nat :=
  if i == 0 then (fun a => nth 0 psl211_r4_tbl a)
  else (fun a => nth 0 psl211_m6_tbl a).

(** psl211_papply w a — the position reached from a by applying the letters
    of the
    word w left to right. *)
Definition psl211_papply (w : seq nat) (a : nat) : nat :=
  foldl (fun x i => psl211_wgenn i x) a w.

(* One letter applied coordinatewise to a list of positions. *)
Local Definition wstep (i : nat) (t : seq nat) : seq nat :=
  map (psl211_wgenn i) t.

(** wapply w t — the word w applied coordinatewise to a list of positions. *)
Local Definition wapply (w : seq nat) (t : seq nat) : seq nat :=
  foldl (fun acc i => wstep i acc) t w.

(* Fueled word search, keeping one word per reached pair. *)
Local Fixpoint word_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (wstep i tw.1, rcons tw.2 i) | i <- [:: 0; 1]] | tw <- seen] in
    let add := foldl (fun acc tw =>
      if has (fun sw : seq nat * seq nat => sw.1 == tw.1) (seen ++ acc)
      then acc else rcons acc tw) [::] nxt in
    if size add == 0 then seen else word_bfs f (seen ++ add)
  end.

(* Reached pairs paired with a carrying word, from the base pair. *)
Local Definition word_table : seq (seq nat * seq nat) :=
  word_bfs 20 [:: ([:: 0; 1], [::])].

(* Every ordered distinct pair has a table word carrying the base pair to it. *)
Local Definition word_table_ok : bool :=
  all (fun a => all (fun b =>
    (a != b) ==>
    has (fun sw : seq nat * seq nat =>
      (sw.1 == [:: a; b]) && (wapply sw.2 [:: 0; 1] == [:: a; b]))
      word_table)
    (iota 0 12)) (iota 0 12).

(* Every word in the table re-verifies against every ordered distinct pair. *)
Local Lemma word_table_okT : word_table_ok.
Proof. by vm_compute. Qed.

(* Word application on a pair is coordinatewise scalar application. *)
Local Lemma wapply_map (w : seq nat) (a b : nat) :
  wapply w [:: a; b] = [:: psl211_papply w a; psl211_papply w b].
Proof. by elim: w a b => [|i w IH] a b //=. Qed.

(* The perm-level letter selected by a word index. *)
Local Definition gen_of (i : nat) : {perm 'I_12} :=
  if i == 0 then psl211_r4_perm else psl211_m6_perm.

(** psl211_word_perm w — the word w folded into the composite shuffle
    permutation
    obtained by multiplying its letters left to right. *)
Definition psl211_word_perm (w : seq nat) : {perm 'I_12} :=
  foldl (fun g i => (g * gen_of i)%g) 1%g w.

(* Each letter lies in the generated shuffle group. *)
Local Lemma gen_of_mem (i : nat) : gen_of i \in pgg_G psl211_M.
Proof.
apply: mem_gen; apply/imsetP; rewrite /gen_of.
case: (i == 0); first by exists (@Ordinal 2 0 isT).
by exists (@Ordinal 2 1 isT).
Qed.

(** psl211_word_perm_mem — every composite word permutation lies in the
    shuffle
    group. *)
Lemma psl211_word_perm_mem (w : seq nat) :
  psl211_word_perm w \in pgg_G psl211_M.
Proof.
rewrite /psl211_word_perm.
have g1 : 1%g \in pgg_G psl211_M by exact: group1.
elim: w (1%g) g1 => [|i w IH] g gG //=.
by apply: IH; apply: groupM => //; exact: gen_of_mem.
Qed.

(* The perm-level letter agrees with the nat-level table action. *)
Local Lemma gen_of_val (i : nat) (x : 'I_12) :
  val (gen_of i x) = psl211_wgenn i (val x).
Proof.
rewrite /gen_of /psl211_wgenn; case: (i == 0).
  by rewrite psl211_r4_permE.
by rewrite psl211_m6_permE.
Qed.

(** psl211_word_perm_val — the composite word permutation agrees with
    nat-level word
    application along val: the perm and table layers name one action. *)
Lemma psl211_word_perm_val (w : seq nat) (x : 'I_12) :
  val (psl211_word_perm w x) = psl211_papply w (val x).
Proof.
rewrite /psl211_word_perm /psl211_papply.
have H : forall (w' : seq nat) (g : {perm 'I_12}) (y : 'I_12),
    val (foldl (fun h i => (h * gen_of i)%g) g w' y)
    = foldl (fun a i => psl211_wgenn i a) (val (g y)) w'.
  by elim=> [|i w' IH] g y //=; rewrite IH permM gen_of_val.
by rewrite H perm1.
Qed.

(* For every ordered distinct pair the BFS table exhibits a carrying word. *)
Local Lemma pair_word (x y : 'I_12) :
  x != y ->
  exists w : seq nat, psl211_papply w 0 = val x /\ psl211_papply w 1 = val y.
Proof.
move=> nxy.
have Hin : forall n : 'I_12, val n \in iota 0 12.
  by move=> n; rewrite mem_iota; case: n.
have Hd : val x != val y by rewrite val_eqE.
move: word_table_okT.
move=> /allP/(_ _ (Hin x))/allP/(_ _ (Hin y)).
move=> /implyP/(_ Hd)/hasP[[t w] /= _ /andP[_ /eqP Hw]].
exists w; move: Hw; rewrite wapply_map.
by case=> -> ->.
Qed.

(** psl211_2transitive — the shuffle group acts 2-transitively on the twelve
    positions. Ten-reveal ambiguity transport and single-card profile
    uniformity rest on this; the privacy threshold does not, since that bound
    comes from the equal pattern counts of the two Steiner tables. *)
Lemma psl211_2transitive :
  ntransitive 2 (@pgg_rho psl211_M @* pgg_G psl211_M) [set: 'I_12] 'P.
Proof.
rewrite /ntransitive psl211_rho_im.
pose t0 : 2.-tuple 'I_12 := [tuple (@Ordinal 12 0 isT); (@Ordinal 12 1 isT)].
have Ht0 : t0 \in 2.-dtuple([set: 'I_12]).
  by rewrite inE; apply/andP; split=> //; apply/subsetP => u _; rewrite inE.
apply/imsetP; exists t0 => //.
apply/setP => u; apply/idP/idP => [Hu | /orbitP[a aG <-]]; last first.
  apply: n_act_dtuple => //.
  by apply/astabsP => v; rewrite !inE.
case/tupleP: u Hu => x u; case/tupleP: u => y u.
rewrite tuple0 inE => /andP[Huniq _].
have nxy : x != y by move: Huniq; rewrite /= !inE andbT.
have [w [Hx Hy]] := pair_word nxy.
apply/orbitP; exists (psl211_word_perm w); first exact: psl211_word_perm_mem.
apply: eq_from_tnth => j.
rewrite tnth_map.
case: j => -[|[|//]] Hj; apply: val_inj => /=.
  by rewrite [tnth t0 _]/= psl211_word_perm_val Hx.
by rewrite [tnth t0 _]/= psl211_word_perm_val Hy.
Qed.
