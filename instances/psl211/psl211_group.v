(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_group: the PSL(2,11) monodromy on the twelve card positions         *)
(*                                                                            *)
(* The twelve card positions are identified with 'I_12. Two shuffle letters   *)
(* generate the monodromy group, each given as an explicit permutation table  *)
(* of 'I_12 read off psl211_blocks.v:                                         *)
(*                                                                            *)
(*   psl211_r4_perm == reverse each of the three four-card blocks             *)
(*                     0..3, 4..7, 8..11                                      *)
(*                     (psl211_r4_tbl    = [3;2;1;0;7;6;5;4;11;10;9;8])       *)
(*   psl211_m6_perm == Monge-shuffle each of the two halves 0..5, 6..11       *)
(*                     (psl211_m6_tbl    = [3;2;4;1;5;0;9;8;10;7;11;6]),      *)
(*                     inverted by the milk table                             *)
(*                     (psl211_milk6_tbl = [5;3;1;0;2;4;11;9;7;6;8;10])       *)
(*                                                                            *)
(* A third letter, the inverse of the half-Monge shuffle, closes the          *)
(* alphabet under inversion. A nat-level breadth-first search enumerates      *)
(* the group as permutation tables of 'I_12 and a checker re-verifies the     *)
(* 660-entry closure, which fixes the group order. That closure, its          *)
(* predecessor table and the table transport psl211_ptbl are the ground       *)
(* layer a length-L random word walk on the group runs on.                    *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_gens == the two letters as a 2.-tuple {perm 'I_12}                *)
(*   psl211_M    == the MonodromyReprType [@Gen_PGGTypes 1 10 psl211_gens]    *)
(*                  (a Notation, so HB keeps the hasGenerators structure)     *)
(*   psl211_word_perm w == a word w over the two letter indices, folded       *)
(*                          into the composite shuffle permutation it names   *)
(*   psl211_moves == the inverse-closed three-letter walk alphabet            *)
(*   psl211_inv_letter == the letter inverting letter j, an involution        *)
(*                        of the three letter indices                         *)
(*   psl211_mtbl j == the permutation table of the j-th letter                *)
(*   psl211_mcomp, psl211_idt == composition of permutation tables, and       *)
(*                        the table of the identity shuffle                   *)
(*   psl211_elem_table == the closure of the group as permutation tables,     *)
(*                        keys paired with carrying words                     *)
(*   psl211_tbl_index t == the state index of the table t                     *)
(*   psl211_pred_table == the three reverse-walk predecessors of a key        *)
(*   psl211_entry_perm k == the shuffle named by state index k                *)
(*   psl211_ptbl g == the permutation table of a shuffle                      *)
(*   psl211_gen3_of j == the letter of the walk alphabet at index j           *)
(*   psl211_word3_perm w == a word over the three letter indices, folded      *)
(*                        into the shuffle permutation it names               *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_N'          == the deck has twelve positions                      *)
(*   psl211_G_pos       == the shuffle group is nonempty                      *)
(*   psl211_rho_im      == rho's image is the generated group itself          *)
(*   psl211_2transitive == the group acts 2-transitively on the twelve        *)
(*                         positions                                          *)
(*   psl211_ptbl_morph  == the table of a product is the composition of       *)
(*                         the two tables                                     *)
(*   psl211_ptbl_inj    == distinct shuffles have distinct tables             *)
(*   psl211_gen3_eq     == the three letters generate the shuffle group       *)
(*   psl211_card        == the shuffle group has exactly 660 elements         *)
(*                                                                            *)
(* 2-transitivity carries the ten-reveal ambiguity transport and the          *)
(* single-card uniformity of the profile (psl211_2transitive). The            *)
(* privacy threshold does not rest on it: that bound comes from the equal     *)
(* pattern counts of the two Steiner tables in psl211_blocks.v.               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finset fingroup perm.
From mathcomp Require Import morphism action bigop div.
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

(* -------------------------------------------------------------------------- *)
(* The three-letter walk alphabet and its permutation tables of 'I_12.        *)
(* -------------------------------------------------------------------------- *)

(** psl211_moves — the three-letter alphabet the random word walks along:
    block reversal, the half-Monge shuffle, and the inverse of the half-Monge
    shuffle.  Block reversal is an involution and the other two letters are
    mutually inverse, so the alphabet is closed under inversion and the
    L-letter word shuffle is a symmetric random walk on the group the three
    letters generate, which is the PSL(2,11) shuffle group. *)
Definition psl211_moves : 3.-tuple {perm 'I_12} :=
  [tuple psl211_r4_perm; psl211_m6_perm; (psl211_m6_perm^-1)%g].

(** psl211_inv_letter — the letter whose permutation inverts letter j, and so
    the letter carrying a state back along the reverse walk.  Block reversal
    is paired with itself and the two Monge letters with each other, so the
    reverse walk needs no letter the forward walk does not already have.
    Inversion-closure, weaker than every letter being an involution, is what
    makes the transition matrix of the walk symmetric. *)
Definition psl211_inv_letter (j : nat) : nat := nth 0 [:: 0; 2; 1] j.

(** psl211_mtbl j — the permutation table of the j-th letter, read off by
    position from psl211_blocks.v.  The alphabet is described entirely by
    these three rows, which is the form the breadth-first search and the walk
    recursion compute in. *)
Definition psl211_mtbl (j : nat) : seq nat :=
  nth [::] [:: psl211_r4_tbl; psl211_m6_tbl; psl211_milk6_tbl] j.

(* The three letters agree with the rows of psl211_mtbl they were written
   down as, so the inverse letter reaches the kernel as a table rather than
   as an inversion. *)
Local Lemma gfwd_r4 (x : 'I_12) :
  val (psl211_r4_perm x) = nth 0 (psl211_mtbl 0) (val x).
Proof. exact: psl211_r4_permE. Qed.
Local Lemma gfwd_m6 (x : 'I_12) :
  val (psl211_m6_perm x) = nth 0 (psl211_mtbl 1) (val x).
Proof. exact: psl211_m6_permE. Qed.
Local Lemma gfwd_milk6 (x : 'I_12) :
  val ((psl211_m6_perm^-1)%g x) = nth 0 (psl211_mtbl 2) (val x).
Proof. exact: psl211_m6_permVE. Qed.

(* Each of the three letters sends a position to the entry of its own table
   at that position. *)
Local Lemma mtbl_val (j : 'I_3) (x : 'I_12) :
  val (tnth psl211_moves j x) = nth 0 (psl211_mtbl j) (val x).
Proof.
case: j => -[|[|[|//]]] Hj; rewrite (tnth_nth 1%g) /=.
- exact: gfwd_r4.
- exact: gfwd_m6.
- exact: gfwd_milk6.
Qed.

(* -------------------------------------------------------------------------- *)
(* Nat-level breadth-first search over the group as permutation tables.       *)
(* -------------------------------------------------------------------------- *)

(** psl211_mcomp t1 t2 — composition of two permutation tables: the table of
    the second read at the entries of the first. *)
Definition psl211_mcomp (t1 t2 : seq nat) : seq nat :=
  map (fun x => nth 0 t2 x) t1.

(** psl211_idt — the table of the identity shuffle, the twelve positions in
    order.  The state the walk starts from. *)
Definition psl211_idt : seq nat := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].

(* Fueled search keeping, for each reached table, a carrying letter word. *)
Local Fixpoint elem_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (psl211_mcomp tw.1 (psl211_mtbl j), rcons tw.2 j)
           | j <- [:: 0; 1; 2]]
      | tw <- seen] in
    let add := foldl (fun acc tw =>
      if has (fun sw : seq nat * seq nat => sw.1 == tw.1) (seen ++ acc)
      then acc else rcons acc tw) [::] nxt in
    if size add == 0 then seen else elem_bfs f (seen ++ add)
  end.

(** psl211_elem_table — the shuffle group enumerated as permutation tables,
    each key paired with a letter word carrying the identity to it.  The
    state space of the word walk, in the representation a kernel computation
    can reduce. *)
Definition psl211_elem_table : seq (seq nat * seq nat) :=
  elem_bfs 12 [:: (psl211_idt, [::])].

(** psl211_tbl_index t — the position of the table t among the enumerated
    keys, and the state index the walk addresses t by. *)
Definition psl211_tbl_index (t : seq nat) : nat :=
  find (fun sw : seq nat * seq nat => sw.1 == t) psl211_elem_table.

(** psl211_pred_table — for each key, the indices of its three reverse-walk
    predecessors, one per letter.  The transition data the length-L walk
    recursion folds over. *)
Definition psl211_pred_table : seq (seq nat) :=
  [seq [seq psl211_tbl_index
          (psl211_mcomp sw.1 (psl211_mtbl (psl211_inv_letter j)))
       | j <- [:: 0; 1; 2]]
  | sw <- psl211_elem_table].

(* The closure has 660 uniq keys, opens at the identity, every recorded word
   folds to its key, every one-letter successor stays in the list, and every
   word carries only letters below three. *)
Local Definition elem_table_ok : bool :=
  [&& size psl211_elem_table == 660,
      uniq (unzip1 psl211_elem_table),
      nth ([::], [::]) psl211_elem_table 0 == (psl211_idt, [::]),
      all (fun sw : seq nat * seq nat =>
             foldl (fun t j => psl211_mcomp t (psl211_mtbl j))
                   psl211_idt sw.2 == sw.1)
          psl211_elem_table,
      all (fun sw : seq nat * seq nat =>
             all (fun j => nth [::] (unzip1 psl211_elem_table)
                     (psl211_tbl_index (psl211_mcomp sw.1 (psl211_mtbl j)))
                   == psl211_mcomp sw.1 (psl211_mtbl j))
                 [:: 0; 1; 2])
          psl211_elem_table
    & all (fun sw : seq nat * seq nat =>
             all (fun j => j < 3) sw.2) psl211_elem_table].

(* Every conjunct of elem_table_ok holds.  This single kernel computation is
   what the group order and the walk's 660-state indexing both rest on: it
   fixes the number of states, their uniqueness, the state of the identity,
   and closure of the state set under the three letters. *)
Local Lemma elem_table_okT : elem_table_ok.
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* Small facts read off the closure checker: the six conjuncts of             *)
(* elem_table_ok, each projected out for use on its own.                      *)
(* -------------------------------------------------------------------------- *)

(** psl211_size_elem_table — the closure holds 660 entries.  The conjunct
    that fixes the order of the shuffle group, the entries being in bijection
    with it. *)
Lemma psl211_size_elem_table : size psl211_elem_table = 660.
Proof. by move: elem_table_okT => /andP[/eqP H _]. Qed.

(** psl211_uniq_elem_keys — distinct entries of the closure carry distinct
    keys, so a key names at most one state index. *)
Lemma psl211_uniq_elem_keys : uniq (unzip1 psl211_elem_table).
Proof. by move: elem_table_okT => /andP[_ /andP[H _]]. Qed.

(** psl211_elem_table0 — state 0 is the identity shuffle, reached by the
    empty word. *)
Lemma psl211_elem_table0 :
  nth ([::], [::]) psl211_elem_table 0 = (psl211_idt, [::]).
Proof. by move: elem_table_okT => /andP[_ /andP[_ /andP[/eqP H _]]]. Qed.

(* Every recorded word folds the identity table to its own key. *)
Local Lemma elem_fold_key (sw : seq nat * seq nat) :
  sw \in psl211_elem_table ->
  foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) psl211_idt sw.2 = sw.1.
Proof.
move=> Hsw; apply/eqP.
by move: elem_table_okT =>
  /andP[_ /andP[_ /andP[_ /andP[/allP/(_ _ Hsw) H _]]]].
Qed.

(* Every one-letter successor of a key is found again among the keys. *)
Local Lemma elem_closed (sw : seq nat * seq nat) :
  sw \in psl211_elem_table ->
  all (fun j => nth [::] (unzip1 psl211_elem_table)
          (psl211_tbl_index (psl211_mcomp sw.1 (psl211_mtbl j)))
        == psl211_mcomp sw.1 (psl211_mtbl j)) [:: 0; 1; 2].
Proof.
move=> Hsw.
by move: elem_table_okT =>
  /andP[_ /andP[_ /andP[_ /andP[_ /andP[/allP/(_ _ Hsw) H _]]]]].
Qed.

(* Every recorded word carries only letters of the three-letter alphabet. *)
Local Lemma elem_letters (sw : seq nat * seq nat) :
  sw \in psl211_elem_table -> all (fun j => j < 3) sw.2.
Proof.
move=> Hsw.
by move: elem_table_okT =>
  /andP[_ /andP[_ /andP[_ /andP[_ /andP[_ /allP/(_ _ Hsw) H]]]]].
Qed.

(* Tables composed by psl211_mcomp and folded keep length twelve. *)
Local Lemma size_mcomp (t1 t2 : seq nat) :
  size (psl211_mcomp t1 t2) = size t1.
Proof. by rewrite /psl211_mcomp size_map. Qed.
Local Lemma size_fold (w : seq nat) :
  size (foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) psl211_idt w) = 12.
Proof.
have gen : forall (w' : seq nat) (t : seq nat), size t = 12 ->
    size (foldl (fun t0 j => psl211_mcomp t0 (psl211_mtbl j)) t w') = 12.
  by elim=> [|j w' IH] t Ht //=; apply: IH; rewrite size_mcomp.
by apply: gen.
Qed.

(* Every closure key is a table of the twelve positions. *)
Local Lemma elem_key_size (sw : seq nat * seq nat) :
  sw \in psl211_elem_table -> size sw.1 = 12.
Proof. by move=> Hsw; rewrite -(elem_fold_key Hsw) size_fold. Qed.

(* Every one-letter successor of a key is itself a key. *)
Local Lemma elem_closed_mem (sw : seq nat * seq nat) (j : nat) :
  sw \in psl211_elem_table -> j \in [:: 0; 1; 2] ->
  psl211_mcomp sw.1 (psl211_mtbl j) \in unzip1 psl211_elem_table.
Proof.
move=> Hsw Hj.
have /eqP Heq := allP (elem_closed Hsw) j Hj.
have Hsz : size (psl211_mcomp sw.1 (psl211_mtbl j)) = 12
  by rewrite size_mcomp (elem_key_size Hsw).
rewrite -Heq; apply: mem_nth.
rewrite ltnNge; apply/negP => Hge.
move: Heq; rewrite (nth_default _ Hge) => Habs.
by move: Hsz; rewrite -Habs.
Qed.

(* The identity table is a key, and by psl211_elem_table0 it is the key at
   index 0, so state 0 of the walk is the identity shuffle. *)
Local Lemma idt_in_keys : psl211_idt \in unzip1 psl211_elem_table.
Proof.
have -> : psl211_idt = nth [::] (unzip1 psl211_elem_table) 0.
  rewrite (nth_map ([::], [::])); last by rewrite psl211_size_elem_table.
  by rewrite psl211_elem_table0.
by apply: mem_nth; rewrite size_map psl211_size_elem_table.
Qed.

(* -------------------------------------------------------------------------- *)
(* The permutation-table map and its group structure.                         *)
(* -------------------------------------------------------------------------- *)

(** psl211_ptbl g — the table of a permutation of 'I_12: its list of images
    in position order.  The transport between {perm 'I_12}, where the shuffle
    group lives, and seq nat, where vm_compute reduces. *)
Definition psl211_ptbl (g : {perm 'I_12}) : seq nat :=
  [seq val (g x) | x <- enum 'I_12].

Local Lemma ptbl_nth (g : {perm 'I_12}) (x : 'I_12) :
  nth 0 (psl211_ptbl g) (val x) = val (g x).
Proof.
rewrite /psl211_ptbl (nth_map x) ?size_enum_ord ?ltn_ord //.
by rewrite nth_ord_enum.
Qed.
Local Lemma ptbl_size (g : {perm 'I_12}) : size (psl211_ptbl g) = 12.
Proof. by rewrite /psl211_ptbl size_map size_enum_ord. Qed.

(** psl211_ptbl_id — the identity shuffle has the identity table, so state 0
    of the walk and the unit of the group are the same object. *)
Lemma psl211_ptbl_id : psl211_ptbl 1%g = psl211_idt.
Proof.
apply: (@eq_from_nth _ 0); rewrite ?ptbl_size // => i Hi.
have := ptbl_nth 1%g (Ordinal Hi); rewrite perm1 /= => ->.
by case: i Hi => [|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]].
Qed.

Local Lemma size_mtbl (j : nat) : j < 3 -> size (psl211_mtbl j) = 12.
Proof. by case: j => [|[|[|//]]]. Qed.

(** psl211_ptbl_of_fwd — a permutation whose images are read off a
    length-twelve list has that list as its table.  The direction that turns
    a written-down table into a statement about a shuffle. *)
Lemma psl211_ptbl_of_fwd (g : {perm 'I_12}) (F : seq nat) :
  (forall x, val (g x) = nth 0 F (val x)) -> size F = 12 -> psl211_ptbl g = F.
Proof.
move=> Hfwd HF; apply: (@eq_from_nth _ 0); first by rewrite ptbl_size HF.
move=> i; rewrite ptbl_size => Hi.
transitivity (val (g (Ordinal Hi))); first by rewrite -ptbl_nth.
by rewrite Hfwd.
Qed.

(* The tables of the two generators and of the inverse letter are the
   psl211_mtbl rows they were written down as, so the alphabet the closure
   search closes under is the alphabet of the shuffle. *)
Local Lemma ptbl_r4 : psl211_ptbl psl211_r4_perm = psl211_mtbl 0.
Proof. by apply: psl211_ptbl_of_fwd => //; exact: gfwd_r4. Qed.
Local Lemma ptbl_m6 : psl211_ptbl psl211_m6_perm = psl211_mtbl 1.
Proof. by apply: psl211_ptbl_of_fwd => //; exact: gfwd_m6. Qed.
Local Lemma ptbl_milk6 : psl211_ptbl (psl211_m6_perm^-1)%g = psl211_mtbl 2.
Proof. by apply: psl211_ptbl_of_fwd => //; exact: gfwd_milk6. Qed.

(** psl211_ptbl_sym — the permutation table of letter j is the j-th row of
    the literal alphabet table.  The alphabet the walk runs on is the
    alphabet written down, so a computation over the tables settles a
    question about the permutations. *)
Lemma psl211_ptbl_sym (j : 'I_3) :
  psl211_ptbl (tnth psl211_moves j) = psl211_mtbl (val j).
Proof.
by apply: psl211_ptbl_of_fwd;
  [exact: mtbl_val | rewrite size_mtbl // ltn_ord].
Qed.

(** psl211_ptbl_morph — the table of a product is the composition of the two
    tables.  With psl211_ptbl_inj this makes psl211_ptbl a faithful
    representation of the shuffle group inside seq nat, which is what lets a
    computation on the 660 tables settle a question about the group. *)
Lemma psl211_ptbl_morph (g h : {perm 'I_12}) :
  psl211_ptbl (g * h)%g = psl211_mcomp (psl211_ptbl g) (psl211_ptbl h).
Proof.
apply: (@eq_from_nth _ 0);
  first by rewrite ptbl_size /psl211_mcomp size_map ptbl_size.
move=> i; rewrite ptbl_size => Hi.
transitivity (val ((g * h)%g (Ordinal Hi))); first by rewrite -ptbl_nth.
rewrite permM /psl211_mcomp (nth_map 0) ?ptbl_size //.
have -> : nth 0 (psl211_ptbl g) i = val (g (Ordinal Hi)) by rewrite -ptbl_nth.
by rewrite ptbl_nth.
Qed.

(** psl211_ptbl_inj — distinct shuffles have distinct tables, so an identity
    of tables is an identity of shuffles.  The direction that turns a table
    computation back into a group fact. *)
Lemma psl211_ptbl_inj : injective psl211_ptbl.
Proof.
move=> g h Heq; apply/permP => x; apply: val_inj.
by rewrite -(ptbl_nth g) -(ptbl_nth h) Heq.
Qed.

Local Lemma ptbl_gen (i0 : 'I_2) :
  psl211_ptbl (tnth psl211_gens i0) = psl211_mtbl (val i0).
Proof.
by case: i0 => -[|[|//]] Hi0'; [exact: ptbl_r4 | exact: ptbl_m6].
Qed.

(* Every one-letter successor of a key-table is a key. *)
Local Lemma keys_closed_mem (t : seq nat) (j : nat) :
  t \in unzip1 psl211_elem_table -> j \in [:: 0; 1; 2] ->
  psl211_mcomp t (psl211_mtbl j) \in unzip1 psl211_elem_table.
Proof. by move=> /mapP[sw Hsw ->] Hj; exact: elem_closed_mem. Qed.
(* The index of a generator is one of the three letter indices. *)
Local Lemma gen_letter_mem (i0 : 'I_2) : val i0 \in [:: 0; 1; 2].
Proof. by move: i0 => [[|[|m]] Hm]. Qed.

(* Composing a key with the table of a generator gives a key. *)
Local Lemma gen_key_mem (h : {perm 'I_12}) (t : seq nat) :
  h \in [set tnth psl211_gens i0 | i0 : 'I_2] ->
  t \in unzip1 psl211_elem_table ->
  psl211_mcomp t (psl211_ptbl h) \in unzip1 psl211_elem_table.
Proof.
move=> /imsetP[i0 _ ->] Ht; rewrite ptbl_gen.
exact: (keys_closed_mem Ht (gen_letter_mem i0)).
Qed.

(* Every group element has its table among the closure keys: a group element
   is a product of generators, and the keys are closed under the generators
   and contain the identity.  The keys therefore cover the group. *)
Local Lemma group_key (g : {perm 'I_12}) :
  g \in pgg_G psl211_M -> psl211_ptbl g \in unzip1 psl211_elem_table.
Proof.
suff key : forall (n : nat) (c : 'I_n -> {perm 'I_12}),
    (forall i, c i \in [set tnth psl211_gens i0 | i0 : 'I_2]) ->
    psl211_ptbl (\prod_(i < n) c i)%g \in unzip1 psl211_elem_table.
  by move=> /gen_prodgP[n [c Hc ->]]; apply: key.
elim=> [|n IH] c Hc.
  by rewrite big_ord0 psl211_ptbl_id idt_in_keys.
rewrite big_ord_recr psl211_ptbl_morph.
have HP : psl211_ptbl (\prod_(i < n) c (widen_ord (leqnSn n) i))%g
    \in unzip1 psl211_elem_table.
  by apply: IH => i; exact: Hc.
exact: (gen_key_mem (Hc ord_max) HP).
Qed.

(* -------------------------------------------------------------------------- *)
(* The reverse direction: each key is the table of a word permutation.        *)
(* -------------------------------------------------------------------------- *)

(** psl211_gen3_of j — the perm-level letter selected by a nat index of the
    three-letter alphabet.  The bridge from the nat words the breadth-first
    search records to the shuffles they name. *)
Definition psl211_gen3_of (j : nat) : {perm 'I_12} :=
  tnth psl211_moves (inord j).

(** psl211_gen3_of_mem — every letter of the three-letter alphabet lies in
    the shuffle group, the inverse letter because a group is closed under
    inversion.  So symmetrizing the alphabet does not enlarge the state
    space. *)
Lemma psl211_gen3_of_mem (j : nat) : psl211_gen3_of j \in pgg_G psl211_M.
Proof.
rewrite /psl211_gen3_of; move: (inord j : 'I_3) => [[|[|[|m]]] Hm] //;
  rewrite (tnth_nth 1%g) /=.
- exact: (psl211_gens_in_G (@Ordinal 2 0 isT)).
- exact: (psl211_gens_in_G (@Ordinal 2 1 isT)).
- by rewrite groupV; exact: (psl211_gens_in_G (@Ordinal 2 1 isT)).
Qed.

(** psl211_word3_perm w — a word over the three-letter alphabet folded into
    the composite shuffle permutation obtained by multiplying its letters
    left to right.  One outcome of the word walk, realized as a shuffle. *)
Definition psl211_word3_perm (w : seq nat) : {perm 'I_12} :=
  foldl (fun g j => (g * psl211_gen3_of j)%g) 1%g w.

(** psl211_word3_perm_mem — every composite word over the three-letter
    alphabet lies in the shuffle group, so the walk never leaves the group it
    is meant to mix on. *)
Lemma psl211_word3_perm_mem (w : seq nat) :
  psl211_word3_perm w \in pgg_G psl211_M.
Proof.
rewrite /psl211_word3_perm.
have g1 : (1%g : {perm 'I_12}) \in pgg_G psl211_M by exact: group1.
elim: w (1%g) g1 => [|j w IH] g gG //=.
by apply: IH; apply: groupM => //; exact: psl211_gen3_of_mem.
Qed.

(* The table of the permutation of a letter word is the fold of the letters'
   tables from the identity table.  The fold over words in the breadth-first
   search and the group's product over letters are the same object, read
   through psl211_ptbl. *)
Local Lemma ptbl_word3 (w : seq nat) :
  all (fun j => j < 3) w ->
  psl211_ptbl (psl211_word3_perm w)
  = foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) psl211_idt w.
Proof.
rewrite /psl211_word3_perm.
have gen : forall (w' : seq nat) (g : {perm 'I_12}),
    all (fun j => j < 3) w' ->
    psl211_ptbl (foldl (fun h j => (h * psl211_gen3_of j)%g) g w') =
    foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) (psl211_ptbl g) w'.
  elim=> [|j w' IH] g //= /andP[Hj Hall].
  rewrite IH //; congr (foldl _ _ _).
  rewrite psl211_ptbl_morph; congr (psl211_mcomp _ _).
  rewrite /psl211_gen3_of psl211_ptbl_sym; congr psl211_mtbl.
  exact: (inordK Hj).
by move=> Hw; rewrite (gen w 1%g Hw) psl211_ptbl_id.
Qed.

(** psl211_entry_perm k — the shuffle named by state index k: the composite
    permutation of the word the closure recorded for the k-th key. *)
Definition psl211_entry_perm (k : nat) : {perm 'I_12} :=
  psl211_word3_perm (nth ([::], [::]) psl211_elem_table k).2.

(** psl211_entry_perm_mem — every state index names a member of the shuffle
    group.  With psl211_mem_G_Ps this is one half of the bijection between
    the 660 walk states and the group. *)
Lemma psl211_entry_perm_mem (k : nat) :
  psl211_entry_perm k \in pgg_G psl211_M.
Proof. exact: psl211_word3_perm_mem. Qed.

(** psl211_ptbl_entry — the table of psl211_entry_perm k is the k-th key, so
    psl211_entry_perm is a section of the key indexing: every state index the
    walk uses names an actual shuffle. *)
Lemma psl211_ptbl_entry (k : nat) : k < 660 ->
  psl211_ptbl (psl211_entry_perm k) = nth [::] (unzip1 psl211_elem_table) k.
Proof.
move=> Hk.
have Hin : nth ([::], [::]) psl211_elem_table k \in psl211_elem_table
  by apply: mem_nth; rewrite psl211_size_elem_table.
rewrite /psl211_entry_perm (ptbl_word3 (elem_letters Hin)) (elem_fold_key Hin).
by rewrite /unzip1 (nth_map ([::], [::])) ?psl211_size_elem_table.
Qed.

(* -------------------------------------------------------------------------- *)
(* The group is exactly the 660 word permutations, counted by their keys.     *)
(* -------------------------------------------------------------------------- *)

(** psl211_keys_size — keys and entries agree in count, so a state index of
    the walk is equally an index into the list of keys. *)
Lemma psl211_keys_size : size (unzip1 psl211_elem_table) = 660.
Proof. by rewrite /unzip1 size_map psl211_size_elem_table. Qed.

(** psl211_mem_G_Ps — every group element is psl211_entry_perm k for some
    index k below 660.  With psl211_entry_perm_inj this makes
    k |-> psl211_entry_perm k a bijection from the 660 walk states onto the
    shuffle group. *)
Lemma psl211_mem_G_Ps (g : {perm 'I_12}) :
  g \in pgg_G psl211_M -> g \in [seq psl211_entry_perm k | k <- iota 0 660].
Proof.
move=> Hg.
have Hk := group_key Hg.
set k := index (psl211_ptbl g) (unzip1 psl211_elem_table).
have Hklt : k < 660 by rewrite /k -psl211_keys_size index_mem.
have Hkey : psl211_ptbl (psl211_entry_perm k) = psl211_ptbl g.
  rewrite (psl211_ptbl_entry Hklt).
  exact: (@nth_index _ [::] (psl211_ptbl g) (unzip1 psl211_elem_table) Hk).
have Hgk : g = psl211_entry_perm k by apply: psl211_ptbl_inj; rewrite Hkey.
by rewrite Hgk; apply: map_f; rewrite mem_iota /= Hklt.
Qed.

(** psl211_entry_perm_inj — distinct indices below 660 name distinct
    shuffles, because their keys are distinct. *)
Lemma psl211_entry_perm_inj : {in iota 0 660 &, injective psl211_entry_perm}.
Proof.
move=> k1 k2; rewrite !mem_iota /= => Hk1 Hk2 Heq.
have Hs1 : k1 < size (unzip1 psl211_elem_table) by rewrite psl211_keys_size.
have Hs2 : k2 < size (unzip1 psl211_elem_table) by rewrite psl211_keys_size.
apply/eqP.
rewrite -(nth_uniq [::] Hs1 Hs2 psl211_uniq_elem_keys).
by apply/eqP;
  rewrite -(psl211_ptbl_entry Hk1) -(psl211_ptbl_entry Hk2) Heq.
Qed.

(** psl211_gen3_eq — the three-letter alphabet generates the same group as
    the two shuffle letters.  The realistic word shuffle therefore explores
    exactly the PSL(2,11) shuffle group, neither a subgroup nor a larger one,
    so uniformity on that group is the right mixing target. *)
Lemma psl211_gen3_eq :
  <<[set tnth psl211_moves j | j : 'I_3]>>%G = pgg_G psl211_M.
Proof.
apply: group_inj => /=; apply/eqP; rewrite eqEsubset; apply/andP; split.
- rewrite gen_subG; apply/subsetP => x /imsetP[j _ ->].
  by move: (psl211_gen3_of_mem (val j)); rewrite /psl211_gen3_of inord_val.
- rewrite gen_subG; apply/subsetP => x /imsetP[i _ ->].
  apply: mem_gen; apply/imsetP.
  move: i => [[|[|//]] Hi'].
  + by exists (@Ordinal 3 0 isT).
  + by exists (@Ordinal 3 1 isT).
Qed.

(** psl211_card — the PSL(2,11) shuffle group has exactly 660 elements.  The
    in-kernel order of the generated group, tying the walk's 660-entry state
    space to the whole group. *)
Lemma psl211_card : #|pgg_G psl211_M| = 660.
Proof.
have Hii : pgg_G psl211_M =i [seq psl211_entry_perm k | k <- iota 0 660].
  move=> g; apply/idP/idP; first exact: psl211_mem_G_Ps.
  by move=> /mapP[k _ ->]; exact: psl211_entry_perm_mem.
rewrite (eq_card Hii).
have Huniq : uniq [seq psl211_entry_perm k | k <- iota 0 660].
  by rewrite map_inj_in_uniq;
    [exact: iota_uniq | exact: psl211_entry_perm_inj].
move/card_uniqP: Huniq => ->.
by rewrite size_map size_iota.
Qed.
