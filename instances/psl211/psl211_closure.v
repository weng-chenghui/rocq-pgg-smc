(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_closure: the enumerated PSL(2,11) shuffle group, its permutation    *)
(*                 tables and its order                                       *)
(*                                                                            *)
(* The two shuffle letters of psl211_group.v are completed to an              *)
(* inverse-closed three-letter alphabet by adjoining the inverse of the       *)
(* half-Monge shuffle. A nat-level breadth-first search enumerates the group  *)
(* they generate as permutation tables of 'I_12, paired with carrying letter  *)
(* words, and a six-conjunct checker re-verifies that enumeration by kernel   *)
(* computation. The enumeration is kept as the search application and not     *)
(* as its 660-row value: storing the value made psl211_mixing.v run past      *)
(* 997 s at 4 GB against 158 s (measured 2026-09-15), although every single   *)
(* conversion site measured on its own gets faster with the value; the        *)
(* mechanism of the whole-file regression is not established.                 *)
(*                                                                            *)
(* The table transport psl211_ptbl carries the shuffle group faithfully into  *)
(* seq nat, where a kernel computation reduces; the checker's closure         *)
(* conjunct together with that transport identifies the 660 enumerated keys   *)
(* with the group, which fixes the group order at 660. Those 660 states, the  *)
(* predecessor table and the letter alphabet are the ground layer a length-L  *)
(* random word walk on the group runs on.                                     *)
(*                                                                            *)
(* Definitions:                                                               *)
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
(*   psl211_ptbl g == the permutation table of a shuffle                      *)
(*   psl211_gen3_of j == the letter of the walk alphabet at index j           *)
(*   psl211_word3_perm w == a word over the three letter indices, folded      *)
(*                        into the shuffle permutation it names               *)
(*   psl211_entry_perm k == the shuffle named by state index k                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_size_elem_table == the enumeration holds 660 entries              *)
(*   psl211_keys_uniq       == distinct entries carry distinct keys           *)
(*   psl211_elem_table0     == state 0 is the identity shuffle                *)
(*   psl211_ptbl_moves      == letter j has the j-th row of the alphabet      *)
(*                             table                                          *)
(*   psl211_ptbl_morph      == the table of a product is the composition of   *)
(*                             the two tables                                 *)
(*   psl211_ptbl_inj        == distinct shuffles have distinct tables         *)
(*   psl211_keys_closed     == the keys are closed under the three letters    *)
(*   psl211_tbl_index_lt    == a key is indexed below 660                     *)
(*   psl211_tbl_index_key   == the indexing is a section of the key list      *)
(*   psl211_ptbl_inv_letter == the inverse of letter j has the table of       *)
(*                             letter psl211_inv_letter j                     *)
(*   psl211_inv_letterE     == the inverse of letter j is again a letter      *)
(*   psl211_ptbl_entry      == state index k names the shuffle of key k       *)
(*   psl211_size_keys       == the key list has 660 entries                   *)
(*   psl211_mem_entry_perm  == every group element is named by a state index  *)
(*   psl211_entry_perm_inj  == distinct indices below 660 name distinct       *)
(*                             shuffles                                       *)
(*   psl211_gen3_eq         == the three letters generate the shuffle group   *)
(*   psl211_card            == the shuffle group has exactly 660 elements     *)
(*                                                                            *)
(* The group order is what the block stabiliser count of psl211_secrecy.v     *)
(* divides, and the 660-state indexing is what the walk of psl211_mixing.v    *)
(* tabulates. Neither the orbit certificates nor the deal scheme reads this   *)
(* file, so the closure computation stays off their build path.               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finset fingroup perm.
From mathcomp Require Import bigop.
From pgg_smc Require Import pgg_interface psl211_blocks psl211_group.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* The three-letter walk alphabet and its permutation tables of 'I_12.        *)
(* -------------------------------------------------------------------------- *)

(** psl211_moves — the three-letter alphabet the random word walks along:
    segment reversal, the half-Monge shuffle, and the inverse of the half-Monge
    shuffle.  Block reversal is an involution and the other two letters are
    mutually inverse, so the alphabet is inverse-closed and the L-letter word
    shuffle is a symmetric random walk on the group the three letters
    generate, which is the PSL(2,11) shuffle group. *)
Definition psl211_moves : 3.-tuple {perm 'I_12} :=
  [tuple psl211_r4_perm; psl211_m6_perm; (psl211_m6_perm^-1)%g].

(** psl211_inv_letter — the letter whose permutation inverts letter j, and so
    the letter carrying a state back along the reverse walk.  Block reversal
    is paired with itself and the two Monge letters with each other, so the
    reverse walk needs no letter the forward walk does not already have.
    An inverse-closed alphabet, weaker than every letter being an involution,
    is what makes the transition matrix of the walk symmetric. *)
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
    can reduce.  The search is left as an application rather than stored as
    its 660-row value: storing the value made psl211_mixing.v run past 997 s
    at 4 GB against 158 s, although each conversion site measured alone is
    faster with the value; why the whole file regresses is not established.
    Do not re-seal without re-measuring the whole file. *)
Definition psl211_elem_table : seq (seq nat * seq nat) :=
  elem_bfs 12 [:: (psl211_idt, [::])].

(** psl211_tbl_index t — the position of the table t among the enumerated
    keys, and the state index the walk addresses t by.  A table that is not a
    key gets the index 660, one past the last state, so every statement about
    psl211_tbl_index carries a membership premise. *)
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
Proof. by move: elem_table_okT => /andP[/eqP Hsize _]. Qed.

(** psl211_keys_uniq — distinct entries of the closure carry distinct
    keys, so a key names at most one state index. *)
Lemma psl211_keys_uniq : uniq (unzip1 psl211_elem_table).
Proof. by move: elem_table_okT => /andP[_ /andP[Huniq _]]. Qed.

(** psl211_elem_table0 — state 0 is the identity shuffle, reached by the
    empty word. *)
Lemma psl211_elem_table0 :
  nth ([::], [::]) psl211_elem_table 0 = (psl211_idt, [::]).
Proof. by move: elem_table_okT => /andP[_ /andP[_ /andP[/eqP Hzero _]]]. Qed.

(* Every recorded word folds the identity table to its own key. *)
Local Lemma elem_fold_key (sw : seq nat * seq nat) :
  sw \in psl211_elem_table ->
  foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) psl211_idt sw.2 = sw.1.
Proof.
move=> Hsw; apply/eqP.
by move: elem_table_okT =>
  /andP[_ /andP[_ /andP[_ /andP[/allP/(_ _ Hsw) Hfold _]]]].
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
  /andP[_ /andP[_ /andP[_ /andP[_ /andP[/allP/(_ _ Hsw) Hclosed _]]]]].
Qed.

(* Every recorded word carries only letters of the three-letter alphabet. *)
Local Lemma elem_letters (sw : seq nat * seq nat) :
  sw \in psl211_elem_table -> all (fun j => j < 3) sw.2.
Proof.
move=> Hsw.
by move: elem_table_okT =>
  /andP[_ /andP[_ /andP[_ /andP[_ /andP[_ /allP/(_ _ Hsw) Hlet]]]]].
Qed.

(* Tables composed by psl211_mcomp and folded keep length twelve. *)
Local Lemma size_mcomp (t1 t2 : seq nat) :
  size (psl211_mcomp t1 t2) = size t1.
Proof. by rewrite /psl211_mcomp size_map. Qed.
Local Lemma size_fold (w : seq nat) :
  size (foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) psl211_idt w) = 12.
Proof.
have size_gen : forall (w' : seq nat) (t : seq nat), size t = 12 ->
    size (foldl (fun t0 j => psl211_mcomp t0 (psl211_mtbl j)) t w') = 12.
  by elim=> [|j w' IH] t Ht //=; apply: IH; rewrite size_mcomp.
by apply: size_gen.
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

(* Membership in the key list as a decidable search over the enumeration. *)
Local Lemma mem_unzip1_has (t : seq nat) :
  (t \in unzip1 psl211_elem_table)
  = has (fun sw : seq nat * seq nat => sw.1 == t) psl211_elem_table.
Proof. by rewrite /unzip1 -has_pred1 has_map. Qed.

(** psl211_tbl_index_lt — a key is found at an index below 660, so
    psl211_tbl_index lands in the walk's state range.  Every use of the
    indexing carries this membership premise, since a non-key would be given
    the out-of-range index 660. *)
Lemma psl211_tbl_index_lt (t : seq nat) :
  t \in unzip1 psl211_elem_table -> (psl211_tbl_index t < 660)%N.
Proof.
rewrite mem_unzip1_has /psl211_tbl_index -psl211_size_elem_table -has_find.
exact: id.
Qed.

(** psl211_tbl_index_key — reading the key list at the index
    psl211_tbl_index assigns a key returns that key, so the indexing is a
    section of the key list and a state index of the walk determines the
    permutation table it stands for. *)
Lemma psl211_tbl_index_key (t : seq nat) :
  t \in unzip1 psl211_elem_table ->
  nth [::] (unzip1 psl211_elem_table) (psl211_tbl_index t) = t.
Proof.
(* The side conditions carrying psl211_elem_table are supplied as premises:
   letting done touch them forces the enumeration through lazy kernel
   reduction instead of reading the stored rows. *)
move=> Ht.
have Hh : has (fun sw : seq nat * seq nat => sw.1 == t) psl211_elem_table.
  by rewrite -mem_unzip1_has; exact: Ht.
have Hlt : (psl211_tbl_index t < size psl211_elem_table)%N.
  by rewrite /psl211_tbl_index -has_find; exact: Hh.
rewrite /unzip1 (nth_map ([::], [::]) _ _ Hlt).
by apply/eqP; exact: (nth_find ([::], [::]) Hh).
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

(** psl211_ptbl_moves — the permutation table of letter j is the j-th row of
    the literal alphabet table.  The alphabet the walk runs on is the
    alphabet written down, so a computation over the tables settles a
    question about the permutations. *)
Lemma psl211_ptbl_moves (j : 'I_3) :
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

(* A permutation whose forward images are read off the table F has (g^-1) x at
   Finv, whenever Finv is a right inverse of F on the twelve positions.  The
   inverse of the segment-reversal letter is given by a table this way, so no
   permutation is ever inverted inside a kernel computation. *)
Local Lemma perm_inv_val (g : {perm 'I_12}) (F Finv : seq nat) (x : 'I_12) :
  (forall y : 'I_12, val (g y) = nth 0 F (val y)) ->
  (forall k, k < 12 -> nth 0 F (nth 0 Finv k) = k) ->
  (forall k, k < 12 -> nth 0 Finv k < 12) ->
  val ((g^-1)%g x) = nth 0 Finv (val x).
Proof.
move=> Hfwd Hcomp Hrange.
have Hc12 : nth 0 Finv (val x) < 12 by apply: Hrange; exact: ltn_ord.
pose z : 'I_12 := Ordinal Hc12.
have Hgz : g z = x.
  by apply/val_inj; rewrite Hfwd /= Hcomp //; exact: ltn_ord.
have Hzx : (g^-1)%g x = z by rewrite -Hgz permK.
by rewrite Hzx.
Qed.

(* The inverse of the segment-reversal letter has the segment-reversal letter's
   own table.  Reversal of each four-position segment is an involution, which
   is why the inverse-closed alphabet has three letters and not four. *)
Local Lemma ptbl_r4_inv :
  psl211_ptbl ((psl211_r4_perm)^-1)%g = psl211_mtbl 0.
Proof.
apply: (psl211_ptbl_of_fwd (F := psl211_mtbl 0)); last by [].
move=> x; apply: (perm_inv_val (F := psl211_mtbl 0)); first exact: gfwd_r4.
- by case=> [|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]].
- by case=> [|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]].
Qed.

(** psl211_ptbl_inv_letter — the inverse of letter j has the table of letter
    psl211_inv_letter j.  The three reverse steps of the walk are again
    letters of the alphabet, which is the reason the alphabet is
    inverse-closed: the reverse walk needs no table the forward walk does not
    already have.  Read through psl211_ptbl_inj this is the inverse-closure
    the symmetric mixing bound requires of the generator multiset. *)
Lemma psl211_ptbl_inv_letter (j : 'I_3) :
  psl211_ptbl ((tnth psl211_moves j)^-1)%g
  = psl211_mtbl (psl211_inv_letter (val j)).
Proof.
case: j => -[|[|[|//]]] Hj; rewrite (tnth_nth 1%g) /=.
- exact: ptbl_r4_inv.
- exact: (psl211_ptbl_moves (@Ordinal 3 2 isT)).
- by rewrite invgK; exact: (psl211_ptbl_moves (@Ordinal 3 1 isT)).
Qed.

(** psl211_inv_letterE — the inverse of letter j is the letter at index
    psl211_inv_letter j, at the level of permutations rather than tables.
    The alphabet is therefore inverse-closed as a multiset of shuffles, which
    is what makes the word walk a symmetric random walk on the group. *)
Lemma psl211_inv_letterE (j : 'I_3) :
  ((tnth psl211_moves j)^-1)%g
  = tnth psl211_moves (inord (psl211_inv_letter (val j))).
Proof.
apply: psl211_ptbl_inj.
rewrite psl211_ptbl_inv_letter psl211_ptbl_moves; congr psl211_mtbl.
(* inordK is applied, not rewritten with: its left-hand side leaves the
   ordinal bound an evar, which no subterm of the goal fixes. *)
by apply/esym/inordK; case: j => -[|[|[|//]]].
Qed.

Local Lemma ptbl_gen (i0 : 'I_2) :
  psl211_ptbl (tnth psl211_gens i0) = psl211_mtbl (val i0).
Proof.
by case: i0 => -[|[|//]] Hi0'; [exact: ptbl_r4 | exact: ptbl_m6].
Qed.

(** psl211_keys_closed — every one-letter successor of a key-table is a key,
    so the 660 enumerated states are closed under the three letters and the
    walk never steps outside the state space it is tabulated on.  This is the
    conjunct of the checker that makes the enumeration the whole group rather
    than a reachable part of it. *)
Lemma psl211_keys_closed (t : seq nat) (j : nat) :
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
exact: (psl211_keys_closed Ht (gen_letter_mem i0)).
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
    search records to the shuffles they name.  An index of three or more is
    clamped by inord to the last letter, so a statement about a specific
    letter carries the bound on its index. *)
Definition psl211_gen3_of (j : nat) : {perm 'I_12} :=
  tnth psl211_moves (inord j).

(** psl211_gen3_of_mem — every letter of the three-letter alphabet lies in
    the shuffle group, the inverse letter because a group is closed under
    inversion.  So making the alphabet inverse-closed does not enlarge the
    state space. *)
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
have ptbl_gen_fold : forall (w' : seq nat) (g : {perm 'I_12}),
    all (fun j => j < 3) w' ->
    psl211_ptbl (foldl (fun h j => (h * psl211_gen3_of j)%g) g w') =
    foldl (fun t j => psl211_mcomp t (psl211_mtbl j)) (psl211_ptbl g) w'.
  elim=> [|j w' IH] g //= /andP[Hj Hall].
  rewrite IH //; congr (foldl _ _ _).
  rewrite psl211_ptbl_morph; congr (psl211_mcomp _ _).
  rewrite /psl211_gen3_of psl211_ptbl_moves; congr psl211_mtbl.
  exact: (inordK Hj).
by move=> Hw; rewrite (ptbl_gen_fold w 1%g Hw) psl211_ptbl_id.
Qed.

(** psl211_entry_perm k — the shuffle named by state index k: the composite
    permutation of the word the closure recorded for the k-th key.  An index
    of 660 or more reads past the enumeration and so names the identity
    shuffle, which is why injectivity below is claimed only on iota 0 660. *)
Definition psl211_entry_perm (k : nat) : {perm 'I_12} :=
  psl211_word3_perm (nth ([::], [::]) psl211_elem_table k).2.

(** psl211_entry_perm_mem — every state index names a member of the shuffle
    group.  This is the first of the three parts that make k |->
    psl211_entry_perm k a bijection from the 660 walk states onto the group:
    it lands in the group, psl211_mem_entry_perm makes it onto, and
    psl211_entry_perm_inj makes it injective on iota 0 660. *)
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

(** psl211_size_keys — keys and entries agree in count, so a state index of
    the walk is equally an index into the list of keys. *)
Lemma psl211_size_keys : size (unzip1 psl211_elem_table) = 660.
Proof. by rewrite /unzip1 size_map psl211_size_elem_table. Qed.

(** psl211_mem_entry_perm — every group element is psl211_entry_perm k for
    some index k below 660.  This is the second of the three parts of the
    bijection between the walk states and the group: with
    psl211_entry_perm_mem it lands in the group and covers it, and with
    psl211_entry_perm_inj on iota 0 660 the count of states is the group
    order. *)
Lemma psl211_mem_entry_perm (g : {perm 'I_12}) :
  g \in pgg_G psl211_M -> g \in [seq psl211_entry_perm k | k <- iota 0 660].
Proof.
move=> Hg.
have Hk := group_key Hg.
set k := index (psl211_ptbl g) (unzip1 psl211_elem_table).
have Hklt : k < 660 by rewrite /k -psl211_size_keys index_mem.
have Hkey : psl211_ptbl (psl211_entry_perm k) = psl211_ptbl g.
  rewrite (psl211_ptbl_entry Hklt).
  exact: (nth_index [::] Hk).
have Hgk : g = psl211_entry_perm k by apply: psl211_ptbl_inj; rewrite Hkey.
by rewrite Hgk; apply: map_f; rewrite mem_iota /= Hklt.
Qed.

(** psl211_entry_perm_inj — distinct indices below 660 name distinct
    shuffles, because their keys are distinct. *)
Lemma psl211_entry_perm_inj : {in iota 0 660 &, injective psl211_entry_perm}.
Proof.
move=> k1 k2; rewrite !mem_iota /= => Hk1 Hk2 Heq.
have Hs1 : k1 < size (unzip1 psl211_elem_table) by rewrite psl211_size_keys.
have Hs2 : k2 < size (unzip1 psl211_elem_table) by rewrite psl211_size_keys.
apply/eqP.
rewrite -(nth_uniq [::] Hs1 Hs2 psl211_keys_uniq).
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
  rewrite gen_subG; apply/subsetP => x /imsetP[j _ ->].
  by move: (psl211_gen3_of_mem (val j)); rewrite /psl211_gen3_of inord_val.
rewrite gen_subG; apply/subsetP => x /imsetP[i _ ->].
apply: mem_gen; apply/imsetP; move: i => [[|[|//]] Hi'].
  by exists (@Ordinal 3 0 isT).
by exists (@Ordinal 3 1 isT).
Qed.

(** psl211_card — the PSL(2,11) shuffle group has exactly 660 elements.  The
    in-kernel order of the generated group, tying the walk's 660-entry state
    space to the whole group. *)
Lemma psl211_card : #|pgg_G psl211_M| = 660.
Proof.
have Hii : pgg_G psl211_M =i [seq psl211_entry_perm k | k <- iota 0 660].
  move=> g; apply/idP/idP; first exact: psl211_mem_entry_perm.
  by move=> /mapP[k _ ->]; exact: psl211_entry_perm_mem.
rewrite (eq_card Hii).
have Huniq : uniq [seq psl211_entry_perm k | k <- iota 0 660].
  by rewrite map_inj_in_uniq;
    [exact: iota_uniq | exact: psl211_entry_perm_inj].
move/card_uniqP: Huniq => ->.
by rewrite size_map size_iota.
Qed.
