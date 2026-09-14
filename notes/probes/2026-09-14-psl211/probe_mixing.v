(* probe_mixing: ledger rows L14, L15 of the PSL(2,11) spec.
   The elem_bfs closure and the walkN recursion of pgl27_mixing.v, at the
   three-letter alphabet {r4, m6, m6i} on 12 positions.
   PROVER: keep every statement; report wall-clock time of elem_table_okT
   and of walk100_ok; do NOT attempt L = 570 here. *)

From Stdlib Require Import BinNat Nnat.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Load "psl211_tables.v".

(* Letters 0 = r4, 1 = m6, 2 = m6i (inverse-closed alphabet). *)
Local Definition mtbl (j : nat) : seq nat :=
  nth [::] [:: r4_tbl; m6_tbl; m6i_tbl] j.

(* Composition of tables: (mcomp t1 t2) x = t1 (t2 x). *)
Local Definition mcomp (t1 t2 : seq nat) : seq nat :=
  [seq nth 0 t1 x | x <- t2].

Local Definition idt : seq nat := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].

(* Fueled BFS closure, one carrying word per element (pgl27_mixing shape). *)
Local Fixpoint elem_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | f.+1 =>
    let nxt := flatten
      [seq [seq (mcomp (mtbl j) tw.1, rcons tw.2 j) | j <- [:: 0; 1; 2]]
      | tw <- seen] in
    let add := foldl (fun acc tw =>
      if has (fun sw : seq nat * seq nat => sw.1 == tw.1) (seen ++ acc)
      then acc else rcons acc tw) [::] nxt in
    if nilp add then seen else elem_bfs f (seen ++ add)
  end.

Local Definition elem_table : seq (seq nat * seq nat) :=
  elem_bfs 20 [:: (idt, [::])].

(* L14. PROVER: time this. *)
Local Lemma size_elem_table : size elem_table = 660.
Proof. by vm_compute. Qed.

Local Lemma uniq_elem_keys : uniq (unzip1 elem_table).
Proof. by vm_compute. Qed.

(* Closure under the three letters. *)
Local Definition elem_closed_ok : bool :=
  all (fun tw => all (fun j => mcomp (mtbl j) tw.1 \in unzip1 elem_table)
                     [:: 0; 1; 2]) elem_table.
Local Lemma elem_closed_okT : elem_closed_ok. Proof. by vm_compute. Qed.

(* Mutation: the one-letter closure over r4 alone has two elements. *)
Local Fixpoint elem_bfs1 (fuel : nat) (seen : seq (seq nat)) : seq (seq nat) :=
  match fuel with
  | 0 => seen
  | f.+1 =>
    let nxt := [seq mcomp r4_tbl t | t <- seen] in
    let add := foldl (fun acc t => if t \in seen ++ acc then acc else rcons acc t)
                     [::] nxt in
    if nilp add then seen else elem_bfs1 f (seen ++ add)
  end.
Local Lemma size_closure_r4 : size (elem_bfs1 20 [:: idt]) = 2.
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------------ *)
(* L15: the walk.  Index of a key in the table, transition by letters, and  *)
(* the length-L distribution as binary-N numerators over denominator 3^L.   *)
(* ------------------------------------------------------------------------ *)

Local Definition keys : seq (seq nat) := unzip1 elem_table.

Local Definition tbl_index (t : seq nat) : nat := index t keys.

(* Successor indices of entry k under the three letters. *)
Local Definition succ (k : nat) : seq nat :=
  [seq tbl_index (mcomp (mtbl j) (nth [::] keys k)) | j <- [:: 0; 1; 2]].

Local Definition succ_table : seq (seq nat) := [seq succ k | k <- iota 0 660].

(* One step: new mass at state s is the sum of masses of predecessors. *)
Local Definition pred_table : seq (seq nat) :=
  [seq [seq k <- iota 0 660 | s \in nth [::] succ_table k] | s <- iota 0 660].

Local Fixpoint walkN (L : nat) : seq N :=
  match L with
  | 0 => 1%num :: nseq 659 0%num
  | L'.+1 =>
    let d := walkN L' in
    [seq foldl (fun a k => (a + nth 0%num d k)%num) 0%num ps | ps <- pred_table]
  end.

(* Sanity at L = 0 and L = 1: total mass 3^L. *)
Local Definition total (d : seq N) : N := foldl (fun a x => (a + x)%num) 0%num d.
Local Lemma walk1_total : total (walkN 1) = 3%num. Proof. by vm_compute. Qed.

(* L15 cost sample. PROVER: time this lemma; report it.  Extrapolation to
   L = 570 with 570/100 steps and ~5.7x longer numerators is the spec's cost
   estimate. *)
Local Lemma walk100_total : total (walkN 100) = N.pow 3 100.
Proof. by vm_compute. Qed.

(* ---- assumption audit ---- *)
Print Assumptions size_elem_table.
Print Assumptions uniq_elem_keys.
Print Assumptions elem_closed_okT.
Print Assumptions size_closure_r4.
Print Assumptions walk1_total.
Print Assumptions walk100_total.
