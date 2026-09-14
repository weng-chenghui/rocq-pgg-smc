(* audit_mixing584: the real L15 question - the length-584 mixing certificate
   of the pgl27_mixing.v shape at 660 states and three letters, with the
   %N/%num scope bug of probe_mixing.v repaired.  Read the wall-clock time. *)
From Stdlib Require Import BinNat Nnat.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Load "psl211_tables.v".
Local Definition mtbl (j : nat) : seq nat :=
  nth [::] [:: r4_tbl; m6_tbl; m6i_tbl] j.
Local Definition mcomp (t1 t2 : seq nat) : seq nat :=
  [seq nth 0 t1 x | x <- t2].
Local Definition idt : seq nat := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].
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
Local Definition keys : seq (seq nat) := unzip1 elem_table.
Local Definition tbl_index (t : seq nat) : nat := index t keys.
Local Definition succ (k : nat) : seq nat :=
  [seq tbl_index (mcomp (mtbl j) (nth [::] keys k)) | j <- [:: 0; 1; 2]].
Local Definition succ_table : seq (seq nat) := [seq succ k | k <- iota 0 660].
Local Definition pred_table : seq (seq nat) :=
  [seq [seq k <- iota 0 660 | s \in nth [::] succ_table k] | s <- iota 0 660].
Local Fixpoint walkN (L : nat) : seq N :=
  match L with
  | 0 => 1%num :: nseq 659 0%num
  | L'.+1 =>
    let d := walkN L' in
    [seq foldl (fun a k => (a + nth 0%num d k)%num) 0%num ps | ps <- pred_table]
  end.
Local Definition absdiffN (a b : N) : N :=
  if (a <? b)%num then (b - a)%num else (a - b)%num.
(* The pgl27_mixing.v integer form of the mixing bound, at 660 states, three
   letters and L = 584: 2^40 times the total absolute deviation of the walk
   counts from the uniform value 3^570/660 is at most 660 * 3^570. *)
Local Definition mixing_bound_ok : bool :=
  let D := (3 ^ 584)%num in
  ((2 ^ 40) * foldl (fun acc c => (acc + absdiffN (660 * c) D)%num) 0%num
                    (walkN 584)
   <=? 660 * D)%num.
Local Lemma mixing_bound_okT : mixing_bound_ok.
Proof. by vm_compute. Qed.
