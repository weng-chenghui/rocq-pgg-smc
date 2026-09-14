(* audit_mixing: ledger row L15 of the PSL(2,11) spec, with the scope bug of
   probe_mixing.v line 91 repaired (%N is mathcomp's nat_scope, not BinNat's
   N_scope; pgl27_mixing.v writes %num).  Compile with
     sh run.sh audit-soundness/audit_mixing.v
   from notes/probes/2026-09-14-psl211, and read the wall-clock time. *)

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

(* Every state has exactly three predecessors, so the walk really does count
   length-L words and the total mass is 3^L. *)
Local Lemma pred_table_regular : all (fun ps => size ps == 3) pred_table.
Proof. by vm_compute. Qed.

Local Fixpoint walkN (L : nat) : seq N :=
  match L with
  | 0 => 1%num :: nseq 659 0%num
  | L'.+1 =>
    let d := walkN L' in
    [seq foldl (fun a k => (a + nth 0%num d k)%num) 0%num ps | ps <- pred_table]
  end.

Local Definition total (d : seq N) : N := foldl (fun a x => (a + x)%num) 0%num d.

Local Lemma walk1_total : total (walkN 1) = 3%num. Proof. by vm_compute. Qed.
Local Lemma walk50_total : total (walkN 50) = N.pow 3 50.
Proof. by vm_compute. Qed.
Local Lemma walk100_total : total (walkN 100) = N.pow 3 100.
Proof. by vm_compute. Qed.
Local Lemma walk200_total : total (walkN 200) = N.pow 3 200.
Proof. by vm_compute. Qed.
