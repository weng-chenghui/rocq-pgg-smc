(* audit-naming scratch: independent check of the two numbers the ledger
   leans on, |<r4,m6>| = 660 (L14/L17) and the row counts 132/132 (needed by
   the row-count-to-element-count bridge but absent from the ledger). *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Load "psl211_tables.v".

Local Definition idt : seq nat := [:: 0;1;2;3;4;5;6;7;8;9;10;11].
Local Definition mcomp (t1 t2 : seq nat) : seq nat := [seq nth 0 t1 x | x <- t2].

Local Fixpoint closure (fuel : nat) (seen : seq (seq nat)) : seq (seq nat) :=
  match fuel with
  | 0 => seen
  | f.+1 =>
    let nxt := flatten [seq [seq mcomp t s | t <- [:: r4_tbl; m6_tbl]]
                       | s <- seen] in
    let add := foldl (fun acc s => if s \in seen ++ acc then acc else rcons acc s)
                     [::] nxt in
    if nilp add then seen else closure f (seen ++ add)
  end.

(* |<r4, m6>| = 660, the two-letter closure.  L14 runs the three-letter one. *)
Local Lemma group_order_660 : size (closure 20 [:: idt]) = 660.
Proof. by vm_compute. Qed.

(* Both tables have 132 rows and no row in common: the two facts the
   element-count bridge needs and the ledger never states. *)
Local Lemma size_tblA : size tblA = 132. Proof. by vm_compute. Qed.
Local Lemma size_tblB : size tblB = 132. Proof. by vm_compute. Qed.
Local Lemma tblA_uniq : uniq tblA. Proof. by vm_compute. Qed.
Local Lemma tblB_uniq : uniq tblB. Proof. by vm_compute. Qed.
Local Lemma tblAB_disjoint : all (fun R => R \notin tblB) tblA.
Proof. by vm_compute. Qed.

(* 660 = 132 * 5: with card_orbit_stab this pins both stabilisers at order
   five, which is what makes the two row counts comparable as element
   counts. *)
Local Lemma stab_order : 132 * 5 = 660. Proof. by []. Qed.
