(* Audit probe for the STATUS.md claim that vm_compute ignores Local Opaque.
   The question is whether opaque_vm_test.v isolates vm_compute, or whether
   ssreflect's done would have closed the same goal by kernel conversion. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Definition tbl : seq nat := [:: 1; 2; 3; 4].

Local Opaque tbl.

(* A: no vm_compute at all. If this succeeds, the original test does not
   separate vm_compute from ordinary conversion. *)
Lemma tbl_count_by_done : count (fun n => n == 3) tbl = 1.
Proof. by []. Qed.

(* B: what each reduction machine actually does to the term. *)
Eval simpl in (count (fun n => n == 3) tbl).
Eval cbv in (count (fun n => n == 3) tbl).
Eval vm_compute in (count (fun n => n == 3) tbl).

(* Result, rocq 9.0.0: tbl_count_by_done compiles, so ssreflect's done closes
   the goal by kernel conversion and opaque_vm_test.v does not separate
   vm_compute from ordinary conversion. Eval simpl and Eval cbv both leave tbl
   folded; Eval vm_compute prints 1. So the claim itself holds, and this pair
   of Eval lines is the evidence for it. *)
