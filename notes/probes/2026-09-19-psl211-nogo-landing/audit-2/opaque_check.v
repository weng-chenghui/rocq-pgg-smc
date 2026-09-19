From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Definition tbl : seq nat := [:: 1; 2; 3; 4].

Local Opaque tbl.

(* simpl and cbv respect Local Opaque and leave tbl folded; vm_compute
   ignores it and prints 1. A lemma is no evidence here: ssreflect's done
   closes count (fun n => n == 3) tbl = 1 by kernel conversion, which
   ignores the oracle as well. *)
Eval simpl in (count (fun n => n == 3) tbl).
Eval cbv in (count (fun n => n == 3) tbl).
Eval vm_compute in (count (fun n => n == 3) tbl).
