From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Definition tbl : seq nat := [:: 1; 2; 3; 4].

Local Opaque tbl.

Lemma tbl_size : count (fun n => n == 3) tbl = 1.
Proof. by vm_compute. Qed.
