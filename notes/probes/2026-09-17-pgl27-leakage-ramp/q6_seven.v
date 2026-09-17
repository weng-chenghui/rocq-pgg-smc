From mathcomp Require Import all_ssreflect.
From pgg_smc Require Import pgl27_leakage_census.

Set Implicit Arguments.

Definition rep_seven : seq nat := [:: 0; 1; 2; 3; 4; 5; 6].

Lemma q6_uniq_seven :
  uniq (code_views false rep_seven) && uniq (code_views true rep_seven).
Proof. by vm_compute. Qed.

Lemma q6_collisions_seven : pgl27_collisions rep_seven = 0.
Proof. by vm_compute. Qed.

Lemma q6_size_views : size (code_views false rep_seven) = 336.
Proof. by vm_compute. Qed.

(* eight-position: also uniq? *)
Lemma q6_uniq_eight :
  uniq (code_views false [:: 0;1;2;3;4;5;6;7])
  && uniq (code_views true [:: 0;1;2;3;4;5;6;7]).
Proof. by vm_compute. Qed.

Lemma q6_collisions_eight : pgl27_collisions [:: 0;1;2;3;4;5;6;7] = 0.
Proof. by vm_compute. Qed.
