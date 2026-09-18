(* Axiom check after orbit_encode became the threshold-five pair and the two *)
(* instances swapped roles: the six headline statements of                   *)
(* pgl27_leakage_r7.v and pgl27_leakage_r5.v, expected to rest on the three  *)
(* boolp axioms only, and the decoder agreement of                           *)
(* pgl27_encoding_compare.v, expected closed.                                *)
From pgg_smc Require Import pgl27_leakage_r7 pgl27_leakage_r5.
From pgg_smc Require Import pgl27_encoding_compare.

Print Assumptions pgl27_r7_view_mutual_infoE.
Print Assumptions pgl27_r5_view_mutual_infoE.
Print Assumptions pgl27_r7_trace_mutual_infoE.
Print Assumptions pgl27_r5_trace_mutual_infoE.
Print Assumptions pgl27_r5_view_determines.
Print Assumptions pgl27_r7_view_determines.
Print Assumptions pgl27_compare_classE.
