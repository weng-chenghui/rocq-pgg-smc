(* Axiom check after the style-audit-D fixes: the six headline statements of *)
(* pgl27_leakage_r7.v and pgl27_leakage_r5.v, expected to rest on the three  *)
(* boolp axioms only.                                                        *)
From pgg_smc Require Import pgl27_leakage_r7 pgl27_leakage_r5.

Print Assumptions pgl27_r7_view_mutual_infoE.
Print Assumptions pgl27_r5_view_mutual_infoE.
Print Assumptions pgl27_r7_trace_mutual_infoE.
Print Assumptions pgl27_r5_trace_mutual_infoE.
Print Assumptions pgl27_r7_view_determines.
Print Assumptions pgl27_r5_view_determines.
