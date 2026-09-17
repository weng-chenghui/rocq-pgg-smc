(* Axiom check of the four headline closed forms after the style-ruling pass
   of 2026-09-18. Expected: the three boolp axioms only. *)
From pgg_smc Require Import pgl27_leakage_r7 pgl27_leakage_r5.

Print Assumptions pgl27_r7_view_mutual_infoE.
Print Assumptions pgl27_r5_view_mutual_infoE.
Print Assumptions pgl27_r7_trace_mutual_infoE.
Print Assumptions pgl27_r5_trace_mutual_infoE.
