(* Axiom check after the group-C ruling pass of 2026-09-18 (fix agent F2).
   T1 replaced the two pgl27_r7_* trace bridges by delta-unfolding proofs.
   Each About line labels the Print Assumptions block that follows it. *)
From pgg_smc Require Import pgl27_trace_encoding.
From pgg_smc Require Import pgl27_leakage_r7 pgl27_leakage_r5.
From pgg_smc Require Import pgl27_encoding_compare.

About pgl27_r7_player_traceE.
Print Assumptions pgl27_r7_player_traceE.

About pgl27_r7_coalition_traceE.
Print Assumptions pgl27_r7_coalition_traceE.

About pgl27_compare_classE.
Print Assumptions pgl27_compare_classE.

About pgl27_r7_trace_mutual_infoE.
Print Assumptions pgl27_r7_trace_mutual_infoE.

About pgl27_r5_trace_mutual_infoE.
Print Assumptions pgl27_r5_trace_mutual_infoE.

About pgl27_compare_recovery_thresholdE.
Print Assumptions pgl27_compare_recovery_thresholdE.
