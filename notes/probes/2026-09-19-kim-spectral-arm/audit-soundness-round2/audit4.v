(* Round-2 soundness audit scratch file, part 3. NOT part of the probe.
   What a landing breaks in manifest/pgg_analysis_manifest.v itself. *)
From mathcomp Require Import all_boot.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.

(* C1. The manifest's own status pins are erefl Checks. At the values a
   spectral landing writes, each of these three is an error and not a
   warning, so the landing edits them or the manifest stops compiling. *)
Fail Timeout 60 Check (erefl : apr_transfer five_card_row_biased = IdealFinite).
Fail Timeout 60 Check
  (erefl : apr_completion five_card_row_repeated = AnalysisBridged).
Fail Timeout 60 Check
  (erefl : apr_transfer five_card_row_repeated = IdealFinite).

(* C2. The model-slot pin survives the level change. *)
Timeout 60 Check (apr_model five_card_row_repeated
  : AnalysisModelFamily FiveCardAnalysis.observed).

(* C3. A failing Check is a hard error: this file would not compile without
   the Fail wrappers above. *)
Check (erefl : apr_transfer five_card_row_biased = StaticExecutedOnly).
