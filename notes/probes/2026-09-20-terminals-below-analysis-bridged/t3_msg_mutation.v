(* PROBE, not production. The mutation of row T3, compiled without Fail so    *)
(* that its message can be read and quoted in LEDGER.md: the same program     *)
(* published under the baseline assumption status does not build the          *)
(* manifest's deterministic path.                                             *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import s5_tableau_observed.
From belowprobe Require Import t_framework.
From belowprobe Require Import t_s5.

Definition s5_det_baseline_pathE_false :
  published_level_path (publish_observed BaselineClassicalOnly s5_dealt)
  = s5_det_path := erefl.
