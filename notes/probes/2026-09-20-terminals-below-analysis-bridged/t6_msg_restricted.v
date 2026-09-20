(* PROBE, not production. The rejection row T6 rests on, compiled without     *)
(* Fail so that its message can be read and quoted in LEDGER.md.              *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From belowprobe Require Import t_framework.

Check (fun (a : AssumptionStatus) (s : Tableau Sampled) =>
         publish_sampled_restricted a IdealFinite s).
