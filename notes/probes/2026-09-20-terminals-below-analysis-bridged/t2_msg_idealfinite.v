(* PROBE, not production. The rejection of the two-record landing landing in        *)
(* instances/s5/tableau/s5_tableau_checks.v, compiled without Fail so that   *)
(* its message can be read and quoted: rocq compile prints nothing for a     *)
(* passing Fail.                                                             *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed.
From belowprobe Require Import t_framework_two_records.
From belowprobe Require Import t_syntax_two_records.
From belowprobe Require Import t_s5_two_records.

Check (fun (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) =>
         publish_sampled a q pf IdealFinite).
