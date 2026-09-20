(* PROBE, not production. The rejection of row T5, fourth case, compiled      *)
(* without Fail so that its message can be read and quoted in LEDGER.md.      *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From belowprobe Require Import t_framework.

Section M.
Variable r : PublishedObserved.
Check (r : Published).
End M.
