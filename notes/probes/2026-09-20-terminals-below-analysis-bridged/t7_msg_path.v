(* PROBE, not production. The rejection of row T7, compiled without Fail so   *)
(* that its message can be read and quoted in LEDGER.md.                      *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From belowprobe Require Import t_framework.
From belowprobe Require Import t_pgl27.

Definition pgl27_word_published_pathE_false :
  published_level_path pgl27_word_published_sampled = pgl27_word_path := erefl.
