(* Audit round 2, question 6: the concluded-against-unconcluded coordinate
   equation, closed by by [] instead of exact: erefl.  The comment of
   t0_sampled_branch_pgl27.v says this search does not return. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset order ssralg ssrnum reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import pgl27_rows.
From tableau_ext_probe Require Import t0_sampled_branch_pgl27.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Lemma q6b_concluded_done :
  published_at pgl27_row_word_branch
  = published_at pgl27_row_word_branch39.
Proof. by []. Qed.
