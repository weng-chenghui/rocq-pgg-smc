(* P8 arm-relations probe, second name pass: the bridge between a pushforward
   read as a law and a pushforward read as a probability, and the small facts
   the two ledgers consume. No claim is proved here. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Search "pfwd1" inside proba.
Check @Pr_set0.
Check @Pr_setT.
Check @fdist_prodE.
Check @var_dist_fdistmap_pair.
Check @idealproximity_tail.
Check @instance_endpoints_stmt.
Check @exec_static_endpoints.
Check @pnatr_eq0.
Check @cards0.
Check @Order.POrderTheory.le_lt_trans.
Check @Order.POrderTheory.ltxx.
