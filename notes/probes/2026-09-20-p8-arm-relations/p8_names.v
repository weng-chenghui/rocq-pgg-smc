(* P8 arm-relations probe: resolve the library names the ledger cites, and
   check the one conversion B2 depends on. No claim is proved here. *)

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

Print var_dist.
Print inde_RV.
Check @inde_dist_of_RV2.
Check @fdistmap_comp.
Check @fdist_prod1.
Check @var_dist_fdistmap.
Check @var_dist_triangle.
Check @fdist_prod_snd.
Check @var_dist_prodR.
Check @fdistmap_prodr.
Check @var_dist_le2.
Check @fdistmap_neq0_codom.
Check @sa_coalition_viewE.
Check @static_coalition_obs.
Check @pfwd1E.

Search "inde_RV" inside proba.

Section conversion_between_the_two_input_carriers.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Check (erefl : ex_inputT E = ep_inputT (instance_exec E)).
End conversion_between_the_two_input_carriers.
