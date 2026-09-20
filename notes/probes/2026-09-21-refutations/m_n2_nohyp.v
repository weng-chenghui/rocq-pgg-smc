(* Probe for notes/20260921-refutations-probe-design.md. Not production text. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From refuteprobe Require Import n_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(* N2 with its hypothesis deleted: the obstruction claimed out of nothing.
   The proof body is the original one with the hypothesis H removed. *)
Fail Definition mutant_no_hypothesis (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R)
  : NoIndistinguishabilityCertNear sa U eps
  := ltac:(move=> cert Hc;
           exact (@ic_const R A E sa cert)).
