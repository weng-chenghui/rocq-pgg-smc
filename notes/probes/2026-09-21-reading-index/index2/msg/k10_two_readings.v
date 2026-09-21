(* The K10 mutation of index2/k7_k11_tails.v with its Fail removed, so the
   message the guard hides is on the console.  Expected to FAIL. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework.
From pgg_smc Require Import pgg_tableau.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Section m.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Definition k10_mutation (r r' : EndpointReading A)
    (cert : IndistinguishabilityCert sa r') (c c' : R)
    (Hd : InputDistinguishabilityPropAt sa r c)
    (Hp : IndistinguishabilityPropAt cert c') : c <= c' :=
  let: ex_intro C (ex_intro x (ex_intro x' (conj HC Hge))) := Hd in
  Order.POrderTheory.le_trans Hge (Hp C x x' HC).
End m.
