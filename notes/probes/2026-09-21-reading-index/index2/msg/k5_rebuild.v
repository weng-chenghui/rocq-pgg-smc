(* The K5 mutation of index2/k5_default_reading.v with its Fail removed:
   the field-by-field rebuild of an indexed witness at a reading that is not
   the identity.  Expected to FAIL. *)
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
Record ExactWitness0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkExactWitness0 {
    ew_secretT0 : finType ;
    ew_secret0  : {RV (sa_sampleP sa) -> ew_secretT0} ;
    ew_indep0   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      sa_sampleP sa |= (fun u => static_coalition_obs C (sa.(sa_arg) u)
                                   (sa.(sa_cut) u)) _|_ ew_secret0 }.
Section m.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Definition blind_reading : EndpointReading A :=
  @MkEndpointReading A
    (fun _ => [the finType of
                 {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                    -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}])
    (fun _ _ => [ffun _ => ord0]).

Definition k5_mutation_rebuild (w : ExactWitness sa blind_reading)
  : ExactWitness0 sa :=
  @MkExactWitness0 R A E sa (ew_secretT w) (ew_secret w)
    (@ew_indep R A E sa blind_reading w).
End m.
