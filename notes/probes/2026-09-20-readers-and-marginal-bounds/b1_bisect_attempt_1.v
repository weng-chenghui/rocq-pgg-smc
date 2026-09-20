(* PROBE bisect file: which command of r_framework.v diverges.
   Every proof is a Timeout-guarded term, so the first offender is named. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound pgg_analysis_status.
From pgg_smc Require Import var_dist_supp.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Section static_reader.

Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.
Local Notation cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1.

Record StaticReader := MkStaticReader {
  sr_T : {set seats} -> finType ;
  sr_read : forall C : {set seats},
    ex_inputT E -> pgg_gT (mp_M (instance_profile A)) -> sr_T C }.

Definition coalition_reading_reader : StaticReader :=
  @MkStaticReader (fun _ => [the finType of {ffun seats -> cards}])
    (@static_coalition_obs A E).

Timeout 60 Definition b1a (C : {set seats}) :
  sr_T coalition_reading_reader C = [the finType of {ffun seats -> cards}]
  := ltac:(exact: erefl).

Timeout 60 Definition b1b (C : {set seats}) (x : ex_inputT E)
  (g : pgg_gT (mp_M (instance_profile A))) :
  sr_read coalition_reading_reader C x g = static_coalition_obs C x g
  := ltac:(exact: erefl).

End static_reader.

Arguments StaticReader {A} E.
Arguments sr_T {A E}.
Arguments sr_read {A E}.
Arguments coalition_reading_reader {A} E.

Section reader_propositions.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

Definition ReaderIndistinguishabilityPropAt (r : StaticReader E) (c : R)
    : Prop :=
  forall (C : {set seats}) (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (sr_read r C x) (sa_cut_dist sa))
             (fdistmap (sr_read r C x') (sa_cut_dist sa))
    <= c.

Timeout 60 Definition b2_reflexivity
    (cert : IndistinguishabilityCert sa) (c : R) :
  ReaderIndistinguishabilityPropAt (coalition_reading_reader E) c
  = IndistinguishabilityPropAt cert c
  := ltac:(reflexivity).

Timeout 60 Definition b3_erefl
    (cert : IndistinguishabilityCert sa) (c : R) :
  ReaderIndistinguishabilityPropAt (coalition_reading_reader E) c
  = IndistinguishabilityPropAt cert c
  := ltac:(exact: erefl).

End reader_propositions.
