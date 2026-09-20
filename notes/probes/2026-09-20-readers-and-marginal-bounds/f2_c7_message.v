(* PROBE: the SAME command as the Fail guard in r_framework.v, without the
   Fail, so the rejection message is read and quoted rather than guessed.
   rocq compile prints nothing for a passing Fail. *)

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


From readersprobe Require Import r_framework.

Section msg.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

Check (fun (i : seats)
           (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1)
           (secretT : finType)
           (secret : {RV (sa_sampleP sa) -> secretT}) =>
  (seat_marginal_at_two sa i ideal
     : ReaderExactPropAt sa (coalition_reading_reader E) secret)).

End msg.
