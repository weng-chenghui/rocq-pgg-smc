(* PROBE: is the PGL(2,7) trace reader CONVERTIBLE with the canonical reader,
   or only propositionally equal? The equation of R5 is proved by a finite
   function extensionality and a case split, so a conversion check would have
   to reduce the interpreter; the Timeout bounds that. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_trace pgl27_mixing.
From pgg_smc Require Import pgl27_word_privacy pgl27_exec pgl27_models.
From pgg_smc Require Import pgl27_proximity.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From readersprobe Require Import r_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.


From readersprobe Require Import r_pgl27.

Section m1.
Variable R : realType.

Timeout 60 Fail Definition trace_reader_is_convertible
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1})
    (x : ex_inputT pgl27_dealt_params)
    (g : pgg_gT (mp_M (instance_profile pgl27_algebra))) :
  sr_read (coalition_reading_reader pgl27_dealt_params) C x g
  = sr_read (pgl27_trace_reader R) C x g :=
  ltac:(exact: erefl).

End m1.
