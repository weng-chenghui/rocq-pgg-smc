(* PROBE: print the goal of R4 after the cut-law rewrite, and the type of the
   cited theorem, so the mismatch behind "Cannot apply lemma" is read and not
   guessed. *)

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
From readersprobe Require Import r_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

About pgl27_static_obsE.
About pgl27_coalition_trace_E.
About pgl27_content_traceE.
About pgl27_view_indep.
About pgl27_coalition_trace_secrecy.
About pgl27_exec_content_trace.
About pgl27_word_cert.
About pow2_split.
About indistinguishability_tail.
About cert_eps.
About pgl27_exact_family.
