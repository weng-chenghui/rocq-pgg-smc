(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* n_pgl27_nonvacuity: the refuted class is inhabited at another model        *)
(*                     (probe, ledger row N4)                                 *)
(*                                                                            *)
(* An obstruction that no model could satisfy says nothing. The class         *)
(* NoIndistinguishabilityCertNear denies is the certificates whose ideal cut  *)
(* sits within a number of a named law, and at the eight-card orbit           *)
(* instance's 200-letter word model that class has a member: pgl27_word_cert  *)
(* takes the group-uniform law itself as its ideal, at distance zero. So the  *)
(* proposition is false there at every number, and what the PSL(2,11) row     *)
(* states is a property of that model and not of the shape of the            *)
(* proposition.                                                               *)
(******************************************************************************)

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
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_exec.
From pgg_smc Require Import pgl27_models.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From refuteprobe Require Import n_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** The sum of the absolute differences between a law and itself is zero.
    infotheo's variation_dist.v proves the two directions around this point,
    positivity and that a vanishing distance identifies the laws, and not the
    point itself. *)
Lemma var_dist_self (R : realType) (A : finType) (d : R.-fdist A) :
  var_dist d d = 0 :> R.
Proof. by rewrite /var_dist; apply: big1 => a _; rewrite subrr normr0. Qed.

(** The ideal cut of the eight-card orbit instance's word certificate is the
    group-uniform law itself, at distance zero from it. The instance's
    perfect half is exactly this: everything the certificate says about its
    ideal cut is exact and three-transitive, and the walk's 2^-40 is the only
    statistical quantity in the program. *)
Lemma pgl27_word_cert_ideal_uniform (R : realType) (secretP : R.-fdist bool) :
  var_dist ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M))
    (ic_ideal (@pgl27_word_cert R secretP)) = 0 :> R.
Proof. exact: var_dist_self. Qed.

(** At the eight-card orbit instance's word model no number denies the
    certificates whose ideal sits that near the group-uniform law, the
    instance's own certificate being one of them at distance zero. The
    obstruction the PSL(2,11) row publishes is therefore a statement about
    the twelve-card chirality model and not a proposition false of every
    model. *)
Theorem pgl27_word_no_certificate_near_false (R : realType)
    (secretP : R.-fdist bool) (eps : R) :
  0 <= eps ->
  ~ NoIndistinguishabilityCertNear (amf_sample pgl27_word_family R secretP)
      ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M)) eps.
Proof.
move=> Heps H.
apply: (H (@pgl27_word_cert R secretP)).
by rewrite pgl27_word_cert_ideal_uniform.
Qed.

(** In particular at the number zero, where the obstruction is weakest. *)
Corollary pgl27_word_no_certificate_near0_false (R : realType)
    (secretP : R.-fdist bool) :
  ~ NoIndistinguishabilityCertNear (amf_sample pgl27_word_family R secretP)
      ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M)) 0.
(* eps occurs only in the conclusion, so Unset Strict Implicit makes it
   implicit and a positional exact: mis-assigns the hypothesis; the goal
   fixes it under apply:. *)
Proof.
apply: pgl27_word_no_certificate_near_false.
exact: Order.POrderTheory.lexx.
Qed.
