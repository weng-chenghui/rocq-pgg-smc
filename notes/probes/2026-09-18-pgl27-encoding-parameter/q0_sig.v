(* PROBE Q0 (task P0): exact signatures of the generic entry points, so the
   Q3/Q4/Q5 probes are written against the real arities. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

About coalition_view.
About dealt_secret.
About ttrans_view_indep_gen.
About coalition_view_mutual_info_le.
About pgl27_view.
About pgl27_secret.
About pgl27_G_pos.

(* Q3 core question: is pgl27_view R C the generic coalition_view at
   orbit_encode, on the nose? *)
Lemma q0_view_is_coalition_view (R : realType) (C : {set 'I_8}) :
  pgl27_view R C
  = coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
      orbit_encode C.
Proof. by []. Qed.

Lemma q0_secret_is_dealt_secret (R : realType) :
  pgl27_secret R
  = dealt_secret (G := pgg_G pgl27_M) (fdist_uniform card_bool) pgl27_G_pos.
Proof. by []. Qed.
