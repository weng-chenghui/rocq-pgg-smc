(* P8 arm-relations probe: the two headlines' statements compose.             *)
(*                                                                            *)
(* Each headline is derived here from its supporting statements alone, and    *)
(* those statements are assumed rather than proved, so what this file shows   *)
(* is that the shapes fit: nothing beyond what the supports assert is needed  *)
(* to reach either headline. The supports themselves are theorems in          *)
(* p8a_degenerate_certificate.v and p8b_proximity_from_indistinguishability.v.*)
(* This is the only file of the probe where Admitted appears.                 *)

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
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_tableau.
From p8probe Require Import p8a_degenerate_certificate.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section the_two_headlines_from_their_supports.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(******************************************************************************)
(*     Headline A                                                             *)
(******************************************************************************)

(* Support of headline A: at a coalition below the threshold the degenerate
   certificate's two joint laws are two apart, so any number the proximity
   proposition holds at is at least two. It is A1 applied to the disjointness
   of the two secrets' supports. *)
Lemma degenerate_proximity_bound_ge2 (c : R) :
  (0 < profile_k (instance_profile A))%N ->
  IdealProximityPropAt (degenerate_proximity_cert sa) c -> 2%:R <= c.
Admitted.

(** Headline A, from that support alone. *)
Lemma headline_no_proximity_below2 (c : R) :
  (0 < profile_k (instance_profile A))%N -> c < 2%:R ->
  ~ IdealProximityPropAt (degenerate_proximity_cert sa) c.
Proof.
move=> Hk Hc H.
move: (Order.POrderTheory.le_lt_trans (degenerate_proximity_bound_ge2 Hk H) Hc).
by rewrite Order.POrderTheory.ltxx.
Qed.

(** Headline A, at the premise the parent statement had in view. *)
Corollary headline_indistinguishability_gives_no_proximity_below2
    (ic : IndistinguishabilityCert sa) (c : R) :
  (0 < profile_k (instance_profile A))%N -> c < 2%:R ->
  ~ (IndistinguishabilityPropAt ic (cert_eps ic) ->
     forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
Proof.
move=> Hk Hc Himp.
exact: (headline_no_proximity_below2 Hk Hc
          (Himp (indistinguishability_tail ic) (degenerate_proximity_cert sa))).
Qed.

(******************************************************************************)
(*     Headline B                                                             *)
(******************************************************************************)

Variable cert : IdealProximityCert sa.

(* First support of headline B: the model's executed coalition reader is the
   direct computation. It is sa_coalition_viewE at the program's own endpoint
   equation. *)
Lemma model_coalition_viewE :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
    = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)).
Admitted.

(* Second support: the same for the certificate's ideal model, which runs the
   same execution and so meets the same endpoint equation. *)
Lemma ideal_coalition_viewE :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    @sa_coalition_view R (instance_profile A) (instance_exec E)
      (ipc_ideal cert) 0 C
    = (fun u => static_coalition_obs C ((ipc_ideal cert).(sa_arg) u)
                  ((ipc_ideal cert).(sa_cut) u)).
Admitted.

(** Headline B, from the two link statements and the certificate's own
    distance field, at the certificate's own number. *)
Lemma headline_proximity_prop_at_cert_eps :
  IdealProximityPropAt cert (ipc_eps cert).
Proof.
exact: (idealproximity_tail cert model_coalition_viewE ideal_coalition_viewE).
Qed.

End the_two_headlines_from_their_supports.
