(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P8: the proximity arm against the spectral arm                       *)
(*                                                                            *)
(* The spectral arm and the proximity arm each carry a number, and both       *)
(* numbers can be read off one variation distance on the cut group, so a      *)
(* reader may take one proposition for a restatement of the other. They are   *)
(* not. The spectral arm's proposition does not mention its certificate at    *)
(* all: it compares two readings of one model at two run arguments, and       *)
(* spectral_prop_cert_free below says that replacing the certificate, ideal   *)
(* cut and all, leaves it the same proposition. It therefore constrains the   *)
(* actual cut law alone and cannot decide any distance to an ideal model. The *)
(* proximity arm's proposition does mention its certificate, through the      *)
(* ideal adapter, that ideal's witness and the actual model's secret, and the *)
(* recorded failure beside it says that replacing the certificate does not    *)
(* leave it the same. What they do share is a carrier:                        *)
(* idealproximity_reading_le reads the proximity number as a bound between    *)
(* the two models' reading marginals, which is the carrier the spectral arm   *)
(* states its own bound on.                                                   *)
(*   spectral_prop_cert_free   == the spectral proposition does not mention   *)
(*                                the certificate it is stated at             *)
(*   idealproximity_reading_le == the proximity number bounds the distance    *)
(*                                between the two models' reading marginals   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import p1_joint_law_distance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section proximity_against_spectral.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(** The spectral arm's proposition at two certificates over one model is one
    proposition. The certificate is a parameter of the statement and occurs
    nowhere in it, so what the spectral arm claims is a property of the
    model's own cut law and the number, and the ideal law the certificate
    names has left the claim by the time it is published. A statement about
    how far that model is from an ideal one therefore cannot follow from it,
    whatever the numbers are. *)
Lemma spectral_prop_cert_free (cert cert' : SpectralCert sa) (c : R) :
  SpectralPropAt cert c = SpectralPropAt cert' c.
Proof. by []. Qed.

(** The proximity arm's proposition is not certificate-free: two certificates
    over one model naming two ideals are two claims. It is what separates the
    arm from the spectral one, and what makes the ideal a part of what a
    proximity row publishes rather than a part of how it was proved. *)
Fail Definition idealproximity_prop_cert_free
    (cert cert' : IdealProximityCert sa) (c : R) :
  IdealProximityPropAt cert c = IdealProximityPropAt cert' c
  := ltac:(by []).

(** The two propositions do not take one certificate either: a spectral
    certificate carries no secret and no ideal model, so the proximity
    proposition cannot be stated at it, and the two are not two readings of
    one object. *)
Fail Definition spectral_cert_in_proximity_prop
    (cert : SpectralCert sa) (c : R) : Prop := IdealProximityPropAt cert c.

(** The proximity number bounds the distance between the two models' reading
    marginals, at every coalition below the threshold. The secret leaves the
    statement by data processing along the first projection, and the ideal's
    joint law is a product, so its first marginal is the ideal reading
    outright. This is the arm's number read on the carrier the spectral arm
    states its bound on, and it is the sharpest comparison of the spectral
    arm with the proximity arm that does not need a model of one to be a model
    of the other. *)
Lemma idealproximity_reading_le (cert : IdealProximityCert sa) (c : R) :
  IdealProximityPropAt cert c ->
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist
      (fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                   sa 0 C) (sa_sampleP sa))
      (fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                   (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert)))
    <= c.
Proof.
move=> H C HC.
have Hl : fdistmap fst
    (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                           (instance_exec E) sa 0 C u, ipc_secret cert u))
       (sa_sampleP sa))
  = fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                sa 0 C) (sa_sampleP sa).
  by rewrite fdistmap_comp.
have Hr : fdistmap fst
    ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                  (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert)))
     `x (fdistmap (ew_secret (ipc_witness cert))
           (sa_sampleP (ipc_ideal cert))))
  = fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert)).
  exact: fdist_prod1.
rewrite -Hl -Hr.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) (H C HC)).
Qed.

End proximity_against_spectral.
