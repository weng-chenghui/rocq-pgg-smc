(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P8: the proximity arm against the spectral arm                       *)
(*                                                                            *)
(* The spectral arm and the proximity arm each carry a number, and both       *)
(* numbers can be read off one variation distance on the cut group, so a      *)
(* reader may take one proposition for a restatement of the other. Four       *)
(* statements separate them, and two of the four are compiled.                *)
(*                                                                            *)
(* Compiled: the spectral arm's proposition does not mention its certificate. *)
(* spectral_prop_cert_free says it is one proposition at two certificates     *)
(* over one model, so the ideal cut and the constancy field are spent inside  *)
(* spectral_tail and have left the claim.                                     *)
(*                                                                            *)
(* Compiled: at the five-card instance the proximity proposition at the       *)
(* published one fiftieth is a theorem outright, so the implication from the  *)
(* spectral proposition holds there for a reason that does not read the       *)
(* spectral premise at all, and idealproximity_ceiling of p7_mutations.v      *)
(* holds the same implication at two from any premise whatever.               *)
(*                                                                            *)
(* Argued and not compiled: no implication holds uniformly in the proximity   *)
(* certificate. A countermodel is what would settle it, and it needs a model  *)
(* whose reading law is the same at every run argument, which is what the     *)
(* spectral proposition asks, and far from the ideal's, which is what the     *)
(* proximity conclusion forbids. No such model is built here.                 *)
(*                                                                            *)
(* Not compiled: the statement the spec intends, in which the proximity       *)
(* proposition is derived from the spectral certificate's own fields at a     *)
(* stated constant, rather than proved beside it at one instance.             *)
(*                                                                            *)
(* What the two arms share is a carrier: idealproximity_reading_le reads the  *)
(* proximity number as a bound between the two models' reading marginals,     *)
(* which is the carrier the spectral arm states its own bound on.             *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   spectral_prop_cert_free   == the spectral proposition does not mention   *)
(*                                the certificate it is stated at             *)
(*   idealproximity_reading_le == the proximity number bounds the distance    *)
(*                                between the two models' reading marginals   *)
(*   five_card_biased_proximity_prop_holds                                    *)
(*                             == the proximity proposition at one fiftieth,  *)
(*                                at the five-card instance                   *)
(*   five_card_biased_spectral_implies_proximity                              *)
(*                             == the same, from a spectral premise unread    *)
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
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models five_card_leakage.
From pgg_smc Require Import five_card_kim kim_input_privacy five_card_mixing.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import p1_joint_law_distance five_card_rows.
From tableau_ext_probe Require Import p4_kim_biased_proximity.

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
    names has left the claim. An ideal a proximity certificate names can
    therefore not be recovered from a spectral premise, and a bound on the
    distance to that ideal has to be proved from something else. The
    implication is not empty for all that: idealproximity_ceiling holds it at
    two whatever the premise, and the two lemmas at the end of this file hold
    it at the five-card instance at one fiftieth. *)
Lemma spectral_prop_cert_free (cert cert' : SpectralCert sa) (c : R) :
  SpectralPropAt cert c = SpectralPropAt cert' c.
Proof. by []. Qed.

(** The proximity arm's proposition mentions its certificate, through the
    ideal adapter, that ideal's witness and the actual model's secret, so the
    two are not two readings of one object. The recorded failure beside it
    says that the equality between the proposition at two certificates is not
    closed by conversion, and no more: two logically equivalent propositions
    would still be equal under propositional extensionality. *)
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

(******************************************************************************)
(*     Where the implication does hold, and why that is not the spec's claim  *)
(******************************************************************************)

(** The proximity proposition of Kim's one-cut row at the number that row
    publishes, taken off the published row itself. It is the conclusion the
    spec's P8 row wants, standing on its own at this instance. *)
Lemma five_card_biased_proximity_prop_holds (R : realType) :
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt). Qed.

(** The spectral proposition implies the proximity proposition at the
    five-card instance, at every constant the spectral premise is stated at,
    because the conclusion is a theorem there and the premise is discarded.
    The implication holds and carries no information: what the spec asks for
    is a derivation that reads the spectral certificate's fields, and this is
    not one. *)
Lemma five_card_biased_spectral_implies_proximity (R : realType) (c : R) :
  SpectralPropAt (kim_biased_cert R tt) c ->
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. by move=> _; exact: five_card_biased_proximity_prop_holds. Qed.
