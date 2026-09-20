(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_tableau_arm_relations: what separates the arms' propositions           *)
(*                                                                            *)
(* A Tableau row certifies one of three arms, and two of the three carry a    *)
(* number. Both numbers can be read off one variation distance on the cut     *)
(* group, so a reader may take one arm's proposition for a restatement of the *)
(* other's. The statements here separate the two that carry a number. Every   *)
(* one of them is stated at an arbitrary algebra, arbitrary execution         *)
(* parameters and an arbitrary sample adapter, so none names an instance.     *)
(*                                                                            *)
(* The input-indistinguishability proposition does not mention the            *)
(* certificate it is stated at: it is one proposition at two certificates     *)
(* over one model, so the ideal cut and the constancy field are spent inside  *)
(* indistinguishability_tail and have left the claim. The proximity           *)
(* proposition does mention its certificate, through the ideal adapter, that  *)
(* ideal's witness and the actual model's secret, as its definition shows.    *)
(* The two recorded failures beside it record what a written term does with   *)
(* that: the equality of the proposition at two certificates is not closed by *)
(* conversion, and the proposition cannot be stated at an                     *)
(* input-indistinguishability certificate at all.                             *)
(*                                                                            *)
(* What the two arms share is a carrier. idealproximity_reading_le reads the  *)
(* proximity number as a bound between the two models' reading marginals,     *)
(* which is the carrier the input-indistinguishability arm states its own     *)
(* bound on.                                                                  *)
(*                                                                            *)
(* idealproximity_prop_at2 fixes the scale a published number is read         *)
(* against. The number bounds a sum of absolute differences, twice the total  *)
(* variation distance, so a distinguisher's advantage is at most half of it.  *)
(*                                                                            *)
(* The arm's mathematics is spent on the ideal witness's independence: it     *)
(* turns the ideal joint law into the product of its marginals, and the arm's *)
(* proposition compares the actual joint law with exactly that product. One   *)
(* recorded failure below is a written term that omits that independence.     *)
(*                                                                            *)
(* Not claimed. An implication from the input-indistinguishability            *)
(* proposition to the proximity proposition at a constant below two, uniform  *)
(* in the proximity certificate. Refuting it needs a model whose coalition    *)
(* readings at any two run arguments stay within the constant the             *)
(* input-indistinguishability proposition names, and whose distance to the    *)
(* ideal exceeds the constant the proximity conclusion is stated at. No such  *)
(* model is built here, and no proof of the implication is given either. Nor  *)
(* is the proximity proposition derived from an input-indistinguishability    *)
(* certificate's own fields at a stated constant. The implication that does   *)
(* hold at the five-card one-cut model, in                                    *)
(* instances/kim2025/tableau/five_card_tableau_analysis_bridged.v, holds      *)
(* because its conclusion is a theorem there and its premise is discarded.    *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   idealproximity_prop_at2    == every proximity certificate satisfies the  *)
(*                                 arm's proposition at two                   *)
(*   indistinguishability_prop_cert_free                                      *)
(*                              == the input-indistinguishability proposition *)
(*                                 does not mention the certificate it is     *)
(*                                 stated at                                  *)
(*   idealproximity_reading_le  == the proximity number bounds the distance   *)
(*                                 between the two models' reading marginals  *)
(******************************************************************************)

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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The scale the proximity number is read against                         *)
(******************************************************************************)

(** Every proximity certificate satisfies the arm's proposition at two,
    whatever its model, its ideal and its own number, because a variation
    distance between two laws on a finite carrier never exceeds two. A row
    publishing two therefore rules nothing out, and a published number says
    something about a coalition exactly in so far as it is below two. *)
Lemma idealproximity_prop_at2 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) :
  IdealProximityPropAt cert 2%:R.
Proof. by move=> C _; exact: var_dist_le2. Qed.

(******************************************************************************)
(*     The two arms' propositions are two propositions                        *)
(******************************************************************************)

Section proximity_against_indistinguishability.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(** The input-indistinguishability arm's proposition at two certificates over
    one model is one proposition. The certificate is a parameter of the
    statement and occurs nowhere in it, so what the
    input-indistinguishability arm claims is a property of the model's own
    cut law and the number, and the ideal law the certificate names has left
    the claim. An ideal a proximity certificate names can therefore not be
    recovered from an input-indistinguishability premise, and a bound on the
    distance to that ideal has to be proved from something else. An
    implication from this proposition to the proximity proposition does hold
    for all that, its premise discarded: idealproximity_prop_at2 gives the
    proximity proposition at two whatever the premise. *)
Lemma indistinguishability_prop_cert_free
    (cert cert' : IndistinguishabilityCert sa) (c : R) :
  IndistinguishabilityPropAt cert c = IndistinguishabilityPropAt cert' c.
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

(** The two propositions do not take one certificate either: an
    input-indistinguishability certificate carries no secret and no ideal
    model, so the proximity proposition cannot be stated at it, and the two
    are not two readings of one object. *)
Fail Definition indistinguishability_cert_in_proximity_prop
    (cert : IndistinguishabilityCert sa) (c : R) : Prop :=
  IdealProximityPropAt cert c.

(** The proximity number bounds the distance between the two models' reading
    marginals, at every coalition below the threshold. The secret leaves the
    statement by data processing along the first projection, and the ideal's
    joint law is a product, so its first marginal is the ideal reading
    outright. This is the arm's number read on the carrier the
    input-indistinguishability arm states its own bound on, and it needs no
    model of one arm to be a model of the other. *)
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

End proximity_against_indistinguishability.

(******************************************************************************)
(*     The ideal witness's independence is load-bearing                       *)
(******************************************************************************)

(** The composition law with the ideal witness's independence deleted from its
    proof. What remains is the certificate's distance between two joint laws
    and the two link lemmas, and the arm's proposition compares the actual
    joint law with a product, so the step that turns the ideal joint law into
    the product of its marginals is where the witness is spent. Without it the
    final application does not typecheck. *)
Fail Definition idealproximity_tail_without_independence (R : realType)
    (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (cert : IdealProximityCert sa)
    (Hview : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)))
    (Hideal : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E)
         (ipc_ideal cert) 0 C
       = (fun u => static_coalition_obs C ((ipc_ideal cert).(sa_arg) u)
                     ((ipc_ideal cert).(sa_cut) u)))
  : IdealProximityPropAt cert (ipc_eps cert)
  := ltac:(move=> C HC; rewrite (Hview C) (Hideal C);
           exact: (@ipc_close _ _ _ _ cert C HC)).
