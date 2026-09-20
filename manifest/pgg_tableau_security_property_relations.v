(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_tableau_security_property_relations: what separates the two security   *)
(* properties' propositions                                                   *)
(*                                                                            *)
(* A Tableau program certifies one of three security properties, and two of   *)
(* the three carry a number. Both numbers can be read off one variation       *)
(* distance on the cut group, so a reader may take one property's proposition *)
(* for a restatement of the other's. The statements here separate the two     *)
(* that carry a number. Every one of them is stated at an arbitrary algebra,  *)
(* arbitrary execution parameters and an arbitrary sample adapter, so none    *)
(* names an instance.                                                         *)
(*                                                                            *)
(* The input-indistinguishability proposition does not mention the            *)
(* certificate it is stated at: it is one proposition at two certificates     *)
(* over one model, so the ideal cut and the constancy field are used inside   *)
(* indistinguishability_tail and have left the claim. The ideal-proximity     *)
(* proposition does mention its certificate, through the ideal adapter, that  *)
(* ideal's witness and the actual model's secret, as its definition shows.    *)
(* The two recorded failures beside it record what a written term does with   *)
(* that: the equality of the proposition at two certificates is not closed by *)
(* conversion, and the proposition cannot be stated at an                     *)
(* input-indistinguishability certificate at all.                             *)
(*                                                                            *)
(* What the two propositions share is a carrier. idealproximity_reading_le    *)
(* reads the proximity number as a bound between the two models' reading      *)
(* marginals, which is the carrier the input-indistinguishability proposition *)
(* states its own bound on.                                                   *)
(*                                                                            *)
(* idealproximity_prop_at2 fixes the scale a published number is read         *)
(* against. The number bounds a sum of absolute differences, twice the total  *)
(* variation distance, so a distinguisher's advantage is at most half of it.  *)
(*                                                                            *)
(* The mathematics of ideal proximity rests on the ideal witness's            *)
(* independence: it turns the ideal joint law into the product of its         *)
(* marginals, and the ideal-proximity proposition compares the actual joint   *)
(* law with exactly that product. One recorded failure below is a written     *)
(* term that omits that independence.                                         *)
(*                                                                            *)
(* Below two nothing holds uniformly in the proximity certificate. Over an    *)
(* arbitrary model there is a proximity certificate whose ideal is that model *)
(* itself, whose ideal secret is the constant true and whose own secret is    *)
(* the constant false. At the empty coalition the two joint laws the          *)
(* ideal-proximity proposition compares carry mass at no common point of the  *)
(* secret coordinate, so they are exactly two apart, and the proposition is   *)
(* false at every number below two. Since that certificate is available over  *)
(* a model about which nothing is known, a premise about the model does not   *)
(* change the verdict: the corollary here refutes the implication whose       *)
(* premise is the input-indistinguishability proposition at a certificate's   *)
(* own number, a proposition indistinguishability_tail proves with no         *)
(* hypothesis.                                                                *)
(*                                                                            *)
(* At a model that draws its run argument independently of its cut, an        *)
(* input-indistinguishability certificate does build ideal-proximity          *)
(* evidence over that same model, and the ideal-proximity proposition holds   *)
(* there at the certificate's marginal-bound epsilon once, where the          *)
(* input-indistinguishability proposition holds at that epsilon twice. The    *)
(* independence is a hypothesis on the model and not a theorem about it, and  *)
(* the comparison is an average over the prior on the run argument, at one    *)
(* run. The construction reads the run argument through a finite coordinate   *)
(* of the sample point, and the strength of the conclusion is the fineness    *)
(* of that coordinate. Two further hypotheses are carried, not proved: the    *)
(* run argument factors through that coordinate, and the model's executed     *)
(* coalition reading is its static one, which every program at Sampled        *)
(* holds. At a one-point carrier the statement is true and says nothing.      *)
(*                                                                            *)
(* Not claimed. No implication reaching a proximity certificate an instance   *)
(* chose for itself, whose ideal is a model of its own: the refutation        *)
(* refutes a universal over certificates and says nothing at a given one,     *)
(* and the construction produces a certificate of its own rather than         *)
(* reaching a given one. Nothing for a model whose cut depends on its run     *)
(* argument, which fails the product hypothesis. No instance of the           *)
(* construction at a production model: the instance files record the product  *)
(* form of a model's joint law and the number a construction would carry,     *)
(* not a built certificate. The implication that does hold at the five-card   *)
(* one-cut model, in                                                          *)
(* instances/kim2025/tableau/five_card_tableau_analysis_bridged.v, holds      *)
(* because its conclusion is a theorem there and its premise is discarded.    *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   exact_witness_cst_true     == the exact witness over an arbitrary model  *)
(*                                 whose secret is the constant true          *)
(*   idealproximity_cert_cst_secrets_true_false                               *)
(*                              == the proximity certificate over an          *)
(*                                 arbitrary model whose two secrets are the  *)
(*                                 constants true and false                   *)
(*   ideal_prod_adapter         == the ideal model drawing the run argument   *)
(*                                 from the actual model's law and the cut    *)
(*                                 from the certificate's ideal law           *)
(*   exact_witness_ideal_prod   == the ideal model's exact witness, its       *)
(*                                 secret that model's own run argument       *)
(*   idealproximity_cert_of_indistinguishability                              *)
(*                              == the ideal-proximity evidence an            *)
(*                                 input-indistinguishability certificate     *)
(*                                 builds under the product hypothesis        *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   idealproximity_prop_at2    == every proximity certificate satisfies the  *)
(*                                 ideal-proximity proposition at two         *)
(*   indistinguishability_prop_cert_free                                      *)
(*                              == the input-indistinguishability proposition *)
(*                                 does not mention the certificate it is     *)
(*                                 stated at                                  *)
(*   idealproximity_reading_le  == the proximity number bounds the distance   *)
(*                                 between the two models' reading marginals  *)
(*   profile_k_gt0              == the privacy threshold of every algebra is  *)
(*                                 positive                                   *)
(*   idealproximity_prop_cst_secrets_lt2_false                                *)
(*                              == below two that certificate's               *)
(*                                 ideal-proximity proposition is false       *)
(*   idealproximity_prop_lt2_uniform_in_cert_false                            *)
(*                              == below two the ideal-proximity proposition  *)
(*                                 does not hold of every certificate over a  *)
(*                                 model                                      *)
(*   indistinguishability_prop_idealproximity_lt2_false                       *)
(*                              == the input-indistinguishability proposition *)
(*                                 does not give the ideal-proximity          *)
(*                                 proposition below two uniformly in the     *)
(*                                 certificate                                *)
(*   ideal_prod_reading_arg_prodE                                             *)
(*                              == below the threshold the ideal model's      *)
(*                                 joint law of a coalition's reading and the *)
(*                                 run argument is the product of its two     *)
(*                                 marginals                                  *)
(*   ideal_prod_reading_indep_arg                                             *)
(*                              == the same as an independence                *)
(*   arg_read_distE             == the ideal model's secret is distributed as *)
(*                                 the actual model's finite coordinate       *)
(*   var_dist_joint_reading_arg_le                                            *)
(*                              == the two models' joint laws of the reading  *)
(*                                 and the finite coordinate are no further   *)
(*                                 apart than the two cut laws                *)
(*   idealproximity_close_of_indistinguishability                             *)
(*                              == the distance field of the built evidence,  *)
(*                                 at the marginal-bound epsilon              *)
(*   idealproximity_prop_of_indistinguishability                              *)
(*                              == the ideal-proximity proposition at the     *)
(*                                 built evidence, at the marginal-bound      *)
(*                                 epsilon once                               *)
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
From pgg_smc Require Import fdist_prod_cst_cond var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework.
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

(** Every proximity certificate satisfies the ideal-proximity proposition at
    two, whatever its model, its ideal and its own number, because a variation
    distance between two laws on a finite carrier never exceeds two. A program
    publishing two therefore rules nothing out, and a published number says
    something about a coalition exactly in so far as it is below two. *)
Lemma idealproximity_prop_at2 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) :
  IdealProximityPropAt cert 2%:R.
Proof. by move=> C _; exact: var_dist_le2. Qed.

(******************************************************************************)
(*     The two security properties' propositions are two propositions         *)
(******************************************************************************)

Section proximity_against_indistinguishability.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(** The input-indistinguishability proposition at two certificates over one
    model is one proposition. The certificate is a parameter of the statement
    and occurs nowhere in it, so what the input-indistinguishability proposition
    claims is determined by the model's own cut law and the number, and the
    ideal law the certificate names has left the claim. An ideal a proximity
    certificate names can therefore not be recovered from an
    input-indistinguishability premise, and a bound on the distance to that
    ideal has to be proved from something else. An implication from this
    proposition to the ideal-proximity proposition does hold for all that, its
    premise discarded: idealproximity_prop_at2 gives the ideal-proximity
    proposition at two whatever the premise. *)
Lemma indistinguishability_prop_cert_free
    (cert cert' : IndistinguishabilityCert sa) (c : R) :
  IndistinguishabilityPropAt cert c = IndistinguishabilityPropAt cert' c.
Proof. by []. Qed.

(** The ideal-proximity proposition mentions its certificate, through the
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
    input-indistinguishability certificate carries no secret and no ideal model,
    so the ideal-proximity proposition cannot be stated at it, and the two are
    not two readings of one object. *)
Fail Definition indistinguishability_cert_in_proximity_prop
    (cert : IndistinguishabilityCert sa) (c : R) : Prop :=
  IdealProximityPropAt cert c.

(** The proximity number bounds the distance between the two models' reading
    marginals, at every coalition below the threshold. The secret leaves the
    statement by data processing along the first projection, and the ideal's
    joint law is a product, so its first marginal is the ideal reading outright.
    This is the proximity number read on the carrier the
    input-indistinguishability proposition states its own bound on, and it needs
    no model of one proposition to be a model of the other. *)
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
    and the two link lemmas, and the ideal-proximity proposition compares the
    actual joint law with a product, so the step that turns the ideal joint
    law into the product of its marginals is where the witness is used.
    Without it the final application does not typecheck. *)
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

(******************************************************************************)
(*     The privacy threshold of every algebra is positive                     *)
(******************************************************************************)

(** The privacy threshold of an algebra's profile is positive. A threshold
    scheme's parameter is a successor by construction, so the empty coalition
    is below the threshold at every algebra and a statement quantified over
    coalitions below the threshold is never empty. *)
Lemma profile_k_gt0 (A : PGGAlgebraic) :
  (0 < profile_k (instance_profile A))%N.
Proof. by rewrite /profile_k /ts_k. Qed.

(******************************************************************************)
(*     A certificate over every model, its two secrets constant               *)
(******************************************************************************)

Section idealproximity_cert_over_any_model.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(** The exact witness over an arbitrary model whose secret is the constant
    true. Its independence field is inde_RV_cst, which uses no property of
    the model, so holding an exact witness is by itself no statement about
    what a model hides. *)
Definition exact_witness_cst_true : ExactWitness sa :=
  @MkExactWitness R A E sa bool ((fun=> true) : {RV (sa_sampleP sa) -> bool})
    (fun C _ =>
       @inde_RV_cst R (sa_sampleT sa) (sa_sampleP sa) _ bool
         (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))
         true).

(** The proximity certificate over an arbitrary model: its ideal is that
    model itself, its ideal secret is the constant true, its own secret the
    constant false, and its number two, which var_dist_le2 proves with no
    hypothesis. Every field is available at an arbitrary algebra, arbitrary
    execution parameters and an arbitrary sample adapter, so ideal-proximity
    evidence exists over a model about which nothing is known. *)
Definition idealproximity_cert_cst_secrets_true_false
  : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa sa exact_witness_cst_true
    ((fun=> false) : {RV (sa_sampleP sa) -> bool}) 2%:R
    (fun C _ => var_dist_le2 _ _).

(** At that certificate the ideal-proximity proposition is false at every
    number below two. The empty coalition is below the threshold by
    profile_k_gt0, and there the two joint laws the proposition compares put
    their mass on opposite values of the secret coordinate, so they are
    exactly two apart. No property of the model enters. *)
Lemma idealproximity_prop_cst_secrets_lt2_false (c : R) :
  c < 2%:R ->
  ~ IdealProximityPropAt idealproximity_cert_cst_secrets_true_false c.
Proof.
move=> Hc H.
have Hcard : (#|@set0 'I_(pi_T' (mp_PI (instance_profile A))).+1|
              < profile_k (instance_profile A))%N
  by rewrite cards0 profile_k_gt0.
have Hcst : fdistmap ((fun=> true) : sa_sampleT sa -> bool) (sa_sampleP sa)
              false = 0 :> R by apply: fdistmap_notin_codom0.
have H2 : var_dist
    (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                           (instance_exec E) sa 0 set0 u, false))
       (sa_sampleP sa))
    ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                  sa 0 set0) (sa_sampleP sa))
     `x (fdistmap ((fun=> true) : sa_sampleT sa -> bool) (sa_sampleP sa)))
  = 2%:R.
  apply: var_dist_supp_disjoint_eq2 => -[v []].
  - by left; apply: fdistmap_notin_codom0 => u; rewrite xpair_eqE andbF.
  - by right; rewrite fdist_prodE /= Hcst mulr0.
have H2c : (2%:R : R) <= c by rewrite -H2; exact: (H set0 Hcard).
move: (Order.POrderTheory.le_lt_trans H2c Hc).
by rewrite Order.POrderTheory.ltxx.
Qed.

(** Below two the ideal-proximity proposition does not hold of every
    proximity certificate over a model. This refutes a universal over
    certificates. It says nothing at a certificate an instance builds, whose
    ideal is a model of its own and whose secret is the value the execution
    computes. *)
Lemma idealproximity_prop_lt2_uniform_in_cert_false (c : R) :
  c < 2%:R ->
  ~ (forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
Proof.
move=> Hc H.
exact: (idealproximity_prop_cst_secrets_lt2_false Hc
          (H idealproximity_cert_cst_secrets_true_false)).
Qed.

(** The input-indistinguishability proposition at a certificate's own
    number, which indistinguishability_tail proves with no hypothesis, does
    not give the ideal-proximity proposition at a number below two uniformly
    in the proximity certificate. The premise holds over every model, so what
    fails is not its strength but the quantifier over certificates in the
    conclusion. *)
Lemma indistinguishability_prop_idealproximity_lt2_false
    (ic : IndistinguishabilityCert sa) (c : R) :
  c < 2%:R ->
  ~ (IndistinguishabilityPropAt ic (cert_eps ic) ->
     forall cert : IdealProximityCert sa, IdealProximityPropAt cert c).
Proof.
move=> Hc Himp.
exact: (idealproximity_prop_lt2_uniform_in_cert_false Hc
          (Himp (indistinguishability_tail ic))).
Qed.

End idealproximity_cert_over_any_model.

(******************************************************************************)
(*     Ideal proximity from input indistinguishability                        *)
(******************************************************************************)

Section idealproximity_from_indistinguishability.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Variable argT : finType.
Variable arg_decode : argT -> ex_inputT E.
Variable arg_read : sa_sampleT sa -> argT.
Hypothesis Harg : forall u : sa_sampleT sa,
  sa.(sa_arg) u = arg_decode (arg_read u).
Hypothesis Hprod :
  fdistmap (fun u => (arg_read u, sa.(sa_cut) u)) (sa_sampleP sa)
  = (fdistmap arg_read (sa_sampleP sa)) `x (sa_cut_dist sa).
Variable ic : IndistinguishabilityCert sa.

(** The ideal model: the same execution run on a sample space that draws the
    run argument from the actual model's own law of arg_read and the cut
    from the certificate's ideal law, the two independent. What it holds no
    coordinate for is any coupling between the run argument and the cut, and
    the distance below is what that omission costs. *)
Definition ideal_prod_adapter : SampleAdapter R (instance_exec E) :=
  @MkSampleAdapter R (instance_profile A) (instance_exec E)
    [the finType of (argT * pgg_gT (mp_M (instance_profile A)))%type]
    ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic))
    (fun z => arg_decode z.1) (fun z => z.2).

(** Below the threshold the ideal model's joint law of a coalition's reading
    and the run argument is the product of its two marginals. It is the
    input-indistinguishability certificate's constancy field read on that
    model, and it is what makes the ideal a model whose own privacy is
    proved rather than stipulated. *)
Lemma ideal_prod_reading_arg_prodE
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
              (static_coalition_obs C (arg_decode z.1) z.2, z.1))
    ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic))
  = (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 static_coalition_obs C (arg_decode z.1) z.2)
       ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
    `x (fdistmap arg_read (sa_sampleP sa)).
Proof.
move=> HC.
exact: (@fdistmap_pair_fst_prodE R argT _ _
  (fdistmap arg_read (sa_sampleP sa)) (ic_ideal ic)
  (fun (x : argT) (g : pgg_gT (mp_M (instance_profile A))) =>
     static_coalition_obs C (arg_decode x) g)
  (fun x x' => @ic_const _ _ _ _ ic C HC (arg_decode x) (arg_decode x'))).
Qed.

(** The same fact in the form an exact witness asks for: below the threshold
    the ideal model's coalition reading is independent of its run argument. *)
Lemma ideal_prod_reading_indep_arg
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  sa_sampleP ideal_prod_adapter
  |= ((fun z => static_coalition_obs C (ideal_prod_adapter.(sa_arg) z)
                  (ideal_prod_adapter.(sa_cut) z))
      : {RV (sa_sampleP ideal_prod_adapter)
           -> {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                 -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}})
     _|_ ((fun z => z.1)
          : {RV (sa_sampleP ideal_prod_adapter) -> argT}).
Proof.
move=> HC v x.
have Hfst : fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) => z.1)
              ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic))
            = fdistmap arg_read (sa_sampleP sa) by exact: fdist_prod1.
rewrite -!dist_of_RVE.
transitivity
  (((fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
        static_coalition_obs C (arg_decode z.1) z.2)
      ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
    `x (fdistmap arg_read (sa_sampleP sa))) (v, x)).
  rewrite -(ideal_prod_reading_arg_prodE HC); exact: erefl.
rewrite fdist_prodE /=.
have Hfstx : fdistmap arg_read (sa_sampleP sa) x
           = fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) => z.1)
               ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)) x
  by rewrite Hfst.
rewrite Hfstx; exact: erefl.
Qed.

(** The ideal model's exact witness, its secret being that model's own run
    argument. The ideal-proximity proposition compares an actual joint law
    with a product of two marginals, and this independence is what makes
    that product the ideal's own joint law. *)
Definition exact_witness_ideal_prod : ExactWitness ideal_prod_adapter :=
  @MkExactWitness R A E ideal_prod_adapter argT
    ((fun z => z.1) : {RV (sa_sampleP ideal_prod_adapter) -> argT})
    ideal_prod_reading_indep_arg.

(** The ideal model's secret is distributed as the finite coordinate arg_read
    takes off the actual model's sample point. The two sides of the
    ideal-proximity proposition therefore speak of one secret and not only of
    one carrier, and idealproximity_close_of_indistinguishability then bounds
    the distance between the two joint laws of that secret with a coalition's
    reading. *)
Lemma arg_read_distE :
  fdistmap (ew_secret exact_witness_ideal_prod)
    (sa_sampleP ideal_prod_adapter)
  = fdistmap arg_read (sa_sampleP sa).
Proof. exact: fdist_prod1. Qed.

(** At every coalition the two models' joint laws of the reading and the
    finite coordinate are no further apart than the two cut laws. Both models
    draw that coordinate from one law and read one function of the pair, so
    the only quantity the two sides can differ in is the cut law. The
    threshold plays no part here. *)
Lemma var_dist_joint_reading_arg_le
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 (static_coalition_obs C (arg_decode z.1) z.2, z.1))
       ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
  <= var_dist (sa_cut_dist sa) (ic_ideal ic).
Proof.
(* Rewrite the actual side as one map on a product with the same left factor,
   then var_dist_fdistmap_prodR_le. *)
have HL : fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                                (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa)
        = fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                      (static_coalition_obs C (arg_decode z.1) z.2, z.1))
            ((fdistmap arg_read (sa_sampleP sa)) `x (sa_cut_dist sa)).
  rewrite -Hprod fdistmap_comp; congr fdistmap.
  by apply: funext => u; rewrite Harg.
rewrite HL.
exact: var_dist_fdistmap_prodR_le.
Qed.

(** The distance field of the proximity certificate, at the
    input-indistinguishability certificate's marginal-bound epsilon. The
    certificate's identification of its bound's law with the model's cut and
    the closeness of its ideal law are what carry the number across. The
    threshold hypothesis is the field's shape; the bound holds at every
    coalition. The bound is an average over the prior on the run argument, at
    one run, and it is unconditional: no assumption on an adversary
    enters. *)
Lemma idealproximity_close_of_indistinguishability
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z => (static_coalition_obs C
                           (ideal_prod_adapter.(sa_arg) z)
                           (ideal_prod_adapter.(sa_cut) z),
                         ew_secret exact_witness_ideal_prod z))
       (sa_sampleP ideal_prod_adapter))
  <= sw_bound_eps (ic_b ic).
Proof.
move=> _.
apply: (Order.POrderTheory.le_trans (var_dist_joint_reading_arg_le C)).
rewrite -(ic_Hd ic); exact: (ic_close ic).
Qed.

(** The ideal-proximity evidence an input-indistinguishability certificate
    builds over a model that draws its cut apart from its run argument. Its
    ideal is the product model, its ideal secret that model's own run
    argument, its own secret the actual model's run argument, and its number
    the marginal-bound epsilon once, where cert_eps is that epsilon twice. *)
Definition idealproximity_cert_of_indistinguishability
  : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa ideal_prod_adapter exact_witness_ideal_prod
    (arg_read : {RV (sa_sampleP sa) -> argT}) (sw_bound_eps (ic_b ic))
    idealproximity_close_of_indistinguishability.

(** The ideal-proximity proposition at that evidence, at the marginal-bound
    epsilon once. The premise instance_endpoints_stmt E identifies each
    model's executed coalition reading with the static one; every program at
    Sampled holds it, so a user inside a program has it and a user outside
    supplies it. The strength of the statement is the fineness of arg_read:
    at a one-point argT that coordinate is constant, the statement is true
    and it says nothing. var_dist is the sum of absolute differences,
    twice the literature's total variation distance, so a distinguisher's
    advantage is at most half the number. *)
Lemma idealproximity_prop_of_indistinguishability
    (Hendp : instance_endpoints_stmt E) :
  IdealProximityPropAt idealproximity_cert_of_indistinguishability
    (sw_bound_eps (ic_b ic)).
Proof.
exact: (idealproximity_tail idealproximity_cert_of_indistinguishability
  (fun C => @sa_coalition_viewE R (instance_profile A) (instance_exec E)
              sa 0 (ex_content_obs E) (fun u => Hendp _ _) C)
  (fun C => @sa_coalition_viewE R (instance_profile A) (instance_exec E)
              ideal_prod_adapter 0 (ex_content_obs E)
              (fun u => Hendp _ _) C)).
Qed.

(** A written term that closes the proposition above by the ssreflect
    terminator alone. Neither of the two joint laws the proposition compares
    reduces to the other, and its number is read off neither, so the term is
    rejected. The record is about that one term: the proposition itself is
    the lemma above. *)
Fail Definition idealproximity_prop_of_indistinguishability_by_conversion
  : IdealProximityPropAt idealproximity_cert_of_indistinguishability
      (sw_bound_eps (ic_b ic))
  := ltac:(by []).

End idealproximity_from_indistinguishability.

(* Section discharge under Set Implicit Arguments makes a section variable
   implicit as soon as a later one mentions it, so an application that passes
   the data arguments positionally can land them on the hypotheses. These
   lines pin the shape each declaration is used at. *)
Arguments ideal_prod_adapter {R A E sa argT} arg_decode arg_read ic.
Arguments ideal_prod_reading_arg_prodE {R A E sa argT} arg_decode arg_read ic
  {C}.
Arguments ideal_prod_reading_indep_arg {R A E sa argT} arg_decode arg_read ic
  {C}.
Arguments exact_witness_ideal_prod {R A E sa argT} arg_decode arg_read ic.
Arguments arg_read_distE {R A E sa argT} arg_decode arg_read ic.
Arguments var_dist_joint_reading_arg_le {R A E sa argT arg_decode arg_read}
  Harg Hprod ic C.
Arguments idealproximity_close_of_indistinguishability
  {R A E sa argT arg_decode arg_read} Harg Hprod ic {C}.
Arguments idealproximity_cert_of_indistinguishability
  {R A E sa argT arg_decode arg_read} Harg Hprod ic.
Arguments idealproximity_prop_of_indistinguishability
  {R A E sa argT arg_decode arg_read} Harg Hprod ic Hendp.
