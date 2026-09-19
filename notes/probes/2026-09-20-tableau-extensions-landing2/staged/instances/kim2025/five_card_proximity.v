(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_proximity: Kim's one-cut row through the proximity arm           *)
(*                                                                            *)
(* Kim's one-cut model and the den Boer uniform model of the five-card        *)
(* instance run one execution and share one sample space, the pair of         *)
(* committed bits with the sampled rotation; they differ in the law that      *)
(* space carries. That is the shape the proximity arm compares, so this       *)
(* instance is the first carrier of the arm. The uniform model is the ideal:  *)
(* five_card_row_uniform_tableau publishes it with the exact arm, so what the *)
(* certificate holds as its ideal is a model whose own privacy is already a   *)
(* theorem, and kim_biased_proximity_cert_idealE says the two are one term.   *)
(*                                                                            *)
(* One named Tableau Sampled value, five_card_row_biased_tableau of           *)
(* five_card_rows.v, carries both claims about the one-cut model: the         *)
(* input-indistinguishability one, which the tree already publishes, and the  *)
(* proximity one. The two are two rows over one model, and the equations      *)
(* below say that the input-indistinguishability branch and the unbranched    *)
(* input-indistinguishability program hold one coordinate.                    *)
(*                                                                            *)
(* Both numbers come from one distance on the cut group, the one fiftieth of  *)
(* kim_biased_cut_mixing_exact. The input-indistinguishability arm doubles    *)
(* whatever marginal bound its certificate carries and the proximity arm      *)
(* spends the distance once, so the proximity row publishes one fiftieth      *)
(* where the row built on kim_biased_cert_exact, five_card_row_biased_inv25   *)
(* of five_card_rows.v, publishes one twenty-fifth. The                       *)
(* input-indistinguishability row continued below carries kim_biased_cert     *)
(* instead, whose marginal bound is the one-cut bundle's spectral number, and *)
(* publishes sqrt 5 over forty. The proximity row publishes its certificate's *)
(* own number, with no terminal between the certificate and the reader. That  *)
(* number bounds a sum of absolute differences, twice the total variation     *)
(* distance, so a distinguisher's advantage against this row is at most one   *)
(* hundredth.                                                                 *)
(*                                                                            *)
(* Three readings of the published number follow the row. Against the bound   *)
(* two that var_dist_le2 gives it is one percent of what a pair of laws on a  *)
(* finite carrier can reach, so the certificate is a weak separation and not  *)
(* a cryptographic one. With the ideal removed it bounds the distance of the  *)
(* one-cut model's own joint law from the product of that law's two           *)
(* marginals, at three fiftieths: the ideal's two marginals are within the    *)
(* number of the actual model's, once for each, and the comparison with the   *)
(* actual product spends the number a third time. Downward it cannot move,    *)
(* because the obligation conclude asks of a terminal republishing this row   *)
(* at one hundredth is refutable and not merely unproved.                     *)
(*                                                                            *)
(* Not claimed. That the proximity proposition follows from the               *)
(* input-indistinguishability proposition for a reason that reads the         *)
(* input-indistinguishability certificate's fields. The implication proved at *)
(* the end holds because its conclusion is a theorem at this instance and its *)
(* premise is discarded, and manifest/pgg_tableau_arm_relations.v holds the   *)
(* same implication at two from any premise whatever. What separates the two  *)
(* arms in general is stated there.                                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   kim_biased_proximity_cert  == the one-cut model's proximity certificate  *)
(*   five_card_row_biased_branch_indistinguishability                         *)
(*                              == the input-indistinguishability claim, from *)
(*                                 the named value                            *)
(*   five_card_row_biased_proximity                                           *)
(*                              == the proximity claim, published at 1/50     *)
(*   five_card_reprice_inv100   == the constant one hundredth, as a reprice   *)
(*   five_card_biased_proximity_at_singleton                                  *)
(*                              == the row's claim at one concrete seat       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_uniform_pairE    == the uniform law on the committed pair is   *)
(*                                 one law under either cardinality proof     *)
(*   five_card_reading_secretE  == a coalition's reading and the secret       *)
(*                                 factor through the pair of the committed   *)
(*                                 bits and the cut                           *)
(*   five_card_arg_cut_prodE    == that pair's joint law is the uniform pair  *)
(*                                 tensored with the model's cut law          *)
(*   kim_biased_proximity_close == the two models' joint laws of reading and  *)
(*                                 secret are within one fiftieth             *)
(*   kim_biased_proximity_cert_idealE                                         *)
(*                              == the certificate's ideal and witness are    *)
(*                                 the uniform row's model and port           *)
(*   kim_biased_proximity_cert_epsE                                           *)
(*                              == the certificate's number is one fiftieth   *)
(*   kim_biased_proximity_eps_halfE                                           *)
(*                              == the exact input-indistinguishability       *)
(*                                 certificate's number is twice the          *)
(*                                 proximity certificate's                    *)
(*   kim_biased_proximity_cert_eps_lt2                                        *)
(*                              == that number is below the bound two         *)
(*                                 var_dist_le2 gives                         *)
(*   five_card_row_biased_branch_indistinguishability_atE                     *)
(*                              == the branch and the program written out     *)
(*                                 from the prefix hold one coordinate        *)
(*   five_card_row_biased_branch_indistinguishability_rowE                    *)
(*   five_card_row_biased_proximity_rowE                                      *)
(*                              == each of the two rows publishes the         *)
(*                                 manifest's row for the biased path         *)
(*   five_card_row_biased_proximity_publishedE                                *)
(*                              == the three coordinates the proximity row    *)
(*                                 publishes                                  *)
(*   five_card_row_biased_branch_indistinguishability_armE                    *)
(*                              == the branch carries the                     *)
(*                                 input-indistinguishability arm             *)
(*   five_card_row_biased_proximity_armE                                      *)
(*                              == the proximity row carries the proximity    *)
(*                                 arm                                        *)
(*   five_card_row_biased_arm_neq                                             *)
(*                              == the two rows over the one model carry      *)
(*                                 different arms                             *)
(*   five_card_biased_view_proximity                                          *)
(*                              == the proximity row's security statement     *)
(*   five_card_biased_view_own_marginals                                      *)
(*                              == the same with the ideal removed, at three  *)
(*                                 fiftieths                                  *)
(*   kim_biased_conclude_below_false                                          *)
(*                              == the conclude obligation at a number below  *)
(*                                 the certificate's own is false             *)
(*   five_card_singleton_below_threshold                                      *)
(*                              == one seat is below the five-card privacy    *)
(*                                 threshold                                  *)
(*   five_card_biased_proximity_prop_holds                                    *)
(*                              == the arm's proposition at the number the    *)
(*                                 row publishes                              *)
(*   five_card_biased_indistinguishability_implies_proximity                  *)
(*                              == the input-indistinguishability proposition *)
(*                                 implies it, its premise discarded          *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import five_card_leakage five_card_kim kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import five_card_rows s5_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The distance between the two models' joint laws                        *)
(******************************************************************************)

Section five_card_proximity_distance.
Variable R : realType.

(** The uniform law on the pair of committed bits, under the two cardinality
    proofs the tree carries for that pair. Kim's law is built over the first
    and the den Boer law over the second, and the product step below asks for
    one common left factor. *)
Lemma five_card_uniform_pairE :
  fdist_uniform card_bool2 = fdist_uniform five_card_card_bool2
    :> R.-fdist (bool * bool).
Proof. by apply/fdist_ext => x; rewrite !fdist_uniformE. Qed.

(** The pair of a coalition's reading and the secret, as a reading of the pair
    of the committed bits and the cut. Both readers of a five-card sample
    point factor through that pair, which is the carrier on which the two
    models are compared. *)
Lemma five_card_reading_secretE
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1})
    (d : R.-fdist five_card_leakage.Omega) :
  fdistmap (fun u => (@static_coalition_obs five_card_algebra five_card_params
                        C (five_card_sample_arg u) (five_card_sample_cut u),
                      five_card_leakage.Secret R u)) d
  = fdistmap (fun ag : (bool * bool) *
                pgg_gT (mp_M (instance_profile five_card_algebra)) =>
                (@static_coalition_obs five_card_algebra five_card_params C
                   ag.1 ag.2, ag.1.1 && ag.1.2))
      (fdistmap (fun u : five_card_leakage.Omega =>
                   (u.1, five_card_sample_cut u)) d).
Proof.
rewrite fdistmap_comp; congr fdistmap.
by apply: funext; case=> -[a b] k.
Qed.

(** The joint law of the committed bits and the cut, at a law on the sample
    space written as a product. The committed bits are drawn uniformly in both
    models and the cut is the rotation the second factor names, so the joint
    law is the uniform pair tensored with that model's cut law. *)
Lemma five_card_arg_cut_prodE (W : R.-fdist 'I_5) :
  fdistmap (fun u : five_card_leakage.Omega => (u.1, five_card_sample_cut u))
    ((fdist_uniform five_card_card_bool2) `x W)
  = ((fdist_uniform five_card_card_bool2)
     `x (fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) W)).
Proof.
exact: (fdistmap_prodr (fdist_uniform five_card_card_bool2) W
          (fun k : 'I_5 => (fc_sigma ^+ k)%g)).
Qed.

(** At every coalition, the joint law of that coalition's reading with the
    secret under Kim's one biased cut is within one fiftieth of the same joint
    law under the uniform rotation. It is the certificate field of the
    proximity arm at this instance: the two models differ only in the law of
    the rotation, the committed bits are drawn uniformly and independently of
    it in both, so the distance on the cut group is the distance of the two
    joint laws of the bits and the cut, and the pair of a reading and the
    secret is a deterministic function of those. The bound holds at every
    coalition and not only below the threshold; the threshold enters the arm's
    proposition and not this distance. *)
Lemma kim_biased_proximity_close
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  var_dist
    (fdistmap (fun u => (@static_coalition_obs five_card_algebra
                           five_card_params C (five_card_sample_arg u)
                           (five_card_sample_cut u),
                         five_card_leakage.Secret R u))
       (kim_input_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fdistmap (fun u => (@static_coalition_obs five_card_algebra
                           five_card_params C (five_card_sample_arg u)
                           (five_card_sample_cut u),
                         five_card_leakage.Secret R u))
       (five_card_leakage.P R))
  <= 1 / 50 :> R.
Proof.
rewrite !five_card_reading_secretE.
apply: var_dist_fdistmap_pair.
rewrite /kim_input_dist five_card_uniform_pairE.
rewrite (five_card_sample_uniform_prodE R) !five_card_arg_cut_prodE.
rewrite var_dist_prodR.
rewrite -(@kim_single_cut_distE R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)).
rewrite -(five_card_sample_cut_distE R) /five_card_sample_cut_dist.
rewrite -(kim_biased_sample_cut_witnessE R).
exact: kim_biased_cut_mixing_exact.
Qed.

End five_card_proximity_distance.

(******************************************************************************)
(*     The certificate, and its ideal                                         *)
(******************************************************************************)

(** The proximity certificate of Kim's one-cut row. Its five fields are the
    den Boer uniform model as the ideal; that model's exact witness, which is
    what makes the ideal an execution whose coalitions learn nothing at all;
    the conjunction of the committed bits as the one-cut model's own secret;
    one fiftieth; and the distance above. The ideal and the witness are the
    terms the published uniform row carries, which
    kim_biased_proximity_cert_idealE states, and the secret is the same
    conjunction that row's witness is stated at. The number is the bound
    kim_biased_cut_mixing_exact proves on the cut group's own distance, and
    the last field is kim_biased_proximity_close of this file, which says the
    distance between the two joint laws is at most that number. *)
Definition kim_biased_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_biased_family R idx) :=
  @MkIdealProximityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (amf_sample five_card_uniform_family R idx)
    (five_card_exact_witness R idx)
    (five_card_leakage.Secret R)
    (1 / 50)
    (fun C _ => @kim_biased_proximity_close R C).

(** The model the certificate calls ideal, and the witness it carries for it,
    are the model and the witness of the published uniform row. Conversion
    decides both, so the ideal a biased row is measured against is the model
    the manifest's uniform row publishes and not a second description of
    it. *)
Lemma kim_biased_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (kim_biased_proximity_cert R idx)
  = amf_sample (ab_f (published_at five_card_row_uniform_tableau)) R idx
  /\ ExactIndependence (ipc_witness (kim_biased_proximity_cert R idx))
     = ab_port (published_at five_card_row_uniform_tableau) R idx.
Proof. by split. Qed.

(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

Section kim_biased_proximity_numbers.
Variable R : realType.

(** The certificate's number is one fiftieth, the variation distance
    kim_biased_cut_mixing_exact proves between Kim's one biased cut and the
    uniform rotation on the cut group. *)
Lemma kim_biased_proximity_cert_epsE (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50 :> R.
Proof. exact: erefl. Qed.

(** The number kim_biased_cert_exact carries at this model is twice the
    number kim_biased_proximity_cert carries. Both are read off
    kim_biased_cut_mixing_exact, the one distance on the cut group; the
    input-indistinguishability arm spends it once for each of the two
    committed pairs it compares and the proximity arm compares one law with
    one law. The relation is between these two certificates and not between
    the two arms: the same model also carries kim_biased_cert, whose marginal
    bound is sqrt 5 over eighty and which therefore publishes sqrt 5 over
    forty, so neither arm determines the number of the other. *)
Lemma kim_biased_proximity_eps_halfE (idx : unit) :
  cert_eps (kim_biased_cert_exact R idx)
  = ipc_eps (kim_biased_proximity_cert R idx)
    + ipc_eps (kim_biased_proximity_cert R idx).
Proof. exact: erefl. Qed.

(** The certificate's own number is under two, the bound var_dist_le2 gives
    for a variation distance, so the certificate is not vacuous. At one
    percent of that bound it is a weak separation and not a cryptographic
    one, as is kim_biased_cert_exact at one twenty-fifth. *)
Lemma kim_biased_proximity_cert_eps_lt2 (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) < 2%:R.
Proof. by rewrite kim_biased_proximity_cert_epsE; lra. Qed.

End kim_biased_proximity_numbers.

(******************************************************************************)
(*     One model, two claims, two rows                                        *)
(******************************************************************************)

(** Kim's one-cut model certified by the input-indistinguishability arm,
    continued from the named Sampled value rather than written out from the
    prefix. It is the sibling of the proximity row below: the two continue
    one term, so what separates them is the arm and nothing about the
    algebra, the run or the law. *)
Definition five_card_row_biased_branch_indistinguishability : PublishedRow :=
  five_card_row_biased_tableau
    certify InputIndistinguishability kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The branch and the program written out from the prefix hold one
    AnalysisBridged coordinate, so naming the Sampled value costs the
    input-indistinguishability row nothing. *)
(* exact: erefl and not by [], because done does not return on an equation
   between two rows' coordinates. *)
Lemma five_card_row_biased_branch_indistinguishability_atE :
  published_at five_card_row_biased_branch_indistinguishability
  = published_at five_card_row_biased_indistinguishability_tableau.
Proof. exact: erefl. Qed.

(** The branch publishes the manifest's own row for the biased path. *)
Lemma five_card_row_biased_branch_indistinguishability_rowE :
  published_row five_card_row_biased_branch_indistinguishability
  = five_card_row_biased.
Proof. exact: erefl. Qed.

(** Kim's one-cut model certified by the proximity arm and published at its
    certificate's own number, one fiftieth. What a coalition of fewer than
    two seats is shown is that the joint law of its reading with the
    conjunction of the committed bits is within that number of the product of
    the two marginals the den Boer uniform execution has, where the reading
    and the conjunction are independent outright. The number is spent once,
    against the input-indistinguishability row's twice. Its transfer status is
    IdealFinite, the same the input-indistinguishability row carries, and the
    two certificates compare against the same ideal cut. *)
Definition five_card_row_biased_proximity : PublishedRow :=
  five_card_row_biased_tableau
    certify IdealProximity kim_biased_proximity_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The proximity row publishes the manifest's row for the biased path, as
    its input-indistinguishability sibling does. An AnalysisPathRow holds
    descriptive metadata and no Prop, so one manifest row carrying an
    input-indistinguishability row and a proximity row says nothing about
    either claim. *)
Lemma five_card_row_biased_proximity_rowE :
  published_row five_card_row_biased_proximity = five_card_row_biased.
Proof. exact: erefl. Qed.

(** The three coordinates the proximity row publishes. *)
Lemma five_card_row_biased_proximity_publishedE :
  apr_completion (published_row five_card_row_biased_proximity)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_biased_proximity) = IdealFinite
  /\ apr_assumptions (published_row five_card_row_biased_proximity)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(** The arm the input-indistinguishability branch carries, at every real
    field and index. *)
Lemma five_card_row_biased_branch_indistinguishability_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_biased_branch_indistinguishability))
             R) :
  security_arm_of five_card_row_biased_branch_indistinguishability R idx
  = InputIndistinguishabilityArm.
Proof. by []. Qed.

(** The arm the proximity row carries, at every real field and index: the
    distance to a private ideal model, and not the distance between two
    readings of one model. *)
Lemma five_card_row_biased_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_proximity)) R) :
  security_arm_of five_card_row_biased_proximity R idx = IdealProximityArm.
Proof. by []. Qed.

(** The two rows over the one model carry different arms, so the pair is two
    statements about one probability model and not one statement published
    twice. *)
Lemma five_card_row_biased_arm_neq (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_proximity)) R) :
  security_arm_of five_card_row_biased_proximity R idx
  <> security_arm_of five_card_row_biased_branch_indistinguishability R idx.
Proof. by []. Qed.

(******************************************************************************)
(*     What the proximity row states at this instance                         *)
(******************************************************************************)

(** The proximity row's security statement at the five-card instance: at fewer
    than two colluding seats, the joint law of the coalition's executed
    reading and the conjunction of the committed bits under Kim's one biased
    cut is within one fiftieth of the product of the two marginals of the den
    Boer uniform execution. The proof is the row's security projection
    applied, so the row and this statement are one theorem. *)
Theorem five_card_biased_view_proximity (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap (@sa_coalition_view R five_card_profile five_card_exec_plug
                  (five_card_sample R) 0 C) (P R))
     `x (fdistmap (five_card_leakage.Secret R) (P R)))
  <= 1 / 50.
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt C HC). Qed.

(** The one-cut row's bound restated against the executed law's own two
    marginals: at fewer than two colluding seats, the joint law of the
    coalition's reading with the conjunction of the committed bits is within
    three fiftieths of the product of that same law's two marginals. The den
    Boer uniform model has left the statement. What remains is a bound on how
    far the one-cut run is from making a coalition's reading and the secret
    independent, and the advantage a distinguisher gets from it is at most
    three hundredths. *)
Theorem five_card_biased_view_own_marginals (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap fst
        (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                               five_card_exec_plug
                               (amf_sample kim_biased_family R tt) 0 C u,
                             five_card_leakage.Secret R u))
           (sa_sampleP (amf_sample kim_biased_family R tt))))
     `x (fdistmap snd
           (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                                  five_card_exec_plug
                                  (amf_sample kim_biased_family R tt) 0 C u,
                                five_card_leakage.Secret R u))
              (sa_sampleP (amf_sample kim_biased_family R tt)))))
  <= 3%:R * (1 / 50).
Proof.
exact: (var_dist_own_marginals (@five_card_biased_view_proximity R C HC)).
Qed.

(******************************************************************************)
(*     A number below the certificate's is refused                            *)
(******************************************************************************)

(** The name one hundredth, half of what Kim's one-cut proximity certificate
    proves. *)
Definition five_card_reprice_inv100 : Reprice := fun R => Some (1 / 100 : R).

(** The obligation conclude asks of a terminal that would republish Kim's
    one-cut proximity row at one hundredth is false, and not merely beyond
    what could be proved: one fiftieth is not at most one hundredth. A
    published number may therefore be moved upward and never downward, and
    that is decided by the ordering ConcludePayload states and not by which
    tactic a terminal reaches for. *)
Lemma kim_biased_conclude_below_false (R : realType) (idx : unit) :
  ~ (ipc_eps (kim_biased_proximity_cert R idx)
     <= odflt (ipc_eps (kim_biased_proximity_cert R idx))
          (five_card_reprice_inv100 R)).
Proof. rewrite kim_biased_proximity_cert_epsE /= => H; lra. Qed.

(******************************************************************************)
(*     Every hypothesis discharged at one concrete coalition                  *)
(******************************************************************************)

(** One seat is below the five-card privacy threshold. *)
Fact five_card_singleton_below_threshold (i : 'I_5) :
  (#|[set i]| < profile_k (instance_profile five_card_algebra))%N.
Proof. by rewrite cards1. Qed.

(** Kim's one-cut row's claim with every hypothesis discharged: one real
    field, one coalition of one named seat, and the threshold condition proved
    rather than assumed. The coalition is not empty, so the reading the bound
    is stated on is the seat's own content observation at that seat, where the
    empty coalition's reading is ord0 at every seat. *)
Definition five_card_biased_proximity_at_singleton (R : realType) (i : 'I_5) :=
  @five_card_biased_view_proximity R [set i]
    (five_card_singleton_below_threshold i).

(******************************************************************************)
(*     The conclusion does not hold by computation                            *)
(******************************************************************************)

(** The arm's proposition at Kim's one-cut certificate is not closed by
    conversion. A variation distance between two laws on a real field is not a
    Boolean a kernel reduces, so a proof of the row's claim has to be the
    mathematics and cannot be the computation. *)
Fail Definition five_card_biased_proximity_by_computation (R : realType)
    (idx : unit)
  : IdealProximityPropAt (kim_biased_proximity_cert R idx)
      (ipc_eps (kim_biased_proximity_cert R idx))
  := ltac:(move=> C HC; reflexivity).

(** Nor by done, which is what a clause left to a tactic in a row would
    reach. *)
Fail Definition five_card_biased_proximity_by_done (R : realType) (idx : unit)
  : IdealProximityPropAt (kim_biased_proximity_cert R idx)
      (ipc_eps (kim_biased_proximity_cert R idx))
  := ltac:(by []).

(******************************************************************************)
(*     What a certificate may name as its ideal                               *)
(******************************************************************************)

(** Another instance's model is not an ideal for this one. The ideal adapter
    is typed over the row's own execution parameters, so a model of the S5
    instance and the witness proved about it are rejected where they are
    written and not deep inside the proposition. *)
Fail Definition kim_biased_cert_s5_ideal (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_biased_family R idx) :=
  @MkIdealProximityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (amf_sample s5_rand_family R idx)
    (s5_rand_exact_witness R idx)
    (five_card_leakage.Secret R)
    (1 / 50)
    (fun C _ => @kim_biased_proximity_close R C).

(** Two models of one instance whose families carry one index type are still
    two adapters. The one-cut model's proximity certificate is rejected where
    the seven-cut model's is required: a certificate is typed over the sample
    adapter, and the two adapters differ in their sample space as well as in
    their law. *)
Fail Definition kim_centi_proximity_from_biased (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_centi_family R idx) :=
  kim_biased_proximity_cert R idx.

(** The same rejection where it is written in a row: the seven-cut model's
    named Sampled value does not take the one-cut model's certificate. *)
Fail Definition five_card_row_repeated_proximity : Tableau AnalysisBridged :=
  five_card_row_repeated_tableau
    certify IdealProximity kim_biased_proximity_cert.

(** The converse direction, at the arm the tree already carries: the
    seven-cut model's input-indistinguishability certificate is rejected
    where the one-cut model's is required. The proximity arm and the
    input-indistinguishability arm are rejected at the same argument, the
    sample adapter each certificate type is indexed by, so the proximity arm
    adds no new way for two models of one instance to be confused. *)
Fail Definition kim_biased_indistinguishability_from_centi
  (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_biased_family R idx) :=
  kim_centi_cert R idx.

(******************************************************************************)
(*     The proximity proposition at this instance, and what implies it        *)
(******************************************************************************)

(** The proximity proposition of Kim's one-cut row at the number that row
    publishes, taken off the published row itself. It is the arm's conclusion
    standing on its own at this instance. *)
Lemma five_card_biased_proximity_prop_holds (R : realType) :
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt). Qed.

(** The input-indistinguishability proposition implies the proximity
    proposition at the five-card instance, at every constant the
    input-indistinguishability premise is stated at, because the conclusion
    is a theorem there and the premise is discarded. The implication holds
    and carries no information: a derivation that reads the
    input-indistinguishability certificate's fields is a different statement
    and is not this one. *)
Lemma five_card_biased_indistinguishability_implies_proximity
    (R : realType) (c : R) :
  IndistinguishabilityPropAt (kim_biased_cert R tt) c ->
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. by move=> _; exact: five_card_biased_proximity_prop_holds. Qed.
