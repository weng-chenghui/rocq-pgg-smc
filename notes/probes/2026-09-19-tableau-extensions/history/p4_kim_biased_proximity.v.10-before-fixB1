(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P4: Kim's one-cut row through the proximity arm                      *)
(*                                                                            *)
(* Kim's one-cut model and the den Boer uniform model of the five-card        *)
(* instance run one execution and share one sample space, the pair of         *)
(* committed bits with the sampled rotation; they differ in the law that      *)
(* space carries. That is the shape the proximity arm compares, so this       *)
(* instance is the first carrier of the arm. The uniform model is the ideal:  *)
(* five_card_row_uniform_tableau publishes it with the exact arm, so what     *)
(* the certificate holds as its ideal is a model whose own privacy is already *)
(* a theorem, and kim_biased_cert_idealE says the two are one term.           *)
(*                                                                            *)
(* One named Tableau Sampled value, five_card_row_biased_tableau of           *)
(* five_card_rows.v, carries both claims about the one-cut model: the         *)
(* spectral one, which the tree already publishes, and the proximity one. The *)
(* two are two rows over one model, and the equations below say that the      *)
(* spectral branch and the unbranched spectral program hold one coordinate.   *)
(*                                                                            *)
(* Both numbers come from one distance, kim_biased_cut_mixing on the cut      *)
(* group. The spectral arm spends it once for each of the two committed       *)
(* pairs it compares and the proximity arm spends it once, so the proximity   *)
(* number is half the spectral one at this model. The row is concluded at one *)
(* twenty-fifth, the number five_card_row_biased_inv25 publishes for the      *)
(* spectral arm, so the two rows are read in one column.                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   kim_biased_proximity_cert == the one-cut model's proximity certificate   *)
(*   five_card_row_biased_branch_spectral                                     *)
(*                             == the spectral claim, from the named value    *)
(*   five_card_row_biased_proximity                                           *)
(*                             == the proximity claim, published at 1/25      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   kim_biased_proximity_close                                               *)
(*                             == the two models' joint laws of reading and   *)
(*                                secret are within the cut distance          *)
(*   kim_biased_cert_idealE    == the certificate's ideal is the uniform row  *)
(*   kim_biased_proximity_eps_halfE                                           *)
(*                             == the spectral number is twice this one       *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import five_card_leakage five_card_kim kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import p1_joint_law_distance five_card_rows.

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
    secret under Kim's one biased cut is within the one-cut bundle's spectral
    number of the same joint law under the uniform rotation. It is the
    certificate field of the proximity arm at this instance: the two models
    differ only in the law of the rotation, the committed bits are drawn
    uniformly and independently of it in both, so the distance on the cut
    group is the distance of the two joint laws of the bits and the cut, and
    the pair of a reading and the secret is a deterministic function of those.
    The bound holds at every coalition and not only below the threshold; the
    threshold enters the arm's proposition and not this distance. *)
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
  <= sw_bound_eps (kim_biased_marginal_bound R).
Proof.
rewrite !five_card_reading_secretE.
apply: var_dist_fdistmap_pair.
rewrite /kim_input_dist five_card_uniform_pairE.
rewrite (five_card_sample_uniform_prodE R) !five_card_arg_cut_prodE.
rewrite var_dist_prodR.
rewrite -(@kim_single_cut_distE R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)).
rewrite -(five_card_sample_cut_distE R) /five_card_sample_cut_dist.
rewrite -(kim_biased_sample_cut_witnessE R).
exact: kim_biased_cut_mixing.
Qed.

End five_card_proximity_distance.

(******************************************************************************)
(*     The certificate, and its ideal                                         *)
(******************************************************************************)

(** The proximity certificate of Kim's one-cut row. Its five fields are the
    den Boer uniform model as the ideal; that model's exact witness, which is
    what makes the ideal an execution whose coalitions learn nothing at all;
    the conjunction of the committed bits as the one-cut model's own secret;
    the one-cut bundle's spectral number; and the distance above. The only
    inexact quantity is that number: the ideal, its witness and the secret are
    the terms the uniform row already publishes. *)
Definition kim_biased_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_biased_family R idx) :=
  @MkIdealProximityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (amf_sample five_card_uniform_family R idx)
    (five_card_exact_witness R idx)
    (five_card_leakage.Secret R)
    (sw_bound_eps (kim_biased_marginal_bound R))
    (fun C _ => @kim_biased_proximity_close R C).

(** The model the certificate calls ideal, and the witness it carries for it,
    are the model and the witness of the published uniform row. Conversion
    decides both, so the ideal a biased row is measured against is the row the
    manifest already carries and not a second description of it. *)
Lemma kim_biased_cert_idealE (R : realType) (idx : unit) :
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

(** The certificate's number in closed form: the one-cut bundle's spectral
    number, sqrt 5 over eighty. *)
Lemma kim_biased_proximity_cert_epsE (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) = Num.sqrt 5%:R * (1 / 80).
Proof. exact: kim_biased_epsE. Qed.

(** The spectral arm's number at this model is twice the proximity arm's. Both
    are read off kim_biased_cut_mixing, the one distance on the cut group; the
    spectral arm spends it once for each of the two committed pairs it
    compares and the proximity arm compares one law with one law. *)
Lemma kim_biased_proximity_eps_halfE (idx : unit) :
  cert_eps (kim_biased_cert R idx)
  = ipc_eps (kim_biased_proximity_cert R idx)
    + ipc_eps (kim_biased_proximity_cert R idx).
Proof. by []. Qed.

(** Three is above the square root of five, at every real field. *)
Fact five_card_sqrt5_le3 : Num.sqrt 5%:R <= 3%:R :> R.
Proof.
rewrite -(@ler_pXn2r R 2 isT).
2: by rewrite nnegrE sqrtr_ge0.
2: by rewrite nnegrE ler0n.
by rewrite sqr_sqrtr ?ler0n // -natrX ler_nat.
Qed.

(** The certificate's number is under one twenty-fifth, the constant the
    one-cut row publishes for the spectral arm. It is the obligation of the
    terminal that concludes the proximity row at that constant. *)
Lemma kim_biased_proximity_le_inv25 :
  sw_bound_eps (kim_biased_marginal_bound R) <= 1 / 25 :> R.
Proof.
have Hs0 : 0 <= Num.sqrt 5%:R :> R by exact: sqrtr_ge0.
have Hs := five_card_sqrt5_le3.
by rewrite kim_biased_epsE; lra.
Qed.

(** The certificate's own number is under two, the ceiling var_dist_le2 gives
    for a variation distance, so the certificate is not vacuous. At about one
    and a half percent of the ceiling it is a weak separation and not a
    cryptographic one, as the spectral certificate of the same model is. *)
Lemma kim_biased_proximity_cert_eps_lt2 (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) < 2%:R.
Proof.
have Hs0 : 0 <= Num.sqrt 5%:R :> R by exact: sqrtr_ge0.
have Hs := five_card_sqrt5_le3.
by rewrite kim_biased_proximity_cert_epsE; lra.
Qed.

End kim_biased_proximity_numbers.

(******************************************************************************)
(*     One model, two claims, two rows                                        *)
(******************************************************************************)

(** Kim's one-cut model certified by the spectral arm, continued from the
    named Sampled value rather than written out from the prefix. It is the
    sibling of the proximity row below: the two continue one term, so what
    separates them is the arm and nothing about the algebra, the run or the
    law. *)
Definition five_card_row_biased_branch_spectral : PublishedRow :=
  five_card_row_biased_tableau
    certify SpectralDecay kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The branch and the program written out from the prefix hold one
    AnalysisBridged coordinate, so naming the Sampled value costs the spectral
    row nothing. *)
(* exact: erefl and not by [], following the hang shape recorded in STATUS.md:
   done does not return on an equation between two rows' coordinates. *)
Lemma five_card_row_biased_branch_spectral_atE :
  published_at five_card_row_biased_branch_spectral
  = published_at five_card_row_biased_spectral_tableau.
Proof. exact: erefl. Qed.

(** The branch publishes the manifest's own row for the biased path. *)
Lemma five_card_row_biased_branch_spectral_rowE :
  published_row five_card_row_biased_branch_spectral = five_card_row_biased.
Proof. exact: erefl. Qed.

(** Kim's one-cut model certified by the proximity arm and concluded at one
    twenty-fifth, the constant the spectral row of the same model publishes.
    What a coalition of fewer than two seats is shown is that the joint law of
    its reading with the conjunction of the committed bits is within that
    number of the product of the two marginals the den Boer uniform execution
    has, where the reading and the conjunction are independent outright. The
    number is spent once, against the spectral row's twice, and the transfer
    status is the one the spectral row earns, since the same ideal cut is what
    both certificates compare against. *)
Definition five_card_row_biased_proximity
  : PublishedRowAt five_card_reprice_inv25 :=
  five_card_row_biased_tableau
    certify IdealProximity kim_biased_proximity_cert
    |> conclude five_card_reprice_inv25
       by (fun R _ => kim_biased_proximity_le_inv25 R)
    |> publish IdealFinite BaselineClassicalOnly.

(** The proximity row publishes the manifest's row for the biased path, as its
    spectral sibling does. An AnalysisPathRow holds descriptive metadata and
    no Prop, so one manifest row carrying a spectral row and a proximity row
    says nothing about either claim. *)
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

(** The arm the spectral branch carries, at every real field and index. *)
Lemma five_card_row_biased_branch_spectral_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_branch_spectral))
             R) :
  security_arm_of five_card_row_biased_branch_spectral R idx
  = SpectralDecayArm.
Proof. by []. Qed.

(** The arm the proximity row carries, at every real field and index: the
    distance to a private ideal model, and not the distance between two
    readings of one model. This is the value a paper's table prints in the arm
    column for this row. *)
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
  <> security_arm_of five_card_row_biased_branch_spectral R idx.
Proof. by []. Qed.

(******************************************************************************)
(*     What the proximity row states at this instance                         *)
(******************************************************************************)

(** The proximity row's security statement at the five-card instance: at fewer
    than two colluding seats, the joint law of the executed coalition view and
    the conjunction of the committed bits under Kim's one biased cut is within
    one twenty-fifth of the product of the two marginals of the den Boer
    uniform execution. The proof is the row's security projection applied, so
    the row and this statement are one theorem. *)
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
  <= 1 / 25.
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt C HC). Qed.
