(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_proximity: the laws and the distance Kim's one-cut proximity     *)
(* certificate is built from                                                  *)
(*                                                                            *)
(* Kim's one-cut model and the den Boer uniform model of the five-card        *)
(* instance run one execution and share one sample space, the pair of         *)
(* committed bits with the sampled rotation; they differ in the law that      *)
(* space carries. This file holds the mathematics that separates the two,     *)
(* with no program and no published row in it.                                *)
(*                                                                            *)
(* The distance is the certificate field of the proximity arm: at every       *)
(* coalition, the joint law of that coalition's reading with the conjunction  *)
(* of the committed bits under Kim's one biased cut is within one fiftieth of *)
(* the same joint law under the uniform rotation. The number is the bound     *)
(* kim_biased_cut_mixing_exact proves on the cut group's own distance. The    *)
(* bound holds at every coalition and not only below the threshold of two;    *)
(* the threshold enters the arm's proposition and not this distance.          *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, which is twice    *)
(* the total variation distance of the literature, so a bound of one fiftieth *)
(* here is a distinguishing advantage of at most one hundredth wherever it is *)
(* used.                                                                      *)
(*                                                                            *)
(* Three laws carry that proof. The uniform law on the pair of committed bits *)
(* is one law under either of the two cardinality proofs the tree holds for   *)
(* that pair, which is what gives the product step below one common left      *)
(* factor. The pair of a coalition's reading and the secret factors through   *)
(* the pair of the committed bits and the cut, which is the carrier on which  *)
(* the two models are compared. And at a product law on the sample space that *)
(* pair's joint law is the uniform pair tensored with the model's cut law, so *)
(* the distance between the two models on the cut group is the distance       *)
(* between their two joint laws.                                              *)
(*                                                                            *)
(* The certificate itself, the row it publishes and the statements about them *)
(* are in instances/kim2025/tableau/, whose AnalysisBridged file requires     *)
(* this one. This file requires no tableau module, so the arrow between the   *)
(* mathematics and the tableau runs one way, upward.                          *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_uniform_pairE == the uniform law on the committed pair is one  *)
(*                              law under either cardinality proof            *)
(*   five_card_reading_secretE                                                *)
(*                           == a coalition's reading and the secret factor   *)
(*                              through the pair of the committed bits and    *)
(*                              the cut                                       *)
(*   five_card_arg_cut_prodE == at a product law on the sample space, that    *)
(*                              pair's joint law is the uniform pair tensored *)
(*                              with the model's cut law                      *)
(*   kim_biased_proximity_close                                               *)
(*                           == at every coalition, the two models' joint     *)
(*                              laws of reading and secret are within one     *)
(*                              fiftieth                                      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import five_card_leakage five_card_kim kim_input_privacy.
From pgg_smc Require Import five_card_mixing.

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
