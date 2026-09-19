(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P6, second half: the PSL(2,11) word row through the proximity arm    *)
(*                                                                            *)
(* The word model psl211_word_family names and the all-decks model of         *)
(* psl211_models.v run one execution over one sample space and differ in the  *)
(* law of the cut alone. That is the shape the proximity arm compares, and    *)
(* the twelve-card chirality instance is its third carrier after Kim's        *)
(* one-cut five-card model and the eight-card orbit instance. The ideal is an *)
(* execution whose own privacy is a theorem: psl211_row_alldecks_tableau      *)
(* publishes it with the exact arm, and psl211_word_proximity_cert_idealE     *)
(* says that the model the certificate calls ideal and the model that row     *)
(* publishes are one term.                                                    *)
(*                                                                            *)
(* Word gloss of this instance. A deck description is the whole run argument, *)
(* a chirality bit together with a deal. A deal is the block line of that     *)
(* chirality's Steiner system, the labelling of the heart codes and the       *)
(* labelling of the club codes, the three coordinates other than the secret.  *)
(* The secret is the chirality bit. The two models share the sample space, so *)
(* psl211_alldecks_secret is the secret of both and the certificate needs no  *)
(* second reading of the bit.                                                 *)
(*                                                                            *)
(* Six is the privacy threshold the derived profile declares, so every        *)
(* statement below is about a static coalition of at most five of the twelve  *)
(* seats reading its own endpoints. The row publishes the number the          *)
(* certificate proves and names no constant: this instance has no row         *)
(* carrying a constant for this model to be read in one column with, the      *)
(* constancy field a spectral certificate would need being refuted at it.     *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_word_proximity_cert == the word model's proximity certificate     *)
(*   psl211_row_word_proximity  == the proximity claim, published at 2^-40    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_word_proximity_close                                              *)
(*                              == the two models' joint laws of reading and  *)
(*                                 chirality are within 2^-40                 *)
(*   psl211_word_proximity_cert_idealE                                        *)
(*                              == the certificate's ideal is the all-decks   *)
(*                                 row's model and witness                    *)
(*   psl211_word_proximity_cert_epsE                                          *)
(*                              == the certificate's number in closed form    *)
(*   psl211_pow2_40_ge1         == two to the fortieth is at least one        *)
(*   psl211_pow2_40_gt0         == two to the fortieth is positive            *)
(*   psl211_word_proximity_cert_eps_lt2                                       *)
(*                              == the number is under the ceiling every      *)
(*                                 variation distance meets                   *)
(*   psl211_row_word_proximity_armE                                           *)
(*                              == the row carries the proximity arm          *)
(*   psl211_row_word_proximity_publishedE                                     *)
(*                              == the three coordinates the row publishes    *)
(*   psl211_word_view_proximity == what the row states at this instance       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_instance pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_closure psl211_profile.
From pgg_smc Require Import psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import psl211_rows p1_joint_law_distance.
From tableau_ext_probe Require Import p6_psl211_word_model.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(******************************************************************************)
(*     The distance between the two models' joint laws                        *)
(******************************************************************************)

(** At every coalition of at most five of the twelve seats, the joint law of
    that coalition's reading with the chirality under the 584-letter word
    shuffle is within 2^-40 of the same joint law under the uniform shuffle.
    It is the certificate field of the proximity arm at this instance: the two
    models differ in the law of the cut alone, and the pair of a reading and
    the chirality is a deterministic function of the sample point, so the
    distance between the two cuts carries down to that pair unchanged. The
    claim is an average over the deck description and the cut. The bound holds
    at every coalition and not only below the threshold; the threshold enters
    the arm's proposition and not this distance. *)
Lemma psl211_word_proximity_close (R : realType) (C : {set seatT}) :
  (#|C| < profile_k (instance_profile psl211_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_word_sample R).(sa_arg) u)
                           ((psl211_word_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_word_sample R)))
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_alldecks_sample R).(sa_arg) u)
                           ((psl211_alldecks_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_alldecks_sample R)))
  <= 2%:R^-40.
Proof.
(* The two maps are one term, the two adapters reading a sample point by the
   same two projections, so the data processing step of p1 applies with no
   pointwise rewriting of either reader. *)
move=> _.
apply: var_dist_fdistmap_pair.
rewrite psl211_word_sampleP_E psl211_alldecks_sampleP_E.
exact: psl211_word_lawE.
Qed.

(******************************************************************************)
(*     The certificate, and its ideal                                         *)
(******************************************************************************)

(** The proximity certificate of the PSL(2,11) word row. Its five fields are
    the all-decks model as the ideal; that model's exact witness, which is
    what makes the ideal an execution whose coalitions of at most five seats
    learn nothing at all; the chirality, which is the secret of the two models
    as one term; the word walk's number 2^-40; and the distance above. The
    only inexact quantity is that number: the ideal, its witness and the
    secret are the terms the all-decks row already publishes. *)
Definition psl211_word_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample psl211_word_family R idx) :=
  @MkIdealProximityCert R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_word_family R idx)
    (amf_sample psl211_exact_family R idx)
    (psl211_exact_witness R idx)
    (psl211_alldecks_secret R)
    (2%:R^-40)
    (fun C HC => @psl211_word_proximity_close R C HC).

(** The model the certificate calls ideal, and the witness it carries for it,
    are the model and the witness of the published all-decks row. Conversion
    decides both, so the ideal a word row is measured against is the model
    psl211_rows.v publishes and not a second description of it. *)
Lemma psl211_word_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample (ab_f (published_at psl211_row_alldecks_tableau)) R idx
  /\ ExactIndependence (ipc_witness (psl211_word_proximity_cert R idx))
     = ab_port (published_at psl211_row_alldecks_tableau) R idx.
(* exact: erefl and not by []: done does not return on an equation between two
   rows' coordinates, where exact: erefl decides it at once. Both projections
   were measured at 0.000 s on 2026-09-19. *)
Proof. split; exact: erefl. Qed.

(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

(** The certificate's number in closed form: the 584-letter walk's number,
    2^-40, which is 9.094947017729282e-13. *)
Lemma psl211_word_proximity_cert_epsE (R : realType) (idx : unit) :
  ipc_eps (psl211_word_proximity_cert R idx) = 2%:R^-40 :> R.
Proof. exact: erefl. Qed.

(** Two to the fortieth is at least one, at every real field. *)
Fact psl211_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. by apply: exprn_ege1; rewrite ler1n. Qed.

(** Two to the fortieth is positive, at every real field. *)
Fact psl211_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. by rewrite exprn_gt0 // ltr0n. Qed.

(** The certificate's number is under two, the ceiling var_dist_le2 of
    lib/var_dist_supp.v gives for a variation distance, so the certificate is
    not vacuous. At about 4.5e-13 of that ceiling it is a cryptographic
    separation and not a weak one, as the proximity certificate of Kim's
    one-cut model is. *)
Lemma psl211_word_proximity_cert_eps_lt2 (R : realType) (idx : unit) :
  ipc_eps (psl211_word_proximity_cert R idx) < 2%:R :> R.
Proof.
have H1 : 2%:R^-40 <= (1:R)
  by rewrite invf_le1 ?psl211_pow2_40_gt0 ?psl211_pow2_40_ge1.
rewrite psl211_word_proximity_cert_epsE; lra.
Qed.

(******************************************************************************)
(*     The row                                                                *)
(******************************************************************************)

(** The word model certified by the proximity arm and published at 2^-40, the
    number the certificate proves. What a static coalition of at most five of
    the twelve seats is shown is that the joint law of its reading with the
    chirality is within that number, in the sum of absolute differences, of
    the product of the two marginals the all-decks execution has, where the
    reading and the chirality are independent outright; a distinguisher's
    advantage is therefore at most half of it. The claim is an average over
    the deck description and the cut and is not a statement at a fixed deck
    description: the reading of a coalition below the threshold is not
    constant in the run argument, which psl211_alldecks_constancy_false and
    psl211_dealt_constancy_false of psl211_spectral_constancy.v refute in both
    run modes, and those refutations stay true beside this row. Its transfer
    status is IdealFinite, an idealised shuffle being replaced here by a
    shuffle of 584 letters. *)
Definition psl211_row_word_proximity : PublishedRow :=
  psl211_alldecks_prefix
    sample  psl211_word_family
    certify IdealProximity psl211_word_proximity_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The arm the row carries, at every real field and index: the distance to a
    private ideal model, and not the distance between two readings of one
    model. This is the value a paper's table prints in the arm column for this
    row. *)
Lemma psl211_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_row_word_proximity)) R) :
  security_arm_of psl211_row_word_proximity R idx = IdealProximityArm.
Proof. exact: erefl. Qed.

(** The three coordinates the row publishes. The manifest of the tree carries
    no row at this model, an AnalysisPathRow recording the model family and
    this family being new, so the row below is the word model's own and not
    psl211_row_alldecks under another name. *)
Lemma psl211_row_word_proximity_publishedE :
  apr_completion (published_row psl211_row_word_proximity) = AnalysisBridged
  /\ apr_transfer (published_row psl211_row_word_proximity) = IdealFinite
  /\ apr_assumptions (published_row psl211_row_word_proximity)
     = BaselineClassicalOnly.
Proof. split; [exact: erefl | split; exact: erefl]. Qed.

(******************************************************************************)
(*     What the row states at this instance                                   *)
(******************************************************************************)

(** The row's security statement at the twelve-card chirality instance: at a
    static coalition of at most five of the twelve seats, the joint law of the
    executed coalition view and the chirality under the 584-letter word
    shuffle is within 2^-40, in the sum of absolute differences, of the
    product of the two marginals of the all-decks execution. The proof is the
    row's security projection applied, so the row and this statement are one
    theorem. *)
Theorem psl211_word_view_proximity (R : realType) (C : {set seatT})
    (HC : (#|C| <= 5)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R (instance_profile psl211_algebra)
                           (instance_exec psl211_alldecks_params)
                           (amf_sample psl211_word_family R tt) 0 C u,
                         psl211_alldecks_secret R u))
       (sa_sampleP (amf_sample psl211_word_family R tt)))
    ((fdistmap (@sa_coalition_view R (instance_profile psl211_algebra)
                  (instance_exec psl211_alldecks_params)
                  (psl211_alldecks_sample R) 0 C) (psl211_alldecksP R))
     `x (fdistmap (psl211_alldecks_secret R) (psl211_alldecksP R)))
  <= 2%:R^-40.
Proof. exact: (view_proximity_of psl211_row_word_proximity R tt C HC). Qed.
