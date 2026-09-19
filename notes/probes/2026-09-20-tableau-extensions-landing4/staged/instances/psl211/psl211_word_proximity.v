(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_word_proximity: the twelve-card word row through the proximity arm  *)
(*                                                                            *)
(* The word model psl211_word_family names and the all-decks model of         *)
(* psl211_models.v run one execution over one sample space and differ in the  *)
(* law of the cut alone. That is the shape the proximity arm compares, and    *)
(* the twelve-card chirality instance is the third carrier of that arm,       *)
(* beside Kim's one-cut five-card model and the eight-card orbit instance.    *)
(* The ideal is an execution whose own privacy is a theorem:                  *)
(* psl211_row_alldecks_tableau publishes it with the exact arm, and           *)
(* psl211_word_proximity_cert_idealE says that the model the certificate      *)
(* calls ideal and the model that row publishes are one term.                 *)
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
(* carrying a constant for this model to be read in one column with. The      *)
(* constancy field an input-indistinguishability certificate would need is    *)
(* refuted at the group-uniform ideal cut and at the 584-letter word cut law, *)
(* and psl211_alldecks_no_small_eps_cert excludes every                       *)
(* input-indistinguishability certificate whose shuffle bound is strictly     *)
(* below 1/1320. The larger bounds are left open, so no                       *)
(* input-indistinguishability sibling exists here to read this row in one     *)
(* column with and none is shown impossible.                                  *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, which is twice    *)
(* the total variation distance of the literature, so a distinguisher's       *)
(* advantage against the published row is at most half of 2^-40.              *)
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
(*   psl211_word_proximity_cert_secretE                                       *)
(*                              == the certificate's secret and the secret    *)
(*                                 its witness carries are one term           *)
(*   psl211_word_proximity_cert_secretTE                                      *)
(*                              == the carrier of that secret is bool         *)
(*   psl211_word_proximity_cert_epsE                                          *)
(*                              == the certificate's number in closed form    *)
(*   psl211_pow2_40_ge1         == two to the fortieth is at least one        *)
(*   psl211_pow2_40_gt0         == two to the fortieth is positive            *)
(*   psl211_word_law_le2        == the two models' laws are within the bound  *)
(*                                 every pair of laws on one sample space     *)
(*                                 meets                                      *)
(*   psl211_word_proximity_cert_eps_lt2                                       *)
(*                              == the certificate's number is below that     *)
(*                                 bound                                      *)
(*   psl211_row_word_proximity_armE                                           *)
(*                              == the row carries the proximity arm          *)
(*   psl211_row_word_proximity_rowE                                           *)
(*                              == the row publishes psl211_row_word          *)
(*   psl211_word_view_proximity == what the row states at this instance       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_instance pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_closure psl211_profile.
From pgg_smc Require Import psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_rows psl211_word_model.

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

(** At every coalition of the twelve seats, the joint law of
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
   same two projections, so var_dist_fdistmap_pair applies with no pointwise
   rewriting of either reader. *)
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
   close by exact: erefl in under 0.01 s. *)
Proof. split; exact: erefl. Qed.

(** The secret the certificate names and the secret its witness carries are
    one term, psl211_alldecks_secret. A proximity certificate whose two
    secrets differ compares a coalition's reading against a product taken in
    a different bit, so what a coalition is shown says nothing about the bit
    the arm's proposition names. *)
Lemma psl211_word_proximity_cert_secretE (R : realType) (idx : unit) :
  ipc_secret (psl211_word_proximity_cert R idx) = psl211_alldecks_secret R
  /\ ew_secret (ipc_witness (psl211_word_proximity_cert R idx))
     = psl211_alldecks_secret R.
Proof. split; exact: erefl. Qed.

(** The carrier of that secret is the two-element type of the chirality bit.
    At a one-point carrier the arm's proposition compares two readings and
    mentions no secret at all, the second factor of the product being a point
    mass, so the number would bound nothing about what a coalition learns of
    the bit. *)
Lemma psl211_word_proximity_cert_secretTE (R : realType) (idx : unit) :
  ew_secretT (ipc_witness (psl211_word_proximity_cert R idx)) = bool.
Proof. exact: erefl. Qed.

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

(** The two models' laws are within two of each other by the bound every
    pair of laws on one finite sample space meets, with no fact about the
    twelve-card instance and no fact about the 584-letter walk. A proximity
    certificate carrying two would be a certificate about nothing, which is
    why the number a row publishes is what a reader of the arm must read. *)
Lemma psl211_word_law_le2 (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R.
Proof. exact: var_dist_le2. Qed.

(** The same bound does not reach 2^-40. The rejection is a failure to unify
    the two numbers:

      The term "var_dist_le2 ?P ?Q" has type "is_true (var_dist ?P ?Q <= 2)"
      while it is expected to have type
       "is_true (var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2 ^- 40)".

    So the number psl211_word_lawE proves is carried by psl211_word_mixing and
    by nothing that holds of an arbitrary pair of laws. *)
Fail Definition psl211_word_law_tauto (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40
  := var_dist_le2 _ _.

(** The certificate's number is below two, the bound var_dist_le2 of
    lib/var_dist_supp.v gives for a variation distance. What this rules out
    is that bound's own tautology: psl211_word_law_le2 proves the distance
    at two with no fact about this instance and no fact about the walk, and
    the same term is rejected at 2^-40. The number is 2^-41 of that bound.
    The second shape a proximity certificate can be vacuous in is closed
    beside that rejection: psl211_word_proximity_cert_secretE and
    psl211_word_proximity_cert_secretTE give the certificate's secret and
    its witness's secret as one term at the carrier bool, and the ideal is
    refused as the model the certificate is about. *)
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
    description. That every coalition below the threshold reads an ideal cut
    by the same law at every run argument is false at each cut named here:
    psl211_alldecks_constancy_false refutes it at the group-uniform cut under
    the all-decks run, psl211_alldecks_constancy_false_word584 at every cut
    within eps of the 584-letter word law this row's model draws, once twice
    the sum of eps and 2^-40 stays below 1/660, and
    psl211_dealt_constancy_false at the group-uniform cut under the
    dealer-dealt run, a different execution. Each is witnessed at a coalition
    of three seats, and all three stay true beside this row. Its transfer
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

(** The manifest row the program publishes: the row of the twelve-card
    chirality instance at the 584-letter word model. Its five coordinates are
    the observed execution the program runs on, the completion level the
    publish terminal reaches, the model family the sample step named, and the
    two statuses the terminal was given, so the manifest's description of this
    path is read off the program and not written beside it. It differs from
    psl211_row_alldecks in the model family and in the transfer status, the
    all-decks row comparing no idealized model where this one replaces an
    idealized shuffle by a finite word. *)
Lemma psl211_row_word_proximity_rowE :
  published_row psl211_row_word_proximity = psl211_row_word.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     What the row states at this instance                                   *)
(******************************************************************************)

(** The row's security statement at the twelve-card chirality instance: at a
    static coalition of at most five of the twelve seats, the joint law of the
    executed coalition reading and the chirality under the 584-letter word
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

(******************************************************************************)
(*     Which ideal the arm refuses                                            *)
(******************************************************************************)

(** The eight-card orbit instance's exact family cannot be the ideal of a
    twelve-card word row. A certificate's ideal is a sample adapter over the
    row's own execution, and the two instances run different executions, so
    the field is rejected at its type and no distance is reached. The
    rejection is a failure to unify the two executions:

      The term "amf_sample pgl27_exact_family R tt" has type
       "SampleAdapter R (OE.oe_execution pgl27_exec.pgl27_observed)"
      while it is expected to have type
       "SampleAdapter R (instance_exec psl211_alldecks_params)".
*)
Fail Definition psl211_word_proximity_cert_pgl27_ideal (R : realType)
    (idx : unit)
  : IdealProximityCert (amf_sample psl211_word_family R idx) :=
  @MkIdealProximityCert R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_word_family R idx)
    (amf_sample pgl27_exact_family R tt)
    (psl211_exact_witness R idx)
    (psl211_alldecks_secret R)
    (2%:R^-40)
    (fun C HC => @psl211_word_proximity_close R C HC).

(** The certificate's ideal is not the word model it is about. A certificate
    naming its own model as the ideal holds its distance field at zero, the
    two sides of that field being one term, so the number it publishes bounds
    a distance from the model to itself. The rejection is a failure to unify
    the two models:

      The term "erefl" has type
       "ipc_ideal (psl211_word_proximity_cert R idx) =
        ipc_ideal (psl211_word_proximity_cert R idx)"
      while it is expected to have type
       "ipc_ideal (psl211_word_proximity_cert R idx) =
        amf_sample psl211_word_family R idx".
*)
Fail Definition psl211_word_proximity_cert_ideal_self (R : realType)
    (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample psl211_word_family R idx := erefl.
