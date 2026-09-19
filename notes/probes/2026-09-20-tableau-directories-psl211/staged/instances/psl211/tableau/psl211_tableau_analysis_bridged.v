(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_analysis_bridged: the twelve-card instance at               *)
(*                                  AnalysisBridged                           *)
(*                                                                            *)
(* The AnalysisBridged level adjoins one security payload per real field and  *)
(* per index of the model, and the proposition it carries is that payload's   *)
(* arm on top of everything the levels below proved. This is the level at     *)
(* which a row says something about a coalition, and the arm decides what it  *)
(* says: the exact arm asserts independence, and the proximity arm a distance *)
(* to a model whose own privacy is a theorem.                                 *)
(*                                                                            *)
(* Six is the privacy threshold the derived profile declares, so every        *)
(* statement here is about a coalition of at most five of the twelve seats,   *)
(* each seat reading the card at its own position. The deck description, the  *)
(* whole run argument, is a chirality bit with a deal, and it is drawn        *)
(* uniformly: one of the two chiralities, one of the 132 block lines of that  *)
(* chirality's Steiner system for the six heart positions, one of the 720     *)
(* labellings of the heart codes and one of the 720 labellings of the club    *)
(* codes.                                                                     *)
(*                                                                            *)
(* Two rows are published here and they part at the model. Over the uniform   *)
(* cut, what a coalition is shown is independent of the chirality outright,   *)
(* at every real field and with no number in the claim; that is the exact     *)
(* arm, and the instance owes it one witness. Over the 584-letter word cut,   *)
(* what a coalition is shown is within 2^-40, in the sum of absolute          *)
(* differences, of what the uniform-cut execution shows it, so a              *)
(* distinguisher's advantage is at most 2^-41; that is the proximity arm, and *)
(* the instance owes it a certificate whose ideal is the first row's own      *)
(* model. Both numbers are the certificate's, not a constant read from        *)
(* elsewhere.                                                                 *)
(*                                                                            *)
(* No input-indistinguishability row is published over either model. A        *)
(* certificate of that arm carries a constancy field, and                     *)
(* instances/psl211/psl211_reading_constancy.v restates that field as         *)
(* coalition_reading_constancy and refutes it in both run modes.              *)
(*                                                                            *)
(* The mathematics reaches these rows through the payloads alone, and through *)
(* three named facts: psl211_alldecks_exact_viewE and                         *)
(* psl211_alldecks_view_indep of psl211_models.v, and                         *)
(* psl211_word_proximity_close of psl211_word_proximity.v. No other security  *)
(* statement of the instance enters either row.                               *)
(*                                                                            *)
(* The phase files are required and imported one by one and export nothing of *)
(* each other, so a file outside this directory names the phase that declares *)
(* the name it wants: this file for a payload, a published row or a row       *)
(* equation, psl211_tableau_sampled for a named model, psl211_tableau_observed*)
(* for a run prefix, and psl211_tableau_executable for a parameter record.    *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_exact_witness    == the exact arm's witness at every field and    *)
(*                              index                                         *)
(*   psl211_row_alldecks_tableau                                              *)
(*                           == the all-decks row as a program                *)
(*   psl211_word_proximity_cert                                               *)
(*                           == the word model's proximity certificate        *)
(*   psl211_row_word_proximity == the proximity claim, published at 2^-40     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_row_alldecks_rowE == the program publishes the manifest's row     *)
(*   psl211_row_alldecks_armE == the row carries the exact arm                *)
(*   psl211_row_alldecks_sampledE                                             *)
(*                           == the row is the named Sampled value with the   *)
(*                              payload and the terminal adjoined             *)
(*   psl211_alldecks_view_secrecy                                             *)
(*                           == the exact arm's four conjuncts at this        *)
(*                              instance                                      *)
(*   psl211_word_proximity_cert_idealE                                        *)
(*                           == the certificate's ideal is the all-decks      *)
(*                              row's model, and the port built from its      *)
(*                              witness is that row's port                    *)
(*   psl211_word_proximity_cert_secretE                                       *)
(*                           == the certificate's secret and the secret its   *)
(*                              witness carries are one term                  *)
(*   psl211_word_proximity_cert_secretTE                                      *)
(*                           == the carrier of that secret is bool            *)
(*   psl211_word_proximity_cert_epsE                                          *)
(*                           == the certificate's number is 2^-40             *)
(*   psl211_word_proximity_cert_eps_lt2                                       *)
(*                           == the certificate's number is below the bound   *)
(*                              two var_dist_le2 gives                        *)
(*   psl211_row_word_proximity_armE                                           *)
(*                           == the row carries the proximity arm             *)
(*   psl211_row_word_proximity_rowE                                           *)
(*                           == the row publishes psl211_row_word             *)
(*   psl211_row_word_proximity_sampledE                                       *)
(*                           == that row too is its named Sampled value with  *)
(*                              the payload and the terminal adjoined         *)
(*   psl211_word_view_proximity                                               *)
(*                           == the proximity row's security statement, at    *)
(*                              2^-40                                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_smc Require Import smc_interpreter pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_closure.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_word_model psl211_word_proximity.
From pgg_smc Require Import psl211_tableau_observed psl211_tableau_sampled.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(** cardT — a card of the twelve-card deck, the value a seat reads. *)
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).

(******************************************************************************)
(*     The exact arm's witness                                                *)
(******************************************************************************)

(** psl211_exact_witness — the exact arm's witness: the chirality as a random
    variable on the all-decks sample space, and, at every coalition of fewer
    than six of the twelve seats, the independence of that coalition's reading
    from it. The independence is psl211_alldecks_view_indep, which is the
    equality of the two chiralities' deal counts read as a privacy statement,
    and it is exact: a uniform deck description and a uniform cut leave the
    reading carrying no information about the chirality at all, not a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is the whole of what this instance owes the exact
    arm. *)
Definition psl211_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample psl211_exact_family R idx) :=
  @MkExactWitness R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_exact_family R idx) bool (psl211_alldecks_secret R)
    (fun C HC =>
       let H5 : (#|C| <= 5)%N := HC in
       (eq_ind_r
          (fun v => psl211_alldecksP R |= v _|_ psl211_alldecks_secret R)
          (psl211_alldecks_view_indep R H5)
          (psl211_alldecks_exact_viewE C))).

(******************************************************************************)
(*     The row program                                                        *)
(******************************************************************************)

(** psl211_row_alldecks_tableau — the published row. What the finished row
    carries about a coalition of fewer than six of the twelve seats is
    independence of the chirality, at every real field, with no numeric bound
    in it; the independence is exact, not small, because both the deck
    description and the cut are drawn uniformly and the two Steiner systems
    are met in the same block patterns by every set of at most five positions.
    Its last line publishes a row whose transfer status is StaticExecutedOnly,
    because the cut this model draws is already the uniform one and no
    idealized shuffle is being compared with a real one. *)
Definition psl211_row_alldecks_tableau : PublishedRow :=
  psl211_alldecks_prefix
    sample  psl211_exact_family
    certify ExactIndependence psl211_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** psl211_row_alldecks_rowE — the row this program publishes is the
    manifest's own row for this instance. Conversion decides it, so the
    descriptive row and the theorem proved about it cannot drift apart. *)
Lemma psl211_row_alldecks_rowE :
  published_row psl211_row_alldecks_tableau = psl211_row_alldecks.
Proof. by []. Qed.

(** The arm this row carries, at every real field and index: independence of
    the coalition's view from the chirality, and not a distance between two
    readings. This is the value a paper's table prints in the arm column for
    this row, settled by the certify statement the program wrote. *)
Lemma psl211_row_alldecks_armE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_row_alldecks_tableau)) R) :
  security_arm_of psl211_row_alldecks_tableau R idx = ExactIndependenceArm.
Proof. by []. Qed.

(** psl211_row_alldecks_sampledE — the row is the named Sampled value with
    the payload and the terminal adjoined. The program above writes the run
    and the model in one chain and the Sampled file names the value they
    build, so this equation is what keeps the two spellings of the row's
    prefix from parting. *)
Lemma psl211_row_alldecks_sampledE :
  (psl211_exact_sampled
     certify ExactIndependence psl211_exact_witness
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = psl211_row_alldecks_tableau.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The exact arm's four conjuncts at this instance                        *)
(******************************************************************************)

(** psl211_alldecks_view_secrecy — the row's view secrecy at this instance: at
    fewer than six colluding seats the executed coalition reading is
    independent of the chirality, carries zero mutual information with it,
    leaves the chirality's entropy unchanged under conditioning, and stays
    independent of it under every deterministic function of the seat-to-card
    map. The four conjuncts are the whole content of the exact arm here; the
    proof is the row's security projection applied, so a reader who wants the
    information-theoretic reading of the row needs no further derivation. *)
Theorem psl211_alldecks_view_secrecy (R : realType) (C : {set seatT})
    (HC : (#|C| < 6)%N) :
  [/\ psl211_alldecksP R
      |= (@sa_coalition_view R (instance_profile psl211_algebra)
            (instance_exec psl211_alldecks_params)
            (psl211_alldecks_sample R) 0 C) _|_ (psl211_alldecks_secret R),
      `I( psl211_alldecks_secret R ;
          @sa_coalition_view R (instance_profile psl211_algebra)
            (instance_exec psl211_alldecks_params)
            (psl211_alldecks_sample R) 0 C ) = 0,
      `H( psl211_alldecks_secret R |
          @sa_coalition_view R (instance_profile psl211_algebra)
            (instance_exec psl211_alldecks_params)
            (psl211_alldecks_sample R) 0 C )
      = `H `p_ (psl211_alldecks_secret R)
    & forall (W : finType) (h : {ffun seatT -> cardT} -> W),
        psl211_alldecksP R
        |= (h `o (@sa_coalition_view R (instance_profile psl211_algebra)
                    (instance_exec psl211_alldecks_params)
                    (psl211_alldecks_sample R) 0 C))
           _|_ (psl211_alldecks_secret R)].
Proof. exact: (view_secrecy_of psl211_row_alldecks_tableau R tt C HC). Qed.

(******************************************************************************)
(*     The certificate, and its ideal                                         *)
(******************************************************************************)

(** The proximity certificate of the PSL(2,11) word row. Its five fields are
    the all-decks model as the ideal; that model's exact witness, which is
    what makes the ideal an execution whose coalitions of at most five seats
    learn nothing at all; the chirality, which is the secret of the two models
    as one term; the word walk's number 2^-40; and psl211_word_proximity_close
    as the distance field, which bounds by that number the distance between
    the two models' joint laws of a coalition's reading with the chirality.
    The ideal, its witness and the secret are terms the all-decks row
    publishes, and the number is this certificate's own. *)
Definition psl211_word_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample psl211_word_family R idx) :=
  @MkIdealProximityCert R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_word_family R idx)
    (amf_sample psl211_exact_family R idx)
    (psl211_exact_witness R idx)
    (psl211_alldecks_secret R)
    (2%:R^-40)
    (fun C HC => @psl211_word_proximity_close R C HC).

(** The model the certificate calls ideal is the model the published
    all-decks row carries, and the port built from the witness the certificate
    carries is that row's port. Conversion decides both, so the ideal a word
    row is measured against is the model the all-decks row publishes and not a
    second description of it. *)
Lemma psl211_word_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample (ab_f (published_at psl211_row_alldecks_tableau)) R idx
  /\ ExactIndependence (ipc_witness (psl211_word_proximity_cert R idx))
     = ab_port (published_at psl211_row_alldecks_tableau) R idx.
Proof.
(* exact: erefl and not by []: done does not return on an equation between two
   rows' coordinates, where exact: erefl decides it at once. *)
split; exact: erefl.
Qed.

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
    the bit. The secret is also the one the protocol reconstructs:
    psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v
    reads it as the value the run recovers, at every sample point. *)
Lemma psl211_word_proximity_cert_secretTE (R : realType) (idx : unit) :
  ew_secretT (ipc_witness (psl211_word_proximity_cert R idx)) = bool.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

(** The certificate's number is the 584-letter walk's number, 2^-40. *)
Lemma psl211_word_proximity_cert_epsE (R : realType) (idx : unit) :
  ipc_eps (psl211_word_proximity_cert R idx) = 2%:R^-40 :> R.
Proof. exact: erefl. Qed.

(** The certificate's number is below two, the bound var_dist_le2 of
    lib/var_dist_supp.v gives for a sum of absolute differences. What this
    rules out is that bound's own tautology: psl211_word_law_le2 proves the
    distance at two with no fact about this instance and no fact about the
    walk, and the same term is rejected at 2^-40. The number is 2^-41 of that
    bound. The second shape a proximity certificate can be vacuous in is
    closed beside that rejection: psl211_word_proximity_cert_secretE and
    psl211_word_proximity_cert_secretTE give the certificate's secret and its
    witness's secret as one term at the carrier bool, and the ideal is refused
    as the model the certificate is about. *)
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
    advantage is therefore at most 2^-41. The claim is an average over
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
    status is IdealFinite: the cut is a shuffle of 584 letters where
    the model of psl211_row_alldecks draws it uniformly from the group. *)
Definition psl211_row_word_proximity : PublishedRow :=
  psl211_alldecks_prefix
    sample  psl211_word_family
    certify IdealProximity psl211_word_proximity_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The arm the row carries, at every real field and index: the distance to a
    private ideal model, and not the distance between two readings of one
    model. *)
Lemma psl211_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_row_word_proximity)) R) :
  security_arm_of psl211_row_word_proximity R idx = IdealProximityArm.
Proof. exact: erefl. Qed.

(** The manifest row the program publishes: the row of the twelve-card
    chirality instance at the 584-letter word model. Its five coordinates are
    the observed execution the program runs on, the completion level the
    publish terminal reaches, the model family the sample step named, and the
    two statuses the terminal was given. The manifest writes those coordinates
    in the facade's vocabulary and the program in this file's, and conversion
    decides the equation, so the manifest's row for this path is a claim this
    equation discharges rather than a table maintained beside the program. It
    differs from psl211_row_alldecks in the model family and in the transfer
    status, the all-decks row comparing no idealized model where this one
    replaces an idealized shuffle by a finite word. *)
Lemma psl211_row_word_proximity_rowE :
  published_row psl211_row_word_proximity = psl211_row_word.
Proof. exact: erefl. Qed.

(** psl211_row_word_proximity_sampledE — the proximity row too is its named
    Sampled value with the payload and the terminal adjoined, so the two rows
    of this instance are each written once above the model they branch at. *)
Lemma psl211_row_word_proximity_sampledE :
  (psl211_word_sampled
     certify IdealProximity psl211_word_proximity_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = psl211_row_word_proximity.
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
