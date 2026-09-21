(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_analysis_bridged: the twelve-card instance at               *)
(*                                  AnalysisBridged                           *)
(*                                                                            *)
(* The AnalysisBridged level adjoins one security payload per real field and  *)
(* per index of the model, and the proposition it carries is the one that     *)
(* payload proves, on top of everything the levels below proved. This is the  *)
(* level at which a program says something about a coalition, and which       *)
(* security property the evidence proves is what it says: the                 *)
(* exact-independence proposition asserts independence, and the               *)
(* ideal-proximity proposition a distance to a model whose own privacy is a   *)
(* theorem.                                                                   *)
(*                                                                            *)
(* Six is the threshold the derived profile declares, so every statement here *)
(* that quantifies over a coalition quantifies over at most five of the       *)
(* twelve seats, each seat reading the card at the cut image of its own       *)
(* position. The deck description, the whole run argument, is a chirality bit *)
(* with a deal, and it is drawn uniformly: one of the two chiralities, one of *)
(* the 132 block lines of that chirality's Steiner system for the six heart   *)
(* positions, one of the 720 labellings of the heart codes and one of the 720 *)
(* labellings of the club codes.                                              *)
(*                                                                            *)
(* Two programs with security evidence are published here and they part at    *)
(* the model. Over the uniform cut, what a coalition is shown is independent  *)
(* of the chirality outright, at every real field and with no number in the   *)
(* claim; that is exact independence, and the instance supplies one witness   *)
(* for it. Over the 584-letter word cut, what a coalition is shown is within  *)
(* 2^-40, in the sum of absolute differences, of what the uniform-cut         *)
(* execution shows it, so a distinguisher's advantage is at most 2^-41; that  *)
(* is ideal proximity, and the instance supplies a certificate whose ideal is *)
(* the first program's own model. Both numbers are the certificate's, not a   *)
(* constant read from elsewhere.                                              *)
(*                                                                            *)
(* No input-indistinguishability program is published over either model. An   *)
(* input-indistinguishability certificate carries a constancy field, and      *)
(* instances/psl211/psl211_reading_constancy.v restates that field as         *)
(* coalition_reading_constancy and refutes it in both run modes. A third      *)
(* program over the all-decks model publishes that reason rather than         *)
(* describing it: psl211_alldecks_obstruction_published carries the           *)
(* obstruction that the model is input distinguishable at 1/660, from which   *)
(* the number bound and the exclusion of certificates with a close ideal both *)
(* follow. It certifies no security property, and the path it publishes is    *)
(* the manifest's psl211_alldecks_obstruction_path, which records             *)
(* NegativeTransfer where psl211_alldecks_path, over the same model and the   *)
(* same run, records StaticExecutedOnly.                                      *)
(*                                                                            *)
(* The mathematics reaches these programs through the payloads alone, and     *)
(* through three named facts: psl211_alldecks_exact_viewE and                 *)
(* psl211_alldecks_view_indep of psl211_models.v, and                         *)
(* psl211_word_proximity_close of psl211_word_proximity.v. No other security  *)
(* statement of the instance enters either program.                           *)
(*                                                                            *)
(* The phase files are required and imported one by one and export nothing of *)
(* each other, so a file outside this directory names the phase that declares *)
(* the name it wants: this file for a payload, a published program or a path  *)
(* equation, psl211_tableau_sampled for a named model,                        *)
(* psl211_tableau_observed for a run prefix, and psl211_tableau_executable    *)
(* for a parameter record.                                                    *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_exact_witness    == the exact-independence witness at every field *)
(*                              and index                                     *)
(*   psl211_alldecks_published                                                *)
(*                           == the all-decks path as a program               *)
(*   psl211_word_proximity_cert                                               *)
(*                           == the word model's proximity certificate        *)
(*   psl211_word_proximity_published                                          *)
(*                           == the word path as a program, published at      *)
(*                              2^-40                                         *)
(*   psl211_alldecks_obstruction                                              *)
(*                           == the obstruction at every field and index      *)
(*   psl211_alldecks_obstruction_pf                                           *)
(*                           == its proof there                               *)
(*   psl211_alldecks_obstruction_published                                    *)
(*                           == the all-decks path as a program publishing    *)
(*                              that obstruction                              *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_alldecks_published_pathE                                          *)
(*                           == the program publishes the manifest's path     *)
(*   psl211_alldecks_published_propertyE                                      *)
(*                           == the program's security property is exact      *)
(*                              independence                                  *)
(*   psl211_alldecks_published_sampledE                                       *)
(*                           == the program is the named Sampled value with   *)
(*                              the payload and the terminal adjoined         *)
(*   psl211_alldecks_view_secrecy                                             *)
(*                           == the exact-independence proposition's four     *)
(*                              conjuncts at this instance                    *)
(*   psl211_word_proximity_cert_idealE                                        *)
(*                           == the certificate's ideal is the all-decks      *)
(*                              program's model, and the evidence built from  *)
(*                              its witness is that program's evidence        *)
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
(*   psl211_word_proximity_published_propertyE                                *)
(*                           == the program's security property is ideal      *)
(*                              proximity                                     *)
(*   psl211_word_proximity_published_pathE                                    *)
(*                           == the program publishes psl211_word_path        *)
(*   psl211_word_proximity_published_sampledE                                 *)
(*                           == that program too is its named Sampled value   *)
(*                              with the payload and the terminal adjoined    *)
(*   psl211_word_view_proximity                                               *)
(*                           == the proximity program's security statement,   *)
(*                              at 2^-40                                      *)
(*   psl211_alldecks_obstruction_gt0                                          *)
(*                           == the number the obstruction carries is above   *)
(*                              zero                                          *)
(*   psl211_alldecks_obstruction_published_pathE                              *)
(*                           == the obstruction program publishes the         *)
(*                              manifest's twelfth path                       *)
(*   psl211_alldecks_published_input_distinguishability                       *)
(*                           == the obstruction program's statement: the      *)
(*                              all-decks model is input distinguishable at   *)
(*                              1/660                                         *)
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
From pgg_smc Require Import psl211_reading_constancy.
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
(*     The exact-independence witness                                         *)
(******************************************************************************)

(** psl211_exact_witness — the exact-independence witness: the chirality as a
    random variable on the all-decks sample space, and, at every coalition of
    fewer than six of the twelve seats, the independence of that coalition's
    reading from it. The independence is psl211_alldecks_view_indep, which is
    the equality of the two chiralities' deal counts read as a privacy
    statement, and it is exact: a uniform deck description and a uniform cut
    leave the reading carrying no information about the chirality at all, not a
    small amount. The framework derives the zero mutual information, the
    unchanged conditional entropy and the closure under post-processing from
    this one field, so the witness is all that certifying exact independence
    requires of this instance. *)
Definition psl211_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample psl211_exact_family R idx)
      (coalition_endpoint_reading psl211_algebra) :=
  @MkExactWitness R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_exact_family R idx) (coalition_endpoint_reading psl211_algebra) bool (psl211_alldecks_secret R)
    (fun C HC =>
       let H5 : (#|C| <= 5)%N := HC in
       (eq_ind_r
          (fun v => psl211_alldecksP R |= v _|_ psl211_alldecks_secret R)
          (psl211_alldecks_view_indep R H5)
          (psl211_alldecks_exact_viewE C))).

(******************************************************************************)
(*     The all-decks program                                                  *)
(******************************************************************************)

(** psl211_alldecks_published — the published program. What the finished
    program carries about a coalition of fewer than six of the twelve seats is
    independence of the chirality, at every real field, with no numeric bound in
    it; the independence is exact, not small, because both the deck description
    and the cut are drawn uniformly and the two Steiner systems are met in the
    same block patterns by every set of at most five positions. Its last line
    publishes a path whose transfer status is StaticExecutedOnly, because the
    cut this model draws is already the uniform one and no idealized shuffle is
    being compared with a real one. *)
Definition psl211_alldecks_published : Published :=
  psl211_alldecks_prefix
    sample  psl211_exact_family
    certify ExactIndependence psl211_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** psl211_alldecks_published_pathE — the path this program publishes is the
    manifest's own path for this instance. Conversion decides it, so the
    descriptive path and the theorem proved about it cannot drift apart. *)
Lemma psl211_alldecks_published_pathE :
  published_path psl211_alldecks_published = psl211_alldecks_path.
Proof. by []. Qed.

(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the
    chirality, and not a distance between two readings. The certify statement
    the program wrote settles which property that is. *)
Lemma psl211_alldecks_published_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_alldecks_published)) R) :
  security_property_of psl211_alldecks_published R idx
  = ExactIndependenceProperty.
Proof. by []. Qed.

(** psl211_alldecks_published_sampledE — the program is the named Sampled
    value with the payload and the terminal adjoined. The program above writes
    the run and the model in one chain and the Sampled file names the value they
    build, so this equation is what keeps the two spellings of the program's
    prefix from parting. *)
Lemma psl211_alldecks_published_sampledE :
  (psl211_exact_sampled
     certify ExactIndependence psl211_exact_witness
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = psl211_alldecks_published.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The exact-independence proposition's four conjuncts at this instance   *)
(******************************************************************************)

(** psl211_alldecks_view_secrecy — the program's view secrecy at this
    instance: at fewer than six colluding seats the executed coalition reading
    is independent of the chirality, carries zero mutual information with it,
    leaves the chirality's entropy unchanged under conditioning, and stays
    independent of it under every deterministic function of the seat-to-card
    map. The four conjuncts are the whole content of the exact-independence
    proposition here; the proof is the program's security projection applied, so
    a reader who wants the information-theoretic reading of the program needs no
    further derivation. *)
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
Proof. exact: (view_secrecy_of psl211_alldecks_published R tt C HC). Qed.

(******************************************************************************)
(*     The certificate, and its ideal                                         *)
(******************************************************************************)

(** The proximity certificate of the PSL(2,11) word program. Its five fields are
    the all-decks model as the ideal; that model's exact witness, which is what
    makes the ideal an execution whose coalitions of at most five seats learn
    nothing at all; the chirality, which is the secret of the two models as one
    term; the word walk's number 2^-40; and psl211_word_proximity_close as the
    distance field, which bounds by that number the distance between the two
    models' joint laws of a coalition's reading with the chirality. The ideal,
    its witness and the secret are terms the all-decks program publishes, and
    the number is this certificate's own. *)
Definition psl211_word_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample psl211_word_family R idx)
      (coalition_endpoint_reading psl211_algebra) :=
  @MkIdealProximityCert R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_word_family R idx) (coalition_endpoint_reading psl211_algebra)
    (amf_sample psl211_exact_family R idx)
    (psl211_exact_witness R idx)
    (psl211_alldecks_secret R)
    (2%:R^-40)
    (fun C HC => @psl211_word_proximity_close R C HC).

(** The model the certificate calls ideal is the model the published all-decks
    program carries, and the evidence built from the witness the certificate
    carries is that program's evidence. Conversion decides both, so the ideal a
    word program is measured against is the model the all-decks program
    publishes and not a second description of it. *)
Lemma psl211_word_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample (ab_f (published_at psl211_alldecks_published)) R idx
  /\ ExactIndependence (ipc_witness (psl211_word_proximity_cert R idx))
     = ab_evidence (published_at psl211_alldecks_published) R idx.
Proof.
(* exact: erefl and not by []: done does not return on an equation between two
   programs' coordinates, where exact: erefl decides it at once. *)
split; exact: erefl.
Qed.

(** The secret the certificate names and the secret its witness carries are
    one term, psl211_alldecks_secret. Where a certificate's two secrets differ,
    the ideal-proximity proposition compares a coalition's reading against a
    product taken in a different bit, so what a coalition is shown says nothing
    about the bit the ideal-proximity proposition names. *)
Lemma psl211_word_proximity_cert_secretE (R : realType) (idx : unit) :
  ipc_secret (psl211_word_proximity_cert R idx) = psl211_alldecks_secret R
  /\ ew_secret (ipc_witness (psl211_word_proximity_cert R idx))
     = psl211_alldecks_secret R.
Proof. split; exact: erefl. Qed.

(** The carrier of that secret is the two-element type of the chirality bit.
    At a one-point carrier the ideal-proximity proposition compares two
    readings and mentions no secret at all, the second factor of the product
    being a point mass, so the number would bound nothing about what a
    coalition learns of the bit. The secret is also the one the protocol
    reconstructs: psl211_alldecks_secret_expectedE of
    instances/psl211/psl211_models.v reads it as the value the run recovers,
    at every sample point. *)
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
(*     The program                                                            *)
(******************************************************************************)

(** The word model certified for ideal proximity and published at 2^-40, the
    number the certificate carries. What a static coalition of at most five of
    the twelve seats is shown is that the joint law of its reading with the
    chirality is within that number, in the sum of absolute differences, of the
    product of the two marginals the all-decks execution has, where the reading
    and the chirality are independent outright; a distinguisher's advantage is
    therefore at most 2^-41. The claim is an average over the deck description
    and the cut and is not a statement at a fixed deck description. That every
    coalition below the threshold reads an ideal cut by the same law at every
    run argument is false at each cut named here:
    psl211_alldecks_constancy_false refutes it at the group-uniform cut under
    the all-decks run, psl211_alldecks_constancy_false_word584 at every cut
    within eps of the 584-letter word law this program's model draws, once twice
    the sum of eps and 2^-40 stays below 1/660, and psl211_dealt_constancy_false
    at the group-uniform cut under the dealer-dealt run, a different execution.
    Each is witnessed at a coalition of three seats, and all three stay true
    beside this program. Its transfer status is IdealFinite: the cut is a
    shuffle of 584 letters where the model of psl211_alldecks_path draws it
    uniformly from the group. *)
Definition psl211_word_proximity_published : Published :=
  psl211_alldecks_prefix
    sample  psl211_word_family
    certify IdealProximity psl211_word_proximity_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The security property this program carries, at every real field and index,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two readings of one model. *)
Lemma psl211_word_proximity_published_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_word_proximity_published)) R) :
  security_property_of psl211_word_proximity_published R idx
  = IdealProximityProperty.
Proof. exact: erefl. Qed.

(** The manifest path the program publishes: the path of the twelve-card
    chirality instance at the 584-letter word model. Its five coordinates are
    the observed execution the program runs on, the completion level the publish
    terminal reaches, the model family the sample step named, and the two
    statuses the terminal was given. The manifest writes those coordinates in
    the facade's vocabulary and the program in this file's, and conversion
    decides the equation, so the manifest's path for this program is a claim
    this equation discharges rather than a table maintained beside the program.
    It differs from psl211_alldecks_path in the model family and in the transfer
    status, the all-decks path comparing no idealized model where this one
    replaces an idealized shuffle by a finite word. *)
Lemma psl211_word_proximity_published_pathE :
  published_path psl211_word_proximity_published = psl211_word_path.
Proof. exact: erefl. Qed.

(** psl211_word_proximity_published_sampledE — the proximity program too is
    its named Sampled value with the payload and the terminal adjoined, so the
    two programs with security evidence are each written once above the model
    they branch at. *)
Lemma psl211_word_proximity_published_sampledE :
  (psl211_word_sampled
     certify IdealProximity psl211_word_proximity_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = psl211_word_proximity_published.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     What the program states at this instance                               *)
(******************************************************************************)

(** The program's security statement at the twelve-card chirality instance: at a
    static coalition of at most five of the twelve seats, the joint law of the
    executed coalition reading and the chirality under the 584-letter word
    shuffle is within 2^-40, in the sum of absolute differences, of the product
    of the two marginals of the all-decks execution. The proof is the program's
    security projection applied, so the program and this statement are one
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
Proof.
exact: (view_proximity_of psl211_word_proximity_published R tt C HC).
Qed.

(******************************************************************************)
(*     The obstruction the all-decks model publishes                          *)
(******************************************************************************)

(** psl211_alldecks_obstruction — the obstruction, at every real field and at
    the one index of the all-decks family: the model is input distinguishable
    at 1/660, the reciprocal of the order of the shuffle group. *)
Definition psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled) :=
  fun (R : realType) (idx : unit) =>
    @InputDistinguishabilityObstruction R psl211_algebra
      psl211_alldecks_params (amf_sample psl211_exact_family R idx)
      (coalition_endpoint_reading psl211_algebra)
      ((#|pgg_G psl211_M|%:R)^-1).

(** psl211_alldecks_obstruction_gt0 — the number the obstruction carries is
    above zero, the shuffle group being non-empty. It is the first half of
    what the framework's proposition asks of a published member: at a number
    at or below zero the distance inequality is free and the member would
    compare nothing. *)
Lemma psl211_alldecks_obstruction_gt0 (R : realType) :
  0 < (#|pgg_G psl211_M|%:R)^-1 :> R.
Proof. by rewrite invr_gt0 ltr0n; exact: psl211_G_pos. Qed.

(** psl211_alldecks_obstruction_pf — its proof at every field and index: the
    number is above zero, and the model is input distinguishable at it by
    psl211_alldecks_input_distinguishability at the model the family returns
    there. *)
Definition psl211_alldecks_obstruction_pf
  : ObstructionPayloadProp psl211_alldecks_obstruction :=
  fun (R : realType) (_ : unit) =>
    conj (psl211_alldecks_obstruction_gt0 R)
         (psl211_alldecks_input_distinguishability R).

(** psl211_alldecks_obstruction_published — the all-decks run, the exact model
    and the obstruction, published. What the value carries about the model is
    that three of the twelve seats read the two chiralities of the deal
    psl211_perdeck_deal at least 1/660 apart under the model's own cut law, so
    a distinguisher told to compare those two run arguments has advantage at
    least 1/1320 there, the sum of absolute differences being twice the total
    variation distance of the literature. It certifies no security property:
    its data carries no SecurityEvidence, and every reader of
    manifest/pgg_tableau.v that names one takes a PublishedAt, a different
    inductive type.

    What it refutes. Every number at which an input-indistinguishability
    program over this model states its proposition is at least 1/660, whatever
    the certificate, by psl211_alldecks_indistinguishability_number_ge.
    Through the general form of the tail lemma,
    indistinguishability_prop_of_ideal_close, it also rules out every
    certificate whose ideal cut sits within eps of this model's own cut law
    once eps added to itself stays below 1/660, which is
    no_indistinguishability_cert_ideal_close_of_input_distinguishability at
    this model. The tree's psl211_alldecks_no_small_eps_cert is the companion
    exclusion on the other coordinate: it constrains a certificate's own
    marginal bound rather than where its ideal sits, and it follows by the
    same route at the certificate's own number.

    Why it does not conflict with psl211_alldecks_published. The two are facts
    about one model under different quantifiers over the run argument. Exact
    independence is stated with the deck description drawn uniformly, and it
    says that a coalition of at most five of the twelve seats then learns
    nothing about the chirality, exactly. The obstruction fixes two run
    arguments and compares the readings at those two values. A second and
    separate fact is that the chirality reindexes the laid deck.

    The path. All five coordinates are honest. The level is AnalysisBridged
    because the manifest's own definition of that level admits a limitation
    theorem about the same distribution and the same observer, and this is one;
    the transfer status is NegativeTransfer because that status is defined as a
    theorem transporting an obstruction to the path's observer, and the value's
    own proposition is that theorem. The path this program publishes is the
    manifest's twelfth, psl211_alldecks_obstruction_path, whose capability line
    carries the label input distinguishability. It is not a second description
    of psl211_alldecks_path: the two agree on the observed execution, the
    level, the model family and the assumption status and differ in the
    transfer status, and two paths over one model that differ in a status are
    two descriptions of different theorems. *)
Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_pf BaselineClassicalOnly.

(** psl211_alldecks_obstruction_published_pathE — the path this program
    publishes is the manifest's twelfth path for this instance. Conversion
    decides it, so the descriptive path and the theorem proved about it cannot
    drift apart, as at the instance's two paths with security evidence. *)
Lemma psl211_alldecks_obstruction_published_pathE :
  published_obstruction_path psl211_alldecks_obstruction_published
  = psl211_alldecks_obstruction_path.
Proof. exact: erefl. Qed.

(** psl211_alldecks_published_input_distinguishability — the program's reader
    gives the obstruction back, at every real field, and this is its second
    conjunct: the all-decks model is input distinguishable at 1/660. The first
    conjunct is that 1/660 is above zero, which is what makes the second a
    comparison. The published value and this statement are one theorem. *)
Theorem psl211_alldecks_published_input_distinguishability (R : realType) :
  InputDistinguishabilityPropAt (amf_sample psl211_exact_family R tt)
    (coalition_endpoint_reading psl211_algebra)
    ((#|pgg_G psl211_M|%:R)^-1).
Proof.
exact: (proj2 (obstruction_of psl211_alldecks_obstruction_published R tt)).
Qed.
