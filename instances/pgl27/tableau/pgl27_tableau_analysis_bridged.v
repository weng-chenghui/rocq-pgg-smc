(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_tableau_analysis_bridged: the eight-card orbit instance at the       *)
(* AnalysisBridged level                                                      *)
(*                                                                            *)
(* The AnalysisBridged level adjoins one security arm to a Sampled value, and *)
(* the proposition it carries is that arm's own, on top of run correctness    *)
(* and of the identification of the two readings of a coalition. A publish    *)
(* terminal then turns the value into a PublishedRow. Every payload this      *)
(* instance owes an arm is here, every row it publishes is here, and every    *)
(* statement whose subject is a payload or a row is here.                     *)
(*                                                                            *)
(* Three arms are used over the one dealer-dealt run. The exact arm takes an  *)
(* ExactWitness, whose one field is independence of a coalition's reading     *)
(* from the dealt secret; at the uniform cut this is three-transitivity of    *)
(* PGL(2,7) on the eight points read as a privacy statement, and it is exact, *)
(* with no number in it. The input-indistinguishability arm takes a           *)
(* certificate comparing the readings of two dealt secrets under one model.   *)
(* The proximity arm takes a certificate comparing one model with an ideal    *)
(* one at the same index.                                                     *)
(*                                                                            *)
(* Two numbers, and both are read off the one walk bound. pgl27_word_mixing   *)
(* bounds the distance between the two-hundred-letter walk and the uniform    *)
(* cut on the group by 2^-40, and pgl27_word_marginal_bound carries that      *)
(* number. The input-indistinguishability certificate crosses from the walk   *)
(* to the ideal cut once for each of the two dealt secrets it compares, so    *)
(* its cert_eps is that number added to itself, 2^-39. The proximity          *)
(* certificate compares one law with one law and carries the number itself,   *)
(* 2^-40, and the proximity row concludes at 2^-39, the constant the other    *)
(* row over the same model publishes, so the terminal's obligation is met     *)
(* strictly. Each of these numbers bounds a sum of absolute differences,      *)
(* twice a total variation distance, so a distinguisher's advantage against a *)
(* row concluded at 2^-39 is at most 2^-40. Four is the threshold the derived *)
(* profile declares, so every statement here that quantifies over a coalition *)
(* quantifies over at most three of the eight seats, each seat reading the    *)
(* card at the cut image of its own position, and pgl27_exact_leak4 records   *)
(* that four already leak.                                                    *)
(*                                                                            *)
(* Seven rows are published, and three of them publish the manifest's own.    *)
(* pgl27_row_exact_rowE, pgl27_row_word_rowE and pgl27_row_prior_exact_rowE   *)
(* discharge pgl27_row_exact, pgl27_row_word and pgl27_row_prior_exact of     *)
(* pgg_analysis_manifest.v by conversion, and those three are the             *)
(* AnalysisPathRows the manifest carries for this instance. The other four    *)
(* are the word row concluded at 2^-39 in three spellings, through the        *)
(* surface, through the raw bind and from the named Sampled value, and the    *)
(* proximity row, which publishes the same manifest row under a different     *)
(* arm. An AnalysisPathRow holds descriptive metadata and no Prop, so one     *)
(* manifest row carrying an input-indistinguishability row and a proximity    *)
(* row says nothing about either claim. The manifest carries no fourth row    *)
(* over this instance and publishes none of the three by a route this         *)
(* development's programs do not take.                                        *)
(*                                                                            *)
(* Where each published row's chain is, one entry per row.                    *)
(* pgl27_row_exact_tableau, under The two row programs:                       *)
(*     pgl27_row_exact_sampledE, pgl27_row_exact_rowE, pgl27_row_exact_armE,  *)
(*     and the readings pgl27_exec_exact_view_indep_restated and              *)
(*     pgl27_exact_view_secrecy.                                              *)
(* pgl27_row_word_tableau, under the same banner: pgl27_row_word_sampledE,    *)
(*     pgl27_row_word_rowE, pgl27_row_word_armE, and the reading              *)
(*     pgl27_word_view_indistinguishability_restated.                         *)
(* pgl27_row_word39, under The word row concluded at 2^-39:                   *)
(*     pgl27_row_word39_armE, and no reading of its own.                      *)
(* pgl27_row_word39_bind, under the same banner: tied to the row above by     *)
(*     pgl27_row_word39_bindE.                                                *)
(* pgl27_row_word_branch39, under The same row from the named word model:     *)
(*     written from pgl27_word_sampled, so no _sampledE, and                  *)
(*     pgl27_row_word_branch39_armE.                                          *)
(* pgl27_row_prior_exact_tableau, under The ideal: the exact shuffle at every *)
(*     prior: pgl27_row_prior_exact_sampledE, pgl27_row_prior_exact_rowE,     *)
(*     pgl27_row_prior_exact_armE.                                            *)
(* pgl27_row_word_proximity, under One model, two claims, two rows: written   *)
(*     from pgl27_word_sampled, so no _sampledE,                              *)
(*     pgl27_row_word_proximity_rowE, pgl27_row_word_proximity_armE, and the  *)
(*     reading pgl27_word_view_proximity.                                     *)
(*                                                                            *)
(* An importer of this instance names one module per kind of name. The        *)
(* algebraic file declares the Algebraic value; the executable file the       *)
(* Executable value and the parameter equation; the observed file the two     *)
(* prefixes, the inline fork's parameter equation and the ideal               *)
(* functionality; the sampled file the three named models; this file the      *)
(* payloads, the rows, the row and arm equations, the bridges, the restated   *)
(* theorems and the two arm statements; and the checks file the recorded      *)
(* rejections and the comparison of the two word rows' arms. No file of the   *)
(* six uses Require Export.                                                   *)
(*                                                                            *)
(* This file requires instances/pgl27/pgl27_proximity.v, which holds the      *)
(* reading and the distance mathematics the certificates are built from: the  *)
(* two identifications of the framework's static reading of a coalition with  *)
(* pgl27_view, the dealt secret on the word sample space, the distance        *)
(* between the two models' joint laws, and the two arithmetic facts about     *)
(* 2^-40 the conclude obligation is proved with.                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_exact_witness     == the exact arm's witness at every field and    *)
(*                              index                                         *)
(*   pgl27_word_cert         == the input-indistinguishability arm's          *)
(*                              certificate                                   *)
(*   pgl27_row_exact_tableau == the exact row as a program                    *)
(*   pgl27_row_word_tableau  == the word row as a program                     *)
(*   pgl27_reprice39         == the name 2^-39 for the word row's bound       *)
(*   pgl27_row_word39        == the word row concluded at that number         *)
(*   pgl27_row_word39_bind   == the same row written through the bind         *)
(*   pgl27_row_word_branch39 == the continuation of the named word model      *)
(*                              concluded at 2^-39                            *)
(*   pgl27_reprice41         == the name 2^-41 for a bound                    *)
(*   pgl27_word_target       == the word row's published statement            *)
(*   pgl27_exact_target      == the exact row's published statement           *)
(*   pgl27_word_restated     == the word row through the restate terminal     *)
(*   pgl27_exact_restated    == the exact row through the restate terminal    *)
(*   pgl27_word_same_statement                                                *)
(*                           == the published word statement and the word     *)
(*                              row's restatement inhabit one type            *)
(*   pgl27_exact_same_statement                                               *)
(*                           == the published exact statement and the exact   *)
(*                              row's restatement inhabit one type            *)
(*   pgl27_prior_exact_witness                                                *)
(*                           == the exact arm's witness at the prior-indexed  *)
(*                              exact shuffle                                 *)
(*   pgl27_row_prior_exact_tableau                                            *)
(*                           == that shuffle published as its own program     *)
(*   pgl27_word_proximity_cert                                                *)
(*                           == the word model's proximity certificate        *)
(*   pgl27_row_word_proximity                                                 *)
(*                           == the word row as a program at the proximity    *)
(*                              arm, concluded at 2^-39                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_exact_viewE       == the framework's seat reader is the            *)
(*                              instance's, with the secret left in the       *)
(*                              sample point                                  *)
(*   pgl27_exact_leak4       == four seats of this instance leak the secret   *)
(*   pgl27_word_view_const   == below the four-seat threshold, two secrets    *)
(*                              give one reading of the ideal cut             *)
(*   pgl27_row_exact_sampledE                                                 *)
(*                           == the exact row continues the named exact model *)
(*   pgl27_row_word_sampledE == the word row continues the named word model   *)
(*   pgl27_row_word_certE    == the five written clauses are pgl27_word_cert  *)
(*   pgl27_row_exact_rowE    == the exact program publishes the manifest's    *)
(*                              row                                           *)
(*   pgl27_row_word_rowE     == the word program publishes the manifest's row *)
(*   pgl27_row_exact_armE    == the exact row carries the exact arm           *)
(*   pgl27_row_word_armE     == the word row carries the input-               *)
(*                              indistinguishability arm                      *)
(*   pgl27_row_word39_bindE  == the surface and the bind build one term       *)
(*   pgl27_row_word39_armE   == the concluded row carries that same arm       *)
(*   pgl27_row_word_branch39_armE                                             *)
(*                           == the branch row carries that arm as well       *)
(*   pgl27_word_reprice41_false                                               *)
(*                           == the terminal's obligation at 2^-41 is false   *)
(*   pgl27_word_bridge       == the word row's proposition gives its          *)
(*                              published statement                           *)
(*   pgl27_exact_bridge      == the exact row's proposition gives its         *)
(*                              published statement                           *)
(*   pgl27_word_view_indistinguishability_restated                            *)
(*                           == the word statement, from the word row alone   *)
(*   pgl27_exec_exact_view_indep_restated                                     *)
(*                           == the exact statement, from the exact row alone *)
(*   pgl27_exact_view_secrecy                                                 *)
(*                           == below the four-seat threshold, the exact      *)
(*                              arm's four conjuncts at this instance         *)
(*   pgl27_prior_viewE       == the framework's reading of a coalition at the *)
(*                              prior-indexed exact shuffle is the instance's *)
(*                              own reading pgl27_view                        *)
(*   pgl27_row_prior_exact_sampledE                                           *)
(*                           == the prior-indexed exact row continues the     *)
(*                              named model                                   *)
(*   pgl27_row_prior_exact_armE                                               *)
(*                           == the ideal row carries the exact arm           *)
(*   pgl27_row_prior_exact_rowE                                               *)
(*                           == the ideal program publishes                   *)
(*                              pgl27_row_prior_exact                         *)
(*   pgl27_word_proximity_cert_idealE                                         *)
(*                           == the certificate's ideal is the ideal row's    *)
(*                              model, and the port built from its witness is *)
(*                              that row's port                               *)
(*   pgl27_word_proximity_cert_epsE                                           *)
(*                           == the certificate's number is 2^-40             *)
(*   pgl27_word_proximity_eps_halfE                                           *)
(*                           == the input-indistinguishability certificate's  *)
(*                              number is twice the proximity certificate's   *)
(*   pgl27_word_proximity_le39                                                *)
(*                           == the certificate's number is at most 2^-39     *)
(*   pgl27_word_proximity_cert_eps_lt2                                        *)
(*                           == that number is below the bound two            *)
(*                              var_dist_le2 gives                            *)
(*   pgl27_row_word_proximity_rowE                                            *)
(*                           == the proximity row publishes pgl27_row_word    *)
(*   pgl27_row_word_proximity_armE                                            *)
(*                           == that row carries the proximity arm            *)
(*   pgl27_row_word_families_sampledE                                         *)
(*                           == both rows over the word model read their      *)
(*                              model family off the one named Sampled value  *)
(*   pgl27_row_word_obs_sampledE                                              *)
(*                           == both rows read their observed execution off   *)
(*                              that same value                               *)
(*   pgl27_word_view_proximity                                                *)
(*                           == below the four-seat threshold, the proximity  *)
(*                              row's security statement, at 2^-39            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_observed.
From pgg_smc Require Import pgl27_tableau_sampled.
From pgg_smc Require Import pgl27_proximity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     The exact family's witness                                             *)
(******************************************************************************)

(** The same identification once more, with the secret left inside the sample
    point. The exact arm compares a coalition's reading with the secret on one
    probability space, so the secret cannot be fixed first: the reader is a
    random variable of the pair, and that random variable is pgl27_view R C. *)
Lemma pgl27_exact_viewE (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_exact_family R idx).(sa_arg) u)
              ((amf_sample pgl27_exact_family R idx).(sa_cut) u))
  = pgl27_view R C.
Proof. by apply: boolp.funext; case=> s g; exact: pgl27_static_obsE. Qed.

(** The exact arm's witness: the dealt secret as a random variable on the exact
    sample space, and, at every coalition of fewer than four seats, the
    independence of that coalition's reading from it. The independence is
    pgl27_view_indep, which is three-transitivity of PGL(2,7) on the eight
    points read as a privacy statement, and it is exact: the uniform cut makes
    the reading carry no information about the secret at all, not a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is the whole of what this instance owes the exact
    arm. *)
Definition pgl27_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample pgl27_exact_family R idx) :=
  @MkExactWitness R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_exact_family R idx) bool (pgl27_secret R)
    (fun C HC =>
       let H3 : (#|C| <= 3)%N := HC in
       (eq_ind_r
          (fun v => pgl27P R |= v _|_ pgl27_secret R)
          (pgl27_view_indep R H3)
          (pgl27_exact_viewE R idx C))).

(** A four-seat coalition of this instance reads a view whose mutual
    information with the dealt secret is strictly positive, so the threshold
    four is sharp and not merely as far as the independence proof reached. It
    is pgl27_view_leak_k4, carried to the framework's reader by the same
    identification the witness above is carried by; the coalition is the four
    heart seats of the identity deal, and one coalition is all the statement
    asks for. *)
Lemma pgl27_exact_leak4 :
  ExactLeakAt 4 (tableau_at (pgl27_dealt sample pgl27_exact_family))
    pgl27_exact_witness.
Proof.
move=> R idx; exists pgl27_leak_coalition; split.
  exact: (proj1 (pgl27_view_leak_k4 R)).
rewrite (pgl27_exact_viewE R idx pgl27_leak_coalition).
exact: (proj2 (pgl27_view_leak_k4 R)).
Qed.


(******************************************************************************)
(*     The word family's certificate                                          *)
(******************************************************************************)

(** Two dealt secrets give a coalition of fewer than four seats the same
    reading of the ideal uniform cut. It is pgl27_view_law_const, which is
    three-transitivity of PGL(2,7) read as a privacy statement, carried to
    the framework's reader at each of the two secrets; the statement is
    exact, and it is the half of the input-indistinguishability arm that
    spends no mixing bound. *)
Lemma pgl27_word_view_const (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (#|C| < profile_k (instance_profile pgl27_algebra))%N ->
  forall x x' : bool,
    fdistmap (@static_coalition_obs pgl27_algebra pgl27_dealt_params C x)
             (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
    = fdistmap (@static_coalition_obs pgl27_algebra pgl27_dealt_params C x')
               (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)).
Proof.
move=> HC x x'.
rewrite (pgl27_static_obs_funE R C x) (pgl27_static_obs_funE R C x').
exact: (pgl27_view_law_const R x x' HC).
Qed.

(** The input-indistinguishability arm's certificate at each secret prior.
    Its five fields are the two-hundred-letter walk's marginal bound; the
    identification of that bound's law with the law the word adapter draws
    its cut from, which is pgl27_word_cut_distE read backwards; the uniform
    distribution on the group as the ideal cut; the distance
    pgl27_word_mixing of the walk from that ideal, an unconditional theorem
    about the walk whose bound is 2^-40; and the constancy of a coalition's
    reading of the ideal cut in the dealt secret, which is
    pgl27_word_view_const and is exact. The two currencies are visible in the
    fields: everything about the ideal cut is exact and three-transitive, and
    the only inexact quantity anywhere in this row is the walk's 2^-40. *)
Definition pgl27_word_cert (R : realType) (secretP : R.-fdist bool)
  : IndistinguishabilityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIndistinguishabilityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (pgl27_word_marginal_bound R)
    (esym (pgl27_word_cut_distE secretP))
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
    (pgl27_word_mixing R)
    (pgl27_word_view_const R).


(******************************************************************************)
(*     The two row programs                                                   *)
(******************************************************************************)

(** The exact row: the shared prefix, the exact-shuffle model, the witness
    above, and the manifest row. Its last line publishes a row whose transfer
    status is StaticExecutedOnly, because the cut this model draws is already
    the uniform one and no idealized shuffle is being compared with a real
    one. What the finished row carries about a coalition of fewer than four
    seats is independence of the dealt secret, at every real field, with no
    numeric bound anywhere in it, and beside that the record that four seats
    already leak. *)
Definition pgl27_row_exact_tableau : PublishedRow :=
  pgl27_dealt
    sample  pgl27_exact_family
    certify ExactIndependence pgl27_exact_witness
            leaks at 4 by pgl27_exact_leak4
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The exact row continues the named exact model. The program above writes
    the sample step and the certify statement in one term and the Sampled
    file names the value between them, so this equation is what lets a
    statement made at pgl27_exact_sampled be read as a statement about the
    row. *)
Lemma pgl27_row_exact_sampledE :
  (pgl27_exact_sampled
     certify ExactIndependence pgl27_exact_witness
             leaks at 4 by pgl27_exact_leak4
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = pgl27_row_exact_tableau.
Proof. exact: erefl. Qed.

(** The word row: the same prefix, the two-hundred-letter word model, the
    certificate above, and the manifest row at transfer status IdealFinite,
    which records that a finite walk is being compared with the ideal uniform
    cut. What the finished row carries is a variation distance between the
    readings of two dealt secrets, bounded by 2^-40 + 2^-40: the framework's
    transfer inequality crosses from the walk to the ideal cut and back again,
    and each crossing spends the same mixing bound once. *)
Definition pgl27_row_word_tableau : PublishedRow :=
  pgl27_dealt
    sample  pgl27_word_family
    certify InputIndistinguishability at R idx
            pgl27_word_marginal_bound R
            tied by esym (pgl27_word_cut_distE idx)
            ideal (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
            mixing by pgl27_word_mixing R
            invariant by pgl27_word_view_const R
    |> publish IdealFinite BaselineClassicalOnly.

(** The word row continues the named word model, with the certificate
    written as one record. The five clauses of the program above and the
    record are one term by pgl27_row_word_certE, so this equation carries
    the naming of the model and nothing else. *)
Lemma pgl27_row_word_sampledE :
  (pgl27_word_sampled
     certify InputIndistinguishability pgl27_word_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = pgl27_row_word_tableau.
Proof. exact: erefl. Qed.

(** The same program with the five components bundled as pgl27_word_cert.
    Writing the certificate out in five clauses and writing it as one record
    give the same term, so the surface renames nothing and hides nothing. *)
Lemma pgl27_row_word_certE :
  pgl27_row_word_tableau
  = (pgl27_dealt ;;; sample_step of pgl27_word_family
                 ;;; certify_indistinguishability of pgl27_word_cert
                 ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. by []. Qed.

(** The row the exact program publishes is the manifest's own row for this
    instance. Conversion decides it, so the descriptive row and the theorem
    proved about it cannot drift apart. *)
Lemma pgl27_row_exact_rowE :
  published_row pgl27_row_exact_tableau = pgl27_row_exact.
Proof. by []. Qed.

(** The same for the word program and the manifest's word row. The two rowE
    lemmas together are what makes the manifest a claim this file discharges
    rather than a table maintained beside it. *)
Lemma pgl27_row_word_rowE :
  published_row pgl27_row_word_tableau = pgl27_row_word.
Proof. by []. Qed.

(** The arm the exact row carries, at every real field and index:
    independence of the coalition's view from the secret, and not a distance
    between two readings. This is the value a paper's table prints in the arm
    column for this row; certify_exact_armE and publish_armE are why the
    value is settled by the row's certify statement. *)
Lemma pgl27_row_exact_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_exact_tableau)) R) :
  security_arm_of pgl27_row_exact_tableau R idx = ExactIndependenceArm.
Proof. by []. Qed.

(** The arm the word row carries. The two rows publish different manifest
    rows here, but a reader of the manifest alone could not tell independence
    of the view from a distance between two readings, and this pair of
    equations is what separates them. *)
Lemma pgl27_row_word_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_tableau)) R) :
  security_arm_of pgl27_row_word_tableau R idx = InputIndistinguishabilityArm.
Proof. by []. Qed.


(******************************************************************************)
(*     The word row concluded at 2^-39                                        *)
(******************************************************************************)

(** The name 2^-39 for a bound, at every real field. A single real will not
    serve, because the security port quantifies over the field. *)
Definition pgl27_reprice39 : Reprice := fun R => Some (2%:R^-39 : R).

(** The word row concluded at the single constant 2^-39. The data, the model
    and the certificate are untouched, so the published row asserts about a
    coalition no more than pgl27_row_word_tableau, at the number a reader
    expects to cite. *)
(* The accumulated bound is 2^-40 twice; pow2_split adds the two copies and
   eqW reads that identity as the inequality the terminal's obligation asks
   for. *)
Definition pgl27_row_word39 : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    sample  pgl27_word_family
    certify InputIndistinguishability pgl27_word_cert
    |> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The same row written through the bind and its payloads, with no surface
    notation between the statements. *)
Definition pgl27_row_word39_bind : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_indistinguishability of pgl27_word_cert
    ;;; conclude pgl27_reprice39 of (fun R _ => ssr_ext.eqW (pow2_split R))
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The two spellings are one term, so the conclude and publish surface adds
    no step and hides no payload, as the five input-indistinguishability
    clauses do not for the certify statement. *)
Lemma pgl27_row_word39_bindE : pgl27_row_word39 = pgl27_row_word39_bind.
Proof. by []. Qed.

(** The arm the concluded row carries. Concluding at an upper bound leaves the
    port untouched, so the row at 2^-39 carries the arm the row at its own sum
    carries, and the table column is the same for both. *)
Lemma pgl27_row_word39_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word39)) R) :
  security_arm_of pgl27_row_word39 R idx = InputIndistinguishabilityArm.
Proof. by []. Qed.


(******************************************************************************)
(*     The same row from the named word model                                 *)
(******************************************************************************)

(** The word row built from the named value pgl27_word_sampled rather than
    from the dealt prefix: the same certificate, the same terminal at 2^-39
    and the same two statuses as pgl27_row_word39. Naming the Sampled value
    is what lets a further row over this model be written without repeating
    the prefix. *)
Definition pgl27_row_word_branch39 : PublishedRowAt pgl27_reprice39 :=
  pgl27_word_sampled
    certify InputIndistinguishability pgl27_word_cert
    |> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The arm the branch row carries. Naming the Sampled value before the
    certify statement leaves the port where that statement put it, so the
    branch row's table column is the one pgl27_row_word39 has. *)
Lemma pgl27_row_word_branch39_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_branch39)) R) :
  security_arm_of pgl27_row_word_branch39 R idx = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     A number below the proved one                                          *)
(******************************************************************************)

(** The name 2^-41 for a bound, at every real field. *)
Definition pgl27_reprice41 : Reprice := fun R => Some (2%:R^-41 : R).

(** The word certificate's own bound is 2^-40 twice, and 2^-41 is strictly
    below that, so the terminal's obligation at 2^-41 is refutable and not
    merely unproved. It is what separates publishing an upper bound of the
    distance a row proved from publishing a number the certificate does not
    prove. *)
Lemma pgl27_word_reprice41_false (R : realType) (secretP : R.-fdist bool) :
  ~~ (cert_eps (@pgl27_word_cert R secretP)
      <= odflt (cert_eps (@pgl27_word_cert R secretP)) (pgl27_reprice41 R)).
Proof.
rewrite /cert_eps /= pow2_split -Order.TotalTheory.ltNge.
rewrite ltf_pV2 ?posrE ?exprn_gt0 //.
by rewrite ltr_eXn2l ?ltr1n.
Qed.


(******************************************************************************)
(*     The word statement, from the word row                                  *)
(******************************************************************************)

(** The word family's published statement, as a proposition: at fewer than
    four seats, the coalition-view laws of two dealt secrets under the word
    shuffle are within 2^-39 in variation distance. This is the statement a
    reader of this instance cites, written out so that a row can be handed
    over as it. *)
Definition pgl27_word_target (R : realType) : Prop :=
  forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
    var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
             (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
    <= 2%:R^-39.

(** The derivation from the word row's accumulated proposition to that
    statement. Three rewritings and nothing else: the published 2^-39 is
    unfolded into the two copies of 2^-40 the row accumulated, the framework's
    seat reader is replaced by the instance's at each of the two secrets, and
    the adapter's cut law is replaced by rho_word. No step of the mathematics
    is repeated here; the bound itself comes from the row. *)
Lemma pgl27_word_bridge (R : realType) (secretP : R.-fdist bool)
    (q : StackAt AnalysisBridged)
    (Hq : q = tableau_at (pgl27_dealt
                         ;;; sample_step of pgl27_word_family
                         ;;; certify_indistinguishability of pgl27_word_cert)) :
  StackProp AnalysisBridged q -> pgl27_word_target R.
Proof.
rewrite Hq => pf C s s' HC.
rewrite -pow2_split.
rewrite -(pgl27_static_obs_funE R C s) -(pgl27_static_obs_funE R C s').
rewrite -(pgl27_word_cut_distE secretP).
exact: (proj2 pf R secretP C s s' HC).
Qed.

(** The word row handed over as its published statement. The restate terminal
    keeps the row's data and replaces its accumulated conjunction by the
    proposition the caller wrote out, proved by the bridge above. *)
Definition pgl27_word_restated (R : realType) (secretP : R.-fdist bool)
    : RestatedTableau (pgl27_word_target R) :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_indistinguishability of pgl27_word_cert
    ;;; restate (pgl27_word_target R)
        of (pgl27_word_bridge secretP (q := _) erefl).

(** Two dealt secrets give coalition-view laws within 2^-39 under the word
    shuffle, at fewer than four seats. The statement is that of
    pgl27_word_view_indistinguishability, re-proved by reading the restated
    row's theorem field and applying it, with no proof step of its own; the
    secret prior is an argument because the word model is a family indexed by
    it, and any one index witnesses a statement the prior does not appear in. *)
Theorem pgl27_word_view_indistinguishability_restated (R : realType)
    (secretP : R.-fdist bool) (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
           (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
  <= 2%:R^-39.
Proof. exact: (rq_thm (pgl27_word_restated secretP) C s s'). Qed.


(******************************************************************************)
(*     The exact statement, from the exact row                                *)
(******************************************************************************)

(** The exact family's published statement, as a proposition: at fewer than
    four seats, the joint law of the executed coalition reading and the dealt
    secret is the product of its two marginals. It is the product form of
    independence, which is what a reader comparing this instance with an ideal
    execution wants to see. *)
Definition pgl27_exact_target (R : realType) : Prop :=
  forall C : {set 'I_8}, (#|C| <= 3)%N ->
    fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
    = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
          0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist.

(** The derivation from the exact row's accumulated proposition to that
    statement. The row's first conjunct of the arm is independence of the
    executed reader from the secret, which gives the product law directly; what
    remains is to rewrite the executed reader as the instance's view, using the
    row's own view identification and then pgl27_static_obsE. *)
Lemma pgl27_exact_bridge (R : realType) (q : StackAt AnalysisBridged)
    (Hq : q = tableau_at (pgl27_dealt
                         ;;; sample_step of pgl27_exact_family
                         ;;; certify_exact of pgl27_exact_witness)) :
  StackProp AnalysisBridged q -> pgl27_exact_target R.
Proof.
rewrite Hq => pf C HC.
case: (proj2 pf R tt C HC) => Hi _ _ _.
have Hd := inde_dist_of_RV2 Hi.
rewrite (_ : (fun u => (pgl27_view R C u, pgl27_secret R u))
           = (fun u => (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                          (pgl27_sample R) 0 C u, pgl27_secret R u))).
  by rewrite -Hd.
apply: boolp.funext => u; congr (_, _).
by rewrite (proj2 (proj1 pf) R tt C) (pgl27_static_obsE R C u.1 u.2).
Qed.

(** The exact row handed over as its published statement, by the bridge above.
    The row's data is kept and only its accumulated conjunction is traded. *)
Definition pgl27_exact_restated (R : realType)
    : RestatedTableau (pgl27_exact_target R) :=
  pgl27_dealt
    ;;; sample_step of pgl27_exact_family
    ;;; certify_exact of pgl27_exact_witness
    ;;; restate (pgl27_exact_target R)
        of (@pgl27_exact_bridge R _ erefl).

(** At fewer than four seats the executed coalition reading of the exact
    model and the dealt secret have a product joint law. The statement is
    that of pgl27_exec_exact_view_indep, re-proved by reading the restated
    row's theorem field and applying it. *)
Theorem pgl27_exec_exact_view_indep_restated (R : realType)
    (C : {set 'I_8}) (HC : (#|C| <= 3)%N) :
  fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
  = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
        0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist.
Proof. exact: (rq_thm (pgl27_exact_restated R) C HC). Qed.


(******************************************************************************)
(*     The exact arm's four conjuncts at this instance                        *)
(******************************************************************************)

(** The exact row's view secrecy at this instance: at fewer than four colluding
    seats the executed coalition reading is independent of the dealt secret,
    carries zero mutual information with it, leaves the secret's entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact arm at this instance; the proof is the row's
    security projection applied, so a reader who wants the
    information-theoretic reading of the row needs no further derivation. *)
Theorem pgl27_exact_view_secrecy (R : realType) (C : {set 'I_8})
    (HC : (#|C| < 4)%N) :
  [/\ pgl27P R |= (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                     (pgl27_sample R) 0 C) _|_ (pgl27_secret R),
      `I( pgl27_secret R ;
          @sa_coalition_view R pgl27_profile pgl27_exec_plug
            (pgl27_sample R) 0 C ) = 0,
      `H( pgl27_secret R |
          @sa_coalition_view R pgl27_profile pgl27_exec_plug
            (pgl27_sample R) 0 C ) = `H `p_ (pgl27_secret R)
    & forall (W : finType) (h : {ffun 'I_8 -> 'I_8} -> W),
        pgl27P R |= (h `o (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                             (pgl27_sample R) 0 C)) _|_ (pgl27_secret R)].
Proof. exact: (view_secrecy_of pgl27_row_exact_tableau R tt C HC). Qed.


(******************************************************************************)
(*     Each published statement and its restatement are one statement         *)
(******************************************************************************)

(** The published word statement and the theorem the word row restates inhabit
    one pair type, so the two are the same proposition and not merely two
    propositions about the same objects. A row that reached a weaker bound, a
    larger coalition or a different reader would fail here rather than pass
    with a different theorem under the same name. *)
Definition pgl27_word_same_statement (R : realType) (secretP : R.-fdist bool) :
  (forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
     var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
              (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
     <= 2%:R^-39)
  * (forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
     var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
              (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
     <= 2%:R^-39) :=
  (@pgl27_word_view_indistinguishability R,
   @pgl27_word_view_indistinguishability_restated R secretP).

(** The same check for the exact published statement and the theorem the exact
    row restates. *)
Definition pgl27_exact_same_statement (R : realType) :
  (forall C : {set 'I_8}, (#|C| <= 3)%N ->
     fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
     = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
           0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist)
  * (forall C : {set 'I_8}, (#|C| <= 3)%N ->
     fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
     = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
           0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist) :=
  (@pgl27_exec_exact_view_indep R, @pgl27_exec_exact_view_indep_restated R).


(******************************************************************************)
(*     The ideal: the exact shuffle at every prior                            *)
(******************************************************************************)

(** The framework's static reading of a coalition at this model is the
    instance's own reading pgl27_view, with the secret left inside the sample
    point. Every security statement of a row is made about the left-hand side
    and every theorem of the instance about the right, so this equation is
    the whole of what carries one to the other at the prior-indexed model. *)
Lemma pgl27_prior_viewE (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_arg) u)
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_cut) u))
  = pgl27_view R C.
Proof. by apply: boolp.funext; case=> s g; exact: pgl27_static_obsE. Qed.

(** The exact arm's witness at every prior: the dealt secret as a random
    variable on this sample space, and, at every coalition of fewer than four
    seats, the independence of that coalition's reading from it. The
    independence is pgl27_view_indep_gen, three-transitivity of PGL(2,7) read
    as a privacy statement, which holds whatever the law of the secret is. The
    reading carries no information about the secret at all and not a small
    amount, so this model is an execution a proximity certificate may call
    ideal. *)
Definition pgl27_prior_exact_witness (R : realType) (secretP : R.-fdist bool)
  : ExactWitness (amf_sample pgl27_prior_exact_family R secretP) :=
  @MkExactWitness R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_prior_exact_family R secretP) bool (pgl27_secret R)
    (fun C HC =>
       let H3 : (#|C| <= 3)%N := HC in
       (eq_ind_r
          (fun v => pgl27P_gen secretP |= v _|_ pgl27_secret R)
          (pgl27_view_indep_gen secretP H3)
          (pgl27_prior_viewE secretP C))).

(** The prior-indexed exact shuffle, from the observed prefix the two existing
    PGL(2,7) rows share, certified by the exact arm and published. Its
    transfer status is StaticExecutedOnly, because this model draws the
    uniform cut itself and no idealized shuffle is being compared with a real
    one; what the row carries about a coalition of fewer than four seats is
    independence of the dealt secret, at every real field and every prior,
    with no numeric bound anywhere in it. *)
Definition pgl27_row_prior_exact_tableau : PublishedRow :=
  pgl27_dealt
    sample  pgl27_prior_exact_family
    certify ExactIndependence pgl27_prior_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The prior-indexed exact row continues the named prior-indexed model, so
    the ideal a proximity certificate measures against and the row that
    publishes it are read off one name. *)
Lemma pgl27_row_prior_exact_sampledE :
  (pgl27_prior_exact_sampled
     certify ExactIndependence pgl27_prior_exact_witness
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = pgl27_row_prior_exact_tableau.
Proof. exact: erefl. Qed.

(** The arm the ideal row carries, at every real field and prior:
    independence of the dealt secret, and not a distance to some other
    model. *)
Lemma pgl27_row_prior_exact_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_prior_exact_tableau)) R) :
  security_arm_of pgl27_row_prior_exact_tableau R idx = ExactIndependenceArm.
Proof. by []. Qed.

(** The manifest's typed row for the eight-card orbit instance at the
    prior-indexed exact shuffle is the row this program publishes. Its five
    coordinates are the observed execution the program runs on, the
    completion level the publish terminal reaches, the model family the
    sample step named, and the two statuses the terminal was given. The
    manifest writes those coordinates in the facade's vocabulary and the
    program in this file's, and conversion decides the equation, so the
    manifest's row for this path is a claim this equation discharges rather
    than a table maintained beside the program. *)
Lemma pgl27_row_prior_exact_rowE :
  published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     The proximity certificate, and its ideal                               *)
(******************************************************************************)

(** The proximity certificate of the PGL(2,7) word row at every prior. Its
    five fields are the prior-indexed exact shuffle as the ideal; that
    model's exact witness, which is what makes the ideal an execution whose
    coalitions below four seats learn nothing at all; the dealt secret of
    the word model; the walk's marginal number 2^-40; and the distance
    pgl27_word_proximity_close of pgl27_proximity.v. The only inexact
    quantity is that number: the ideal and its witness are the terms the
    ideal row already publishes, and the secret is the word model's own
    first projection, typed at the carrier that witness names. *)
Definition pgl27_word_proximity_cert (R : realType) (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_prior_exact_family R secretP)
    (pgl27_prior_exact_witness secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The model the certificate calls ideal is the model the published ideal
    row carries, and the port built from the certificate's witness is that
    row's port. Conversion decides both, so the ideal a word row is measured
    against is the model pgl27_row_prior_exact_tableau publishes and not a
    second description of it. *)
Lemma pgl27_word_proximity_cert_idealE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_ideal (pgl27_word_proximity_cert secretP)
  = amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP
  /\ ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP))
     = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP.
Proof. by split. Qed.


(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

(** The certificate's number is the two-hundred-letter walk's marginal
    number, 2^-40. *)
Lemma pgl27_word_proximity_cert_epsE (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40 :> R.
Proof. exact: erefl. Qed.

(** The number pgl27_word_cert carries at this model is twice the number
    pgl27_word_proximity_cert carries. Both are read off pgl27_word_mixing,
    the one bound on the cut group's distance; the input-indistinguishability
    arm spends it once for each of the two dealt secrets it compares and the
    proximity arm compares one law with one law. The relation is between
    these two certificates and not between the two arms: cert_eps is by
    definition the walk's marginal number added to itself, and this proximity
    certificate chooses that same marginal number as its own field, which a
    proximity certificate over the same model and the same ideal is free not
    to do. *)
Lemma pgl27_word_proximity_eps_halfE (R : realType) (secretP : R.-fdist bool) :
  cert_eps (pgl27_word_cert secretP)
  = ipc_eps (pgl27_word_proximity_cert secretP)
    + ipc_eps (pgl27_word_proximity_cert secretP).
Proof. by []. Qed.

(** The certificate's number is at most 2^-39, the constant the word row
    publishes for the input-indistinguishability arm. It is the obligation of
    the terminal that concludes the proximity row at that constant, and the
    obligation is met strictly, the certificate's number being half of the
    published one. *)
Lemma pgl27_word_proximity_le39 (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39 :> R.
Proof.
have H0 : (0:R) < 2%:R^-40 by rewrite invr_gt0 pgl27_pow2_40_gt0.
have He := pow2_split R.
rewrite pgl27_word_proximity_cert_epsE; lra.
Qed.

(** The certificate's own number is below two, the bound var_dist_le2 gives
    for a variation distance, so the certificate is not vacuous. At about
    4.5e-13 of that bound it is a cryptographic separation, where the
    proximity certificate of Kim's one-cut model at one percent of the same
    bound is a weak one. *)
Lemma pgl27_word_proximity_cert_eps_lt2 (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) < 2%:R :> R.
Proof.
have H1 : 2%:R^-40 <= (1:R)
  by rewrite invf_le1 ?pgl27_pow2_40_gt0 ?pgl27_pow2_40_ge1.
rewrite pgl27_word_proximity_cert_epsE; lra.
Qed.


(******************************************************************************)
(*     One model, two claims, two rows                                        *)
(******************************************************************************)

(** The word model certified by the proximity arm and concluded at 2^-39, the
    constant the input-indistinguishability row of the same model publishes and
    the one the published reading statement pgl27_word_view_proximity carries.
    The certificate's own number is 2^-40, half of that. Below four seats its
    distance field, pgl27_word_proximity_close, puts the joint law of a
    coalition's reading with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where the reading and
    the secret are independent outright, so the ideal side is the product of
    its two marginals. The number is spent once, against the
    input-indistinguishability certificate's twice. Its transfer status is
    IdealFinite, the same the input-indistinguishability row carries, and the
    two certificates compare against the same ideal cut. *)
Definition pgl27_row_word_proximity : PublishedRowAt pgl27_reprice39 :=
  pgl27_word_sampled
    certify IdealProximity pgl27_word_proximity_cert
    |> conclude pgl27_reprice39 by (fun R idx => pgl27_word_proximity_le39 idx)
    |> publish IdealFinite BaselineClassicalOnly.

(** The proximity row publishes the manifest's row for the word path, as
    pgl27_row_word_rowE says of the word program. An AnalysisPathRow holds
    descriptive metadata and no Prop, so one manifest row carrying an input-
    indistinguishability row and a proximity row says nothing about either
    claim. *)
Lemma pgl27_row_word_proximity_rowE :
  published_row pgl27_row_word_proximity = pgl27_row_word.
Proof.
(* exact: erefl and not by []: done does not return on an equation between
   two rows' coordinates. *)
exact: erefl.
Qed.

(** The arm the proximity row carries, at every real field and prior: the
    distance to a private ideal model, and not the distance between two
    readings of one model. *)
Lemma pgl27_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_proximity)) R) :
  security_arm_of pgl27_row_word_proximity R idx = IdealProximityArm.
Proof. by []. Qed.

(** Both rows over the word model read their analysis model family off the one
    named Tableau Sampled value, so the pair differs in the arm and in nothing
    about the algebra, the run or the law. The family is what a continuation
    of a named value reads off the name. *)
Lemma pgl27_row_word_families_sampledE :
  ab_f (published_at pgl27_row_word_proximity)
  = sp_f (tableau_at pgl27_word_sampled)
  /\ ab_f (published_at pgl27_row_word_branch39)
     = sp_f (tableau_at pgl27_word_sampled).
Proof. split; exact: erefl. Qed.

(** Both rows read their observed execution off that same named value, so the
    two claims are made about one run and one static observation of it and
    not about two executions that happen to agree. Together with the family
    equation above, everything the two rows hold in common comes from the one
    name. *)
Lemma pgl27_row_word_obs_sampledE :
  ab_obs (published_at pgl27_row_word_proximity)
  = sp_obs (tableau_at pgl27_word_sampled)
  /\ ab_obs (published_at pgl27_row_word_branch39)
     = sp_obs (tableau_at pgl27_word_sampled).
Proof.
(* Each row stated against the named value closes by exact: erefl in under
   0.01 s. The row-against-row form is the expensive one, 96.0 s by
   exact: erefl and 48.1 s by reflexivity, and is not stated. *)
split; exact: erefl.
Qed.


(******************************************************************************)
(*     What the proximity row states at this instance                         *)
(******************************************************************************)

(** The proximity row's security statement at the eight-card orbit instance:
    at fewer than four colluding seats and at every prior on the dealt secret,
    the joint law of the executed coalition reading and that secret under the
    two-hundred-letter word walk is within 2^-39 of the product of the two
    marginals of the exact execution at the same prior. The proof is the row's
    security projection applied, so the row and this statement are one
    theorem. *)
Theorem pgl27_word_view_proximity (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_8}) (HC : (#|C| <= 3)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                           (amf_sample pgl27_word_family R secretP) 0 C u,
                         pgl27_word_secret secretP u))
       (sa_sampleP (amf_sample pgl27_word_family R secretP)))
    ((fdistmap (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                  (pgl27_prior_sample secretP) 0 C) (pgl27P_gen secretP))
     `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)))
  <= 2%:R^-39.
Proof.
exact: (view_proximity_of pgl27_row_word_proximity R secretP C HC).
Qed.
