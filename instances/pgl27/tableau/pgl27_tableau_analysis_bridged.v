(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_tableau_analysis_bridged: the eight-card orbit instance at the       *)
(* AnalysisBridged level                                                      *)
(*                                                                            *)
(* The AnalysisBridged level adjoins security evidence to a Sampled value at  *)
(* every real field and index, and the proposition it carries is the one that *)
(* evidence proves, on top of run correctness and of the identification of    *)
(* the two readings of a coalition. A publish terminal then turns the value   *)
(* into a Published. Every payload this instance gives a certify statement is *)
(* here, every program it publishes is here, and every statement whose        *)
(* subject is a payload or a program is here.                                 *)
(*                                                                            *)
(* All three security properties are certified over the one dealer-dealt run. *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's reading from the dealt secret; at the        *)
(* uniform cut this is three-transitivity of PGL(2,7) on the eight points     *)
(* read as a privacy statement, and it is exact, with no number in it.        *)
(* Certifying input indistinguishability takes a certificate comparing the    *)
(* readings of two dealt secrets under one model. Certifying ideal proximity  *)
(* takes a certificate comparing one model with an ideal one at the same      *)
(* index.                                                                     *)
(*                                                                            *)
(* Two numbers, and both are read off the one walk bound. pgl27_word_mixing   *)
(* bounds the distance between the two-hundred-letter walk and the uniform    *)
(* cut on the group by 2^-40, and pgl27_word_marginal_bound carries that      *)
(* number. The input-indistinguishability tail makes two hops from the walk   *)
(* to the ideal cut, one for each of the two dealt secrets the proposition    *)
(* compares, so cert_eps is that number added to itself, 2^-39. The           *)
(* ideal-proximity proposition compares one law with one law, and the         *)
(* certificate carries the number itself, 2^-40, and the proximity program    *)
(* concludes at 2^-39, the constant the other program over the same model     *)
(* publishes, so the terminal's obligation is met strictly. Each of these     *)
(* numbers bounds a sum of absolute differences, twice a total variation      *)
(* distance, so a distinguisher's advantage against a program concluded at    *)
(* 2^-39 is at most 2^-40. Four is the threshold the derived profile          *)
(* declares, so every statement here that quantifies over a coalition         *)
(* quantifies over at most three of the eight seats, each seat reading the    *)
(* card at the cut image of its own position, and pgl27_exact_leak4 records   *)
(* that four already leak.                                                    *)
(*                                                                            *)
(* Seven programs are published, and three of them publish the manifest's     *)
(* own. pgl27_exact_published_pathE, pgl27_word_published_pathE and           *)
(* pgl27_prior_exact_published_pathE discharge pgl27_exact_path,              *)
(* pgl27_word_path and pgl27_prior_exact_path of pgg_analysis_manifest.v by   *)
(* conversion, and those three are the AnalysisPaths the manifest carries for *)
(* this instance. The other four are the word program concluded at 2^-39 in   *)
(* three spellings, through the surface, through the raw bind and from the    *)
(* named Sampled value, and the proximity program, which publishes the same   *)
(* manifest path for a different security property. An AnalysisPath holds     *)
(* descriptive metadata and no Prop, so one manifest path published by an     *)
(* input-indistinguishability program and by a proximity program says nothing *)
(* about either claim. The manifest carries no fourth path over this          *)
(* instance, and none of the three is published by a route this development's *)
(* programs do not take.                                                      *)
(*                                                                            *)
(* Where each published program's chain is, one entry per program.            *)
(* pgl27_exact_published, under The exact and the word program:               *)
(*     pgl27_exact_published_sampledE, pgl27_exact_published_pathE,           *)
(*     pgl27_exact_published_propertyE, and the readings                      *)
(*     pgl27_exec_exact_view_indep_restated and pgl27_exact_view_secrecy.     *)
(* pgl27_word_published, under the same banner:                               *)
(*     pgl27_word_published_sampledE, pgl27_word_published_pathE,             *)
(*     pgl27_word_published_propertyE, and the reading                        *)
(*     pgl27_word_view_indistinguishability_restated.                         *)
(* pgl27_word_published39, under The word program concluded at 2^-39:         *)
(*     pgl27_word_published39_propertyE, and no reading of its own.           *)
(* pgl27_word_published39_bind, under the same banner: tied to the program    *)
(*     above by pgl27_word_published39_bindE.                                 *)
(* pgl27_word_branch_published39, under The same program from the named word  *)
(*     model: written from pgl27_word_sampled, so no _sampledE, and           *)
(*     pgl27_word_branch_published39_propertyE.                               *)
(* pgl27_prior_exact_published, under The ideal: the exact shuffle at every   *)
(*     prior: pgl27_prior_exact_published_sampledE,                           *)
(*     pgl27_prior_exact_published_pathE,                                     *)
(*     pgl27_prior_exact_published_propertyE.                                 *)
(* pgl27_word_proximity_published, under One model, two claims, two programs: *)
(*     written from pgl27_word_sampled, so no _sampledE,                      *)
(*     pgl27_word_proximity_published_pathE,                                  *)
(*     pgl27_word_proximity_published_propertyE, and the reading              *)
(*     pgl27_word_view_proximity.                                             *)
(*                                                                            *)
(* An importer of this instance names one module per kind of name. The        *)
(* algebraic file declares the Algebraic value; the executable file the       *)
(* Executable value and the parameter equation; the observed file the two     *)
(* prefixes, the inline fork's parameter equation and the ideal               *)
(* functionality; the sampled file the three named models; this file the      *)
(* payloads, the programs, the path and security-property equations, the      *)
(* bridges, the restated theorems and the two theorems stating the certified  *)
(* properties; and the checks file the recorded rejections and the comparison *)
(* of the two word programs' security properties. No file of the six uses     *)
(* Require Export.                                                            *)
(*                                                                            *)
(* This file requires instances/pgl27/pgl27_proximity.v, which holds the      *)
(* reading and the distance mathematics the certificates are built from: the  *)
(* two identifications of the framework's static reading of a coalition with  *)
(* pgl27_view, the dealt secret on the word sample space, the distance        *)
(* between the two models' joint laws, and the two arithmetic facts about     *)
(* 2^-40 the conclude obligation is proved with.                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_exact_witness     == the exact-independence witness at every field *)
(*                              and index                                     *)
(*   pgl27_word_cert         == the input-indistinguishability certificate    *)
(*   pgl27_exact_published   == the exact path as a program                   *)
(*   pgl27_word_published    == the word path as a program                    *)
(*   pgl27_bound39           == the name 2^-39 for the word program's bound   *)
(*   pgl27_word_published39  == the word program concluded at that number     *)
(*   pgl27_word_published39_bind                                              *)
(*                           == the same program written through the bind     *)
(*   pgl27_word_branch_published39                                            *)
(*                           == the continuation of the named word model      *)
(*                              concluded at 2^-39                            *)
(*   pgl27_bound41           == the name 2^-41 for a bound                    *)
(*   pgl27_word_target       == the word program's published statement        *)
(*   pgl27_exact_target      == the exact program's published statement       *)
(*   pgl27_word_restated     == the word program through the restate terminal *)
(*   pgl27_exact_restated    == the exact program through the restate         *)
(*                              terminal                                      *)
(*   pgl27_word_same_statement                                                *)
(*                           == the published word statement and the word     *)
(*                              program's restatement inhabit one type        *)
(*   pgl27_exact_same_statement                                               *)
(*                           == the published exact statement and the exact   *)
(*                              program's restatement inhabit one type        *)
(*   pgl27_prior_exact_witness                                                *)
(*                           == the exact-independence witness at the         *)
(*                              prior-indexed exact shuffle                   *)
(*   pgl27_prior_exact_published                                              *)
(*                           == that shuffle published as its own program     *)
(*   pgl27_word_proximity_cert                                                *)
(*                           == the word model's proximity certificate        *)
(*   pgl27_word_proximity_published                                           *)
(*                           == the word path as a program certifying ideal   *)
(*                              proximity, concluded at 2^-39                 *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_exact_viewE       == the framework's seat reader is the            *)
(*                              instance's, with the secret left in the       *)
(*                              sample point                                  *)
(*   pgl27_exact_leak4       == four seats of this instance leak the secret   *)
(*   pgl27_word_view_const   == below the four-seat threshold, two secrets    *)
(*                              give one reading of the ideal cut             *)
(*   pgl27_exact_published_sampledE                                           *)
(*                           == the exact program continues the named exact   *)
(*                              model                                         *)
(*   pgl27_word_published_sampledE                                            *)
(*                           == the word program continues the named word     *)
(*                              model                                         *)
(*   pgl27_word_published_certE                                               *)
(*                           == the five written clauses are pgl27_word_cert  *)
(*   pgl27_exact_published_pathE                                              *)
(*                           == the exact program publishes the manifest's    *)
(*                              path                                          *)
(*   pgl27_word_published_pathE                                               *)
(*                           == the word program publishes the manifest's     *)
(*                              path                                          *)
(*   pgl27_exact_published_propertyE                                          *)
(*                           == the exact program's security property is      *)
(*                              exact independence                            *)
(*   pgl27_word_published_propertyE                                           *)
(*                           == the word program's security property is input *)
(*                              indistinguishability                          *)
(*   pgl27_word_published39_bindE                                             *)
(*                           == the surface and the bind build one term       *)
(*   pgl27_word_published39_propertyE                                         *)
(*                           == the concluded program's security property is  *)
(*                              input indistinguishability                    *)
(*   pgl27_word_branch_published39_propertyE                                  *)
(*                           == the branch program's security property is     *)
(*                              input indistinguishability as well            *)
(*   pgl27_word_bound41_false                                                 *)
(*                           == the terminal's obligation at 2^-41 is false   *)
(*   pgl27_word_bridge       == the word program's proposition gives its      *)
(*                              published statement                           *)
(*   pgl27_exact_bridge      == the exact program's proposition gives its     *)
(*                              published statement                           *)
(*   pgl27_word_view_indistinguishability_restated                            *)
(*                           == the word statement, from the word program     *)
(*                              alone                                         *)
(*   pgl27_exec_exact_view_indep_restated                                     *)
(*                           == the exact statement, from the exact program   *)
(*                              alone                                         *)
(*   pgl27_exact_view_secrecy                                                 *)
(*                           == below the four-seat threshold, the            *)
(*                              exact-independence proposition's four         *)
(*                              conjuncts at this instance                    *)
(*   pgl27_prior_viewE       == the framework's reading of a coalition at the *)
(*                              prior-indexed exact shuffle is the instance's *)
(*                              own reading pgl27_view                        *)
(*   pgl27_prior_exact_published_sampledE                                     *)
(*                           == the prior-indexed exact program continues the *)
(*                              named model                                   *)
(*   pgl27_prior_exact_published_propertyE                                    *)
(*                           == the ideal program's security property is      *)
(*                              exact independence                            *)
(*   pgl27_prior_exact_published_pathE                                        *)
(*                           == the ideal program publishes                   *)
(*                              pgl27_prior_exact_path                        *)
(*   pgl27_word_proximity_cert_idealE                                         *)
(*                           == the certificate's ideal is the ideal          *)
(*                              program's model, and the evidence built from  *)
(*                              its witness is that program's evidence        *)
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
(*   pgl27_word_proximity_published_pathE                                     *)
(*                           == the proximity program publishes               *)
(*                              pgl27_word_path                               *)
(*   pgl27_word_proximity_published_propertyE                                 *)
(*                           == that program's security property is ideal     *)
(*                              proximity                                     *)
(*   pgl27_word_published_families_sampledE                                   *)
(*                           == both programs over the word model read their  *)
(*                              model family off the one named Sampled value  *)
(*   pgl27_word_published_obs_sampledE                                        *)
(*                           == both programs read their observed execution   *)
(*                              off that same value                           *)
(*   pgl27_word_view_proximity                                                *)
(*                           == below the four-seat threshold, the proximity  *)
(*                              program's security statement, at 2^-39        *)
(*   pgl27_word_proximity_eps_sw_boundE                                       *)
(*                           == the certificate's number is the marginal      *)
(*                              bound pgl27_word_cert carries                 *)
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
    point. The exact-independence proposition compares a coalition's reading
    with the secret on one probability space, so the secret cannot be fixed
    first: the reader is a random variable of the pair, and that random variable
    is pgl27_view R C. *)
Lemma pgl27_exact_viewE (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_exact_family R idx).(sa_arg) u)
              ((amf_sample pgl27_exact_family R idx).(sa_cut) u))
  = pgl27_view R C.
Proof. by apply: boolp.funext; case=> s g; exact: pgl27_static_obsE. Qed.

(** The exact-independence witness: the dealt secret as a random variable on the
    exact sample space, and, at every coalition of fewer than four seats, the
    independence of that coalition's reading from it. The independence is
    pgl27_view_indep, which is three-transitivity of PGL(2,7) on the eight
    points read as a privacy statement, and it is exact: the uniform cut makes
    the reading carry no information about the secret at all, not a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is all that certifying exact independence requires of
    this instance. *)
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
    exact, and it is the half of the input-indistinguishability certificate
    that appeals to no mixing bound. *)
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

(** The input-indistinguishability certificate at each secret prior. Its
    five fields are the two-hundred-letter walk's marginal bound; the
    identification of that bound's law with the law the word adapter draws its
    cut from, which is pgl27_word_cut_distE read backwards; the uniform
    distribution on the group as the ideal cut; the distance pgl27_word_mixing
    of the walk from that ideal, an unconditional theorem about the walk whose
    bound is 2^-40; and the constancy of a coalition's reading of the ideal cut
    in the dealt secret, which is pgl27_word_view_const and is exact. Perfect
    and statistical security are both visible in the fields: everything about
    the ideal cut is exact and three-transitive, and the only statistical
    quantity anywhere in this program is the walk's 2^-40. *)
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
(*     The exact and the word program                                         *)
(******************************************************************************)

(** The exact program: the shared prefix, the exact-shuffle model, the witness
    above, and the manifest path. Its last line publishes a path whose transfer
    status is StaticExecutedOnly, because the cut this model draws is already
    the uniform one and no idealized shuffle is being compared with a real one.
    What the finished program carries about a coalition of fewer than four seats
    is independence of the dealt secret, at every real field, with no numeric
    bound anywhere in it, and beside that the record that four seats
    already leak. *)
Definition pgl27_exact_published : Published :=
  pgl27_dealt
    sample  pgl27_exact_family
    certify ExactIndependence pgl27_exact_witness
            leaks at 4 by pgl27_exact_leak4
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The exact program continues the named exact model. The program above writes
    the sample step and the certify statement in one term and the Sampled file
    names the value between them, so this equation is what lets a statement made
    at pgl27_exact_sampled be read as a statement about the program. *)
Lemma pgl27_exact_published_sampledE :
  (pgl27_exact_sampled
     certify ExactIndependence pgl27_exact_witness
             leaks at 4 by pgl27_exact_leak4
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = pgl27_exact_published.
Proof. exact: erefl. Qed.

(** The word program: the same prefix, the two-hundred-letter word model, the
    certificate above, and the manifest path at transfer status IdealFinite,
    which records that a finite walk is being compared with the ideal uniform
    cut. What the finished program carries is a variation distance between the
    readings of two dealt secrets, bounded by 2^-40 + 2^-40: the framework's
    transfer inequality crosses from the walk to the ideal cut and back again,
    and each of the two hops loses the same mixing bound. *)
Definition pgl27_word_published : Published :=
  pgl27_dealt
    sample  pgl27_word_family
    certify InputIndistinguishability at R idx
            pgl27_word_marginal_bound R
            tied by esym (pgl27_word_cut_distE idx)
            ideal (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
            mixing by pgl27_word_mixing R
            invariant by pgl27_word_view_const R
    |> publish IdealFinite BaselineClassicalOnly.

(** The word program continues the named word model, with the certificate
    written as one record. The five clauses of the program above and the record
    are one term by pgl27_word_published_certE, so this equation carries the
    naming of the model and nothing else. *)
Lemma pgl27_word_published_sampledE :
  (pgl27_word_sampled
     certify InputIndistinguishability pgl27_word_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = pgl27_word_published.
Proof. exact: erefl. Qed.

(** The same program with the five components bundled as pgl27_word_cert.
    Writing the certificate out in five clauses and writing it as one record
    give the same term, so the surface renames nothing and hides nothing. *)
Lemma pgl27_word_published_certE :
  pgl27_word_published
  = (pgl27_dealt ;;; sample_step of pgl27_word_family
                 ;;; certify_indistinguishability of pgl27_word_cert
                 ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. by []. Qed.

(** The path the exact program publishes is the manifest's own path for this
    instance. Conversion decides it, so the descriptive path and the theorem
    proved about it cannot drift apart. *)
Lemma pgl27_exact_published_pathE :
  published_path pgl27_exact_published = pgl27_exact_path.
Proof. by []. Qed.

(** The same for the word program and the manifest's word path. The two pathE
    lemmas together are what makes the manifest a claim this file discharges
    rather than a table maintained beside it. *)
Lemma pgl27_word_published_pathE :
  published_path pgl27_word_published = pgl27_word_path.
Proof. by []. Qed.

(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the secret,
    and not a distance between two readings. The program's certify statement
    settles which property that is, through certify_exact_propertyE and
    publish_propertyE. *)
Lemma pgl27_exact_published_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_exact_published)) R) :
  security_property_of pgl27_exact_published R idx = ExactIndependenceProperty.
Proof. by []. Qed.

(** The security property the word program carries. The two programs publish
    different manifest paths here, but a reader of the manifest alone could not
    tell independence of the view from a distance between two readings, and this
    pair of equations is what separates them. *)
Lemma pgl27_word_published_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_word_published)) R) :
  security_property_of pgl27_word_published R idx
  = InputIndistinguishabilityProperty.
Proof. by []. Qed.


(******************************************************************************)
(*     The word program concluded at 2^-39                                    *)
(******************************************************************************)

(** The name 2^-39 for a bound, at every real field. A single real will not
    serve, because the security evidence is given at every real field. *)
Definition pgl27_bound39 : ConcludedBound := fun R => Some (2%:R^-39 : R).

(** The word program concluded at the single constant 2^-39. The data, the model
    and the certificate are untouched, so the published program asserts about a
    coalition no more than pgl27_word_published, at the number a reader expects
    to cite. *)
(* The accumulated bound is 2^-40 twice; pow2_split adds the two copies and
   eqW reads that identity as the inequality the terminal's obligation asks
   for. *)
Definition pgl27_word_published39 : PublishedAt pgl27_bound39 :=
  pgl27_dealt
    sample  pgl27_word_family
    certify InputIndistinguishability pgl27_word_cert
    |> conclude pgl27_bound39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The same program written through the bind and its payloads, with no surface
    notation between the statements. *)
Definition pgl27_word_published39_bind : PublishedAt pgl27_bound39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_indistinguishability of pgl27_word_cert
    ;;; conclude pgl27_bound39 of (fun R _ => ssr_ext.eqW (pow2_split R))
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The two spellings are one term, so the conclude and publish surface adds
    no step and hides no payload, as the five input-indistinguishability
    clauses do not for the certify statement. *)
Lemma pgl27_word_published39_bindE :
  pgl27_word_published39 = pgl27_word_published39_bind.
Proof. by []. Qed.

(** The security property the concluded program carries. Concluding at an upper
    bound leaves the evidence untouched, so the program at 2^-39 carries the
    property the program at its own sum carries. *)
Lemma pgl27_word_published39_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_word_published39)) R) :
  security_property_of pgl27_word_published39 R idx
  = InputIndistinguishabilityProperty.
Proof. by []. Qed.


(******************************************************************************)
(*     The same program from the named word model                             *)
(******************************************************************************)

(** The word program built from the named value pgl27_word_sampled rather than
    from the dealt prefix: the same certificate, the same terminal at 2^-39 and
    the same two statuses as pgl27_word_published39. Naming the Sampled value is
    what lets a further program over this model be written without repeating the
    prefix. *)
Definition pgl27_word_branch_published39 : PublishedAt pgl27_bound39 :=
  pgl27_word_sampled
    certify InputIndistinguishability pgl27_word_cert
    |> conclude pgl27_bound39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The security property the branch program carries. Naming the Sampled value
    before the certify statement leaves the evidence where that statement put
    it, so the branch program carries the property pgl27_word_published39
    carries. *)
Lemma pgl27_word_branch_published39_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_word_branch_published39)) R) :
  security_property_of pgl27_word_branch_published39 R idx
  = InputIndistinguishabilityProperty.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     A number below the proved one                                          *)
(******************************************************************************)

(** The name 2^-41 for a bound, at every real field. *)
Definition pgl27_bound41 : ConcludedBound := fun R => Some (2%:R^-41 : R).

(** The word certificate's own bound is 2^-40 twice, and 2^-41 is strictly below
    that, so the terminal's obligation at 2^-41 is refutable and not merely
    unproved. It is what separates publishing an upper bound of the distance a
    program proved from publishing a number the certificate does not prove. *)
Lemma pgl27_word_bound41_false (R : realType) (secretP : R.-fdist bool) :
  ~~ (cert_eps (@pgl27_word_cert R secretP)
      <= odflt (cert_eps (@pgl27_word_cert R secretP)) (pgl27_bound41 R)).
Proof.
rewrite /cert_eps /= pow2_split -Order.TotalTheory.ltNge.
rewrite ltf_pV2 ?posrE ?exprn_gt0 //.
by rewrite ltr_eXn2l ?ltr1n.
Qed.


(******************************************************************************)
(*     The word statement, from the word program                              *)
(******************************************************************************)

(** The word family's published statement, as a proposition: at fewer than four
    seats, the coalition-view laws of two dealt secrets under the word shuffle
    are within 2^-39 in variation distance. This is the statement a reader of
    this instance cites, written out so that a program can be handed over as
    it. *)
Definition pgl27_word_target (R : realType) : Prop :=
  forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
    var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
             (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
    <= 2%:R^-39.

(** The derivation from the word program's accumulated proposition to that
    statement. Three rewritings and nothing else: the published 2^-39 is
    unfolded into the two copies of 2^-40 the program accumulated, the
    framework's seat reader is replaced by the instance's at each of the two
    secrets, and the adapter's cut law is replaced by rho_word. No step of the
    mathematics is repeated here; the bound itself comes from the program. *)
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

(** The word program handed over as its published statement. The restate
    terminal keeps the program's data and replaces its accumulated conjunction
    by the proposition the caller wrote out, proved by the bridge above. *)
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
    program's theorem field and applying it, with no proof step of its own; the
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
(*     The exact statement, from the exact program                            *)
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

(** The derivation from the exact program's accumulated proposition to that
    statement. The first conjunct of the exact-independence proposition the
    program carries is independence of the executed reader from the secret,
    which gives the product law directly; what remains is to rewrite the
    executed reader as the instance's view, using the program's own view
    identification and then pgl27_static_obsE. *)
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

(** The exact program handed over as its published statement, by the bridge
    above. The program's data is kept and only its accumulated conjunction is
    traded. *)
Definition pgl27_exact_restated (R : realType)
    : RestatedTableau (pgl27_exact_target R) :=
  pgl27_dealt
    ;;; sample_step of pgl27_exact_family
    ;;; certify_exact of pgl27_exact_witness
    ;;; restate (pgl27_exact_target R)
        of (@pgl27_exact_bridge R _ erefl).

(** At fewer than four seats the executed coalition reading of the exact model
    and the dealt secret have a product joint law. The statement is that of
    pgl27_exec_exact_view_indep, re-proved by reading the restated program's
    theorem field and applying it. *)
Theorem pgl27_exec_exact_view_indep_restated (R : realType)
    (C : {set 'I_8}) (HC : (#|C| <= 3)%N) :
  fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
  = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
        0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist.
Proof. exact: (rq_thm (pgl27_exact_restated R) C HC). Qed.


(******************************************************************************)
(*     The exact-independence proposition's four conjuncts at this instance   *)
(******************************************************************************)

(** The exact program's view secrecy at this instance: at fewer than four
    colluding seats the executed coalition reading is independent of the dealt
    secret, carries zero mutual information with it, leaves the secret's entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact-independence proposition at this instance; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic reading of the program needs no further
    derivation. *)
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
Proof. exact: (view_secrecy_of pgl27_exact_published R tt C HC). Qed.


(******************************************************************************)
(*     Each published statement and its restatement are one statement         *)
(******************************************************************************)

(** The published word statement and the theorem the word program restates
    inhabit one pair type, so the two are the same proposition and not merely
    two propositions about the same objects. A program that reached a weaker
    bound, a larger coalition or a different reader would fail here rather than
    pass with a different theorem under the same name. *)
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
    program restates. *)
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
    point. Every security statement of a program is made about the left-hand
    side and every theorem of the instance about the right, so this equation is
    the whole of what carries one to the other at the prior-indexed model. *)
Lemma pgl27_prior_viewE (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_arg) u)
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_cut) u))
  = pgl27_view R C.
Proof. by apply: boolp.funext; case=> s g; exact: pgl27_static_obsE. Qed.

(** The exact-independence witness at every prior: the dealt secret as a random
    variable on this sample space, and, at every coalition of fewer than four
    seats, the independence of that coalition's reading from it. The
    independence is pgl27_view_indep_gen, three-transitivity of PGL(2,7) read as
    a privacy statement, which holds whatever the law of the secret is. The
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
    PGL(2,7) programs share, certified for exact independence and published. Its
    transfer status is StaticExecutedOnly, because this model draws the uniform
    cut itself and no idealized shuffle is being compared with a real one; what
    the program carries about a coalition of fewer than four seats is
    independence of the dealt secret, at every real field and every prior, with
    no numeric bound anywhere in it. *)
Definition pgl27_prior_exact_published : Published :=
  pgl27_dealt
    sample  pgl27_prior_exact_family
    certify ExactIndependence pgl27_prior_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The prior-indexed exact program continues the named prior-indexed model, so
    the ideal a proximity certificate measures against and the program that
    publishes it are read off one name. *)
Lemma pgl27_prior_exact_published_sampledE :
  (pgl27_prior_exact_sampled
     certify ExactIndependence pgl27_prior_exact_witness
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = pgl27_prior_exact_published.
Proof. exact: erefl. Qed.

(** The security property the ideal program carries, at every real field and
    prior, is exact independence: independence of the dealt secret, and not a
    distance to some other model. *)
Lemma pgl27_prior_exact_published_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_prior_exact_published)) R) :
  security_property_of pgl27_prior_exact_published R idx
  = ExactIndependenceProperty.
Proof. by []. Qed.

(** The manifest's typed path for the eight-card orbit instance at the
    prior-indexed exact shuffle is the path this program publishes. Its five
    coordinates are the observed execution the program runs on, the completion
    level the publish terminal reaches, the model family the sample step named,
    and the two statuses the terminal was given. The manifest writes those
    coordinates in the facade's vocabulary and the program in this file's, and
    conversion decides the equation, so the manifest's path for this program is
    a claim this equation discharges rather than a table maintained beside the
    program. *)
Lemma pgl27_prior_exact_published_pathE :
  published_path pgl27_prior_exact_published = pgl27_prior_exact_path.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     The proximity certificate, and its ideal                               *)
(******************************************************************************)

(** The proximity certificate of the PGL(2,7) word program at every prior. Its
    five fields are the prior-indexed exact shuffle as the ideal; that model's
    exact witness, which is what makes the ideal an execution whose coalitions
    below four seats learn nothing at all; the dealt secret of the word model;
    the walk's marginal number 2^-40; and the distance
    pgl27_word_proximity_close of pgl27_proximity.v. The only inexact quantity
    is that number: the ideal and its witness are the terms the ideal program
    already publishes, and the secret is the word model's own first projection,
    typed at the carrier that witness names. *)
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
    program carries, and the evidence built from the certificate's witness is
    that program's evidence. Conversion decides both, so the ideal a word
    program is measured against is the model pgl27_prior_exact_published
    publishes and not a second description of it. *)
Lemma pgl27_word_proximity_cert_idealE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_ideal (pgl27_word_proximity_cert secretP)
  = amf_sample (ab_f (published_at pgl27_prior_exact_published)) R secretP
  /\ ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP))
     = ab_evidence (published_at pgl27_prior_exact_published) R secretP.
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
    pgl27_word_proximity_cert carries. Both are read off pgl27_word_mixing, the
    one bound on the cut group's distance; the input-indistinguishability tail
    loses that bound at each of two hops, one per dealt secret, and the
    ideal-proximity proposition compares one law with one law. The relation is
    between these two certificates and not between the two security properties:
    cert_eps is by definition the walk's marginal number added to itself, and
    this proximity certificate chooses that same marginal number as its own
    field, which a proximity certificate over the same model and the same ideal
    is free not to do. *)
Lemma pgl27_word_proximity_eps_halfE (R : realType) (secretP : R.-fdist bool) :
  cert_eps (pgl27_word_cert secretP)
  = ipc_eps (pgl27_word_proximity_cert secretP)
    + ipc_eps (pgl27_word_proximity_cert secretP).
Proof. by []. Qed.

(** The certificate's number is at most 2^-39, the constant the word program
    publishes for input indistinguishability. It is the obligation of the
    terminal that concludes the proximity program at that constant, and the
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
(*     One model, two claims, two programs                                    *)
(******************************************************************************)

(** The word model certified for ideal proximity and concluded at 2^-39, the
    constant the input-indistinguishability program of the same model publishes
    and the one the published reading statement pgl27_word_view_proximity
    carries. The certificate's own number is 2^-40, half of that. Below four
    seats its distance field, pgl27_word_proximity_close, puts the joint law of
    a coalition's reading with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where the reading and the
    secret are independent outright, so the ideal side is the product of its two
    marginals. The proximity certificate's closeness field is one hop to the
    ideal, so that number is lost once, where the input-indistinguishability
    tail makes two hops. Its transfer status is IdealFinite, the same the
    input-indistinguishability program carries, and the two certificates compare
    against the same ideal cut. *)
Definition pgl27_word_proximity_published : PublishedAt pgl27_bound39 :=
  pgl27_word_sampled
    certify IdealProximity pgl27_word_proximity_cert
    |> conclude pgl27_bound39 by (fun R idx => pgl27_word_proximity_le39 idx)
    |> publish IdealFinite BaselineClassicalOnly.

(** The proximity program publishes the manifest's word path, as
    pgl27_word_published_pathE says of the word program. An AnalysisPath holds
    descriptive metadata and no Prop, so one manifest path published by an
    input-indistinguishability program and by a proximity program says nothing
    about either claim. *)
Lemma pgl27_word_proximity_published_pathE :
  published_path pgl27_word_proximity_published = pgl27_word_path.
Proof.
(* exact: erefl and not by []: done does not return on an equation between two
   paths' coordinates. *)
exact: erefl.
Qed.

(** The security property this program carries, at every real field and prior,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two readings of one model. *)
Lemma pgl27_word_proximity_published_propertyE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_word_proximity_published)) R) :
  security_property_of pgl27_word_proximity_published R idx
  = IdealProximityProperty.
Proof. by []. Qed.

(** Both programs over the word model read their analysis model family off the
    one named Tableau Sampled value, so the pair differs in the security
    property and in nothing about the algebra, the run or the law. The family
    is what a continuation of a named value reads off the name. *)
Lemma pgl27_word_published_families_sampledE :
  ab_f (published_at pgl27_word_proximity_published)
  = sp_f (tableau_at pgl27_word_sampled)
  /\ ab_f (published_at pgl27_word_branch_published39)
     = sp_f (tableau_at pgl27_word_sampled).
Proof. split; exact: erefl. Qed.

(** Both programs read their observed execution off that same named value, so
    the two claims are made about one run and one static observation of it and
    not about two executions that happen to agree. Together with the family
    equation above, everything the two programs hold in common comes from the
    one name. *)
Lemma pgl27_word_published_obs_sampledE :
  ab_obs (published_at pgl27_word_proximity_published)
  = sp_obs (tableau_at pgl27_word_sampled)
  /\ ab_obs (published_at pgl27_word_branch_published39)
     = sp_obs (tableau_at pgl27_word_sampled).
Proof.
(* Each program stated against the named value closes by exact: erefl in under
   0.01 s. The program-against-program form is the slow one, 96.0 s by
   exact: erefl and 48.1 s by reflexivity, and is not stated. *)
split; exact: erefl.
Qed.


(******************************************************************************)
(*     What the proximity program states at this instance                     *)
(******************************************************************************)

(** The proximity program's security statement at the eight-card orbit instance:
    at fewer than four colluding seats and at every prior on the dealt secret,
    the joint law of the executed coalition reading and that secret under the
    two-hundred-letter word walk is within 2^-39 of the product of the two
    marginals of the exact execution at the same prior. The proof is the
    program's security projection applied, so the program and this statement are
    one theorem. *)
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
exact: (view_proximity_of pgl27_word_proximity_published R secretP C HC).
Qed.

(******************************************************************************)
(*     The number a construction from pgl27_word_cert would carry             *)
(******************************************************************************)

(** The number pgl27_word_proximity_cert carries is the marginal bound
    pgl27_word_cert carries, the two-hundred-letter walk's 2^-40. A proximity
    certificate built from that input-indistinguishability certificate over
    this model would carry that same number. *)
Lemma pgl27_word_proximity_eps_sw_boundE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP)
  = sw_bound_eps (ic_b (pgl27_word_cert secretP)).
Proof. exact: erefl. Qed.
