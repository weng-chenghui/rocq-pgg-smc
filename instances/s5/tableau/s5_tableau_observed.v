(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_observed: the five-seat instance at the Observed level          *)
(*                                                                            *)
(* The Observed level adjoins the three run facts to the run parameters, and  *)
(* it is the first level at which a row proves anything. What it carries is   *)
(* run correctness: the interpreter finishes within the fuel, every seat      *)
(* reaches an endpoint, and the endpoints decode to the value the run was     *)
(* built to recover. Nothing about a coalition is proved at this level, at    *)
(* any coalition size, under either run mode.                                 *)
(*                                                                            *)
(* Both sharing-family runs of the instance reach this level, and each is     *)
(* named once. The dealer-dealt run's program stops here: the manifest row    *)
(* s5_det_path it answers carries no model and no security payload, because   *)
(* the canonical encoding it deals puts the whole secret on one card, so the  *)
(* single seat the cut sends that card to reads the secret, as does every     *)
(* coalition containing that seat. The manifest carries a second row over     *)
(* this run, s5_word_path, under a finite-word model; the Sampled file        *)
(* records why no program of this instance continues from that model. The     *)
(* supplied run continues, through the tape model of the level above.         *)
(*                                                                            *)
(* Each run's specification sits here too. A specification is an ideal        *)
(* function with a tolerated coalition size, and realising one is a statement *)
(* about the observed execution: the value the run recovers is that           *)
(* function's, as terms. Each realisation lemma is therefore a statement of   *)
(* this level, and neither depends on a probability model.                    *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_dealt             == the dealer-dealt run as a program                *)
(*   s5_supplied          == the supplied run as a program                    *)
(*   s5_F                 == the specification the dealer-dealt run realises  *)
(*   s5_rand_F            == the specification the supplied run realises      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_dealt_path_observedE                                                  *)
(*                        == the dealt program reaches the observed execution *)
(*                           the manifest's deterministic row describes       *)
(*   s5_dealt_executableE == the dealt program is its Executable value with   *)
(*                           the three run facts adjoined                     *)
(*   s5_supplied_paramsE  == the supplied program drives the run              *)
(*                           s5_supplied_params names                         *)
(*   s5_supplied_executableE                                                  *)
(*                        == the supplied program is its Executable value     *)
(*                           with the three run facts adjoined                *)
(*   s5_FE, s5_rand_FE    == the two specifications, written out              *)
(*   s5_F_thresholdE      == the coalition size the dealer-dealt run          *)
(*                           tolerates                                        *)
(*   s5_realises_expected, s5_rand_realises_expected                          *)
(*                        == each run recovers its specification's value      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import s5_exec.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_executable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The dealer-dealt run                                                   *)
(******************************************************************************)

(** The dealer-dealt run of the five-seat instance: the algebra, the secret
    position dealt at fuel 150, and the three run facts. What has been proved
    at this point is run correctness, that the interpreter finishes, collects
    one endpoint per seat and decodes them to the dealt position, and nothing
    about a coalition. This run has no privacy claim at any coalition size:
    the canonical encoding it deals puts the whole secret on one card, so the
    single seat the cut sends that card to reads the secret, and every
    coalition containing that seat does. *)
Definition s5_dealt : Tableau Observed :=
  s5_algebra
    dealt   fuel 150
    execute terminates by s5_dealt_terminates
            endpoints by s5_dealt_endpoints
            recon by s5_dealt_recon.

(** The observed execution this program reaches is the one the manifest's
    deterministic row describes. Conversion decides it, so the row's
    description of the run and the proof of run correctness for it are one
    term, which is the whole of what this path publishes. *)
Lemma s5_dealt_path_observedE :
  ob_obs (tableau_at s5_dealt) = ap_observed s5_det_path.
Proof. by []. Qed.

(** The dealer-dealt program is its own Executable value with the three run
    facts adjoined. The program above writes the algebra and the fuel in one
    line, the Executable file names the parameters they build, and this
    equation is what keeps a reader from having to decide which of the two
    spellings a statement below is made at. *)
Lemma s5_dealt_executableE :
  (s5_dealt_executable
     execute terminates by s5_dealt_terminates
             endpoints by s5_dealt_endpoints
             recon by s5_dealt_recon) = s5_dealt.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The supplied run                                                       *)
(******************************************************************************)

(** The supplied run of the five-seat instance: the algebra, the
    additive layout of a sampler tape at fuel 150, the value the run recovers
    written beside it, and the three run facts. The layout is supplied with
    the run argument and no party commits, so the value recovered is a
    reading of that argument rather than an ideal function of anyone's input;
    what has been proved at this point is run correctness and nothing about a
    coalition. *)
Definition s5_supplied : Tableau Observed :=
  s5_algebra
  supplied inputs 'rV['Z_5]_5
           layout s5_rfree_layout
           expecting (fun u => s5_codec (s5_tape_secret u))
           fuel 150
  execute terminates by s5_supplied_terminates
          endpoints by s5_supplied_endpoints
          recon by s5_supplied_recon.

(** The run the program builds is the one s5_supplied_params names. The
    clauses above spell the parameter record out a second time, and this
    equation is what keeps the two spellings from parting: every statement
    below is made at s5_supplied_params, and the row is made at the
    clauses. *)
Lemma s5_supplied_paramsE :
  projT1 (projT2 (tableau_at s5_supplied)) = s5_supplied_params.
Proof. by []. Qed.

(** The supplied program is its own Executable value with the three run
    facts adjoined, in the same sense as the dealer-dealt case. *)
Lemma s5_supplied_executableE :
  (s5_supplied_executable
     execute terminates by s5_supplied_terminates
             endpoints by s5_supplied_endpoints
             recon by s5_supplied_recon) = s5_supplied.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The two specifications                                                 *)
(******************************************************************************)

(** The specification the dealer-dealt run realises: the identity on the
    dealt position, tolerating coalitions of up to four seats. Neither
    component is chosen here. Both are read off the algebra by
    algebra_functionality, which is what makes the specification a
    consequence of the instance rather than a second description of it that
    could disagree with the first. *)
Definition s5_F : Functionality (oe_inputT s5_observed) (oe_outT s5_observed)
  := algebra_functionality s5_algebra.

(** The ideal function and the tolerated coalition size of the dealer-dealt
    run, written out. Both are read off the algebra, so this equation is
    where a reader of s5_F learns which two values the algebra yields. *)
Lemma s5_FE : s5_F = MkFunctionality id 4.
Proof. by []. Qed.

(** The tolerated size alone, as the scheme's own threshold less one. Four is
    the largest coalition the sum-mod scheme guarantees anything about, and
    no part of the execution narrows or widens it. *)
Lemma s5_F_thresholdE : fn_threshold s5_F = 4.
Proof. by []. Qed.

(** The value the dealer-dealt run is built to recover is that
    specification's function, as terms. Conversion decides it, so this
    correspondence needs no funext and carries no extensionality axiom of its
    own; a specification agreeing with the recovered value only pointwise
    would close through funext instead, and the difference would be visible
    in Print Assumptions. *)
Lemma s5_realises_expected : realises_expected s5_observed s5_F.
Proof. by []. Qed.

(** The specification the supplied run realises: the tape's secret coordinate
    carried through the codec, tolerating coalitions of up to four seats. The
    record is written out rather than taken from a functionality statement,
    because a sharing family names no ideal function: the value recovered is
    a reading of the run's own argument and not a function of any committer's
    input, so there is nothing here a run could fail to meet. Only the
    tolerated size is read off the algebra. *)
Definition s5_rand_F
  : Functionality (oe_inputT s5_rand_observed) (oe_outT s5_rand_observed) :=
  MkFunctionality (fun u => s5_codec (s5_tape_secret u))
    (ts_k' (pga_scheme s5_algebra)).

(** That specification's two components, written out: coordinate zero of the
    tape carried through the codec, and the same four seats the dealer-dealt
    specification tolerates. *)
Lemma s5_rand_FE :
  s5_rand_F = MkFunctionality (fun u => s5_codec (s5_tape_secret u)) 4.
Proof. by []. Qed.

(** The value the supplied run is built to recover is that specification's
    function, as terms, on the same reading of conversion as the
    dealer-dealt case. *)
Lemma s5_rand_realises_expected :
  realises_expected s5_rand_observed s5_rand_F.
Proof. by []. Qed.
