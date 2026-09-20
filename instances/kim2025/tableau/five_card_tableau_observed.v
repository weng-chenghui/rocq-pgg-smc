(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_tableau_observed: the five-card instance at the Observed level   *)
(*                                                                            *)
(* The Observed level adjoins the three run facts to the run parameters, and  *)
(* it is the first level at which a program proves anything. What it carries  *)
(* is run correctness: the interpreter finishes within fuel 100, each of the  *)
(* five seats reaches an endpoint, and the endpoints decode to the            *)
(* conjunction of the two committed bits. Nothing about a coalition is proved *)
(* at this level, at any coalition size.                                      *)
(*                                                                            *)
(* One run reaches this level and one value names it. five_card_committed is  *)
(* the prefix all seven published programs and the three named Sampled values *)
(* of the instance continue from, and it names its three obligations, each an *)
(* existing lemma of five_card_exec.v.                                        *)
(*                                                                            *)
(* The ideal functionality sits here for the same reason. five_card_F is      *)
(* typed over five_card_observed, the execution this level reaches, and       *)
(* realises_expected is an equation between the value that execution names as *)
(* the one to recover and the functionality's function. Neither mentions a    *)
(* coalition and neither mentions a probability model. five_card_FE reads off *)
(* the two values a reader of five_card_F wants, the conjunction and the      *)
(* tolerated coalition size of one seat, and targeted_F takes that size from  *)
(* the scheme rather than from the program.                                   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_committed     == the prefix all seven programs share           *)
(*   five_card_F             == the ideal functionality the run realises      *)
(*   five_card_F_ite         == the ideal function is its conditional         *)
(*                              spelling, up to conversion                    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_committed_paramsE                                              *)
(*                           == the prefix drives the run five_card_params    *)
(*                              names                                         *)
(*   five_card_committed_executableE                                          *)
(*                           == the prefix is its Executable value with the   *)
(*                              three run facts adjoined                      *)
(*   five_card_FE            == that functionality is the conjunction at one  *)
(*                              tolerated seat                                *)
(*   five_card_realises_expected                                              *)
(*                           == the value the run is meant to recover is the  *)
(*                              functionality's                               *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import order ssrnum ssralg reals boolp.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_exec.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_tableau_algebraic.
From pgg_smc Require Import five_card_tableau_executable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(******************************************************************************)
(*     The prefix all seven programs share                                    *)
(******************************************************************************)

(** The first three statements of the five-card program: the algebra with the
    ideal function a run of it computes, the run driven in the encoded-run
    mode at fuel 100, and the three run facts. What has been proved at this
    point is run correctness, that the interpreter finishes, collects one
    endpoint per seat and decodes them to the conjunction of the two
    committed bits, and nothing about a coalition. *)
Definition five_card_committed : Tableau Observed :=
  five_card_algebra functionality (fun ab : bool * bool => ab.1 && ab.2)
  encoded inputs (bool * bool)
          layout den_boer_layout
          by den_boer_assemble_valid
          decoded_by den_boer_decode
          committed_by five_card_commits
          fuel 100
  execute terminates by five_card_terminates
          endpoints by five_card_endpoints
          recon by five_card_recon.

(** The run the prefix builds is the one five_card_params names. The clauses
    above spell the parameter record out a second time, and this equation is
    what keeps the two spellings from parting: every statement below is made
    at five_card_params, and the program is made at the clauses. *)
Lemma five_card_committed_paramsE :
  projT1 (projT2 (tableau_at five_card_committed)) = five_card_params.
Proof. by []. Qed.

(** The committed program is its own Executable value with the three run
    facts adjoined. The program above writes the algebra, the ideal function
    and the run clauses in one term, the Executable file names the
    parameters they build, and this equation is what lets a statement made
    at that named value be read as a statement about the prefix. *)
Lemma five_card_committed_executableE :
  (five_card_committed_executable
     execute terminates by five_card_terminates
             endpoints by five_card_endpoints
             recon by five_card_recon) = five_card_committed.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     The ideal functionality                                                *)
(******************************************************************************)

(** The functionality the five-card run realises: the conjunction of the two
    committed bits, tolerating a coalition of one seat. The tolerated size is
    not chosen here but read off the algebra's scheme by targeted_F, which is
    what makes the specification a consequence of the instance rather than a
    second description of it that could disagree with the first. *)
Definition five_card_F
    : Functionality (oe_inputT five_card_observed) (oe_outT five_card_observed)
  := targeted_F five_card_target.

(** The ideal function and the tolerated coalition size of this instance,
    written out. Both are read off the target and the algebra, so this
    equation is where a reader of five_card_F learns which two values they
    are. *)
Lemma five_card_FE :
  five_card_F = MkFunctionality (fun ab : bool * bool => ab.1 && ab.2) 1.
Proof. by []. Qed.

(** The ideal function is checked up to conversion and not up to spelling: the
    conditional form of the conjunction names the same function. *)
Definition five_card_F_ite
  : fn_f five_card_F = (fun ab : bool * bool => if ab.1 then ab.2 else false)
  := erefl.

(** The value the run is built to recover is that functionality's function, as
    terms. Conversion decides it, so this correspondence needs no funext and
    carries no extensionality axiom of its own; a specification agreeing with
    the recovered value only pointwise would close through funext instead, and
    the difference would be visible in Print Assumptions. *)
Lemma five_card_realises_expected :
  realises_expected five_card_observed five_card_F.
Proof. by []. Qed.
