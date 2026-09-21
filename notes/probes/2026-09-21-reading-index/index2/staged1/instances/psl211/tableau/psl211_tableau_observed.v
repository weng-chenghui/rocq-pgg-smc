(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_observed: the twelve-card instance at the Observed level    *)
(*                                                                            *)
(* The Observed level adjoins the three run facts to the run parameters, and  *)
(* it is the first level at which a program proves anything. What it carries  *)
(* is run correctness: the interpreter finishes within the fuel of 220 steps, *)
(* every one of the twelve seats reaches an endpoint, and the endpoints       *)
(* decode to the chirality bit the run was built to recover. Nothing about a  *)
(* coalition is proved at this level, at any coalition size.                  *)
(*                                                                            *)
(* One run reaches this level and three values name it.                       *)
(* psl211_alldecks_prefix is the one both published programs of the instance  *)
(* continue from, and it names its termination proof. The other two write     *)
(* that proof a different way, and they are here because the difference they  *)
(* make is a fact about the tree and not about the mathematics: an opaque     *)
(* termination lemma is convertible with nothing, so a prefix that builds its *)
(* own obligation reaches a second observed execution, and every value typed  *)
(* against the first would have to be built again over it. The checks file    *)
(* records the two terms the kernel refuses that make the fork visible.       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_alldecks_prefix  == the algebra, the supplied-layout run and the  *)
(*                              three run facts                               *)
(*   psl211_alldecks_prefix_vm                                                *)
(*                           == the prefix with the termination reduction     *)
(*                              written inline                                *)
(*   psl211_alldecks_prefix_lit                                               *)
(*                           == the prefix with the fuel written as a         *)
(*                              literal                                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_alldecks_executableE                                              *)
(*                           == the prefix is its Executable value with the   *)
(*                              three run facts adjoined                      *)
(*   psl211_alldecks_prefix_vm_paramsE                                        *)
(*                           == the inline prefix drives the same run         *)
(*   psl211_alldecks_prefix_lit_paramsE                                       *)
(*                           == and so does the literal fuel                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From pgg_smc Require Import smc_interpreter pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_tableau_executable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The prefix of the all-decks program                                    *)
(******************************************************************************)

(** psl211_alldecks_prefix — the first three statements of the all-decks
    program: the algebra, the run driven in the supplied-layout mode at the
    instance's fuel, and the three run facts. What has been proved at this point
    is run correctness and nothing about a coalition. *)
Definition psl211_alldecks_prefix : Tableau Observed :=
  psl211_algebra
    supplied inputs psl211_inputT
             layout psl211_alldecks_layout
             expecting psl211_alldecks_expected
             fuel psl211_fuel
    execute terminates by psl211_alldecks_terminates
            endpoints by psl211_alldecks_endpoints
            recon by psl211_alldecks_recon.

(** psl211_alldecks_executableE — the prefix is its own Executable value with
    the three run facts adjoined. The prefix writes the algebra and the run
    clauses in one line and the Executable file names the parameters they
    build, so this equation is what keeps a reader from having to decide
    which of the two spellings a statement below is made at. *)
Lemma psl211_alldecks_executableE :
  (psl211_alldecks_executable
     execute terminates by psl211_alldecks_terminates
             endpoints by psl211_alldecks_endpoints
             recon by psl211_alldecks_recon) = psl211_alldecks_prefix.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The same prefix through the literal reduction                          *)
(******************************************************************************)

(** psl211_alldecks_prefix_vm — the prefix again, with the termination
    obligation built where the statement is written instead of named. The
    proposition proved is the one psl211_alldecks_prefix proves and the run is
    the same run, but the term is not psl211_alldecks_terminates, and an opaque
    lemma is convertible with nothing; so the observed execution this prefix
    reaches is a second value, equal to psl211_alldecks_observed only up to the
    irrelevance of an obligation. Everything typed against
    psl211_alldecks_observed, the instance's model first of all, would have to
    be built again over it, which is why no program is written here. *)
Definition psl211_alldecks_prefix_vm : Tableau Observed :=
  psl211_algebra
    supplied inputs psl211_inputT
             layout psl211_alldecks_layout
             expecting psl211_alldecks_expected
             fuel psl211_fuel
    execute terminates by vm_compute
            endpoints by psl211_alldecks_endpoints
            recon by psl211_alldecks_recon.

(** psl211_alldecks_prefix_vm_paramsE — the inline-reduction prefix drives the
    same run as the named one. The run parameters carry no proof, so the two
    prefixes fork only in the three run facts and in the value that packages
    them. *)
Lemma psl211_alldecks_prefix_vm_paramsE :
  projT1 (projT2 (tableau_at psl211_alldecks_prefix_vm))
  = psl211_alldecks_params.
Proof. by []. Qed.

(** psl211_alldecks_prefix_lit — the prefix once more, with the interpreter
    fuel written as the literal 220 rather than named. *)
Definition psl211_alldecks_prefix_lit : Tableau Observed :=
  psl211_algebra
    supplied inputs psl211_inputT
             layout psl211_alldecks_layout
             expecting psl211_alldecks_expected
             fuel 220
    execute terminates by psl211_alldecks_terminates
            endpoints by psl211_alldecks_endpoints
            recon by psl211_alldecks_recon.

(** psl211_alldecks_prefix_lit_paramsE — the prefix written with the fuel
    literal drives the same run, so fuel 220 and fuel psl211_fuel name one run.
    The program names the fuel, so that it is stated once. *)
Lemma psl211_alldecks_prefix_lit_paramsE :
  projT1 (projT2 (tableau_at psl211_alldecks_prefix_lit))
  = psl211_alldecks_params.
Proof. by []. Qed.
