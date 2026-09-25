(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_verifolio_observed: the eight-card orbit instance at the Observed      *)
(* level                                                                      *)
(*                                                                            *)
(* The Observed level adjoins the three run facts to the run parameters, and  *)
(* it is the first level at which a program proves anything. What it carries  *)
(* is run correctness: the interpreter finishes within pgl27_fuel, each of    *)
(* the eight seats reaches an endpoint, and the endpoints decode to the orbit *)
(* class the run was built to recover. Nothing about a coalition is proved at *)
(* this level, at any coalition size.                                         *)
(*                                                                            *)
(* One run parameter record reaches this level and two values name it.        *)
(* pgl27_dealt is the one all seven published programs of the instance        *)
(* continue from, and it names its termination proof. pgl27_inline_dealt      *)
(* writes that proof a different way, and it is here because the difference   *)
(* it makes is a fact about the tree and not about the mathematics: an opaque *)
(* termination lemma is convertible with nothing, so a prefix that builds its *)
(* own obligation reaches a second observed execution, and every value typed  *)
(* against the first, the instance's three model families before anything     *)
(* else, would have to be built again over it. The checks file records the    *)
(* two terms the kernel refuses that make the fork visible.                   *)
(*                                                                            *)
(* The ideal functionality sits here for the same reason. pgl27_F is typed    *)
(* over pgl27_observed, the execution this level reaches, and                 *)
(* realises_expected is an equation between the value that execution names as *)
(* the one to recover and the functionality's function. Neither mentions a    *)
(* coalition and neither mentions a probability model.                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_dealt             == the prefix all seven programs share           *)
(*   pgl27_inline_dealt      == the prefix with the termination reduction     *)
(*                              written inline                                *)
(*   pgl27_F                 == the ideal functionality the run realises      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_dealt_executableE == the prefix is its Executable value with the   *)
(*                              three run facts adjoined                      *)
(*   pgl27_inline_paramsE    == the inline prefix builds the same run         *)
(*   pgl27_FE                == that functionality is the identity at three   *)
(*   pgl27_realises_expected == the value the run is meant to recover is that *)
(*                              functionality's function                      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_verifolio.
From pgg_smc Require Import pgg_verifolio_syntax.
From pgg_smc Require Import pgl27_verifolio_executable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(******************************************************************************)
(*     The prefix all seven programs share                                    *)
(******************************************************************************)

(** The first three lines of every eight-card orbit program: the algebra, the
    secret dealt at pgl27_fuel, and the three run facts. Sequencing stops here
    because the two programs part at the next line, where each adjoins its own
    probability model; everything up to this point is common to both, and what
    has been proved at this point is run correctness and nothing about a
    coalition. *)
Definition pgl27_dealt : Verifolio Observed :=
  pgl27_algebra
    dealt   fuel pgl27_fuel
    execute terminates by pgl27_dealt_terminates
            endpoints by pgl27_dealt_endpoints
            recon by pgl27_dealt_recon.

(** The dealer-dealt program is its own Executable value with the three run
    facts adjoined. The program above writes the algebra and the fuel in one
    line, the Executable file names the parameters they build, and this
    equation is what keeps a reader from having to decide which of the two
    spellings a statement below is made at. *)
Lemma pgl27_dealt_executableE :
  (pgl27_dealt_executable
     execute terminates by pgl27_dealt_terminates
             endpoints by pgl27_dealt_endpoints
             recon by pgl27_dealt_recon) = pgl27_dealt.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     The same prefix through the literal reduction                          *)
(******************************************************************************)

(** The shared prefix again, with the termination obligation built where the
    statement is written instead of named. The proposition proved is the one
    pgl27_dealt proves and the run is the same run, but the term is not
    pgl27_dealt_terminates, and an opaque lemma is convertible with nothing; so
    the observed execution this prefix reaches is a second value, equal to
    pgl27_observed only up to the irrelevance of an obligation. Everything typed
    against pgl27_observed, the instance's models first of all, would have to be
    built again over it, which is why no program is written here. *)
Definition pgl27_inline_dealt : Verifolio Observed :=
  pgl27_algebra
    dealt   fuel pgl27_fuel
    execute terminates by vm_compute
            endpoints by pgl27_dealt_endpoints
            recon by pgl27_dealt_recon.

(** They do build the same run. The run parameters carry no proof, so the fork
    is confined to the three run facts and the value they package. *)
Lemma pgl27_inline_paramsE :
  projT1 (projT2 (verifolio_at pgl27_inline_dealt)) = pgl27_dealt_params.
Proof. by []. Qed.


(******************************************************************************)
(*     The ideal functionality                                                *)
(******************************************************************************)

(** The functionality the eight-card orbit run realises: the identity on the
    dealer's secret, tolerating coalitions of up to three seats. Neither
    component is chosen here. Both are read off the algebra by
    algebra_functionality, which is what makes the specification a consequence
    of the instance rather than a second description of it that could disagree
    with the first. *)
Definition pgl27_F
    : Functionality (oe_inputT pgl27_observed) (oe_outT pgl27_observed) :=
  algebra_functionality pgl27_algebra.

(** The ideal function and the tolerated coalition size of this instance,
    written out. Both are read off the algebra, so this equation is where a
    reader of pgl27_F learns which two values the algebra yields. *)
Lemma pgl27_FE : pgl27_F = MkFunctionality id 3.
Proof. by []. Qed.

(** The value the run is built to recover is that functionality's function, as
    terms. Conversion decides it, so this correspondence needs no funext and
    carries no extensionality axiom of its own; a specification agreeing with
    the recovered value only pointwise would close through funext instead, and
    the difference would be visible in Print Assumptions. *)
Lemma pgl27_realises_expected : realises_expected pgl27_observed pgl27_F.
Proof. by []. Qed.
