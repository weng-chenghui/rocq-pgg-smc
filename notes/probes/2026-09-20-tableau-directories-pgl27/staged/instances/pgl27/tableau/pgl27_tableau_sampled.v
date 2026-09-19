(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_tableau_sampled: the eight-card orbit instance at the Sampled level  *)
(*                                                                            *)
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the run argument and the cut. That identification is what turns a     *)
(* claim about the messages a run exchanges into a claim about a group        *)
(* action, and it is the last thing proved before an arm is named.            *)
(*                                                                            *)
(* Three families are named here, one per model a published row continues     *)
(* from, and all three sit over the one dealer-dealt run. The exact family    *)
(* draws the cut uniformly from PGL(2,7) at the uniform secret, and its index *)
(* is the unit type. The word family draws the cut by evaluating a sampled    *)
(* two-hundred-letter generator word, and its index is a distribution on the  *)
(* booleans, the law of the dealt secret. The prior-indexed exact family      *)
(* draws the cut uniformly at that same law of the secret. The index types    *)
(* are what separate the unit-indexed exact family from the other two, and    *)
(* they separate two families and not two models: the exact family and the    *)
(* prior-indexed exact family draw the same uniform cut, and differ in        *)
(* whether the law of the secret is fixed at the uniform one or carried as an *)
(* index.                                                                     *)
(*                                                                            *)
(* pgl27_word_sampled is a name the instance already had, and the two rows    *)
(* over the word model are written from it. The other two values are named    *)
(* the same way so that a row over any of the three models can be continued   *)
(* from a name rather than from the prefix.                                   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_exact_sampled     == the dealer-dealt run under the uniform cut at *)
(*                              the uniform secret                            *)
(*   pgl27_word_sampled      == the word model named at Sampled, before any   *)
(*                              arm is chosen                                 *)
(*   pgl27_prior_exact_sampled                                                *)
(*                           == the dealer-dealt run under the uniform cut at *)
(*                              every law of the secret                       *)
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
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_observed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(******************************************************************************)
(*     The exact shuffle at the uniform secret                                *)
(******************************************************************************)

(** The dealer-dealt run under the exact shuffle, named at Sampled. The
    family is indexed by the unit type, so one member at each real field,
    and that member fixes the uniform law of the dealt secret. The cut it
    draws is already the uniform one on PGL(2,7), so a row over this model
    compares no finite walk with an ideal. *)
Definition pgl27_exact_sampled : Tableau Sampled :=
  pgl27_dealt sample pgl27_exact_family.


(******************************************************************************)
(*     The word model as a branch point, under an input-indistinguishability  *)
(* payload                                                                    *)
(******************************************************************************)

(* payload                                                                    *)
(** The word model of PGL(2,7), named at Sampled. Its family is indexed by a
    distribution on the booleans, so a continuation here unifies a payload
    whose type mentions both the real field and that index. *)
Definition pgl27_word_sampled : Tableau Sampled :=
  pgl27_dealt sample pgl27_word_family.


(******************************************************************************)
(*     The exact shuffle at every law of the secret                           *)
(******************************************************************************)

(** The dealer-dealt run under the exact shuffle read at every law of the
    dealt secret, named at Sampled. Its family is indexed by a distribution
    on the booleans, the same index the word family carries, which is what
    lets a proximity certificate read the two models at one index. *)
Definition pgl27_prior_exact_sampled : Tableau Sampled :=
  pgl27_dealt sample pgl27_prior_exact_family.
