(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_sampled: the twelve-card instance at the Sampled level      *)
(*                                                                            *)
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the layout and the cut. That identification is what turns a claim     *)
(* about the messages a run exchanges into a claim about a group action, and  *)
(* it is the last thing proved before an arm is named.                        *)
(*                                                                            *)
(* This is where the instance branches. Both models run the one all-decks     *)
(* execution over one sample space, decks times cuts, and they differ in the  *)
(* law of the cut alone. The exact model draws the cut uniformly over the 660 *)
(* elements of the group; the word model draws it as a shuffle of 584         *)
(* letters. A distance between the two laws is therefore a distance between   *)
(* two members of this level, which is the shape the proximity arm compares,  *)
(* and it is the reason the two rows of the instance part here and not lower. *)
(* The deck description is drawn uniformly in both.                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_exact_sampled == the all-decks run under the uniform cut          *)
(*   psl211_word_sampled  == the all-decks run under the 584-letter word cut  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_word_model.
From pgg_smc Require Import psl211_tableau_observed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The uniform cut                                                        *)
(******************************************************************************)

(** The all-decks run under the exact model, named at Sampled. The family is
    indexed by the unit type, so one member at each real field, and its cut
    is uniform over the shuffle group. This is the model the exact arm is
    certified over, and the one a word row is measured against: an execution
    whose own privacy below the six-seat threshold is a theorem rather than a
    number. The value is what psl211_row_alldecks_sampledE continues, so the
    row and the model are named apart. *)
Definition psl211_exact_sampled : Tableau Sampled :=
  psl211_alldecks_prefix sample psl211_exact_family.

(******************************************************************************)
(*     The 584-letter word cut                                                *)
(******************************************************************************)

(** The all-decks run under the word model, named at Sampled. The cut is the
    product of 584 letters drawn from the instance's generators, where the
    model above draws it uniformly from the group, and the deck description
    and the execution are the same in both. A row over this model publishes a
    distance to the model above rather than an independence, because the
    finite word leaves the cut short of uniform by an amount the mixing
    theorem bounds. The value is what psl211_row_word_proximity_sampledE
    continues. *)
Definition psl211_word_sampled : Tableau Sampled :=
  psl211_alldecks_prefix sample psl211_word_family.
