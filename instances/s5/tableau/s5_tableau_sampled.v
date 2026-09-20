(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_sampled: the five-seat instance at the Sampled level            *)
(*                                                                            *)
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the run argument and the cut. That identification is what turns a     *)
(* claim about the messages a run exchanges into a claim about a group        *)
(* action, and it is the last thing proved before an arm is named.            *)
(*                                                                            *)
(* One family is named here, the uniform tape model over the supplied run.    *)
(* Its cut is the identity, so no shuffle enters what a coalition reads and   *)
(* the four shares a coalition of four seats holds are four independent       *)
(* uniform values.                                                            *)
(*                                                                            *)
(* The instance's other model, the finite word over the four adjacent         *)
(* transpositions, is not named at this level. It is a model of the           *)
(* dealer-dealt run, and the manifest's row over it, s5_row_word, is          *)
(* published from a mixing theorem rather than from a program: two of the     *)
(* five parts of an input-indistinguishability certificate over that model    *)
(* are out of reach. Missing is the distance from the walk to an ideal cut, a *)
(* variation distance on the shuffle group that s5_word_base_premise names as *)
(* a premise nothing in the tree proves, the instance's spectral theorem      *)
(* bounding one seat's endpoint marginal on 'I_5 instead. Missing too, and    *)
(* for a reason no proof can remove, is the constancy of a coalition's        *)
(* reading of the ideal cut in the secret, which the certificate's constancy  *)
(* field asks for at every coalition below the threshold and so at every      *)
(* singleton: under every cut exactly one seat holds the card carrying the    *)
(* whole secret, so that seat's reading law moves with the secret, and no     *)
(* choice of ideal avoids it, the seat in question varying with the cut while *)
(* the ideal is fixed before any coalition is named. What the manifest        *)
(* publishes for that path is an endpoint marginal bound against the          *)
(* encoder-image ideal, with no claim about a coalition.                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_rand_sampled      == the supplied run under the uniform tape model    *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From infotheo Require Import fdist proba.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The uniform tape model                                                 *)
(******************************************************************************)

(** The supplied run under the uniform tape model, named at Sampled. The
    family is indexed by the unit type, so one member at each real field, and
    its cut is the identity: what a coalition reads is decided by how the
    shares were drawn and not by how the deck was shuffled. The value is what
    s5_row_rand_sampledE continues, so the row and the model are named
    apart. *)
Definition s5_rand_sampled : Tableau Sampled :=
  s5_supplied sample s5_rand_family.
