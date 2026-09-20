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
(* action, and it is the last thing proved before the certify statement.      *)
(*                                                                            *)
(* One family is named here, the uniform tape model over the supplied run.    *)
(* Its cut is the identity, so no shuffle enters what a coalition reads and   *)
(* the four shares a coalition of four seats holds are four independent       *)
(* uniform values.                                                            *)
(*                                                                            *)
(* The instance's other model, the finite word over the four adjacent         *)
(* transpositions, is not named at this level. It is a model of the           *)
(* dealer-dealt run, and the manifest's path over it, s5_word_path, is        *)
(* justified by a mixing theorem and by no program: two of the five parts of  *)
(* an input-indistinguishability certificate over that model are out of       *)
(* reach. Missing is the distance from the walk to an ideal cut, a variation  *)
(* distance on the shuffle group that s5_word_base_premise names as a premise *)
(* nothing in the tree proves, the instance's spectral theorem bounding one   *)
(* seat's endpoint marginal on 'I_5 instead. Missing too, and for a reason no *)
(* proof can remove, is the constancy of a coalition's reading of the ideal   *)
(* cut in the secret, which the certificate's constancy field asks for at     *)
(* every coalition below the threshold and so at every singleton: under every *)
(* cut exactly one seat holds the card carrying the whole secret, so that     *)
(* seat's reading law moves with the secret, and no choice of ideal avoids    *)
(* it, the seat in question varying with the cut while the ideal is fixed     *)
(* before any coalition is named. What the manifest names for that path is an *)
(* endpoint marginal bound against the encoder-image ideal, with no claim     *)
(* about a coalition. That bound is stated here as s5_word_seat_marginal, a   *)
(* one-seat marginal bound of manifest/pgg_tableau_marginal_bounds.v: it      *)
(* mentions no coalition, no second run argument and no secret, and it is not *)
(* security evidence.                                                         *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_rand_sampled      == the supplied run under the uniform tape model    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_word_seat_marginal                                                    *)
(*                        == one seat's executed endpoint law under the word  *)
(*                           model, as a one-seat marginal bound              *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From infotheo Require Import fdist proba.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import s5_exec s5_mixing s5_models.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_marginal_bounds.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The uniform tape model                                                 *)
(******************************************************************************)

(** The supplied run under the uniform tape model, named at Sampled. The family
    is indexed by the unit type, so one member at each real field, and its cut
    is the identity: what a coalition reads is decided by how the shares were
    drawn and not by how the deck was shuffled. The value is what
    s5_rand_published_sampledE continues, so the program and the model are named
    apart. *)
Definition s5_rand_sampled : Tableau Sampled :=
  s5_supplied sample s5_rand_family.

(******************************************************************************)
(*     The word model's one-seat marginal bound                               *)
(******************************************************************************)

(** One seat's executed endpoint under the finite word model sits within the
    square root of five times alpha to the L of the encoder-image law, as a
    one-seat marginal bound. The ideal law is neither uniform nor independent
    of the secret, so the number bounds the distance to one named law and no
    coalition, privacy or secrecy conclusion follows from it. The number is a
    sum of absolute differences, twice the total variation distance of the
    literature, so a distinguisher separating the two laws has advantage at
    most half of it. It is s5_exec_endpoint_bound of instances/s5/s5_models.v
    stated as the proposition, and it carries that theorem's assumption, the
    group-order axiom s5_group_order_eq of the instance's rigidity module. *)
Lemma s5_word_seat_marginal (R : realType) (secretP : R.-fdist 'I_5)
    (L : nat)
    (i : 'I_(pi_T' (mp_PI (instance_profile s5_algebra))).+1) :
  @SeatMarginalPropAt R s5_algebra s5_dealt_params
    (s5_word_sample secretP L) i (s5_ideal_reading secretP)
    (Num.sqrt 5%:R * (s5_alpha_R R) ^+ L).
Proof. exact: (s5_exec_endpoint_bound secretP L i). Qed.
