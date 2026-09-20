(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* c_adapter: a sample adapter over the twelve-card fixed-dealer colour model *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Ledger row C1 of                *)
(* notes/probes/2026-09-21-psl211-colour-reader/LEDGER.md.                    *)
(*                                                                            *)
(* The colour theorems of instances/psl211/psl211_secrecy.v are read in       *)
(* psl211P, the law of a chirality bit drawn from a prior together with an    *)
(* independent uniform PSL(2,11) shuffle. A proposition of the Tableau is     *)
(* stated at a sample adapter, and psl211P carries none: it occurs in         *)
(* psl211_secrecy.v alone. This file builds one.                              *)
(*                                                                            *)
(* Which execution the adapter is over. psl211P's first coordinate is the     *)
(* chirality bit itself and the colour view reads the fixed encoder deck of   *)
(* that bit through the shuffle, so the run argument of the execution has to  *)
(* be the bit. Of the instance's two run modes that is the dealer-dealt one,  *)
(* psl211_dealt_params, whose run argument carrier is the algebra's secret    *)
(* carrier, bool. The all-decks mode does not fit: its run argument is a      *)
(* whole deck description and its law psl211_alldecksP redraws the deck, so   *)
(* the existing adapter psl211_alldecks_sample is over a different sample     *)
(* space and a different execution. The weighted-word family draws the cut    *)
(* from a walk and not uniformly. No existing family has psl211P as its law,  *)
(* which is why this row is construction rather than restatement.             *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_colour_sample == the fixed-dealer colour model as a sample        *)
(*                           adapter over the dealer-dealt execution          *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_colour_sample_lawE      == the adapter's law is psl211P           *)
(*   psl211_colour_sample_argE      == the run argument is the chirality bit  *)
(*   psl211_colour_sample_cutE      == the cut is the shuffle                 *)
(*   psl211_colour_sample_cut_distE == the cut law is uniform on the group    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     C1: the fixed-dealer colour model as a sample adapter                  *)
(******************************************************************************)

(** psl211_colour_inputTE — the run argument carrier of the dealer-dealt plug
    is the Boolean chirality, the first coordinate of a sample point of
    psl211P. The two layers therefore meet with no coercion between them. *)
Lemma psl211_colour_inputTE :
  ep_inputT (instance_exec psl211_dealt_params) = bool.
Proof. by []. Qed.

(** psl211_colour_sample — the fixed-dealer colour model as a sample adapter:
    one sample point is a chirality bit together with a cut, the bit drawn
    from the prior and the cut uniformly from PSL(2,11), the two independent;
    the run argument is the bit and the cut is the shuffle. It is the adapter
    every colour statement of psl211_secrecy.v is read at once that statement
    is made at a reader. *)
Definition psl211_colour_sample (R : realType) (secretP : R.-fdist bool)
  : SampleAdapter R (instance_exec psl211_dealt_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params)
    ((bool * pgg_gT psl211_M)%type : finType)
    (psl211P secretP) fst snd.

(** psl211_colour_sample_lawE — the adapter's law is the model's law. *)
Lemma psl211_colour_sample_lawE (R : realType) (secretP : R.-fdist bool) :
  sa_sampleP (psl211_colour_sample secretP) = psl211P secretP.
Proof. by []. Qed.

(** psl211_colour_sample_argE — the run argument of a sample point is its
    chirality bit. *)
Lemma psl211_colour_sample_argE (R : realType) (secretP : R.-fdist bool)
    (u : bool * pgg_gT psl211_M) :
  (psl211_colour_sample secretP).(sa_arg) u = u.1.
Proof. by []. Qed.

(** psl211_colour_sample_cutE — the cut of a sample point is its shuffle. *)
Lemma psl211_colour_sample_cutE (R : realType) (secretP : R.-fdist bool)
    (u : bool * pgg_gT psl211_M) :
  (psl211_colour_sample secretP).(sa_cut) u = u.2.
Proof. by []. Qed.

(** psl211_colour_sample_cut_distE — the cut this model draws is the uniform
    law on the shuffle group, whatever the prior on the chirality. Every
    proposition stated at a reader pushes the reader forward along this law,
    so it is the law the colour theorems' own uniformity hypothesis meets. *)
Lemma psl211_colour_sample_cut_distE (R : realType) (secretP : R.-fdist bool) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params) (psl211_colour_sample secretP)
  = (`U psl211_G_pos : R.-fdist (pgg_gT psl211_M)).
Proof.
have -> : @sa_cut_dist R (instance_profile psl211_algebra)
            (instance_exec psl211_dealt_params) (psl211_colour_sample secretP)
        = fdist_snd (psl211P secretP) by [].
apply/fdist_ext => g; rewrite fdist_sndE.
under eq_bigr do rewrite /psl211P fdist_prodE /=.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

Print Assumptions psl211_colour_sample_cut_distE.
