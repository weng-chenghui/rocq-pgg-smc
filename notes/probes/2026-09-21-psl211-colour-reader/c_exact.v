(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* c_exact: exact independence at the colour reader, and the sharpness of     *)
(*          its threshold                                                     *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Ledger rows C4 and C5 of        *)
(* notes/probes/2026-09-21-psl211-colour-reader/LEDGER.md.                    *)
(*                                                                            *)
(* The two colour theorems of instances/psl211/psl211_secrecy.v, restated at  *)
(* the reader interface over the adapter of c_adapter.v. The mathematics is   *)
(* the cited theorems' and none is added here: what the restatement supplies  *)
(* is the identification of the model's colour view with the reader's value,  *)
(* psl211_colour_reader_funE, and the identification of the instance's        *)
(* five-position threshold with the framework's, the derived profile          *)
(* declaring six.                                                             *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_colour_reader_exact == exact independence at the colour reader,   *)
(*                                 below the framework's threshold            *)
(*   psl211_leak_coalition_not_below_k                                        *)
(*                              == the leak coalition is not below it         *)
(*   psl211_colour_reader_dep_at_threshold                                    *)
(*                              == at that coalition and at a prior giving    *)
(*                                 mass to both chiralities the reader's      *)
(*                                 value is not independent of the secret     *)
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
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From readersprobe Require Import r_framework.
From colourprobe Require Import c_adapter c_reader.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     C4: exact independence at the colour reader                            *)
(******************************************************************************)

(** psl211_colour_reader_exact — below the framework's privacy threshold the
    colour reader's value is independent of the dealt chirality, under every
    prior on the chirality. It is psl211_colour_view_indep of
    instances/psl211/psl211_secrecy.v read at the reader: the same theorem,
    the same model, the same coalitions, and no new mathematics. The
    thresholds meet on the nose, the instance's counting argument reaching
    five of the twelve positions and the derived profile declaring six. The
    statement is an independence and not a numeric bound, so the entropy
    forms the framework derives from an exact-independence witness are
    available at it. *)
Lemma psl211_colour_reader_exact (R : realType) (secretP : R.-fdist bool) :
  ReaderExactPropAt (psl211_colour_sample secretP) psl211_colour_reader
    (psl211_secret secretP).
Proof.
move=> C HC.
have HC5 : (#|C| <= 5)%N by rewrite -ltnS -profile_k_psl211_algebra; exact: HC.
by rewrite -psl211_colour_reader_funE; exact: psl211_colour_view_indep HC5.
Qed.


(******************************************************************************)
(*     C5: the threshold is sharp, stated at the reader                       *)
(******************************************************************************)

(** psl211_leak_coalition_not_below_k — the six positions of the mirror
    representative are not below the framework's threshold, so the coalition
    at which the next lemma refutes independence is outside the range
    psl211_colour_reader_exact covers. Without this the two statements would
    contradict each other rather than bound each other. *)
Lemma psl211_leak_coalition_not_below_k :
  ~~ (#|psl211_leak_coalition| < profile_k (instance_profile psl211_algebra))%N.
Proof. by rewrite psl211_leak_coalition_card6 profile_k_psl211_algebra. Qed.

(** psl211_colour_reader_dep_at_threshold — at the six positions of the mirror
    representative, and at a prior giving mass to both chiralities, the colour
    reader's value is not independent of the dealt chirality; that coalition
    has exactly as many positions as the framework's threshold declares. It is
    psl211_colour_view_dep_k6 read at the reader. Together with
    psl211_colour_reader_exact it says that the threshold of the proposition
    at this reader is the largest one: one position past it, independence
    already fails, and it fails at a coalition that is a block of one of the
    two Steiner systems. The two positivity premises are part of the
    mathematics: at a prior supported on one chirality the secret is almost
    surely constant and every reader is independent of it. *)
Lemma psl211_colour_reader_dep_at_threshold (R : realType)
    (secretP : R.-fdist bool) :
  secretP true != 0 -> secretP false != 0 ->
  (#|psl211_leak_coalition| = profile_k (instance_profile psl211_algebra))%N /\
  ~ sa_sampleP (psl211_colour_sample secretP)
      |= (fun u => sr_read psl211_colour_reader psl211_leak_coalition
                     ((psl211_colour_sample secretP).(sa_arg) u)
                     ((psl211_colour_sample secretP).(sa_cut) u))
         _|_ psl211_secret secretP.
Proof.
move=> Ht Hf; have [Hcard Hdep] := psl211_colour_view_dep_k6 secretP Ht Hf.
split; first by rewrite Hcard profile_k_psl211_algebra.
by rewrite -psl211_colour_reader_funE; exact: Hdep.
Qed.

Print Assumptions psl211_colour_reader_exact.
Print Assumptions psl211_colour_reader_dep_at_threshold.
