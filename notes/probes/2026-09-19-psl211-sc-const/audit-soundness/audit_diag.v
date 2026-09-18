(* Soundness audit scratch, 2026-09-19. Diagnostic computations only. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The deck a description names, with the two labellings left out: this is
   psl211_alldecks_seq at identity labellings, written without inord so that
   vm_compute never meets an ordinal constructor. *)
Definition audit_deck (x : psl211_inputT) : seq nat :=
  let H := psl211_alldecks_row x in
  let K := psl211_alldecks_corow x in
  [seq (if p \in H then index p H else 6 + index p K) | p <- iota 0 12].

(* The triple of codes that seats 0, 1 and 2 read, one per tabulated cut. *)
Definition audit_readings (x : psl211_inputT) : seq (nat * nat * nat) :=
  let sq := audit_deck x in
  [seq (nth 0 sq (nth 0 t 0), nth 0 sq (nth 0 t 1), nth 0 sq (nth 0 t 2))
  | t <- unzip1 psl211_elem_table].

(* The L1 distance of the two multiplicity vectors, in units of one cut. Over
   660 cuts the variation distance of the two pushforward laws is this number
   divided by 660. *)
Definition audit_l1gap (l1 l2 : seq (nat * nat * nat)) : nat :=
  foldr (fun v acc =>
           acc + (count (pred1 v) l1 - count (pred1 v) l2)
               + (count (pred1 v) l2 - count (pred1 v) l1))%N 0%N
        (undup (l1 ++ l2)).

Definition audit_d0 : psl211_deal := (ord0, 1%g, 1%g).
Definition audit_d1 : psl211_deal := (@Ordinal 132 1 isT, 1%g, 1%g).

(* The recorded outputs of psl211_deck_diag.v, recomputed. *)
Eval vm_compute in psl211_alldecks_row (true, psl211_perdeck_deal).
Eval vm_compute in psl211_alldecks_row (false, psl211_perdeck_deal).
Eval vm_compute in psl211_rep_list true.
Eval vm_compute in psl211_rep_list false.
Eval vm_compute in psl211_perdeck_seq true.
Eval vm_compute in psl211_perdeck_seq false.

(* audit_deck agrees with the probe's psl211_perdeck_seq at the identity
   labellings, so the readings below are the readings of the real decks. *)
Eval vm_compute in audit_deck (true, psl211_perdeck_deal).
Eval vm_compute in audit_deck (false, psl211_perdeck_deal).
Eval vm_compute in audit_deck (true, audit_d1).

(* How many distinct readings the 660 cuts produce at one deck. *)
Eval vm_compute in size (undup (audit_readings (true, audit_d0))).

(* D1: the two chiralities at the SAME deck description, the probe's
   counterexample pair. *)
Eval vm_compute in
  audit_l1gap (audit_readings (true, audit_d0))
              (audit_readings (false, audit_d0)).

(* D2: two deck descriptions of the SAME chirality. A nonzero value here means
   the constancy field already fails between two run arguments carrying the
   same secret. *)
Eval vm_compute in
  audit_l1gap (audit_readings (true, audit_d0))
              (audit_readings (true, audit_d1)).
