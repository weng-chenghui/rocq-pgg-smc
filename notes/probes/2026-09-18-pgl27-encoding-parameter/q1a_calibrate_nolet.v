(* PROBE Q1a (task P0): cost calibration, WITHOUT a let binding.
   One r5 collision number, the source's own shape of pgl27_collisions:
     count (fun v => v \in code_views false S) (code_views true S)
   where the predicate body recomputes the 336-row view list per element. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From pgg_smc Require Import pgl27_leakage_census.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition views_nolet (deal : bool -> seq nat) (b : bool) (S : seq nat) :
    seq (seq nat) :=
  [seq code_restrict S (code_comp t (deal b)) | t <- pgl27_group_table].

Definition collisions_nolet (deal : bool -> seq nat) (S : seq nat) : nat :=
  count (fun v => v \in views_nolet deal false S) (views_nolet deal true S).

Definition code_tau_r5 : seq nat := [:: 0; 1; 2; 4; 3; 5; 7; 6].
Definition deal_r5 (b : bool) : seq nat := if b then code_tau_r5 else code_id.

Lemma q1a_r5_harmonic : collisions_nolet deal_r5 rep_harmonic = 48.
Proof. by vm_compute. Qed.
