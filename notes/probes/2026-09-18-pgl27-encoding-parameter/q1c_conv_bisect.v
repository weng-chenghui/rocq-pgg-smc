(* PROBE Q1c (task P0): bisect the convertibility bomb found in q1b.

   Result A1 (recorded, then removed so the file compiles): the statement
     Lemma conv_views_by (b : bool) (S : seq nat) :
       gen_views deal_r7 b S = code_views b S.
     Proof. Timeout 30 by []. Qed.
   FAILS with "Timeout!" at 30 s.  ssreflect's done does not find the
   delta-only path; it drives conversion into the 336-row table closure.

   A2/A4 below are the routes that do work. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From pgg_smc Require Import pgl27_leakage_census.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition gen_views (deal : bool -> seq nat) (b : bool) (S : seq nat) :
    seq (seq nat) :=
  [seq code_restrict S (code_comp t (deal b)) | t <- pgl27_group_table].

Definition gen_collisions (deal : bool -> seq nat) (S : seq nat) : nat :=
  count (fun v => v \in gen_views deal false S) (gen_views deal true S).

Definition deal_r7 : bool -> seq nat := code_deal.

(* A2: the delta-only route for the views agreement. *)
Lemma conv_views_delta (b : bool) (S : seq nat) :
  gen_views deal_r7 b S = code_views b S.
Proof. by rewrite /gen_views /deal_r7 /code_views. Qed.

(* A4: the collisions agreement, from A2 by congruence. *)
Lemma conv_collisions_delta (S : seq nat) :
  gen_collisions deal_r7 S = pgl27_collisions S.
Proof.
by rewrite /gen_collisions /pgl27_collisions !conv_views_delta.
Qed.
