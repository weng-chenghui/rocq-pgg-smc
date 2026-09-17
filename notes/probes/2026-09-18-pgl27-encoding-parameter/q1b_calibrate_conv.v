(* PROBE Q1b (task P0): THIS FILE IS THE DIVERGENCE WITNESS AND DOES NOT
   COMPILE.  Do not add it to a build.

   Both agreement lemmas below are closed with "by []".  Compiling the file
   ran past 600 s of wall clock with no progress and was killed; q1c_conv_bisect
   then pinned it down to conv_views with a 30 s Timeout.  ssreflect's done
   does not find the delta-only path and drives conversion into the
   transparent 336-row closure pgl27_group_table.  The working route is
   "rewrite /gen_views /deal_r7 /code_views", which closes in under 0.01 s. *)

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

Lemma conv_views (b : bool) (S : seq nat) :
  gen_views deal_r7 b S = code_views b S.
Proof. by []. Qed.

Lemma conv_collisions (S : seq nat) :
  gen_collisions deal_r7 S = pgl27_collisions S.
Proof. by []. Qed.
