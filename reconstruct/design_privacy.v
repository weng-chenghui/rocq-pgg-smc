(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Design Privacy Bridge                                                 *)
(*                                                                            *)
(* A coalition whose observation has the same fiber cardinalities over the   *)
(* shuffle group under the two secrets observes a law independent of the      *)
(* secret. This is the sibling of the transitivity bridge                     *)
(* (transitivity_privacy.v): same sample space, same conclusion, a counting   *)
(* premise in place of t-transitivity. A t-transitive group satisfies the     *)
(* counting premise for every t-design orbit, so the transitivity bridge is   *)
(* the special case; the counting premise also holds for orbits that are     *)
(* t-designs of a group that is not t-transitive, which is the PSL(2,11)      *)
(* twelve-card instance.                                                      *)
(*                                                                            *)
(* Section 1 -- uniform_fdistmap_fiberE == equal fibers over a uniform law    *)
(*   give equal pushforwards.                                                 *)
(* Section 2 -- colour_view, colour_law, colour_view_indep_laws,              *)
(*   colour_view_indep_fibers == independence of the colour observer.         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Section fibers.
Variables (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N).
Variable T : finType.

(** uniform_fdistmap_fiberE — two maps with equal fiber cardinalities on A
    push the uniform law on A to the same law. *)
Lemma uniform_fdistmap_fiberE (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA).
Proof.
move=> Hfib; apply/fdist_ext => v; rewrite !fdistmapE.
have key (f : X -> T) :
    \sum_(x in X | x \in f @^-1 v) (`U HA) x
    = (#|A|%:R)^-1 *+ #|[set x in A | f x == v]| :> R.
  rewrite -sumr_const big_mkcond [RHS]big_mkcond /=.
  apply: eq_bigr => x _; rewrite !inE /=.
  case: (f x == v); last by rewrite andbF.
  rewrite andbT; case: ifPn => xA.
    by rewrite fdist_uniform_supp_in.
  by rewrite fdist_uniform_supp_notin.
by rewrite !key Hfib.
Qed.

End fibers.

Section colour_view.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : gT -> {perm 'I_N'.+1}.
Variables (R : realType) (secretP : R.-fdist bool).
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.
Variable colour : 'I_N'.+1 -> bool.

Let P := secretP `x (`U card_G_gt0).

(** colour_view C — what a coalition C sees when cards of one colour are
    indistinguishable: the colour of the card dealt to each of its
    positions, false outside C. The observer of the physical deck model. *)
Definition colour_view (C : {set 'I_N'.+1}) :
    {RV P -> {ffun 'I_N'.+1 -> bool}} :=
  fun u => [ffun i => if i \in C
                      then colour (tnth (encode u.1) (rho u.2 i)) else false].

(** colour_law C b — the law of the colour view given the secret b. *)
Definition colour_law (C : {set 'I_N'.+1}) (b : bool) :
    R.-fdist {ffun 'I_N'.+1 -> bool} :=
  fdistmap (fun g => colour_view C (b, g)) (`U card_G_gt0).

(** colour_view_indep_laws — equal conditional laws under the two secrets
    give independence of the colour view from the dealt secret. *)
Lemma colour_view_indep_laws (C : {set 'I_N'.+1}) :
  colour_law C true = colour_law C false ->
  P |= colour_view C _|_ (@dealt_secret gT G R secretP card_G_gt0).
Proof.
move=> Hlaw.
apply: (@inde_prod_fst R bool gT secretP (`U card_G_gt0) _
  (colour_view C) (colour_law C false)) => b.
by case: b; first exact: Hlaw.
Qed.

(** colour_view_indep_fibers — the same from equal fiber counts of the two
    encodings, the form a table certificate delivers. *)
Lemma colour_view_indep_fibers (C : {set 'I_N'.+1}) :
  (forall v : {ffun 'I_N'.+1 -> bool},
     #|[set g in G | colour_view C (true, g) == v]|
     = #|[set g in G | colour_view C (false, g) == v]|) ->
  P |= colour_view C _|_ (@dealt_secret gT G R secretP card_G_gt0).
Proof.
move=> Hfib; apply: colour_view_indep_laws.
exact: (uniform_fdistmap_fiberE _ _ Hfib).
Qed.

End colour_view.
