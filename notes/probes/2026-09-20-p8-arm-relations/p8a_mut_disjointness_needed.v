(* P8 arm-relations probe, mutation check for A1: the disjointness of the     *)
(* two supports is what gives the value two, and without it the equation is   *)
(* refutable at a law and itself.                                             *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(** A1 with its disjointness hypothesis dropped is false: a law is at no
    distance from itself, and zero is not two. *)
Lemma var_dist_eq2_unconditional_false (R : realType) :
  ~ (forall (A : finType) (P Q : R.-fdist A), var_dist P Q = 2%:R).
Proof.
move=> H.
have H0 : var_dist (fdist1 true : R.-fdist bool) (fdist1 true) = 0.
  by rewrite /var_dist big1 // => a _; rewrite subrr normr0.
move: (H bool (fdist1 true) (fdist1 true)); rewrite H0 => /esym /eqP.
by rewrite pnatr_eq0.
Qed.
