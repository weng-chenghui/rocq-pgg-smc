(* Item 1(b), the keyword question at the staged surface rather than at the
   miniature: in a file whose Require lines are ssreflect, pgg_tableau and
   the staged surface, which of the inline terminal's alphabetic tokens is
   reserved.

   InputDistinguishability follows the literal Obstruction; Obstruction,
   Observed and Sampled each follow the literal publish; at, by and
   assuming are reserved already.  The framework's two identifiers sharing
   the kind's prefix are used as global references and as binder names.  A
   reserved token fails at parsing and Fail does not catch a parse error,
   so the outcome is the exit status. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.

Set Implicit Arguments.
Unset Strict Implicit.

Definition InputDistinguishability : nat := 0.

Definition k5s_kind_binder (InputDistinguishability : nat) : nat :=
  InputDistinguishability.

Definition k5s_obstruction_binder (Obstruction : nat) : nat := Obstruction.
Definition k5s_observed_binder (Observed : nat) : nat := Observed.
Definition k5s_sampled_binder (Sampled : nat) : nat := Sampled.

Check InputDistinguishability.
Check @InputDistinguishabilityPropAt.
Check @InputDistinguishabilityObstruction.
Check ExactIndependence.
Check InputIndistinguishability.
Check IdealProximity.
Check Observed.
Check Sampled.
