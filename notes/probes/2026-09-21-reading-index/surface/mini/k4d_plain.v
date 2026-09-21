(* K4(d) of the claim ledger: the obstruction kind with no notation at all,
   as a plain application of the constructor.

   This is the baseline the two notations are priced against.  It reserves
   nothing, so the leading token and every identifier sharing its prefix
   stay free, and it is measured here so that the comparison names a
   measured alternative and not an assumed one.  What it gives up is the
   reading of the term: the two arguments are positional, so which one is
   the reading and which the number is read off the constructor's type and
   not off the text. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core.

Set Implicit Arguments.
Unset Strict Implicit.

Definition k4d_kind_example : ObstructionKind :=
  InputDistinguishabilityObstruction 1 2.

Definition InputDistinguishability : nat := 0.

Definition k4d_bare_binder (InputDistinguishability : nat) : nat :=
  InputDistinguishability.

Definition k4d_slotfirst_binder (distinguishable : nat) : nat :=
  distinguishable.
