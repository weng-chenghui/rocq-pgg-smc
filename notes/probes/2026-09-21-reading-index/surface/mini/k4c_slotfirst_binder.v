(* K4(c), the keyword question: the literal that follows the slot, as a
   binder name in a file requiring the slot-first notation. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core k4c_kind_slotfirst.

Set Implicit Arguments.
Unset Strict Implicit.

Definition k4c_slotfirst_binder (distinguishable : nat) : nat :=
  distinguishable.
