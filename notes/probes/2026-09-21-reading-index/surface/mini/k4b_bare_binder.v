(* K4(b), the keyword question, first half: the bare leading token as a
   binder name in a file requiring the notation. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core k4b_kind.

Set Implicit Arguments.
Unset Strict Implicit.

Definition k4b_bare_binder (InputDistinguishability : nat) : nat :=
  InputDistinguishability.
