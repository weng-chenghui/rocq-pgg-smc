(* K4(e), the other half: the opening word itself, as a binder name in a
   file requiring the rule. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core k4e_kind_prefixed.

Set Implicit Arguments.
Unset Strict Implicit.

Definition k4e_opener_binder (obstruction : nat) : nat := obstruction.
