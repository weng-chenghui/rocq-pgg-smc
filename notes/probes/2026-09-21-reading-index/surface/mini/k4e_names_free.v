(* K4(e), the keyword question: with the rule opened by obstruction, the
   kind's own name follows a literal.  Both are measured here, the kind's
   name as a binder and as a top-level identifier, and the opening word as
   a binder. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core k4e_kind_prefixed.

Set Implicit Arguments.
Unset Strict Implicit.

Definition InputDistinguishability : nat := 0.

Definition k4e_bare_binder (InputDistinguishability : nat) : nat :=
  InputDistinguishability.

Check InputDistinguishability.
Check InputDistinguishabilityPropAt.

(* The rule still parses beside them. *)
Definition k4e_kind_beside : ObstructionKind :=
  obstruction InputDistinguishability of 3 at 4.
