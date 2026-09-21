(* Item 1(a), the keyword question: in a file requiring the inline
   obstruction rule, which of the rule's alphabetic tokens is reserved.

   InputDistinguishability follows the literal Obstruction, which follows
   the literal publish, which follows the slot s.  Only publish's position
   is after a slot, and publish is reserved already.  Every use below is
   measured; a reserved token fails at parsing and Fail does not catch a
   parse error, so the outcome is the exit status. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import ssralg reals.
From surface2_mini Require Import k5_inline.

Set Implicit Arguments.
Unset Strict Implicit.

(* The kind's name, bare, as a top-level identifier and as a binder. *)
Definition InputDistinguishability : nat := 0.

Definition k5_kind_binder (InputDistinguishability : nat) : nat :=
  InputDistinguishability.

(* The two identifiers of the tree that share its prefix. *)
Definition InputDistinguishabilityPropAt (r : nat) (c : nat) : Prop :=
  (0 < r + c)%N = true.

Definition InputDistinguishabilityObstruction (r : nat) (c : nat) : nat :=
  r + c.

Definition k5_prefix_binder
    (InputDistinguishabilityPropAt : nat) : nat :=
  InputDistinguishabilityPropAt.

Definition k5_prefix_binder2
    (InputDistinguishabilityObstruction : nat) : nat :=
  InputDistinguishabilityObstruction.

(* The two level names of the other publish rules. *)
Definition k5_observed_binder (Observed : nat) : nat := Observed.
Definition k5_sampled_binder (Sampled : nat) : nat := Sampled.

(* The literal of the terminal itself. *)
Definition k5_obstruction_binder (Obstruction : nat) : nat := Obstruction.

Check InputDistinguishability.
Check InputDistinguishabilityPropAt.
Check InputDistinguishabilityObstruction.

(* The rule still parses beside all of them. *)
Definition k5_beside : Stage :=
  stage0 |> publish Obstruction InputDistinguishability of 3 at mini_number
            by false assuming BaselineClassicalOnly.
