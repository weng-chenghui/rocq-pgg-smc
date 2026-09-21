(* K4(b), the prefix question: two identifiers begin with the notation's
   leading token and must stay usable in a file requiring it.  Each is used
   as a global reference and as a binder name. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core k4b_kind.

Set Implicit Arguments.
Unset Strict Implicit.

Check InputDistinguishabilityPropAt.
Check InputDistinguishabilityObstruction.

Definition k4b_prefix_use (r : Reading) (c : nat) : Prop :=
  InputDistinguishabilityPropAt r c.

Definition k4b_prefix_binder
    (InputDistinguishabilityPropAt : nat) : nat :=
  InputDistinguishabilityPropAt.

Definition k4b_prefix_binder2
    (InputDistinguishabilityObstruction : nat) : nat :=
  InputDistinguishabilityObstruction.

(* The notation still parses beside the two identifiers. *)
Definition k4b_prefix_kind : ObstructionKind :=
  InputDistinguishability of 3 at 4.
