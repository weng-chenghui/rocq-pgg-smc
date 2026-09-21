(* K4(b), the near-token question: the surface already has an identifier
   two letters away from the token the kind's rule would reserve, the
   security-property name InputIndistinguishability.  This file checks that
   it stays an identifier while InputDistinguishability is a keyword, so
   that the ledger can say whether the two tokens end up with different
   grammatical status. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core k4b_kind.

Set Implicit Arguments.
Unset Strict Implicit.

Definition InputIndistinguishability : nat := 0.

Definition k4b_near_binder (InputIndistinguishability : nat) : nat :=
  InputIndistinguishability.

Check InputIndistinguishability.
