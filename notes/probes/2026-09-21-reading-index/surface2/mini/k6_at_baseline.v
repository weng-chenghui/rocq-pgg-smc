(* Item 2: whether at is reserved before the surface is required at all.

   If the token is already a keyword in a file whose only Require is
   ssreflect, then conclude at c by p reserves nothing new, and the same
   holds for at in the leaks clause and in the five-clause rule. *)

From mathcomp Require Import ssreflect.

Definition k6_at_binder (at : nat) : nat := at.
