(* K1 of the claim ledger, second half: assuming as a top-level identifier.

   A parse error stops the file, so the binder test of k1_assuming.v never
   reaches the top-level test below it.  This file carries the top-level use
   alone and is compiled twice from this one text, before and after, the way
   k1_assuming.v is. *)

From mathcomp Require Import ssreflect.
From pgg_smc Require Import pgg_tableau_syntax.

Definition assuming : nat := 0.

Check assuming.
