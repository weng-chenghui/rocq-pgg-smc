(* K1 of the claim ledger: whether assuming is a global keyword.

   The file is compiled twice from this one text, with the two load paths of
   ./_CoqProject: once without the staged roots, so that pgg_tableau_syntax
   is production's and the token assuming appears in no notation, and once
   with them, so that it is the staged surface where assuming follows the
   slot t of publish t assuming a.  The Require lines are ssreflect and the
   surface alone, which is how the keyword measurements quoted in the header
   of pgg_tableau_syntax.v were taken.

   A token that has become a global keyword fails here at parsing, which Fail
   does not catch, so the two outcomes are read off the exit status and the
   message and not off a Fail. *)

From mathcomp Require Import ssreflect.
From pgg_smc Require Import pgg_tableau_syntax.

(* assuming as a binder name. *)
Definition k1_assuming_binder (assuming : nat) : nat := assuming.

(* assuming as a top-level identifier. *)
Definition assuming : nat := 0.

Check k1_assuming_binder.
Check assuming.
