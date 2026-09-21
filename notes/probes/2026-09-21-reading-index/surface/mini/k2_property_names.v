(* K2 of the claim ledger: the three security-property names after the
   literal certify reserve nothing, before and after the by is added.

   The file is compiled twice from this one text, with the two load paths of
   ./_CoqProject: once without the staged roots, so that pgg_tableau_syntax
   is production's, and once with them.  pgg_tableau is required beside the
   surface because the surface file imports it and does not export it, so
   the three names are in scope only when the statement file requires it
   too, which is what every instance file does.

   Each name is checked twice: as a global reference and as a binder name.
   A name that had become a global keyword fails at parsing, which Fail does
   not catch, so the outcome is read off the exit status and the message. *)

From mathcomp Require Import ssreflect.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.

Check ExactIndependence.
Check InputIndistinguishability.
Check IdealProximity.

Definition k2_binder_exact (ExactIndependence : nat) : nat :=
  ExactIndependence.

Definition k2_binder_indistinguishability
    (InputIndistinguishability : nat) : nat :=
  InputIndistinguishability.

Definition k2_binder_proximity (IdealProximity : nat) : nat :=
  IdealProximity.
