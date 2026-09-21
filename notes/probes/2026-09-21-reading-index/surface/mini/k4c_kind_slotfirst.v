(* K4(c) of the claim ledger: the same obstruction kind written with the
   reading first, so that the rule opens with a slot.

   The alternative exists to price the leading token of K4(b).  Here the
   first literal, distinguishable, follows the slot r, which is the
   position the measurement quoted in the header of pgg_tableau_syntax.v
   says makes a token a global keyword.  What that costs is measured by
   k4c_slotfirst_binder.v and k4c_slotfirst_toplevel.v. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core.

Set Implicit Arguments.
Unset Strict Implicit.

Notation "r 'distinguishable' 'at' c" :=
  (InputDistinguishabilityObstruction r c)
  (at level 10, c at level 0).

Definition k4c_kind_example : ObstructionKind := 1 distinguishable at 2.

Lemma k4c_kind_exampleE :
  k4c_kind_example = InputDistinguishabilityObstruction 1 2.
Proof. exact: erefl. Qed.
