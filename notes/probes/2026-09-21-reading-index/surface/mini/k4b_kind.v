(* K4(b) of the claim ledger: an obstruction kind written as a notation
   whose first token is the kind's name.

   The clause of r names what is read and at c the number, which is the one
   preposition per meaning the spec decides on.  The token
   InputDistinguishability opens the rule, so it follows no slot; of and at
   follow slots, and both are keywords already, of from ssreflect and the
   bind, at from Rocq itself.  Whether the leading token is reserved all the
   same is measured by the three files requiring this one. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core.

Set Implicit Arguments.
Unset Strict Implicit.

Notation "'InputDistinguishability' 'of' r 'at' c" :=
  (InputDistinguishabilityObstruction r c)
  (at level 10, r at level 0, c at level 0).

Definition k4b_kind_example : ObstructionKind :=
  InputDistinguishability of 1 at 2.

Lemma k4b_kind_exampleE :
  k4b_kind_example = InputDistinguishabilityObstruction 1 2.
Proof. exact: erefl. Qed.
