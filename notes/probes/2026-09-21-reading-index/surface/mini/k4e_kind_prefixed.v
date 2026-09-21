(* K4(e) of the claim ledger: the same obstruction kind behind a generic
   opening word.

   K4(b) reserves the kind's own name, because the leading literal of a
   notation is reserved; K4(c) reserves the word after the leading slot.
   Here the rule opens with obstruction, so that word is reserved and
   InputDistinguishability follows a literal, which is the position the
   header of pgg_tableau_syntax.v records as leaving a token an identifier,
   as it does for ExactIndependence, InputIndistinguishability and
   IdealProximity after certify. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core.

Set Implicit Arguments.
Unset Strict Implicit.

Notation "'obstruction' 'InputDistinguishability' 'of' r 'at' c" :=
  (InputDistinguishabilityObstruction r c)
  (at level 10, r at level 0, c at level 0).

Definition k4e_kind_example : ObstructionKind :=
  obstruction InputDistinguishability of 1 at 2.

Lemma k4e_kind_exampleE :
  k4e_kind_example = InputDistinguishabilityObstruction 1 2.
Proof. exact: erefl. Qed.
