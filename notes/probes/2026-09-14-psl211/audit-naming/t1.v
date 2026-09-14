From mathcomp Require Import all_ssreflect all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope group_scope.

Section fibre_of_orbit.
Variables (gT : finGroupType) (G : {group gT}).

(* candidate A: one line, using amove_act + card_rcoset *)
Lemma orbit_fibre_card (S : {set {set 'I_12}}) (to : action G {set 'I_12})
    (x y : {set 'I_12}) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof.
case/orbitP=> a Ga <-.
have -> : [set g in G | to x g == to x a] = amove to G x (to x a) by [].
by rewrite (amove_act to x (subxx _) Ga) card_rcoset.
Qed.

(* candidate B: fully general rT, no unused S, stated as amove *)
Lemma amove_card (rT : finType) (to : action G rT) (x y : rT) :
  y \in orbit to G x -> #|amove to G x y| = #|'C_G[x | to]|.
Proof. by case/orbitP=> a Ga <-; rewrite (amove_act to x (subxx _) Ga) card_rcoset. Qed.

End fibre_of_orbit.
Print Assumptions orbit_fibre_card.
Print Assumptions amove_card.
