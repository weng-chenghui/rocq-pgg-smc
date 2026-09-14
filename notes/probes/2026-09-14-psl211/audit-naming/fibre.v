(* audit-naming scratch, two questions about probe_bridge.v L10
   (`orbit_fibre_card`):
   (1) does the statement even PARSE under probe_bridge.v's own preamble,
       which never imports GroupScope?
   (2) is the lemma a short consequence of mathcomp's action.v, and is its
       `S : {set {set 'I_12}}` argument used anywhere in the statement? *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* --- (1) probe_bridge.v's exact preamble, no `Import GroupScope`. --------- *)
Section parse_as_probe_bridge_does.
Variables (gT : finGroupType) (G : {group gT}).

Fail Lemma orbit_fibre_card_unscoped (S : {set {set 'I_12}})
    (to : action G {set 'I_12}) (x y : {set 'I_12}) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.

End parse_as_probe_bridge_does.

Import GroupScope.

(* --- (2) the lemma from action.v, `S` dropped. ---------------------------- *)
Section fibre.
Variables (gT : finGroupType) (sT : finType).

Lemma orbit_fibre_card (to : {action gT &-> sT}) (G : {group gT}) (x y : sT) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof.
case/orbitP => g0 g0G xg0.
have -> : [set g in G | to x g == y] = 'C_G[x | to] :* g0.
  apply/setP => g; rewrite inE mem_rcoset in_setI.
  have -> : (g * g0^-1 \in G) = (g \in G) by rewrite groupMr ?groupV.
  case: (g \in G) => //=.
  apply/idP/idP => [/eqP xg|/astab1P xgg]; first by
    apply/astab1P; rewrite actM xg -xg0 actK.
  by apply/eqP; rewrite -(mulgKV g0 g) actM xgg xg0.
exact: card_rcoset.
Qed.

(* The `S` of the probe statement is a dead argument: the same proof term
   discharges the statement with it present, which is what makes it
   invisible to a reader. *)
Lemma orbit_fibre_card_with_dead_S (S : {set {set 'I_12}})
    (to : {action gT &-> sT}) (G : {group gT}) (x y : sT) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof. exact: orbit_fibre_card. Qed.

End fibre.

(* Orbit-stabiliser, the lemma that must link a ROW count to an ELEMENT
   count, is already in action.v under this name. *)
About card_orbit_stab.
