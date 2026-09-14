(* audit-naming scratch: isolate WHY probe_bridge.v's L10 statement does not
   elaborate under its own preamble -- scope, or the `action G` domain. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section probe_bridge_preamble.
Variables (gT : finGroupType) (G : {group gT}).

(* (a) exactly probe_bridge.v:60-63. *)
Fail Lemma a_probe_verbatim (S : {set {set 'I_12}})
    (to : action G {set 'I_12}) (x y : {set 'I_12}) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.

(* (b) the same with only the stabiliser dropped: does `action G` itself
   elaborate without GroupScope? *)
Lemma b_no_stabiliser (to : action G {set 'I_12}) (x y : {set 'I_12}) :
  y \in orbit to G x -> #|[set g in G | to x g == y]| = #|[set g in G | to x g == y]|.
Proof. by []. Qed.

(* (c) the stabiliser alone, no GroupScope. *)
Fail Check fun (to : action G {set 'I_12}) (x : {set 'I_12}) =>
  #|'C_G[x | to]|.

End probe_bridge_preamble.

Import GroupScope.

Section with_group_scope.
Variables (gT : finGroupType) (G : {group gT}).

(* (d) the probe statement verbatim, only `Import GroupScope.` added:
   it now elaborates, so the sole defect in probe_bridge.v:60-63 is the
   missing group scope. *)
Check (forall (S : {set {set 'I_12}}) (to : action G {set 'I_12})
              (x y : {set 'I_12}),
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|) : Prop.

(* And the transporter-set = stabiliser-coset fact, on a total action, is
   eight lines of action.v (see fibre.v).  Orbit-stabiliser itself is
   already named. *)
About card_orbit_stab.

End with_group_scope.
