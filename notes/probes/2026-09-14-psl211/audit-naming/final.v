(* Audit probe: both planned lemmas proved with the exact imports of
   notes/probes/2026-09-14-psl211/probe_bridge.v. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Section fibres.
Variables (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N).
Variable T : finType.

Lemma uniform_fdistmap_fibre_ratio (f : X -> T) (v : T) :
  fdistmap f (`U HA) v = #|[set x in A | f x == v]|%:R / #|A|%:R :> R.
Proof.
rewrite fdistmapE (bigID (fun x : X => x \in A)) /=.
rewrite [in X in _ + X]big1 ?addr0; last first.
  by move=> x /andP[_ xA]; rewrite fdist_uniform_supp_notin.
rewrite (eq_bigr (fun=> (#|A|%:R^-1 : R))); last first.
  by move=> x /andP[_ xA]; rewrite fdist_uniform_supp_in.
rewrite sumr_const.
have -> : #|(fun i : X => (i \in preim f (pred1 v)) && (i \in A))|
        = #|[set x in A | f x == v]|.
  by apply: eq_card => x; rewrite !inE /= andbC.
by rewrite mulr_natl.
Qed.

Lemma uniform_fdistmap_of_fibres (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA) = fdistmap f1 (`U HA) :> R.-fdist T.
Proof.
by move=> Hfib; apply/fdist_ext => v; rewrite !uniform_fdistmap_fibre_ratio Hfib.
Qed.

End fibres.

Section fibre_of_orbit.
Variables (gT : finGroupType) (G : {group gT}).
Local Open Scope group_scope.  (* NOT open in probe_bridge.v: see finding T1-d *)

(* planned statement, verbatim (unused S kept) *)
Lemma orbit_fibre_card (S : {set {set 'I_12}}) (to : action G {set 'I_12})
    (x y : {set 'I_12}) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof.
by case/orbitP=> a Ga <-;
   rewrite -[[set g in G | to x g == to x a]]/(amove to G x (to x a))
           (amove_act to x (subxx _) Ga) card_rcoset.
Qed.

(* the same fact stated in mathcomp's own vocabulary, any carrier *)
Lemma amove_card (rT : finType) (to : action G rT) (x y : rT) :
  y \in orbit to G x -> #|amove to G x y| = #|'C_G[x | to]|.
Proof. by case/orbitP=> a Ga <-; rewrite (amove_act to x (subxx _) Ga) card_rcoset. Qed.

End fibre_of_orbit.

Print Assumptions uniform_fdistmap_of_fibres.
Print Assumptions orbit_fibre_card.
Print Assumptions amove_card.
