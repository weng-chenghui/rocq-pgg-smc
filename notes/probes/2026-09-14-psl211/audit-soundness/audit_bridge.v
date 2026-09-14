(* audit_bridge: adversarial counter-probes for ledger rows L8, L10, L12 of
   the PSL(2,11) chirality spec.  Compile with
     sh run.sh audit-soundness/audit_bridge.v
   from notes/probes/2026-09-14-psl211. *)

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

(* ------------------------------------------------------------------ L8 --- *)
Section fibres.
Variables (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N).
Variable T : finType.

(* (a) The statement exactly as probe_bridge.v line 35-37 writes it does not
   elaborate: `U HA leaves the realType argument of fdist_uniform_supp free
   and nothing in the equation pins it. *)
Fail Lemma uniform_fdistmap_of_fibres_asWritten (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA) = fdistmap f1 (`U HA).

(* (b) With R pinned on one side the statement elaborates and is true. *)
Lemma fibre_mass (f : X -> T) (v : T) :
  fdistmap f (`U HA : R.-fdist X) v
  = #|[set x in A | f x == v]|%:R * #|A|%:R^-1.
Proof.
rewrite fdistmapE (bigID (fun x => x \in A)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  by move=> x /andP[_ xNA]; exact: fdist_uniform_supp_notin.
rewrite (eq_bigr (fun _ => (#|A|%:R^-1 : R))); last first.
  by move=> x /andP[_ xA]; exact: fdist_uniform_supp_in.
rewrite big_const iter_addr addr0 -[_ *+ _]mulr_natl.
congr (_%:R * _); apply: eq_card => x.
by rewrite !inE /= andbC.
Qed.

Lemma uniform_fdistmap_of_fibres (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA : R.-fdist X).
Proof. by move=> Hf; apply/fdist_ext => v; rewrite !fibre_mass Hf. Qed.

End fibres.

(* ----------------------------------------------------------------- L10 --- *)
(* (a) probe_bridge.v states L10 under fdist/proba/ring scopes only, with no
   group_scope open, so the stabiliser notation has no interpretation. *)
Section L10_as_written.
Variables (gT : finGroupType) (G : {group gT}).
Fail Lemma orbit_fibre_card_asWritten (S : {set {set 'I_12}})
    (to : action G {set 'I_12}) (x y : {set 'I_12}) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
End L10_as_written.

Local Open Scope group_scope.

(* (b) probe_bridge.v also types the action as `action G _`, i.e. an action
   whose DOMAIN is G.  The action the spec needs it at, 'P^*, is a total
   action (domain [set: {perm 'I_12}]), so it cannot be supplied for that
   argument unless the group is the whole symmetric group. *)
Section L10_domain_mismatch.
Variable G : {group {perm 'I_12}}.
Fail Check (fun (to : action G {set 'I_12}) => to) ('P^*)%act.
(* the total-action form does accept it *)
Check (fun (to : {action {perm 'I_12} &-> {set 'I_12}}) => to) ('P^*)%act.
End L10_domain_mismatch.

(* (c) With group_scope open and the action total, the statement elaborates
   and is true. *)
Section fibre_of_orbit.
Variables (gT : finGroupType) (rT : finType).
Variable to : {action gT &-> rT}.
Variable G : {group gT}.

(** orbit_fibre_card - the elements of G carrying x to a point y of its orbit
    form a right coset of the stabiliser of x, so every fibre of the action
    map g |-> to x g over the orbit has the stabiliser's cardinality.  This is
    what turns a count of blocks into a count of group elements. *)
Lemma orbit_fibre_card (x y : rT) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof.
case/orbitP => g0 g0G <-.
have -> : [set g in G | to x g == to x g0] = 'C_G[x | to] :* g0.
  apply/setP => g; apply/idP/idP.
    rewrite inE => /andP[gG /eqP Hg].
    rewrite mem_rcoset inE groupM ?groupV //=.
    by apply/astab1P; rewrite actM Hg actK.
  move=> Hin; rewrite inE.
  move: Hin; rewrite mem_rcoset inE => /andP[Hm /astab1P Hc].
  have gG : g \in G by rewrite -(groupMr _ (groupVr g0G)) Hm.
  rewrite gG /=; apply/eqP.
  move: Hc; rewrite actM => Hc.
  by have := congr1 (fun z => to z g0) Hc; rewrite actKV.
by rewrite card_rcoset.
Qed.

(** orbit_fibre_uniform - every fibre over the orbit has the same size, so a
    count of orbit points with a given property and a count of group elements
    producing it differ by the single factor #|G| / #|orbit|.  This is the
    step that makes "(number of blocks with pattern A) / 132" the law of the
    colour view. *)
Lemma orbit_fibre_const (x y z : rT) :
  y \in orbit to G x -> z \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|[set g in G | to x g == z]|.
Proof. by move=> Hy Hz; rewrite (orbit_fibre_card Hy) (orbit_fibre_card Hz). Qed.

End fibre_of_orbit.

(* ----------------------------------------------------------------- L12 --- *)
(* The miniature of probe_bridge.v lines 143-154 is FALSE as stated: the toy
   pair SA = {0,1}, SB = {0,2} does not have equal one-point counts, and both
   disjuncts of the existential force (i \in SA) = (i \in SB), which fails at
   i = 1. *)
Section redeal_miniature_refuted.

Local Definition SA : {set 'I_4} := [set x | (val x < 2)%N].
Local Definition SB : {set 'I_4} := [set x | (val x == 0) || (val x == 2)].

Lemma redeal_mini_false :
  ~ (forall i : 'I_4,
       exists S' : {set 'I_4},
         (S' == SB) && ((i \in S') == (i \in SA)) \/
         (S' == SA) && ((i \in S') == (i \in SB))).
Proof.
move=> H; have [S' []] := H (@Ordinal 4 1 isT);
  by case/andP => /eqP ->; rewrite /SA /SB !inE /=.
Qed.

(* And the toy tables really do not have equal 1-point counts, so the
   miniature's own premise ("sharing the point pattern counts for every
   1-coalition") is false too. *)
Lemma toy_counts_differ : (@Ordinal 4 1 isT \in SA) != (@Ordinal 4 1 isT \in SB).
Proof. by rewrite /SA /SB !inE. Qed.

End redeal_miniature_refuted.

(* The shape the spec actually needs, stated on an abstract class family:
   equal intersection patterns give the existential re-deal.  This is the
   content the miniature was meant to exercise. *)
Section redeal_shape.
Variables (n : nat) (clsA clsB : {set {set 'I_n}}).
Hypothesis pattern_match :
  forall (C : {set 'I_n}) (H : {set 'I_n}),
    (#|C| <= 5)%N -> H \in clsA -> exists H', H' \in clsB /\ H' :&: C = H :&: C.

Lemma redeal_pattern (C : {set 'I_n}) (H : {set 'I_n}) :
  (#|C| <= 5)%N -> H \in clsA ->
  exists H', H' \in clsB /\ forall i, i \in C -> (i \in H') = (i \in H).
Proof.
move=> HC HA; have [H' [H'B Heq]] := pattern_match HC HA.
exists H'; split => // i iC.
by move: (congr1 (fun S : {set 'I_n} => i \in S) Heq); rewrite !inE iC !andbT.
Qed.

End redeal_shape.
