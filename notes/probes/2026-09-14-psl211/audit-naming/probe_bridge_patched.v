(* probe_bridge: ledger rows L8, L9, L10, L12 of the PSL(2,11) spec.
   The new privacy bridge: equal fibre counts, not transitivity, give equal
   conditional laws and hence independence of the colour view.
   PROVER: replace every Admitted by a Qed; keep every statement. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------------ *)
(* L8: equal fibres over a uniform law give equal pushforwards.              *)
(* ------------------------------------------------------------------------ *)

Section fibres.
Variables (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N).
Variable T : finType.

(** uniform_fdistmap_of_fibres — two maps with equal fibre cardinalities on
    A push the uniform law on A to the same law. *)
Lemma uniform_fdistmap_of_fibres (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA) = fdistmap f1 (`U HA) :> R.-fdist T.
Proof.
move=> Hfib; apply/fdist_ext => v.
have key (f : X -> T) :
    fdistmap f (`U HA) v = #|[set x in A | f x == v]|%:R / #|A|%:R :> R.
  rewrite fdistmapE (bigID (fun x : X => x \in A)) /=.
  rewrite [in X in _ + X]big1 ?addr0; last first.
    by move=> x /andP[_ xA]; rewrite fdist_uniform_supp_notin.
  rewrite (eq_bigr (fun=> (#|A|%:R^-1 : R))); last first.
    by move=> x /andP[_ xA]; rewrite fdist_uniform_supp_in.
  rewrite sumr_const.
  have -> : #|(fun i : X => (i \in preim f (pred1 v)) && (i \in A))|
          = #|[set x in A | f x == v]| by apply: eq_card => x; rewrite !inE /= andbC.
  by rewrite mulr_natl.
by rewrite !key Hfib.
Qed.

End fibres.

(* Mutation: dropping the fibre hypothesis must not typecheck as a proof.
   (Checked by the prover as: `Fail` on a version with the premise removed
   is meaningless here; instead the tautology probe below.) *)

(* ------------------------------------------------------------------------ *)
(* L10: the fibre of the set action over an orbit point is a stabiliser     *)
(* coset, so its cardinality is that of the stabiliser.                      *)
(* ------------------------------------------------------------------------ *)

Section fibre_of_orbit.
Variables (gT : finGroupType) (G : {group gT}).
Local Open Scope group_scope.

(** orbit_fibre_card — for y in the orbit of x, the elements of G carrying
    x to y are a coset of the stabiliser of x. *)
Lemma orbit_fibre_card (S : {set {set 'I_12}}) (to : action G {set 'I_12})
    (x y : {set 'I_12}) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof.
by case/orbitP=> a Ga <-;
   rewrite -[[set g in G | to x g == to x a]]/(amove to G x (to x a))
           (amove_act to x (subxx _) Ga) card_rcoset.
Qed.

End fibre_of_orbit.

(* ------------------------------------------------------------------------ *)
(* L9: independence of a colour view from equal conditional laws, at the     *)
(* real carrier of transitivity_privacy.v.                                   *)
(* ------------------------------------------------------------------------ *)

Section colour_view.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : gT -> {perm 'I_N'.+1}.
Variables (R : realType) (secretP : R.-fdist bool).
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.
Variable colour : 'I_N'.+1 -> bool.

Let P := secretP `x (`U card_G_gt0).

(** colour_view — what a coalition C sees when cards of one colour are
    indistinguishable: the colour of the card dealt to each of its
    positions, false outside C. *)
Definition colour_view (C : {set 'I_N'.+1}) : {RV P -> {ffun 'I_N'.+1 -> bool}} :=
  fun u => [ffun i => if i \in C then colour (tnth (encode u.1) (rho u.2 i)) else false].

(* The conditional colour law given the secret b. *)
Definition colour_law (C : {set 'I_N'.+1}) (b : bool) :
    R.-fdist {ffun 'I_N'.+1 -> bool} :=
  fdistmap (fun g => colour_view C (b, g)) (`U card_G_gt0).

(** colour_view_indep_of_laws — equal conditional laws for the two secrets
    give independence of the colour view from the dealt secret. *)
Lemma colour_view_indep_of_laws (C : {set 'I_N'.+1}) :
  colour_law C true = colour_law C false ->
  P |= colour_view C _|_ (@dealt_secret gT G R secretP card_G_gt0).
Proof.
(* PROVER: apply: (@inde_prod_fst R bool gT secretP (`U card_G_gt0) _ _
   (colour_law C false)) => b; case: b => //. Check the exact statement shape
   of dealt_secret in transitivity_privacy.v and adjust the section
   variables (ttrans_view_indep_gen is the template). *)
Admitted.

(** colour_view_indep_of_fibres — the same from equal fibre counts of the
    two encodings, the form the table certificate delivers. *)
Lemma colour_view_indep_of_fibres (C : {set 'I_N'.+1}) :
  (forall v : {ffun 'I_N'.+1 -> bool},
     #|[set g in G | colour_view C (true, g) == v]|
     = #|[set g in G | colour_view C (false, g) == v]|) ->
  P |= colour_view C _|_ (@dealt_secret gT G R secretP card_G_gt0).
Proof.
move=> Hfib; apply: colour_view_indep_of_laws.
exact: (uniform_fdistmap_of_fibres _ _ Hfib).
Qed.

End colour_view.

(* Tautology probe: the law equality is not definitional. *)
Section tautology.
Variables (R : realType) (secretP : R.-fdist bool).
Hypothesis card_gt0 : (0 < #|[set: {perm 'I_12}]|)%N.
Variable encode : bool -> 12.-tuple 'I_12.
Fail Lemma taut (C : {set 'I_12}) :
  @colour_law 11 _ [set: {perm 'I_12}]%G id R secretP card_gt0 encode
      (fun c => (val c < 6)%N) C true
  = colour_law [set: {perm 'I_12}]%G id secretP card_gt0 encode (fun c => (val c < 6)%N) C false.
Proof. reflexivity. Qed.
End tautology.

(* ------------------------------------------------------------------------ *)
(* L12 miniature: from equal pattern counts to an existential re-deal, at    *)
(* coalition size <= 1 on a two-row toy table.                               *)
(* ------------------------------------------------------------------------ *)

Section redeal_miniature.
(* Toy: positions 'I_4, two "systems" each a single 2-subset, sharing the
   point pattern counts for every 1-coalition. *)
Local Definition SA : {set 'I_4} := [set x | (val x < 2)%N].
Local Definition SB : {set 'I_4} := [set x | (val x == 0) || (val x == 2)].

(** redeal_mini — a coalition of one position sees the same colour under a
    deck of class A and some deck of class B: constructive re-deal. *)
Lemma redeal_mini (i : 'I_4) :
  exists S' : {set 'I_4}, (S' == SB) && ((i \in S') == (i \in SA)) \/
                         (S' == SA) && ((i \in S') == (i \in SB)).
Proof.
(* PROVER: not the intended shape if trivial; the real shape is in
   probe_decomposition (psl211_private).  Prove by case on val i. *)
Admitted.

End redeal_miniature.
