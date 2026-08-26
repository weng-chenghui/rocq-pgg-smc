From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

Section test.
Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.
Let N := N'.+1.
Let G := pgg_G M.
Let rho := morphism.mfun (@pgg_rho M).
Let rhoG : {set {perm 'I_N}} := [set rho x | x in G].

Hypothesis HrhoG_pos : (0 < #|rhoG|)%N.
Hypothesis Hregular :
  forall s : 'I_N,
  {in rhoG &, injective (fun sigma : {perm 'I_N} => sigma s)}.

Let eval_at (s : 'I_N) : {perm 'I_N} -> 'I_N :=
  fun sigma => sigma s.

Let rho_uniform : R.-fdist {perm 'I_N} :=
  @fdist_uniform_supp R _ rhoG HrhoG_pos.

Let img (s : 'I_N) := (eval_at s) @: rhoG.

(* The orbit of card position s under rhoG, the image of s under every
   permutation in the representation's image group, is nonempty: it
   inherits a witness from rhoG itself being nonempty. *)
Lemma img_pos2 (s : 'I_N) : (0 < #|img s|)%N.
Proof.
rewrite card_gt0; apply/set0Pn.
have /card_gt0P [g Hg] := HrhoG_pos.
by exists (g s); apply/imsetP; exists g.
Qed.

(* Pushing the uniform law on rhoG forward through evaluation at card
   position s gives the uniform law on s's orbit, not merely a distribution
   supported there: under Hregular, evaluation at s is injective on rhoG,
   so the pushforward of a uniform source through an injection is exactly
   uniform on the image. This is the probabilistic form of a regular
   monodromy action's Item-3 guarantee (pgg_abelian_collapse.v): a
   coalition watching one card position under a regular action sees a
   perfectly uniform value over the reachable set, not merely a value
   pinning down the acting element. *)
Lemma test_pushforward (s : 'I_N) :
  fdistmap (eval_at s) rho_uniform =
  @fdist_uniform_supp R _ (img s) (img_pos2 s).
Proof.
have Hinj := Hregular s.
exact: (fdistmap_uniform_supp_inj _ Hinj).
Qed.

End test.
