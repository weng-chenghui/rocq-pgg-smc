(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Certificate bundle for uniform dealing (epsilon = 0)                       *)
(*                                                                            *)
(* When the dealing phase samples a permutation uniformly from a group G      *)
(* that acts regularly (= free + transitive) on card positions, the endpoint *)
(* distribution is exactly uniform, giving epsilon = 0.                       *)
(*                                                                            *)
(* Main result:                                                               *)
(*   uniform_security_witness : ShuffleCertificateBundle R M                  *)
(*     with sw_bound_eps = 0 and scb_exact = Some (se_eps = 0)               *)
(*                                                                            *)
(* Hypotheses:                                                                *)
(*   - pgg_rho is injective on pgg_G M (faithfulness)                         *)
(*   - The image rhoG acts regularly on 'I_N:                                 *)
(*     * pe_inj: eval_at s is injective on rhoG for all s                   *)
(*     * rhoG_trans: the image of rhoG under eval_at s is [set: 'I_N] for all s  *)
(*                                                                            *)
(* Mathematical argument:                                                     *)
(*   uniform(rhoG) --[eval_at s]--> uniform(eval_at s @: rhoG)               *)
(*     = uniform(setT)   [by transitivity]                                    *)
(*     = fdist_uniform   [by extensionality]                                  *)
(*   var_dist(fdist_uniform, fdist_uniform) = 0 <= 0                          *)
(******************************************************************************)

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

(******************************************************************************)
(*  Auxiliary: fdist_uniform_supp over setT equals fdist_uniform              *)
(******************************************************************************)

Section uniform_supp_setT.

Context {R : realType}.
Variable A : finType.
Variable n : nat.
Hypothesis card_A : #|A| = n.+1.

Let HsetT : (0 < #|[set: A]|)%N.
Proof. by rewrite cardsT card_A. Qed.

(* fdist_uniform_supp over the universal set [set: A] equals the
   cardinal-indexed fdist_uniform card_A.  Bridges the support-restricted
   uniform construction, needed while rhoG's support is a proper subset,
   and the plain cardinal-indexed uniform that is the endpoint bound's
   target, once transitivity (img_setT) shows the support has become
   everything. *)
Lemma fdist_uniform_supp_setT :
  @fdist_uniform_supp R A [set: A] HsetT = fdist_uniform card_A.
Proof.
apply/fdist_ext => a.
rewrite fdist_uniform_supp_in ?inE // fdist_uniformE.
by rewrite cardsT.
Qed.

End uniform_supp_setT.

(******************************************************************************)
(*  Auxiliary: var_dist of a distribution with itself is 0                    *)
(******************************************************************************)

Section var_dist_self.

Context {R : realType}.
Variable A : finType.

(* var_dist P P = 0 for any distribution P.  The trivial identity that
   turns eval_pushforward_uniform's exact equality of the pushforward and
   fdist_uniform into the file's epsilon = 0 security bound. *)
Lemma var_dist_self (P : R.-fdist A) : var_dist P P = 0.
Proof.
rewrite /var_dist (eq_bigr (fun _ => 0)); last by move=> a _; rewrite subrr normr0.
by rewrite big1.
Qed.

End var_dist_self.

(******************************************************************************)
(*  Certificate bundle for uniform dealing with regular group action          *)
(******************************************************************************)

Section uniform_security.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.
Let N := N'.+1.
Let G := pgg_G M.

(* The image of G under rho in {perm 'I_N} *)
Let rho := morphism.mfun (@pgg_rho M).
Let rhoG : {set {perm 'I_N}} := [set rho x | x in G].

Hypothesis card_rhoG_gt0 : (0 < #|rhoG|)%N.

(* Regularity: eval_at s is injective on rhoG *)
Hypothesis pe_inj :
  forall s : 'I_N,
  {in rhoG &, injective (fun sigma : {perm 'I_N} => sigma s)}.

(* Transitivity: the orbit of every card position s under rhoG is all of
   'I_N *)
Hypothesis rhoG_trans :
  forall s : 'I_N,
  [set (sigma : {perm 'I_N}) s | sigma in rhoG] = [set: 'I_N].

(* The distribution: uniform over rhoG *)
Let rho_uniform : R.-fdist {perm 'I_N} :=
  @fdist_uniform_supp R _ rhoG card_rhoG_gt0.

(* eval_at s *)
Let eval_at (s : 'I_N) : {perm 'I_N} -> 'I_N :=
  fun sigma => sigma s.

(* The image of rhoG under eval_at s *)
Let img (s : 'I_N) := (eval_at s) @: rhoG.

(* img s, the endpoint image of rhoG at card position s, is non-empty, since
   rhoG itself is non-empty (card_rhoG_gt0).  Housekeeping needed only to
   construct fdist_uniform_supp on img s in eval_pushforward; img_setT
   below is the fact that actually pins down img s. *)
Lemma img_pos (s : 'I_N) : (0 < #|img s|)%N.
Proof.
rewrite card_gt0; apply/set0Pn.
have /card_gt0P [g Hg] := card_rhoG_gt0.
by exists (g s); apply/imsetP; exists g.
Qed.

(* Key: the image is all of 'I_N *)
Lemma img_setT (s : 'I_N) : img s = [set: 'I_N].
Proof. exact: rhoG_trans s. Qed.

(* The pushforward of uniform(rhoG) through eval_at s is uniform(img s) *)
Lemma eval_pushforward (s : 'I_N) :
  fdistmap (eval_at s) rho_uniform =
  @fdist_uniform_supp R _ (img s) (img_pos s).
Proof.
rewrite (@fdistmap_uniform_supp_inj R _ _ rhoG card_rhoG_gt0 (eval_at s) (@pe_inj s)).
congr fdist_uniform_supp; exact: eq_irrelevance.
Qed.

(* The pushforward equals fdist_uniform *)
Lemma eval_pushforward_uniform (s : 'I_N) :
  fdistmap (eval_at s) rho_uniform = fdist_uniform (card_ord N).
Proof.
rewrite eval_pushforward.
apply/fdist_ext => a.
rewrite fdist_uniform_supp_in; last by rewrite img_setT inE.
by rewrite fdist_uniformE img_setT cardsT.
Qed.

(* The endpoint bound: var_dist = 0 <= 0 *)
Lemma endpoint_bound (s : 'I_N) :
  (var_dist (fdistmap (eval_at s) rho_uniform)
            (fdist_uniform (card_ord N)) <= 0)%O.
Proof.
rewrite eval_pushforward_uniform var_dist_self.
exact: Order.POrderTheory.lexx.
Qed.

(* The exact endpoint equality: var_dist = 0 *)
Lemma endpoint_exact (s : 'I_N) :
  var_dist (fdistmap (eval_at s) rho_uniform)
           (fdist_uniform (card_ord N)) = 0.
Proof. by rewrite eval_pushforward_uniform var_dist_self. Qed.

(* The certificate bundle for uniform dealing over a regular group
   action: marginal bound at epsilon = 0 (endpoint_bound) with the exact
   equality var_dist = 0 attached (endpoint_exact via MkSecurityExact),
   no asymptotic slot.  L is carried only as the caller's round-count
   label; the bound and exact-equality proofs never use it, because a
   regular action's uniform dealing produces the exact uniform endpoint
   distribution at every word length.  The file's single result: an
   exact, not merely asymptotic, security witness. *)
Definition uniform_security_witness (L : nat) : ShuffleCertificateBundle R M :=
  @MkShuffleCertificateBundle R M
    (@MkShuffleMarginalBound R M L (0 : R) rho_uniform endpoint_bound)
    (Some (@MkSecurityExact R M rho_uniform 0 endpoint_exact))
    None.

End uniform_security.

Arguments uniform_security_witness {R M} card_rhoG_gt0 pe_inj rhoG_trans L.
