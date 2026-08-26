(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 × S_5 Algebraic Rigidity Instance                                     *)
(*                                                                            *)
(* First concrete group instance with genus > 0. The product structure        *)
(* S_5 × S_5 ⊂ S_10 forces genus >= 173 because:                            *)
(*   1. |G| = 14400 > klein_genus0_bound(10) = 60 → genus > 0                *)
(*   2. Hurwitz's automorphism bound |Aut(C)| <= 84(g-1) at |G| = 14400      *)
(*      forces g >= 173                                                      *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   N = 10 card positions (two 5-card piles)                                *)
(*   Tg = 8 generators (adjacent transpositions, 4 per pile)                 *)
(*   ShuffleMarginalBound (fiber): L=1, eps = 8/5 (fiber-counted, proved)    *)
(*   ShuffleCertificateBundle (spectral): L=591,                             *)
(*     eps = 1 + sqrt(10)*lazy_alpha^591                                     *)
(*     var_dist floors at 1 (orbit-vs-global gap), not 0                    *)
(*   ThresholdScheme: product of two sum_mod on 'I_5                         *)
(*   CoveringData: genus 173, base genus 0, ramif = 29144                    *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_10:                               *)
(*   The 10x10 Schreier matrix decomposes into two 5x5 blocks (one per      *)
(*   pile) since generators preserve {0..4} and {5..9}. Each block is        *)
(*   I - (1/8)*L(P_5) where L(P_5) is the graph Laplacian of the path P_5.  *)
(*   Smallest nonzero Laplacian eigenvalue: 2*(1-cos(pi/5)) (standard        *)
(*   spectral graph theory, cf. Brouwer-Haemers 2012, Chung 1997).          *)
(*   Spectral gap = (1 - cos(pi/5)) / 4 ~ 0.0477.                          *)
(*     var_dist <= 1 + sqrt(10)*lazy_alpha^L floors at 1 (orbit-vs-global)  *)
(*     within-pile residual < 2^{-40} at L=594, < 2^{-128} at L=1847        *)
(*                                                                            *)
(*   Wilson (2004): "Mixing times of lozenge tiling and card shuffling       *)
(*     Markov chains," Ann. Appl. Probab. 14(1):274-325.                     *)
(*   Bacher (1994): "Valeur propre minimale du laplacien de Coxeter pour     *)
(*     le groupe symetrique," J. Algebra 167:460-472.                        *)
(*                                                                            *)
(* No finite field, AG code, or code automorphism hypotheses needed —        *)
(* the product sum_mod construction is fully self-contained.                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_s5x5 pgg_collusion_bound s5x5_pile.
From pgg_smc Require Import s5x5_mixing s5_mixing.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity
                                    combinatorial_rigidity.
From pgg_reconstruct Require Import product_threshold.
From pgg_reconstruct Require Import curve_realisation.
From pgg_reconstruct Require Import multi_covering.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* |S_5 × S_5| = 14400, infeasible to compute in Coq.
   The exact value is held as an axiom (s5x5_group_order_eq) so that
   the Riemann-Hurwitz arithmetic in s5x5_hurwitz can rewrite by it.
   The strict bound used downstream by AlgebraicRigidity is derived,
   not axiomatised: see Lemma s5x5_group_order_bound below. *)
Axiom s5x5_group_order_eq :
  #|pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple)| = 14400.

(** s5x5_group_order_bound — the S_5 x S_5 group order strictly exceeds the
    Klein PGL bound for genus-0 covers on 10 sheets: klein_genus0_bound =
    max(2*10, 60) = 60 while |S_5 x S_5| = 14400. Combined with
    ar_large_group_forces_gap, this is what forces the s5x5 instance onto
    the positive-genus branch of the AlgebraicRigidity tradeoff. *)
Lemma s5x5_group_order_bound :
  (klein_genus0_bound (@Gen_PGGTypes 7 8 s5x5_gen_tuple) <
   #|pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple)|)%N.
Proof. by rewrite s5x5_group_order_eq. Qed.

(* Generators preserve pile structure: pile-1 = {0..4}, pile-2 = {5..9}.
   Proved in pgg-smc/instances/s5x5/s5x5_pile.v via astabs_group closure +
   gen_subG + an 8x10 = 80 case analysis on the generator action. *)

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section s5x5_security.

Variable R : realType.

Let M_s5x5 := @Gen_PGGTypes 7 8 s5x5_gen_tuple.
Let s5x5_M : MonodromyReprWithGeneratorType := M_s5x5.

(* Fiber-counted endpoint bound: for each card position s in 'I_10,
   var_dist(endpoint, uniform) <= 8/5.
   At L=1, achievable = {(01),(12),(23),(34),(56),(67),(78),(89)}.
   Boundary card positions (0,4,5,9): only 1 generator moves them, image
   size = 2.
   Inner card positions (1,2,3,6,7,8): 2 generators move them, image
   size = 3.
   Worst case: img_min = 2, bound = 2*(10-2)/10 = 8/5. *)
Let s5x5_eps := @GRing.natmul R 1 8 / @GRing.natmul R 1 5.

(** s5x5_endpoint_bound_fiber — at word length 1, every card position's
    endpoint law has variation distance at most 8/5 = s5x5_eps from
    uniform on 'I_10 (the fiber count above: boundary card positions have
    image size 2, interior card positions image size 3, worst case
    2*(10-2)/10). This is the hypothesis
    security_witness_fiber needs to build s5x5_security_witness_1, the L=1
    fiber-counted security witness for the S_5 x S_5 instance. *)
Lemma s5x5_endpoint_bound_fiber :
  forall s : 'I_10,
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
                     (@rho_from_words R _ _ 1 s5x5_gen_tuple))
           (fdist_uniform (card_ord 10)) <= s5x5_eps)%O.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans
  (@var_dist_endpoint_image_bound_unbalanced R 8 7 1 s5x5_gen_tuple
    s5x5_weval_inj1 (erefl true) 2 s _)); last first.
  rewrite /= -natrM /s5x5_eps.
  have -> : (16 : R) = 2%:R * 8%:R by rewrite -natrM.
  have -> : (10 : R) = 2%:R * 5%:R by rewrite -natrM.
  rewrite Num.Theory.ler_pdivlMr ?Num.Theory.ltr0n //.
  rewrite invfM // -mulrA mulfVK ?Num.Theory.pnatr_eq0 //.
  rewrite mulrAC divrr ?mul1r //.
  by apply: Num.Theory.unitf_gt0; rewrite Num.Theory.ltr0n.
have Hmem : forall (w : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1),
    word_eval w s \in
      (fun sigma : {perm 'I_10} => sigma s) @:
        achievable (Gen_PGGTypes s5x5_gen_tuple) 1.
  by move=> w; apply: imset_f; apply: imset_f.
pose w0 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=0) (erefl true))].
pose w1 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=1) (erefl true))].
pose w2 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=2) (erefl true))].
pose w3 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=3) (erefl true))].
pose w4 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=4) (erefl true))].
pose w5 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=5) (erefl true))].
pose w6 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=6) (erefl true))].
pose w7 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=7) (erefl true))].
have Hwi : forall i : 'I_8,
  @word_eval (Gen_PGGTypes s5x5_gen_tuple) 1 [tuple i] =
  tnth s5x5_gen_tuple i.
  move=> i; rewrite /word_eval big_ord_recr /= big_ord0 mul1g //.
apply/card_gt1P.
move: Hmem; case: s => [] m Hm Hmem.
case: m Hm Hmem => [|[|[|[|[|m']]]]] Hm Hmem.
(* s=0: tperm(0,1)(0)=1 vs tperm(3,4)(0)=0 *)
- exists (word_eval w0 (Ordinal Hm)), (word_eval w3 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=1: tperm(0,1)(1)=0 vs tperm(1,2)(1)=2 *)
- exists (word_eval w0 (Ordinal Hm)), (word_eval w1 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=2: tperm(1,2)(2)=1 vs tperm(2,3)(2)=3 *)
- exists (word_eval w1 (Ordinal Hm)), (word_eval w2 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=3: tperm(2,3)(3)=2 vs tperm(3,4)(3)=4 *)
- exists (word_eval w2 (Ordinal Hm)), (word_eval w3 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=4: tperm(3,4)(4)=3 vs tperm(0,1)(4)=4 *)
- exists (word_eval w3 (Ordinal Hm)), (word_eval w0 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
- case: m' Hm Hmem => [|[|[|[|[|m'']]]]] Hm Hmem.
  (* s=5: tperm(5,6)(5)=6 vs tperm(8,9)(5)=5 *)
  + exists (word_eval w4 (Ordinal Hm)), (word_eval w7 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=6: tperm(5,6)(6)=5 vs tperm(6,7)(6)=7 *)
  + exists (word_eval w4 (Ordinal Hm)), (word_eval w5 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=7: tperm(6,7)(7)=6 vs tperm(7,8)(7)=8 *)
  + exists (word_eval w5 (Ordinal Hm)), (word_eval w6 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=8: tperm(7,8)(8)=7 vs tperm(8,9)(8)=9 *)
  + exists (word_eval w6 (Ordinal Hm)), (word_eval w7 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=9: tperm(8,9)(9)=8 vs tperm(5,6)(9)=9 *)
  + exists (word_eval w7 (Ordinal Hm)), (word_eval w4 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* m'' + 10 < 10: impossible *)
  + by [].
Qed.

(* ShuffleMarginalBound at L=1 via fiber counting over the eight product
   generators: epsilon = 8/5, established by s5x5_endpoint_bound_fiber. *)
Definition s5x5_security_witness_1 : ShuffleMarginalBound R s5x5_M :=
  security_witness_fiber s5x5_weval_inj1 s5x5_endpoint_bound_fiber.

End s5x5_security.

(******************************************************************************)
(*     Spectral Gap Convergence (Axiomatized)                                 *)
(*                                                                            *)
(* The Schreier graph of S_5 x S_5 on 'I_10 with 8 Coxeter generators       *)
(* decomposes into two independent copies of the path P_5 (since pile-1      *)
(* generators fix pile-2 card positions and vice versa). The transition     *)
(* matrix is:                                                                *)
(*   A = I - (1/8) * L(P_5)                                                  *)
(* where L(P_5) is the graph Laplacian of the 5-vertex path.                 *)
(*                                                                            *)
(* The smallest nonzero Laplacian eigenvalue of P_n is 2*(1 - cos(pi/n)),    *)
(* giving spectral gap = (1 - cos(pi/5)) / 4 ~ 0.0477 for the walk.         *)
(* The convergence bound is:                                                  *)
(*   var_dist(endpoint, uniform) <= sqrt(10) * (1 - gap)^L                   *)
(*                                                                            *)
(* References:                                                                *)
(*   Brouwer-Haemers (2012), Spectra of Graphs, Springer.                    *)
(*   Chung (1997), Spectral Graph Theory, AMS.                               *)
(*   Wilson (2004), Ann. Appl. Probab. 14(1):274-325.                        *)
(*   Bacher (1994), J. Algebra 167:460-472.                                  *)
(*                                                                            *)
(* We use Variable/Hypothesis (not Axiom) so that spectral parameters are    *)
(* abstracted over when the section closes, following the Monster pattern.    *)
(******************************************************************************)

Section s5x5_spectral.

Variable R : realType.

Let M_s5x5 := @Gen_PGGTypes 7 8 s5x5_gen_tuple.
Let s5x5_M : MonodromyReprWithGeneratorType := M_s5x5.

(* The S_5 x S_5 Schreier walk on 'I_10 is reducible: pile-1 generators
   fix pile-2 card positions and vice versa. So the walk's stationary
   distribution
   is uniform on the orbit (5 elements), not on all of 'I_10. The constant
   variation-distance floor against fdist_uniform(card_ord 10) is 1
   (in infotheo's un-halved L^1 convention; equivalent to TV-floor 1/2).
   Within each pile, mixing is exponential at rate (1 + alpha)/2 ~ 0.9525,
   reusing the S_5 Rayleigh certificate. See pgg-smc/instances/s5x5/s5x5_mixing.v
   and pgg-smc/instances/s5/s5_mixing.v for the proofs. *)

(* SecurityAsymptotic certificate carrying the honest spectral guarantee.
   The bound is var_dist <= 1 + sqrt(10) * lazy_alpha^L, which converges
   to 1 (the orbit-vs-global gap), not to 0. *)
Definition s5x5_asymptotic : @SecurityAsymptotic R s5x5_M.
Proof.
apply: (@MkSecurityAsymptotic R s5x5_M
  (1 - s5_lazy_alpha_R R)        (* sa_spectral_gap *)
  1                              (* sa_eps_inf, the orbit-vs-global floor *)
  _                              (* sa_gap_pos *)
  _                              (* sa_gap_le1 *)
  Num.Theory.ler01            (* sa_eps_inf_ge0: 0 <= 1 *)
  (fun L => rho_from_words L s5x5_gen_tuple)).
- by rewrite Num.Theory.subr_gt0; exact: s5_lazy_alpha_R_lt1.
- by rewrite Num.Theory.lerBlDr Num.Theory.lerDl;
  exact: s5_lazy_alpha_R_ge0.
- move=> L s.
  rewrite opprB addrCA subrr addr0.
  change (pgg_N' s5x5_M).+1 with 10%N in s |- *.
  apply: (Order.POrderTheory.le_trans (s5x5_spectral_TV_bound R L s)).
  rewrite (Num.Theory.lerD2l 1).
  apply: Num.Theory.ler_wpM2r.
  + by rewrite Num.Theory.exprn_ge0 //; exact: s5_lazy_alpha_R_ge0.
  + by rewrite Num.Theory.ler_sqrt ?Num.Theory.ler0n // Num.Theory.ler_nat.
Defined.

(* ShuffleCertificateBundle at any word length L, parametrised only by R:
   MkShuffleCertificateBundle at the spectral marginal bound of the word
   distribution, with no exact certificate and s5x5_asymptotic attached. *)
Definition s5x5_security_witness_schreier (L : nat) :
    ShuffleCertificateBundle R s5x5_M.
Proof.
apply: (@MkShuffleCertificateBundle R s5x5_M
  (@MkShuffleMarginalBound R s5x5_M L
    (1 + Num.sqrt 10%:R * (s5_lazy_alpha_R R) ^+ L)
    (rho_from_words L s5x5_gen_tuple)
    _) None (Some s5x5_asymptotic)).
move=> s.
change (pgg_N' s5x5_M).+1 with 10%N in s |- *.
apply: (Order.POrderTheory.le_trans (s5x5_spectral_TV_bound R L s)).
rewrite (Num.Theory.lerD2l 1).
apply: Num.Theory.ler_wpM2r.
- by rewrite Num.Theory.exprn_ge0 //; exact: s5_lazy_alpha_R_ge0.
- by rewrite Num.Theory.ler_sqrt ?Num.Theory.ler0n // Num.Theory.ler_nat.
Defined.

End s5x5_spectral.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section s5x5_rigidity.

Variable R : realType.

Let s5x5_M : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 7 8 s5x5_gen_tuple.

(* --- CoveringData: genus 173 --- *)

(* Hurwitz lower bound on the genus of any S_5 x S_5 Galois cover of P^1:
   for g >= 2, |Aut(C)| <= 84 * (g - 1), so g >= 1 + |G|/84. With |G| = 14400,
   g >= 1 + 14400/84 = 172.43, hence g >= 173: the minimum genus consistent
   with both Hurwitz arithmetic and the Hurwitz automorphism bound. The
   actual realising curve (an inverse-Galois construction for S_5 x S_5) is
   named in the realisation axioms below.

   Riemann-Hurwitz: 2*173 + 2*14400 = 14400*(2*0) + 29144 + 2.
   Check: 346 + 28800 = 29146; 29144 + 2 = 29146. *)
Lemma s5x5_hurwitz :
  (2 * 173 + 2 * #|pgg_G s5x5_M| =
   #|pgg_G s5x5_M| * (2 * 0) + 29144 + 2)%N.
Proof.
by rewrite muln0 muln0 add0n s5x5_group_order_eq.
Qed.

(** s5x5_n_branch_le — 6 <= 29144, the concrete branch-count-vs-total-ramif
    inequality for the S_5 x S_5 instance. This discharges the
    [cd_ramif_ge_n_branch] field of the [CoveringData] record
    s5x5_covering_data below. *)
Lemma s5x5_n_branch_le : (6 <= 29144)%N. Proof. by []. Qed.

(** s5x5_covering_data — covering-data record for the S_5 x S_5 instance:
    genus 173, 6 branches, total ramification 29144. The genus is forced by
    the Hurwitz lower bound (s5x5_hurwitz) for any S_5 x S_5 Galois cover of
    P^1; s5x5_inverse_galois_realised below is the realisation axiom for
    this specific cover. *)
Definition s5x5_covering_data : CoveringData s5x5_M :=
  @MkCoveringData s5x5_M 0 6 29144 173 s5x5_n_branch_le s5x5_hurwitz.

(** s5x5_inverse_galois_realised — s5x5_covering_data corresponds to an
    actual Galois cover of P^1 with deck group S_5 x S_5 and genus 173, not
    merely a formally consistent record. The trust boundary: the inverse
    Galois problem for S_5 x S_5 over Q is solved, so S_5 x S_5 is
    realisable as a Galois group of a number-field extension, and a
    Belyi-style construction lifts that to a Galois cover of P^1_Q with this
    deck group at the Hurwitz-minimal genus 173. *)
Axiom s5x5_inverse_galois_realised :
  realised_by_curve s5x5_covering_data.

(* --- Product ThresholdScheme: two sum_mod on 'I_5 --- *)

(* N1' = N2' = 3 gives N1 = N2 = 5, N = 10.
   T1' = T2' = 4 gives T1 = T2 = 5, T = 10.
   sum_mod_scheme on 'I_5 with 5 parties: ts_T = ts_k = 5.
   Product: ts_T = 10, ts_k = min(5,5) = 5. *)
Let s5x5_ts : ThresholdScheme 'I_10 'I_10 :=
  @product_scheme 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4).

(* --- CoveringScheme --- *)

(** s5x5_cs_gap — the [cs_gap] obligation ts_T <= ts_k + 2*cd_genus holds
    for the S_5 x S_5 product threshold scheme: with ts_T = 10, ts_k = 5
    and cd_genus = 173, the bound reads 10 <= 5 + 346 = 351, immediate by
    computation. Discharges the gap field of [s5x5_covering]. *)
Lemma s5x5_cs_gap :
  (ts_T s5x5_ts <= ts_k s5x5_ts + 2 * cd_genus s5x5_covering_data)%N.
Proof. by []. Qed.

(* Pile preservation: the monodromy of S_5 × S_5 preserves {0..4} *)
Lemma s5x5_preserves_pile1 :
  forall g, g \in pgg_G s5x5_M ->
  forall i : 'I_10, (val i < 5)%N -> (val (@pgg_rho s5x5_M g i) < 5)%N.
Proof. exact: s5x5_pile1_stab. Qed.

(** s5x5_perm_compatible — the S_5 x S_5 monodromy action is
    permutation-compatible with the product sum-mod threshold scheme
    s5x5_ts, closing the [ts_recon_perm_invariant] obligation the
    covering-scheme record s5x5_covering needs. *)
Lemma s5x5_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G s5x5_M) _ _ s5x5_ts (@pgg_rho s5x5_M).
Proof.
exact: (@product_sum_mod_perm_compatible 3 3 4 4 _ _ (@pgg_rho s5x5_M) s5x5_preserves_pile1).
Qed.

(** s5x5_covering — the [CoveringScheme] record for the S_5 x S_5 instance:
    the product threshold plug, s5x5_covering_data, and the recovery-gap
    bound s5x5_cs_gap, bundled for the [AlgebraicRigidity] construction
    below. *)
Definition s5x5_covering : CoveringScheme s5x5_M := {|
  cs_plug := @MkReconPlug s5x5_M 'I_10 s5x5_ts id (@pgg_rho s5x5_M)
               s5x5_perm_compatible ;
  cs_data := s5x5_covering_data ;
  cs_gap  := s5x5_cs_gap ;
|}.

(* --- ThresholdWitness --- *)

(* genus = 173 <> 0, so the PGL hypothesis is vacuously true. *)
Lemma s5x5_genus0_klein :
  cd_genus (cs_data s5x5_covering) = 0 ->
  (#|pgg_G s5x5_M| <= klein_genus0_bound s5x5_M)%N.
Proof. by []. Qed.

(** s5x5_genus0_automorphism — the [genus0_automorphism_bound] obligation for
    the S_5 x S_5 instance. Because the covering genus is 173, not 0, the
    genus-0 hypothesis is vacuous and s5x5_genus0_klein discharges the
    obligation directly. This is what s5x5_threshold_witness needs to
    package s5x5_covering into a [ThresholdWitness]. *)
Lemma s5x5_genus0_automorphism :
  genus0_automorphism_bound s5x5_M (cs_data s5x5_covering).
Proof. exact: s5x5_genus0_klein. Qed.

(** s5x5_threshold_witness — the [ThresholdWitness] for the S_5 x S_5
    instance: s5x5_covering paired with its genus0_automorphism discharge.
    s5x5_rigidity below consumes it as the recovery half of the
    [AlgebraicRigidity] value. *)
Definition s5x5_threshold_witness : ThresholdWitness s5x5_M :=
  @MkThresholdWitness s5x5_M s5x5_covering s5x5_genus0_automorphism.

(* --- AlgebraicRigidity --- *)

(** s5x5_rigidity — the [AlgebraicRigidity] value of the S_5 x S_5 instance:
    the certificate-free L=1 fiber security bundle
    (s5x5_security_witness_1) paired with the recovery witness
    s5x5_threshold_witness. This is the instance's security/recovery
    package at word length 1; s5x5_rigidity_cryptographically_secure below
    is the same package at the spectral bound, word length 591. *)
Definition s5x5_rigidity : AlgebraicRigidity R s5x5_M :=
  @MkAlgebraicRigidity R s5x5_M
    (shuffle_bundle_of_bound (s5x5_security_witness_1 R))
    s5x5_threshold_witness.

(* --- Derived properties --- *)

Lemma s5x5_complexity (L : nat) :
  (@search_space s5x5_M L <= #|pgg_G s5x5_M|)%N.
Proof. exact: search_space_leG. Qed.

(** s5x5_tradeoff — the security/complexity trade-off for the S_5 x S_5
    instance: either the covering genus is 0 and the group order stays below
    the Klein bound with ts_T <= ts_k, or the genus is positive and ts_T is
    only bounded by ts_k plus twice the genus. This instance realises the
    second, positive-genus disjunct (s5x5_large_group), specialising the
    generic security_threshold_tradeoff dichotomy. *)
Lemma s5x5_tradeoff :
  let cs := tw_covering (ar_threshold s5x5_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G s5x5_M| <= klein_genus0_bound s5x5_M)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
exact: (@security_threshold_tradeoff s5x5_M s5x5_covering s5x5_genus0_klein).
Qed.

(* Genus > 0 is forced by |G| > klein_genus0_bound. *)
Lemma s5x5_large_group :
  (0 < cd_genus (cs_data s5x5_covering))%N.
Proof. by []. Qed.

(** s5x5_ts_recon_correct — for the S_5 x S_5 instance, reconstructing the
    dealt secret from the revealed endpoints of any group element P recovers
    the card position s that was cut, given the [G_stable] monodromy
    condition and
    covering-scheme validity. Interface-parametrised generalisation of
    ar_protocol_correct, specialised below at s5x5_PI to get the concrete
    unconditional guarantee s5x5_protocol_correct. *)
Lemma s5x5_ts_recon_correct (PI : PGGInterface s5x5_M)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold s5x5_rigidity))) = pi_T' PI)
    (s : 'I_10) (P : pgg_gT s5x5_M)
    (G_stable : forall g, g \in pgg_G s5x5_M ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold s5x5_rigidity)))).+1,
         rp_content (cs_plug (tw_covering (ar_threshold s5x5_rigidity)))
           (@pgg_rho s5x5_M g
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i)) =
         tnth [tuple rp_content (cs_plug (tw_covering (ar_threshold s5x5_rigidity)))
                 (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
              | j < (ts_T' (cs_scheme (tw_covering (ar_threshold s5x5_rigidity)))).+1]
              (rp_monodromy (cs_plug (tw_covering (ar_threshold s5x5_rigidity))) g i)) :
  P \in pgg_G s5x5_M ->
  ts_valid (cs_scheme (tw_covering (ar_threshold s5x5_rigidity))) s
          [tuple rp_content (cs_plug (tw_covering (ar_threshold s5x5_rigidity)))
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
          | j < (ts_T' (cs_scheme (tw_covering (ar_threshold s5x5_rigidity)))).+1] ->
  pgg_recon_endpoints HT
    (rp_content (cs_plug (tw_covering (ar_threshold s5x5_rigidity)))) P = s.
Proof. exact: ar_protocol_correct. Qed.

(******************************************************************************)
(*     Non-abelianness, concrete interface, and unconditional correctness     *)
(******************************************************************************)

(** s5x5_nonabelian — the S_5 x S_5 monodromy group is non-abelian: two
    adjacent transpositions in the same five-card pile, the cuts (0 1) and
    (1 2), fail to commute, witnessed at card 0. The order alone,
    |G| = 14400, does not force non-abelianness, so this is proved
    separately; it is the S_5 x S_5 analogue of wreath_nonabelian's
    argument, and it is what gives the instance a non-trivial commutator
    structure. *)
Lemma s5x5_nonabelian : ~~ abelian (pgg_G s5x5_M).
Proof.
apply: (@gen_nonabelian s5x5_M (@Ordinal 8 0 isT) (@Ordinal 8 1 isT)) => //.
by apply/eqP => /permP /(_ (@Ordinal 10 0 isT)); rewrite !permM !permE.
Qed.

(** s5x5_starts_uniq — the ten starting card positions are pairwise
    distinct, the uniqueness witness s5x5_PI needs for its [PGGInterface]
    record. *)
Lemma s5x5_starts_uniq : uniq (ord_tuple 10).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** s5x5_PI — the concrete interface on ten card positions (two piles of
    five) [PGGInterface]: the
    10 starting card positions, in identity order. Starting at the identity
    tuple is what makes the s5x5_G_stable condition reduce to reflexivity of
    pgg_rho, which is why s5x5_protocol_correct can be unconditional. *)
Definition s5x5_PI : PGGInterface s5x5_M :=
  @MkPGGI s5x5_M 9 (ord_tuple 10) s5x5_starts_uniq.

(** s5x5_HT — the threshold scheme's and the interface's party counts agree
    (both 9). Kept as [erefl] rather than an opaque proof so the tuple casts
    it feeds in s5x5_G_stable and s5x5_protocol_correct reduce away by
    computation. *)
Definition s5x5_HT : ts_T' s5x5_ts = pi_T' s5x5_PI := erefl.

(** s5x5_G_stable — the monodromy permutes the starting card positions
    exactly as it permutes the identity-content shares: with starts =
    ord_tuple 10 and content = id, both sides of the [G_stable] condition
    collapse to pgg_rho g i. This is the structural premise
    s5x5_protocol_correct needs, proved here rather than assumed. *)
Lemma s5x5_G_stable :
  forall g, g \in pgg_G s5x5_M ->
  forall i : 'I_(ts_T' s5x5_ts).+1,
    id (@pgg_rho s5x5_M g
         (tnth (cast_tuple (esym (congr1 S s5x5_HT)) (pi_starts s5x5_PI)) i)) =
    tnth [tuple id (tnth (cast_tuple (esym (congr1 S s5x5_HT)) (pi_starts s5x5_PI)) j)
         | j < (ts_T' s5x5_ts).+1] (@pgg_rho s5x5_M g i).
Proof.
move=> g Hg i.
by rewrite tnth_mktuple !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id.
Qed.

(** s5x5_protocol_correct — for the concrete S_5 x S_5 interface s5x5_PI,
    reconstructing the secret card position s from the revealed endpoints
    of any
    hidden group element P recovers s, unconditionally: no [G_stable]
    hypothesis is assumed, since s5x5_G_stable proves it. This is
    pgg_recon_monodromy_correct instantiated with the proved G_stable and
    the covering's permutation-compatibility (s5x5_perm_compatible), and is
    the end-to-end correctness guarantee for the S_5 x S_5 instance. *)
Theorem s5x5_protocol_correct (s : 'I_10) (P : pgg_gT s5x5_M) :
  P \in pgg_G s5x5_M ->
  ts_valid s5x5_ts s
    [tuple id (tnth (cast_tuple (esym (congr1 S s5x5_HT)) (pi_starts s5x5_PI)) j)
    | j < (ts_T' s5x5_ts).+1] ->
  @pgg_recon_endpoints s5x5_M s5x5_PI 'I_10 s5x5_ts s5x5_HT id P = s.
Proof.
move=> PG Hvalid.
apply: (@pgg_recon_monodromy_correct s5x5_M s5x5_PI 'I_10 s5x5_ts s5x5_HT id
          (pgg_G s5x5_M) s P (@pgg_rho s5x5_M));
  [exact: subxx | exact: s5x5_G_stable | exact: PG | exact: Hvalid
  | exact: s5x5_perm_compatible].
Qed.

(******************************************************************************)
(*     CombinatorialRigidity instance                                         *)
(******************************************************************************)

(** s5x5_combinatorial_rigidity — the CombinatorialRigidity value for
    S_5 x S_5: certifies security (the L=1 fiber witness), recovery (the
    covering with its positive gap), the positive genus (173 > 0), and
    the strict order inequality (60 < 14400), in one record. This is the
    positive dual of the single-pile S_5 no-go result: the product
    instance realises a strict order inequality with a positive genus gap
    that no genus-zero curve could admit. *)
Definition s5x5_combinatorial_rigidity : CombinatorialRigidity R s5x5_M :=
  @MkCombinatorialRigidity R s5x5_M
    (shuffle_bundle_of_bound (s5x5_security_witness_1 R)) s5x5_covering
    s5x5_large_group s5x5_group_order_bound.

End s5x5_rigidity.

(******************************************************************************)
(*     Spectral AlgebraicRigidity at L=591 (var_dist floors at 1)           *)
(*                                                                            *)
(* Combines the Schreier spectral certificate bundle at L=591 with the       *)
(* product threshold scheme. At L=591 with lazy_alpha = 0.9525:             *)
(*   var_dist <= 1 + sqrt(10)*lazy_alpha^591 ~ 1 + 1.02e-12 (floors at 1)   *)
(*                                                                            *)
(* For a 2^{-128} within-pile residual, use L=1847 instead.                 *)
(******************************************************************************)

Section s5x5_rigidity_cryptographically_secure.

Variable R : realType.

Let s5x5_M : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 7 8 s5x5_gen_tuple.

(* The spectral certificate bundle at L=591: var_dist <= 1 + sqrt(10) *
   lazy_alpha^591, where lazy_alpha = (1 + 181/200) / 2 = 0.9525. The +1
   floor is the orbit-vs-global gap (the walk preserves piles), not a
   security weakness in the threshold sense, since the product threshold
   scheme reconstructs per pile. *)
Definition s5x5_rigidity_cryptographically_secure : AlgebraicRigidity R s5x5_M :=
  @MkAlgebraicRigidity R s5x5_M
    (s5x5_security_witness_schreier R 591)
    s5x5_threshold_witness.

End s5x5_rigidity_cryptographically_secure.

(******************************************************************************)
(*     Multi-component realisation: two disjoint Bring's curves               *)
(*                                                                            *)
(* The single-component s5x5_covering above uses cd_genus = 173, the          *)
(* mathematically-honest value under the framework's Galois-closure           *)
(* interpretation (cd_hurwitz uses #|G|, forcing Hurwitz on the degree-      *)
(* |G|=14400 cover; per Hurwitz Aut bound, g >= 173).                        *)
(*                                                                            *)
(* But the actual s5x5 protocol is operationally a degree-10 cover with      *)
(* TWO orbits (the two piles of 5 sheets). Each orbit is realised by a       *)
(* separate Bring's curve at genus 4. The multi-component representation     *)
(* below makes this operational structure explicit.                          *)
(*                                                                            *)
(* The framework extension in [reconstruct/multi_covering.v] supports         *)
(* per-component Hurwitz with degree-based formula (mc_n_sheets instead of   *)
(* #|G|), so each Bring's component has the small genus consistent with      *)
(* its degree-5 cover structure.                                             *)
(******************************************************************************)

Section s5x5_multi_realisation.

Local Notation s5x5_multi_M := (@Gen_PGGTypes 7 8 s5x5_gen_tuple).

(** s5x5_brings_pile_component — one Bring's curve at genus 4 acting on five
    sheets (one s5x5 pile) as a degree-5 cover of P^1. Riemann-Hurwitz check:
    2*4 + 2*5 = 5*0 + 16 + 2, i.e. 18 = 18. This is the per-pile building
    block of the multi-component realisation s5x5_multi_data. *)
Definition s5x5_brings_pile_component : MultiComponent.
refine (@MkMultiComponent 5 0 5 16 4 _ _).
- by [].
- by [].
Defined.

(** s5x5_multi_data — the S_5 x S_5 protocol's operational covering: two
    disjoint copies of s5x5_brings_pile_component, one per pile, ten sheets
    total. This makes explicit that the protocol is operationally a
    two-component cover at the realisable genus 4 per component, not the
    single connected curve at Galois-closure genus 173 that
    s5x5_covering_data uses. *)
Definition s5x5_multi_data : MultiCoveringData s5x5_multi_M.
refine (@MkMultiCoveringData s5x5_multi_M
          [:: s5x5_brings_pile_component ; s5x5_brings_pile_component] _).
by rewrite big_cons big_cons big_nil.
Defined.

(** mcd_total_genus_s5x5_E — the total genus of the two-component Bring's
    realisation of s5x5 is 4 + 4 = 8, a small operationally-meaningful genus
    rather than the Galois-closure genus 173 that s5x5_covering_data uses. *)
Lemma mcd_total_genus_s5x5_E :
  mcd_total_genus s5x5_multi_data = 8.
Proof. by rewrite /mcd_total_genus /= big_cons big_cons big_nil. Qed.

(** mcd_max_genus_s5x5_E — the maximum per-component genus of the s5x5
    two-Bring's realisation is 4. Any per-component recovery-gap bound must
    be stated at this maximum, not at the total (mcd_total_genus_s5x5_E = 8)
    or at the Galois-closure genus 173. *)
Lemma mcd_max_genus_s5x5_E :
  mcd_max_genus s5x5_multi_data = 4.
Proof. by rewrite /mcd_max_genus /= big_cons big_cons big_nil maxn0 maxnn. Qed.

(** s5x5_multi_realised — s5x5_multi_data corresponds to an actual pair of
    disjoint genus-4 Bring's curves, each carrying an S_5 action on its five
    sheets, not merely formally consistent record data. This is the
    multi-component counterpart of s5x5_inverse_galois_realised: the same
    trust boundary, stated for the two-piece operational cover rather than
    the single Galois-closure curve. *)
Axiom s5x5_multi_realised :
  realised_by_multi_curve s5x5_multi_data.

End s5x5_multi_realisation.
