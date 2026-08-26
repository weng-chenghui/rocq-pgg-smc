(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Overlapping 3-Cycles Algebraic Rigidity Instance                           *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the overlapping       *)
(* 3-cycles group OC = <(0 1 2), (1 2 3)> in S_4.                            *)
(*                                                                            *)
(* The security half is read at word length 2 rather than 1.  Two rounds     *)
(* reach four distinct shuffles where one round reaches two, and the extra    *)
(* round is what brings the fiber-counted epsilon down to 1 from the vacuous  *)
(* value a single round leaves.  Length is the parameter the two halves of    *)
(* this instance are traded against each other along.                        *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 2 (generators), N = 4 (card positions), L = 2, depth = 2          *)
(*   epsilon (fiber) = 1 (fiber-counted, worst-case card position s=1)       *)
(*   epsilon (spectral) = 2 * (1/sqrt(2))^83 at L=83 (40-bit security)      *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_4:                                *)
(*   The 4x4 Schreier matrix with generators (0 1 2) and (1 2 3) is:        *)
(*     | 1/2  1/2   0    0  |                                                *)
(*     |  0    0    1    0  |                                                *)
(*     | 1/2   0    0   1/2 |                                                *)
(*     |  0   1/2   0   1/2 |                                                *)
(*   Eigenvalues: 1, 1/2, (-1+i*sqrt(7))/4, (-1-i*sqrt(7))/4.               *)
(*   |(-1+/-i*sqrt(7))/4| = sqrt(1/2) = 1/sqrt(2).                          *)
(*   Second-largest |eigenvalue| = 1/sqrt(2) ~ 0.707.                        *)
(*   Spectral gap = 1 - 1/sqrt(2) ~ 0.293.                                  *)
(*     L = 83 gives var_dist < 2^{-40}  (40-bit security)                   *)
(*     L = 259 gives var_dist < 2^{-128} (128-bit security)                  *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   oc_security_witness_2 : ShuffleMarginalBound (fiber-counted eps=1)      *)
(*   oc_rigidity : AlgebraicRigidity (security + threshold)                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
From infotheo Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section oc_security.

Variable R : realType.

Let M_oc := @Gen_PGGTypes 1 2 oc_sigmas.
Let R_oc : MonodromyReprWithGeneratorType := M_oc.

Local Open Scope ring_scope.

(* For every card position, the endpoint marginal of the length-2 word
   distribution is within 1 of uniform in the full-L1 convention.  The
   epsilon is read off the fibers rather than from an injectivity argument:
   the four achievable products send each position onto a set of at most two
   images, and the worst position is 1, whose marginal is (1/2,0,0,1/2) at
   distance exactly 1.  The bound is information-theoretic and holds with no
   assumption; the number 1 out of a maximum of 2 is what a two-round
   overlapping-cycle shuffle buys unconditionally, and it is the spectral
   route below, not this one, that reaches cryptographic magnitudes. *)
Lemma oc_endpoint_bound_fiber :
  forall s : 'I_4,
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                     (@rho_from_words R _ _ 2 oc_sigmas))
           (fdist_uniform (card_ord 4)) <= 1)%O.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans
  (@var_dist_endpoint_image_bound R 2 1 2 oc_sigmas oc_weval_inj2
    (erefl _) 2 s _)); last first.
  by rewrite /= subn2 /= -GRing.Theory.natrM /=
     GRing.Theory.divrr // GRing.Theory.unitfE Num.Theory.pnatr_eq0.
have Hmem : forall (w : pgg_word (Gen_PGGTypes oc_sigmas) 2),
    word_eval w s \in
      (fun sigma : {perm 'I_4} => sigma s) @:
        achievable (Gen_PGGTypes oc_sigmas) 2.
  by move=> w; apply: imset_f; apply: imset_f.
pose w00 : pgg_word (Gen_PGGTypes oc_sigmas) 2 := [tuple ord0; ord0].
pose w11 : pgg_word (Gen_PGGTypes oc_sigmas) 2 := [tuple ord_max; ord_max].
pose w01 : pgg_word (Gen_PGGTypes oc_sigmas) 2 := [tuple ord0; ord_max].
have Hw00 : @word_eval (Gen_PGGTypes oc_sigmas) 2 w00 = (oc_s0 * oc_s0)%g.
  rewrite /word_eval /w00 big_ord_recr /= big_ord_recr /= big_ord0 mul1g.
  congr (_ * _)%g; apply: oc_sigmasE.
have Hw11 : @word_eval (Gen_PGGTypes oc_sigmas) 2 w11 = (oc_s1 * oc_s1)%g.
  rewrite /word_eval /w11 big_ord_recr /= big_ord_recr /= big_ord0 mul1g.
  congr (_ * _)%g; apply: oc_sigmasE.
have Hw01 : @word_eval (Gen_PGGTypes oc_sigmas) 2 w01 = (oc_s0 * oc_s1)%g.
  rewrite /word_eval /w01 big_ord_recr /= big_ord_recr /= big_ord0 mul1g.
  congr (_ * _)%g; apply: oc_sigmasE.
apply/card_gt1P.
case: s Hmem => [[|[|[|[|s]]]] Hs] //= Hmem.
- exists (word_eval w00 (Ordinal Hs)), (word_eval w11 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw11 !permM !oc_s0E !oc_s1E].
- exists (word_eval w00 (Ordinal Hs)), (word_eval w11 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw11 !permM !oc_s0E !oc_s1E].
- exists (word_eval w00 (Ordinal Hs)), (word_eval w01 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw01 !permM !oc_s0E !oc_s1E].
- exists (word_eval w00 (Ordinal Hs)), (word_eval w11 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw11 !permM !oc_s0E !oc_s1E].
Qed.

(* The unconditional security half of the rigidity pair: the fiber-counted
   marginal bound at word length 2, epsilon = 1.  The data-processing route
   at the same length gives 40/24, so fiber counting is what makes the
   statement say anything at all here. *)
Definition oc_security_witness_2 : ShuffleMarginalBound R R_oc :=
  security_witness_fiber oc_weval_inj2 oc_endpoint_bound_fiber.

End oc_security.

(******************************************************************************)
(*     Spectral Gap Convergence (Axiomatized)                                 *)
(*                                                                            *)
(* The 4x4 Schreier matrix of OC on 'I_4 is doubly stochastic.               *)
(* Characteristic polynomial: (1/2-lam)(lam-1)(lam^2+lam/2+1/2).             *)
(* Eigenvalues: 1, 1/2, (-1+/-i*sqrt(7))/4.                                  *)
(* |(-1+/-i*sqrt(7))/4| = sqrt(1/16+7/16) = 1/sqrt(2).                       *)
(* Second-largest |eigenvalue| = 1/sqrt(2), spectral gap = 1-1/sqrt(2).       *)
(*                                                                            *)
(* Convergence: var_dist <= sqrt(4) * (1/sqrt(2))^L = 2 * 2^{-L/2}.         *)
(* Equivalently: var_dist <= 2 * (1 - gap)^L with gap = 1-1/sqrt(2).        *)
(*                                                                            *)
(* Reference: Mizuki-Sone (2009), overlapping 3-cycles.                      *)
(******************************************************************************)

Section oc_spectral.

Variable R : realType.

Let M_oc := @Gen_PGGTypes 1 2 oc_sigmas.
Let R_oc : MonodromyReprWithGeneratorType := M_oc.

(* The gap between the largest and the second-largest eigenvalue modulus of
   the Schreier walk, 1 - 1/sqrt(2) for these generators.  It is taken as a
   parameter rather than computed, so every bound in this section is
   conditional on it. *)
Variable oc_spectral_gap : R.
Hypothesis oc_gap_pos : (0 < oc_spectral_gap)%R.
Hypothesis oc_gap_le1 : (oc_spectral_gap <= 1)%R.

(* The law of the shuffle after L steps of the Schreier walk on the four card
   positions, one distribution per number of rounds. *)
Variable oc_schreier_rho : nat -> R.-fdist {perm 'I_4}.

(* The endpoint marginal of the L-round walk is within sqrt(4)*(1-gap)^L of
   uniform.  This is the assumption that carries the whole asymptotic half of
   the instance: the bounds below are exactly as strong as it is, and nothing
   in this file derives it from the eigenvalues quoted in the section header. *)
Hypothesis oc_spectral_convergence :
  forall (L : nat) (s : 'I_4),
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                     (oc_schreier_rho L))
           (fdist_uniform (card_ord 4))
  <= Num.sqrt 4%:R * (1 - oc_spectral_gap) ^+ L)%O.

(* The asymptotic certificate of the overlapping-cycles walk: geometric decay
   at rate 1 - gap with no residual floor, the eps_inf slot being zero.  A
   zero floor is what distinguishes a walk that reaches uniform in the limit
   from one that stalls at a fixed distance, as the abelian instance does. *)
Definition oc_asymptotic : @SecurityAsymptotic R R_oc.
Proof.
apply: (@MkSecurityAsymptotic R R_oc
  oc_spectral_gap 0
  oc_gap_pos oc_gap_le1
  (Order.POrderTheory.lexx 0)
  oc_schreier_rho).
move=> L s.
rewrite add0r.
exact: oc_spectral_convergence.
Defined.

(** oc_security_witness_schreier — the security half read at an arbitrary
    number of rounds: the endpoint marginal of the L-round walk is within
    sqrt(4)*(1-gap)^L of uniform, with the asymptotic certificate attached
    and no exact one.  Unlike the fiber bound at L = 2, whose epsilon is
    fixed at 1, this one prices each additional round, and it is conditional
    on the assumed spectral gap throughout. *)
Definition oc_security_witness_schreier (L : nat) :
    ShuffleCertificateBundle R R_oc :=
  @MkShuffleCertificateBundle R R_oc
    (@MkShuffleMarginalBound R R_oc L
      (Num.sqrt 4%:R * (1 - oc_spectral_gap) ^+ L)
      (oc_schreier_rho L)
      (fun s => oc_spectral_convergence L s))
    None
    (Some oc_asymptotic).

End oc_spectral.

(******************************************************************************)
(*     Spectral AlgebraicRigidity at L=83 (40-bit security)                   *)
(*                                                                            *)
(* 2 * (1/sqrt(2))^83 = 2 * 2^{-83/2} = 2^{1-41.5} = 2^{-40.5} < 2^{-40}. *)
(* For 128-bit security, use L=259 instead.                                   *)
(******************************************************************************)

Section oc_rigidity_cryptographically_secure.

Variable R : realType.

Let R_oc : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 1 2 oc_sigmas.

(* The threshold half enters as a parameter here: this section varies only
   the security half, so any covering whose parameters fit will do, and the
   genus-0 construction is left to the section below. *)
Variable oc_tw : ThresholdWitness R_oc.

(* The same spectral data as above, re-declared because the section closes
   over its own parameters. *)
Variable oc_spectral_gap : R.
Hypothesis oc_gap_pos : (0 < oc_spectral_gap)%R.
Hypothesis oc_gap_le1 : (oc_spectral_gap <= 1)%R.
Variable oc_schreier_rho : nat -> R.-fdist {perm 'I_4}.
Hypothesis oc_spectral_convergence :
  forall (L : nat) (s : 'I_4),
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                     (oc_schreier_rho L))
           (fdist_uniform (card_ord 4))
  <= Num.sqrt 4%:R * (1 - oc_spectral_gap) ^+ L)%O.

(** oc_rigidity_cryptographically_secure — the same algebraic choice read at
    83 rounds, where the geometric bound falls below 2^-40.  The epsilon is
    conditional on the assumed spectral gap and inherits nothing from the
    unconditional fiber bound, so the security half here is a statement about
    the Schreier walk under that hypothesis rather than an information-
    theoretic guarantee; the threshold half is whatever witness the caller
    supplies. *)
Definition oc_rigidity_cryptographically_secure : AlgebraicRigidity R R_oc :=
  @MkAlgebraicRigidity R R_oc
    (@oc_security_witness_schreier R oc_spectral_gap oc_gap_pos
       oc_gap_le1 oc_schreier_rho oc_spectral_convergence 83)
    oc_tw.

End oc_rigidity_cryptographically_secure.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section oc_rigidity.

Variable R : realType.

Let R_oc : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 1 2 oc_sigmas.

(* The monodromy group is nontrivial: the covering construction below needs
   more than one group element to act with. *)
Hypothesis HG_oc : (1 < #|pgg_G R_oc|)%N.

(* The Reed-Solomon alphabet: a finite field GF(q^m') with as many elements as
   there are card positions, so that a card position can carry a field
   element and the code's coordinates can be permuted by the monodromy. *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_oc).+1 = #|GF m' primeq|.

(* Every shuffle in the group acts on the code's coordinates by a permutation
   that fixes the evaluation point 0 and carries codewords to codewords.  This
   is the compatibility that lets the shares survive a shuffle: reconstructing
   after a shuffle and shuffling after reconstruction agree. *)
Variable sigma_code : pgg_gT R_oc -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_oc -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_oc ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* The covering the threshold half is read off: the Reed-Solomon code of the
   parameters above, presented as a genus-0 covering, where reconstruction
   needs no more shares than privacy already forbids. *)
Definition oc_covering : CoveringScheme R_oc :=
  genus0_covering HG_oc qn an HN sigma_fix0 code_auto.

(* The group is no larger than Klein's genus-0 automorphism bound.  This is
   the one algebraic-geometry input the threshold half takes on trust. *)
Hypothesis oc_genus0_klein :
  (#|pgg_G R_oc| <= klein_genus0_bound R_oc)%N.

(* The threshold half of the rigidity pair: the covering above together with
   the Klein bound it needs at genus 0.  Structural only, in the sense that it
   states that the covering's parameters fit together and exhibits no
   erasure-tolerant decoder. *)
Definition oc_threshold_witness : ThresholdWitness R_oc :=
  @MkThresholdWitness R_oc oc_covering (fun _ => oc_genus0_klein).

(** oc_rigidity — one algebraic choice, the two overlapping 3-cycles on four
    card positions, delivering both halves at once: the unconditional
    fiber-counted marginal bound at two rounds and the genus-0 threshold
    witness.  This is the pair without any mixing certificate attached; the
    spectral variant above trades the unconditional epsilon for a conditional
    one that decays with the number of rounds. *)
Definition oc_rigidity : AlgebraicRigidity R R_oc :=
  @MkAlgebraicRigidity R R_oc
    (shuffle_bundle_of_bound (oc_security_witness_2 R))
    oc_threshold_witness.

(* Derived properties *)

(* However long the words, no more group elements are reachable than the group
   holds.  The group here sits inside S_4, so the ceiling is 24 whatever the
   number of rounds; more rounds buy mixing, not search space. *)
Lemma oc_complexity (L : nat) :
  (@search_space R_oc L <= #|pgg_G R_oc|)%N.
Proof. exact: search_space_leG. Qed.

(* The covering falls on one of two sides: at genus 0 the group obeys the
   Klein bound and reconstruction needs exactly the privacy threshold, so the
   gap is closed; at positive genus the gap is at most twice the genus.  This
   is the coupling the rigidity record exists to expose, read here at the
   smallest group in the family for which the security half is nontrivial. *)
Lemma oc_tradeoff :
  let cs := tw_covering (ar_threshold oc_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_oc| <= klein_genus0_bound R_oc)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_oc oc_covering (fun _ => oc_genus0_klein)).
Qed.

End oc_rigidity.
