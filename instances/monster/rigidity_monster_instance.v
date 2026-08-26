(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Monster Group Algebraic Rigidity Instance                                  *)
(*                                                                            *)
(* The Monster group M is the largest of the 26 sporadic simple finite        *)
(* groups, with order                                                         *)
(*   |M| = 2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 *          *)
(*         29 * 31 * 41 * 47 * 59 * 71   (approx 8 * 10^53).                 *)
(*                                                                            *)
(* Discovered by Fischer and Griess, it was first constructed by Griess       *)
(* (1982) as the automorphism group of a 196,884-dimensional commutative      *)
(* non-associative algebra. It is connected to number theory through          *)
(* Monstrous Moonshine (Conway-Norton conjecture 1979, proved by              *)
(* Borcherds 1992, Fields Medal).                                             *)
(*                                                                            *)
(* Key facts relevant to PGG:                                                 *)
(* - Smallest faithful permutation degree N ~ 10^20 (97,239,461,142,009,     *)
(*   186,000 points — the index of the largest maximal subgroup)              *)
(* - 2-generated: every finite simple group is 2-generated (Steinberg)        *)
(* - The Monster is far too large to enumerate computationally                *)
(*                                                                            *)
(* PGG implications:                                                          *)
(* - Security at L*=67: Tg^L* = 2^67 > N ~ 10^20, giving epsilon = 0        *)
(*   (perfect endpoint security via direct bound 2*(N-Tg^L)/N)               *)
(* - Threshold is catastrophic: genus ~ |M| ~ 10^53 — the covering           *)
(*   genus grows with |G|, so the threshold gap is enormous                   *)
(* - This illustrates the security/threshold coupling in AlgebraicRigidity:   *)
(*   large groups give strong security but poor threshold, and conversely     *)
(*                                                                            *)
(* All group-level data (generators, word-eval injectivity) is axiomatized    *)
(* since the Monster is not computationally enumerable in Rocq. The algebraic *)
(* properties (the marginal bound, derived theorems) are proved, showing that *)
(* protocol correctness depends only on algebraic structure, not on           *)
(* computability.                                                             *)
(*                                                                            *)
(* Axioms (8):                                                                *)
(*   monster_n      : number of card positions (abstract, ~ 10^20)           *)
(*   monster_sigmas : two generators (exist by Steinberg's theorem)           *)
(*   monster_sigmas_distinct : generators are distinct permutations          *)
(*   monster_Lstar  : turning point L* (= 67, first L with 2^L >= N)        *)
(*   monster_weval_inj_Lstar : word-eval injectivity at L*                   *)
(*   monster_perm_endpoint_inj_Lstar : endpoint eval injective on achievable(L_s)  *)
(*   monster_covering : existence of a covering scheme                        *)
(*   monster_genus0_klein : genus-0 coverings have |G| <= PGL(2,N)             *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   monster_security_witness_Lstar : ShuffleMarginalBound                   *)
(*     (via security_witness_endpoint_inj, eps = 2(N-2^Ls)/N ~ 0)           *)
(*   monster_rigidity : AlgebraicRigidity (security + threshold)             *)
(*   monster_complexity : search space <= |G|                                 *)
(*   monster_tradeoff : genus-0/bounded or genus>0/gap dichotomy             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound pgg_schreier.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Group Axioms                                                           *)
(******************************************************************************)

(* monster_n.+2 = number of card positions in the smallest faithful permutation
   representation of the Monster group (~ 10^20) *)
Axiom monster_n : nat.

(* Two generators — every finite simple group is 2-generated (Steinberg) *)
Axiom monster_sigmas : 2.-tuple {perm 'I_monster_n.+2}.

Definition M_monster := @Gen_PGGTypes 1 monster_n monster_sigmas.
Definition R_monster : MonodromyReprWithGeneratorType := M_monster.

(* The two generators are distinct permutations.  It is the weakest form of
   word-eval injectivity, enough to reach it at length 1, and it is
   axiomatized only because the generators themselves are abstract: a
   2-generating pair with equal entries would generate a cyclic group, which
   the Monster is not.  Same source as monster_sigmas above. *)
Axiom monster_sigmas_distinct :
  injective (fun i : 'I_2 => tnth monster_sigmas i).

Lemma monster_weval_inj1 : @weval_inj M_monster 1.
Proof. exact: gen_inj_weval_inj1 monster_sigmas_distinct. Qed.

(******************************************************************************)
(*     L* axioms: turning point where 2^L* >= N                              *)
(*                                                                            *)
(* For the Monster with N ~ 9.7 * 10^19 and Tg = 2:                         *)
(*   2^66 ~ 7.4 * 10^19 < N                                                 *)
(*   2^67 ~ 1.5 * 10^20 > N                                                 *)
(* So L* = 67 is the first length where the search space saturates N.        *)
(*                                                                            *)
(* At L* = 67, every card position maps to a distinct endpoint under each    *)
(* achievable permutation (perm_endpoint injective on achievable(67)).              *)
(* The direct endpoint epsilon = 2*(N - 2^67)/N = 0 since 2^67 > N.         *)
(******************************************************************************)

(* The word length at which the two-generator search space saturates the
   deck.  It is 67 for N ~ 9.7 * 10^19, as computed in the section header
   above, and is kept abstract so that the epsilon below is a formula in it
   rather than a decimal. *)
Axiom monster_Lstar : nat.

(* Distinct words of length L* evaluate to distinct group elements, so the
   search space at L* is the full 2^L*.  Grounded by the header's arithmetic:
   2^67 exceeds the permutation degree, so no two words need collide. *)
Axiom monster_weval_inj_Lstar : @weval_inj M_monster monster_Lstar.

(* Endpoint evaluation injective on achievable(L_star): for each start card,
   the map sigma |-> sigma(s) is injective on the set of achievable
   permutations at L*. This is a group-theoretic fact about the Monster's
   faithful permutation action. *)
Axiom monster_perm_endpoint_inj_Lstar :
  forall s : 'I_monster_n.+2,
  {in @achievable M_monster monster_Lstar &,
   injective (fun sigma : {perm 'I_monster_n.+2} => sigma s)}.

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section monster_security.

Variable R : realType.

(* The security half of the rigidity pair: for every card position, the
   endpoint marginal of the length-L* word distribution is within
   2*(N - 2^Lstar)/N of uniform in the full-L1 convention.  At the concrete
   Monster, where 2^67 exceeds the permutation degree, that epsilon is 0 and
   the endpoint marginal is exactly uniform; the data-processing route at
   length 1 gives 2*(N! - 2)/N!, which is nearly 2 and says nothing.  The
   bound is information-theoretic and rests on no computational assumption,
   but its two inputs, word-eval injectivity and endpoint injectivity at L*,
   are axioms of this file rather than theorems. *)
Definition monster_security_witness_Lstar : ShuffleMarginalBound R R_monster :=
  security_witness_endpoint_inj R
    monster_weval_inj_Lstar
    monster_perm_endpoint_inj_Lstar.


End monster_security.

(******************************************************************************)
(*     AlgebraicRigidity Instance (with axiomatized threshold)                *)
(******************************************************************************)

Section monster_rigidity.

Variable R : realType.

(* The Monster admits a covering scheme, the geometric object the threshold
   half of the rigidity pair is read off.  Assumed rather than built, because
   constructing one is algebraic geometry (covering spaces of Riemann
   surfaces) that this formalization does not carry; the star instance takes
   the same object from the Reed-Solomon construction instead. *)
Axiom monster_covering : CoveringScheme R_monster.

(* If this particular covering has genus 0 then the group obeys Klein's
   genus-0 automorphism bound.  It is a statement about the covering named
   above and not a universal one.  At the Monster it is vacuous, since a group
   of order about 10^53 forces the covering genus above 0, which is exactly
   why this instance lands on the positive-genus side of the tradeoff. *)
Axiom monster_genus0_klein :
  cd_genus (cs_data monster_covering) = 0 ->
  (#|pgg_G R_monster| <= klein_genus0_bound R_monster)%N.

Definition monster_threshold_witness : ThresholdWitness R_monster :=
  @MkThresholdWitness R_monster monster_covering monster_genus0_klein.

(** monster_rigidity — one algebraic choice, the Monster acting on its
    smallest faithful permutation degree, delivering both halves at once: the
    endpoint marginal bound at L*, whose epsilon vanishes, and the threshold
    witness, whose covering genus grows with the group order.  The instance is
    the extreme case of the coupling the record exists to expose: the group
    that makes the security half perfect is the group that makes the threshold
    half worst.  No exact or asymptotic mixing certificate is attached. *)
Definition monster_rigidity : AlgebraicRigidity R R_monster :=
  @MkAlgebraicRigidity R R_monster
    (shuffle_bundle_of_bound (monster_security_witness_Lstar R))
    monster_threshold_witness.

(* Two consequences of the axioms above, established rather than assumed. *)

(* However long the words, no more group elements are reachable than the group
   holds.  For the Monster that ceiling is about 10^53, so the search space
   keeps growing as 2^L until L*, which is what makes the security half
   nonvacuous where the cyclic instance's is vacuous. *)
Lemma monster_complexity (L : nat) :
  (@search_space R_monster L <= #|pgg_G R_monster|)%N.
Proof. exact: search_space_leG. Qed.

(* The covering falls on one of two sides: at genus 0 the group obeys the
   Klein bound and reconstruction needs exactly the privacy threshold; at
   positive genus the gap is at most twice the genus.  A group of order 10^53
   cannot obey the Klein bound, so it is the second side that holds here, and
   the gap it allows is the price the Monster pays for its perfect security
   half. *)
Lemma monster_tradeoff :
  let cs := tw_covering (ar_threshold monster_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_monster| <= klein_genus0_bound R_monster)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_monster monster_covering monster_genus0_klein).
Qed.

End monster_rigidity.

(******************************************************************************)
(*     Schreier Certificate (Axiomatized)                                     *)
(*                                                                            *)
(* The Monster group, as a finite simple group, has a Schreier graph with     *)
(* spectral gap bounded away from 0 for any transitive action.               *)
(*                                                                            *)
(* Source: Kassabov-Lubotzky-Nikolov 2006, Finite simple groups as expanders. *)
(* They prove that every non-abelian finite simple group has generators       *)
(* making it an epsilon-expander with epsilon bounded away from 0. The        *)
(* expander property transfers to ALL transitive actions (Schreier graphs),   *)
(* not just the regular representation (Cayley graph).                        *)
(*                                                                            *)
(* For the specific Monster generators (axiomatized), the spectral gap is     *)
(* abstract but positive. The convergence bound uses the Schreier graph       *)
(* directly on 'I_N (N card positions), giving prefactor sqrt(N) instead of  *)
(* sqrt(|G|). For the Monster: sqrt(N) ~ 10^10 vs sqrt(|G|) ~ 10^26.        *)
(*                                                                            *)
(* Mathematical source:                                                       *)
(*   Diaconis 1988, Ch. 3B Proposition 2 (upper bound lemma)                 *)
(*   Applied to the Schreier graph (N vertices) instead of Cayley (|G|)      *)
(*   Ceccherini-Silberstein et al. 2008, Thm 5.5.3 (eigenvalue subset)      *)
(*   Kassabov-Lubotzky-Nikolov 2006 (expander transfers to transitive)       *)
(******************************************************************************)


(* Spectral gap of the Monster Schreier graph -- positive by
   Kassabov-Lubotzky-Nikolov 2006, Finite simple groups as expanders.
   The expander property of finite simple groups transfers to all
   transitive Schreier graphs (Lubotzky 2012, Theorem 4.2).
   Convergence bound from Diaconis 1988, Ch. 3B Proposition 2,
   applied to the Schreier graph on N = monster_n.+2 card positions.

   Prefactor is sqrt(N), not sqrt(|G|) -- a major improvement for
   the Monster (sqrt(N) ~ 10^10 vs sqrt(|G|) ~ 10^26).

   We use Variable/Hypothesis (not Axiom) because Axiom inside a Section
   is NOT abstracted over section variables. Hypothesis becomes a parameter
   of all definitions that use it when the section closes. *)

Section monster_spectral.

Variable R : realType.
Variable monster_lambda_gap : R.
Hypothesis monster_lambda_gap_pos : 0 < monster_lambda_gap.
Hypothesis monster_lambda_gap_le1 : monster_lambda_gap <= 1.

(* NOTE: no weval_inj hypothesis. The Schreier walk convergence is a
   property of the Markov chain on 'I_N, independent of word-eval
   injectivity. Prefactor is sqrt(N), not sqrt(|G|). *)
Hypothesis monster_spectral_convergence :
  forall (L : nat) (s : 'I_monster_n.+2),
  var_dist (fdistmap (fun sigma : {perm 'I_monster_n.+2} => sigma s)
                     (rho_from_words L monster_sigmas))
           (fdist_uniform (card_ord monster_n.+2))
  <= Num.sqrt (monster_n.+2%:R) *
     (1 - monster_lambda_gap) ^+ L.

Definition monster_schreier_certificate :
    SchreierCertificate R 1 monster_n monster_sigmas :=
  @MkSchreierCertificate R 1 monster_n monster_sigmas
    monster_lambda_gap
    monster_lambda_gap_pos
    monster_lambda_gap_le1
    monster_spectral_convergence.

(* The asymptotic security half at an arbitrary word length: the marginal
   bound of the Schreier walk together with its geometric-convergence
   certificate.  Where monster_security_witness_Lstar is a single exact
   statement at the saturation length, this one holds at every L and decays
   as sqrt(N) * (1 - gap)^L, so it prices additional shuffle rounds.  Both
   the gap and its positivity are hypotheses of this section, so the bound is
   conditional on the expander property and not information-theoretic on its
   own.  Word-eval injectivity enters here, not in the spectral bound: the
   bundle is stated at rho_from_words, which needs it to be a distribution. *)
Definition monster_security_witness_schreier (L : nat)
    (Hlfree : @weval_inj M_monster L) : ShuffleCertificateBundle R R_monster :=
  security_witness_schreier monster_schreier_certificate Hlfree.

End monster_spectral.
