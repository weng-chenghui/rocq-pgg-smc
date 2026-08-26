(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Cyclic Group (N-Cycle) Algebraic Rigidity Instance                         *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the cyclic group      *)
(* Z/NZ acting on N card positions via the canonical N-cycle permutation      *)
(* (0 1 2 ... N-1).                                                           *)
(*                                                                            *)
(* The one-generator corner of the instance family: Tg = 1, N = n+2 card      *)
(* positions, word length L = 1.  A single generator makes the length-1 word  *)
(* distribution a point mass on that one permutation, so the endpoint         *)
(* marginal is a point mass too and sits at full-L1 distance 2*(N-1)/N from   *)
(* uniform.  That is the epsilon the marginal bound carries.  It is the       *)
(* no-mixing end of the family, kept because the rigidity record still        *)
(* assembles there: one algebraic choice supplies both halves even when the   *)
(* security half says nothing.                                                *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 1 (one generator: the N-cycle), N = n+2 (card positions), L = 1    *)
(*   epsilon = 2 * (N - 1) / N  (via security_witness_endpoint_inj)           *)
(*                                                                            *)
(* The endpoint-injectivity hypothesis of that constructor is discharged      *)
(* rather than assumed: with one generator the achievable set at L = 1 is a   *)
(* singleton, on which every map is injective.                                *)
(*                                                                            *)
(* Key properties:                                                            *)
(*   ncycle_sigmas_inj : the generator tuple is injective                    *)
(*   ncycle_weval_inj1 : word-eval injectivity at L=1                        *)
(*   ncycle_security_witness_direct_1 : ShuffleMarginalBound (endpoint_inj)  *)
(*   ncycle_rigidity : AlgebraicRigidity (security + threshold)              *)
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
                            pgg_collusion_bound pgg_abelian.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section ncycle_security.

Variable R : realType.
Variable n : nat.

(* The cyclic group Z/NZ acting on the N = n+2 card positions by the
   canonical N-cycle, presented through the generic generator-tuple template
   so that the constructors of algebraic_rigidity.v apply to it verbatim. *)
Let ncycle_sigs := cyclic_sigmas (ncycle n).
Let M_ncycle := @Gen_PGGTypes 0 n ncycle_sigs.
Let R_ncycle : MonodromyReprWithGeneratorType := M_ncycle.

(* Distinct generator indices name distinct permutations.  There is one index,
   so the condition holds with nothing to check; the instance still has to
   supply it, because the search-space theory counts group elements and not
   index patterns. *)
Lemma ncycle_sigmas_inj :
  injective (fun i : 'I_1 => tnth ncycle_sigs i).
Proof. by move=> i j _; rewrite (ord1 i) (ord1 j). Qed.

(* Distinct one-letter words evaluate to distinct group elements. *)
Lemma ncycle_weval_inj1 : @weval_inj M_ncycle 1.
Proof. exact: gen_inj_weval_inj1 ncycle_sigmas_inj. Qed.

(* For each card position, reading a permutation at that position is
   injective on the achievable set at L = 1.  With one generator that set is
   a singleton, so the hypothesis holds for the degenerate reason, and the
   epsilon 2*(N-1)/N it buys is the distance of a point mass from uniform
   rather than a mixing guarantee. *)
Lemma ncycle_perm_endpoint_inj1 :
  forall s : 'I_(n.+2),
  {in @achievable M_ncycle 1 &,
   injective (fun sigma : {perm 'I_(n.+2)} => sigma s)}.
Proof.
(* achievable(1) for Tg=1 has exactly 1 element → perm_endpoint trivially injective *)
move=> s x y Hx Hy _.
suff : (#|@achievable M_ncycle 1| <= 1)%N by move/card_le1_eqP; apply.
have -> : #|@achievable M_ncycle 1| = @search_space M_ncycle 1 by [].
rewrite (weval_inj_search_space ncycle_weval_inj1).
by rewrite exp1n.
Qed.

(** ncycle_security_witness_direct_1 — the security half of the rigidity
    pair: for every card position, the endpoint marginal of the length-1
    N-cycle word distribution is within 2*(N-1)/N of uniform in the full-L1
    convention.  The bound goes through the endpoint route rather than the
    data-processing route, and at a single generator the two coincide in
    saying nothing: the marginal is a point mass and 2*(N-1)/N is its exact
    distance from uniform.  Nothing here is conditional on a computational
    assumption. *)
Definition ncycle_security_witness_direct_1 : ShuffleMarginalBound R R_ncycle :=
  security_witness_endpoint_inj R ncycle_weval_inj1 ncycle_perm_endpoint_inj1.

End ncycle_security.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section ncycle_rigidity.

Variable R : realType.
Variable n : nat.

Let ncycle_sigs := cyclic_sigmas (ncycle n).
Let R_ncycle : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 0 n ncycle_sigs.

(* The monodromy group is nontrivial: the covering construction below needs
   more than one group element to act with. *)
Hypothesis HG_ncycle : (1 < #|pgg_G R_ncycle|)%N.

(* The Reed-Solomon alphabet: a finite field GF(q^m') with as many elements as
   there are card positions, so that a card position can carry a field
   element and the code's coordinates can be permuted by the monodromy. *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_ncycle).+1 = #|GF m' primeq|.

(* Every shuffle in the group acts on the code's coordinates by a permutation
   that fixes the evaluation point 0 and carries codewords to codewords.  This
   is the compatibility that lets the shares survive a shuffle: reconstructing
   after a shuffle and shuffling after reconstruction agree. *)
Variable sigma_code : pgg_gT R_ncycle -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_ncycle -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_ncycle ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* The covering the threshold half is read off: the Reed-Solomon code of the
   parameters above, presented as a genus-0 covering.  Genus 0 is the case
   where reconstruction needs no more shares than privacy already forbids, so
   the threshold gap is zero. *)
Definition ncycle_covering : CoveringScheme R_ncycle :=
  genus0_covering HG_ncycle qn an HN sigma_fix0 code_auto.

(* The group is no larger than Klein's genus-0 automorphism bound.  This is
   the one algebraic-geometry input the threshold half takes on trust; it is
   assumed here rather than derived. *)
Hypothesis ncycle_genus0_klein :
  (#|pgg_G R_ncycle| <= klein_genus0_bound R_ncycle)%N.

(* The threshold half of the rigidity pair: the covering above together with
   the Klein bound it needs at genus 0.  Structural only, in the sense that it
   states that the covering's parameters fit together and exhibits no
   erasure-tolerant decoder. *)
Definition ncycle_threshold_witness : ThresholdWitness R_ncycle :=
  @MkThresholdWitness R_ncycle ncycle_covering (fun _ => ncycle_genus0_klein).

(** ncycle_rigidity — one algebraic choice, the N-cycle acting on N card
    positions, delivering both halves at once: the length-1 endpoint marginal
    bound and the genus-0 threshold witness.  The security half is
    unconditional and vacuous at this group, the threshold half rests on the
    Klein bound hypothesis; no certificate of exact or asymptotic mixing is
    attached to either. *)
Definition ncycle_rigidity : AlgebraicRigidity R R_ncycle :=
  @MkAlgebraicRigidity R R_ncycle
    (shuffle_bundle_of_bound (ncycle_security_witness_direct_1 R n))
    ncycle_threshold_witness.

(* Derived properties *)

(* However long the words, no more group elements are reachable than the group
   holds.  For the N-cycle the group has N elements, so an adversary
   enumerating shuffles faces N candidates whatever L is; adding rounds buys
   no search-space growth here. *)
Lemma ncycle_complexity (L : nat) :
  (@search_space R_ncycle L <= #|pgg_G R_ncycle|)%N.
Proof. exact: search_space_leG. Qed.

(* The covering falls on one of two sides.  At genus 0 the group obeys the
   Klein bound and reconstruction needs exactly the privacy threshold, so the
   gap is closed; at positive genus the gap is at most twice the genus.  This
   is the coupling the rigidity record exists to expose: the same algebraic
   choice that fixes the security half fixes which side of this dichotomy the
   threshold half lands on. *)
Lemma ncycle_tradeoff :
  let cs := tw_covering (ar_threshold ncycle_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_ncycle| <= klein_genus0_bound R_ncycle)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_ncycle ncycle_covering
                                     (fun _ => ncycle_genus0_klein)).
Qed.

End ncycle_rigidity.
