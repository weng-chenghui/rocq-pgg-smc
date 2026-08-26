(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Abelian (Disjoint Transpositions) Algebraic Rigidity Instance              *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the abelian group     *)
(* Z/2Z x Z/2Z acting on 4 card positions via two disjoint transpositions    *)
(* sigma_1 = (0 1) and sigma_2 = (2 3).                                      *)
(*                                                                            *)
(* The two generators commute, so the group they reach is the Klein          *)
(* four-group {id, (01), (23), (01)(23)} and no word, however long, reaches   *)
(* a fifth shuffle.  This is the negative corner of the family: the security  *)
(* half assembles and its epsilon does not improve with the number of rounds. *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 2 (generators), N = 4 (card positions), L = 1, depth = 1          *)
(*   epsilon = 2 * (4 - 2) / 4 = 1, on the endpoint route                   *)
(*                                                                            *)
(* The instance takes the endpoint route rather than the data-processing one, *)
(* whose epsilon here would be 2 * (4! - 2) / 4! = 44/24, nearly the maximum  *)
(* distance of 2.  The endpoint epsilon of 1 is attained: at card position 0  *)
(* the marginal is 1/2 on 0, 1/2 on 1 and nothing elsewhere.                  *)
(*                                                                            *)
(* Key properties:                                                            *)
(*   abel_sigmas_distinct : generators are distinct permutations             *)
(*   abel_weval_inj1 : word-eval injectivity at L=1                          *)
(*   abel_security_witness_direct_1 : ShuffleMarginalBound (endpoint_inj)    *)
(*   abel_rigidity : AlgebraicRigidity (security + threshold)                *)
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

(******************************************************************************)
(*     Generator Definitions                                                  *)
(******************************************************************************)

(* The two generators are the transpositions (0 1) and (2 3) of the four card
   positions.  Their supports are disjoint, which is what makes them commute
   and hence what makes this instance abelian. *)

(** abel_s1 — the first generator, swapping card positions 0 and 1. *)
Definition abel_s1 : {perm 'I_4} :=
  tperm (Ordinal (n:=4) (isT : (0 < 4)%N))
        (Ordinal (n:=4) (isT : (1 < 4)%N)).

(** abel_s2 — the second generator, swapping card positions 2 and 3. *)
Definition abel_s2 : {perm 'I_4} :=
  tperm (Ordinal (n:=4) (isT : (2 < 4)%N))
        (Ordinal (n:=4) (isT : (3 < 4)%N)).

(** abel_sigmas — the two generators as a tuple, the shape a PGGTypes value
    stores its generating family in. *)
Definition abel_sigmas : 2.-tuple {perm 'I_4} :=
  [tuple abel_s1; abel_s2].

(* The two generators are different permutations, as they move different
   cards. *)
Lemma abel_s1_neq_s2 : abel_s1 != abel_s2.
Proof.
apply/eqP => Habs.
have := congr1 (fun sigma : {perm 'I_4} =>
  sigma (Ordinal (n:=4) (isT : (0 < 4)%N))) Habs.
by rewrite /abel_s1 tpermL /abel_s2 tpermD.
Qed.

(** abel_sigmas_distinct — distinct generator indices name distinct
    permutations.  The search-space theory counts group elements, so without
    this the two indices could name one shuffle and the counts below would be
    counting labels. *)
Lemma abel_sigmas_distinct :
  injective (fun i : 'I_2 => tnth abel_sigmas i).
Proof.
move=> i j Heq; apply val_inj.
move: Heq; rewrite /abel_sigmas (tnth_nth abel_s1) (tnth_nth abel_s1).
case: i => [[|[|i]] Hi] //; case: j => [[|[|j]] Hj] //= Habs;
  exfalso; move/eqP: abel_s1_neq_s2; apply;
  first [exact: Habs | exact: esym Habs].
Qed.

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section abel_security.

Variable R : realType.

Let M_abel := @Gen_PGGTypes 1 2 abel_sigmas.
Let R_abel : MonodromyReprWithGeneratorType := M_abel.

(* Distinct one-letter words evaluate to distinct shuffles.  At length 1 a
   word is a generator index, so this is generator distinctness restated at
   the word level; it fails at length 2, where the four words already reach
   only the four group elements once. *)
Lemma abel_weval_inj1 : @weval_inj M_abel 1.
Proof. exact: gen_inj_weval_inj1 abel_sigmas_distinct. Qed.

(* For each card position, reading a permutation at that position is
   injective on the two shuffles a one-letter word can produce: the two
   generators have disjoint supports, so they never agree on any card.  This
   is what buys the endpoint route its epsilon of 2*(4-2)/4 = 1, against the
   data-processing route's 44/24. *)
Lemma abel_perm_endpoint_inj1 :
  forall s : 'I_4,
  {in @achievable M_abel 1 &,
   injective (fun sigma : {perm 'I_4} => sigma s)}.
Proof.
move=> s x y Hx Hy Hf; move: Hf.
rewrite /achievable in Hx Hy.
case/imsetP: Hx => wx _ ->.
case/imsetP: Hy => wy _ ->.
rewrite /word_eval !big_ord_recr !big_ord0 /= !mul1g => Hf.
move: (tnth wx ord_max) (tnth wy ord_max) Hf => i j.
rewrite /pgg_sigmas /abel_sigmas !(tnth_nth abel_s1) /=.
case: i => [[|[|i]] Hi]; case: j => [[|[|j]] Hj] //=;
  rewrite /abel_s1 /abel_s2;
  case: s => [[|[|[|[|s]]]] Hs] //= => Hf;
  by have := congr1 val Hf; rewrite !permE.
Qed.

(** abel_security_witness_direct_1 — the security half of the rigidity pair:
    for every card position, the endpoint marginal of the length-1 word
    distribution is within 1 of uniform in the full-L1 convention, where 2 is
    the largest such distance.  The bound is attained, since the marginal puts
    half its mass on the card and half on its image and none on the other two.
    The epsilon does not fall with the word length, because the group has only
    four elements to spread over; the bound is unconditional and does not rest
    on any computational assumption. *)
Definition abel_security_witness_direct_1 : ShuffleMarginalBound R R_abel :=
  security_witness_endpoint_inj R abel_weval_inj1 abel_perm_endpoint_inj1.

End abel_security.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section abel_rigidity.

Variable R : realType.

Let R_abel : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 1 2 abel_sigmas.

(* The monodromy group is nontrivial: the covering construction below needs
   more than one group element to act with. *)
Hypothesis HG_abel : (1 < #|pgg_G R_abel|)%N.

(* The Reed-Solomon alphabet: a finite field GF(q^m') with as many elements as
   there are card positions, so that a card position can carry a field
   element and the code's coordinates can be permuted by the monodromy. *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_abel).+1 = #|GF m' primeq|.

(* Every shuffle in the group acts on the code's coordinates by a permutation
   that fixes the evaluation point 0 and carries codewords to codewords.  This
   is the compatibility that lets the shares survive a shuffle: reconstructing
   after a shuffle and shuffling after reconstruction agree. *)
Variable sigma_code : pgg_gT R_abel -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_abel -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_abel ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* The covering the threshold half is read off: the Reed-Solomon code of the
   parameters above, presented as a genus-0 covering, where reconstruction
   needs no more shares than privacy already forbids. *)
Definition abel_covering : CoveringScheme R_abel :=
  genus0_covering HG_abel qn an HN sigma_fix0 code_auto.

(* The group is no larger than Klein's genus-0 automorphism bound.  This is
   the one algebraic-geometry input the threshold half takes on trust.  A
   four-element group meets it with room to spare, which is the other side of
   the coupling: the group that gives the worst security half gives the best
   threshold half. *)
Hypothesis abel_genus0_klein :
  (#|pgg_G R_abel| <= klein_genus0_bound R_abel)%N.

(** abel_threshold_witness — the threshold half of the rigidity pair: the
    genus-0 Reed-Solomon covering together with the Klein bound it needs.
    Structural only, in the sense that it states that the covering's
    parameters fit together and exhibits no erasure-tolerant decoder. *)
Definition abel_threshold_witness : ThresholdWitness R_abel :=
  @MkThresholdWitness R_abel abel_covering (fun _ => abel_genus0_klein).

(** abel_rigidity — one algebraic choice, two commuting transpositions of
    four cards, delivering both halves at once: the length-1 endpoint marginal
    bound, whose epsilon is 1 and stays there, and the genus-0 threshold
    witness, which is as good as the family allows.  It is the mirror of the
    Monster instance, where the security half is perfect and the threshold
    half catastrophic, and together the two mark the ends of the coupling the
    rigidity record exists to expose.  No mixing certificate is attached. *)
Definition abel_rigidity : AlgebraicRigidity R R_abel :=
  @MkAlgebraicRigidity R R_abel
    (shuffle_bundle_of_bound (abel_security_witness_direct_1 R))
    abel_threshold_witness.

(* Derived properties *)

(* However long the words, no more shuffles are reachable than the group
   holds, which here is four.  An adversary enumerating shuffles of this
   instance faces four candidates at every round count. *)
Lemma abel_complexity (L : nat) :
  (@search_space R_abel L <= #|pgg_G R_abel|)%N.
Proof. exact: search_space_leG. Qed.

(** abel_tradeoff — the covering falls on one of two sides: at genus 0 the
    group obeys the Klein bound and reconstruction needs exactly the privacy
    threshold, so the gap is closed; at positive genus the gap is at most
    twice the genus.  Read at the smallest group in the family, this is the
    end of the dichotomy where the threshold half costs nothing. *)
Lemma abel_tradeoff :
  let cs := tw_covering (ar_threshold abel_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_abel| <= klein_genus0_bound R_abel)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_abel abel_covering
                                     (fun _ => abel_genus0_klein)).
Qed.

End abel_rigidity.
