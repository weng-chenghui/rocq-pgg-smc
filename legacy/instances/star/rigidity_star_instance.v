(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG — Star-Graph Algebraic Rigidity Instance                               *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the star-graph RAAG.  *)
(*                                                                            *)
(* The marginal bound uses fiber-counted epsilon:                             *)
(*   epsilon = 2 * (m+1) / (m+3)  at L=1 (worst-case card position s≠2)     *)
(*                                                                            *)
(* The ThresholdWitness uses a genus-0 covering scheme constructed from       *)
(* Reed-Solomon codes (via genus0_covering from cover_genus0.v).              *)
(* The PGL bound remains as a hypothesis (algebraic geometry).               *)
(*                                                                            *)
(* vm_compute demonstrations:                                                 *)
(*   star_nt_m2_L1 : n_traces_natB 3 1 (star_comm_nat 2) = 3                *)
(*   star_nt_m2_L2 : n_traces_natB 3 2 (star_comm_nat 2) = 7                *)
(*   star_nt_m2_L3 : n_traces_natB 3 3 (star_comm_nat 2) = 15               *)
(*   star_nt_m2_L4 : n_traces_natB 3 4 (star_comm_nat 2) = 31               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
From infotheo Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import pgg_free_words.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag
                             card_exchange_pismc.
From pgg_smc Require Import pgg_raag_star pgg_raag_clique pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     vm_compute Demonstrations                                              *)
(******************************************************************************)

(* The trace counts of the star graph at m = 2 and m = 3, computed on the
   nat-level model.  They put the abstract lower bound m^L <= n_traces L on
   concrete numbers: at m = 2 the counts 3, 7, 15, 31 stay above 2^L, and at
   m = 3 the counts 4, 13, 40 stay above 3^L.  They also show the counts
   falling short of Tg^L, which is where the center generator's commutations
   are doing their collapsing. *)

(* m=2 (N=5, Tg=3): star with 2 leaves *)
Lemma star_nt_m2_L1 : n_traces_natB 3 1 (star_comm_nat 2) = 3.
Proof. by vm_compute. Qed.

Lemma star_nt_m2_L2 : n_traces_natB 3 2 (star_comm_nat 2) = 7.
Proof. by vm_compute. Qed.

Lemma star_nt_m2_L3 : n_traces_natB 3 3 (star_comm_nat 2) = 15.
Proof. by vm_compute. Qed.

Lemma star_nt_m2_L4 : n_traces_natB 3 4 (star_comm_nat 2) = 31.
Proof. by vm_compute. Qed.

(* m=3 (N=6, Tg=4): star with 3 leaves — cross-check with pgg_raag_clique *)
Lemma star_nt_m3_L1 : n_traces_natB 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

Lemma star_nt_m3_L2 : n_traces_natB 4 2 (star_comm_nat 3) = 13.
Proof. by vm_compute. Qed.

Lemma star_nt_m3_L3 : n_traces_natB 4 3 (star_comm_nat 3) = 40.
Proof. by vm_compute. Qed.

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section star_security.

Variable R : realType.
Variable m : nat.

Let M_star := @Gen_PGGTypes m m.+1 (star_gen_tuple m).
Let R_star : MonodromyReprWithGeneratorType := M_star.
Let N := m.+3.
Let Tg := m.+1.

Local Open Scope ring_scope.

(* Distinct one-letter words evaluate to distinct group elements, which for a
   RAAG follows from the generators being pairwise distinct. *)
Lemma star_weval_inj1 : @weval_inj M_star 1.
Proof. exact: raag_weval_inj1. Qed.

(* For every card position, the endpoint marginal of the length-1 star word
   distribution is within 2*(m+1)/(m+3) of uniform in the full-L1 convention.
   The epsilon is read off the fibers: a position other than 2 is moved by
   exactly one of the m+1 generators and fixed by the other m, so its
   marginal puts mass m/(m+1) on itself and 1/(m+1) on its image.  The bound
   worsens toward 2 as m grows, which is the price of one round on a deck
   that grows with the generator count.
   Taken here without proof, so every statement below that reads the marginal
   bound is conditional on it. *)
Lemma star_endpoint_bound_fiber :
  forall s : 'I_(m.+3),
  (var_dist (fdistmap (fun sigma : {perm 'I_(m.+3)} => sigma s)
                     (@rho_from_words R _ _ 1 (star_gen_tuple m)))
           (fdist_uniform (card_ord m.+3)) <=
   2%:R * m.+1%:R / m.+3%:R)%O.
Proof. Admitted.

(** star_security_witness_1 — the security half of the rigidity pair: the
    fiber-counted marginal bound of the star generators at one round,
    epsilon = 2*(m+1)/(m+3).  The data-processing route gives
    2*(N!-Tg)/N!, which is essentially 2 and says nothing; fiber counting is
    what leaves any margin here.  It inherits the assumed status of
    star_endpoint_bound_fiber. *)
Definition star_security_witness_1 : ShuffleMarginalBound R R_star :=
  security_witness_fiber star_weval_inj1 star_endpoint_bound_fiber.

End star_security.

(******************************************************************************)
(*     ThresholdWitness (genus-0 covering from RS codes)                      *)
(******************************************************************************)

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section star_rigidity.

Variable R : realType.
Variable m : nat.

Let R_star : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes m m.+1 (star_gen_tuple m).

(* The monodromy group is nontrivial: the covering construction below needs
   more than one group element to act with. *)
Hypothesis HG_star : (1 < #|pgg_G R_star|)%N.

(* The Reed-Solomon alphabet: a finite field GF(q^m') with as many elements as
   there are card positions, so that a card position can carry a field
   element and the code's coordinates can be permuted by the monodromy. *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_star).+1 = #|GF m' primeq|.

(* Every shuffle in the group acts on the code's coordinates by a permutation
   that fixes the evaluation point 0 and carries codewords to codewords.  This
   is the compatibility that lets the shares survive a shuffle: reconstructing
   after a shuffle and shuffling after reconstruction agree. *)
Variable sigma_code : pgg_gT R_star -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_star -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_star ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* The covering the threshold half is read off: the Reed-Solomon code of the
   parameters above, presented as a genus-0 covering, where reconstruction
   needs no more shares than privacy already forbids. *)
Definition star_covering : CoveringScheme R_star :=
  genus0_covering HG_star qn an HN sigma_fix0 code_auto.

(* The group is no larger than Klein's genus-0 automorphism bound.  It is
   stated unconditionally rather than under a genus-0 premise, because this
   covering has genus 0 by construction. *)
Hypothesis star_genus0_klein :
  (#|pgg_G R_star| <= klein_genus0_bound R_star)%N.

(* The threshold half of the rigidity pair: the covering above together with
   the Klein bound it needs at genus 0.  Structural only, in the sense that it
   states that the covering's parameters fit together and exhibits no
   erasure-tolerant decoder. *)
Definition star_threshold_witness : ThresholdWitness R_star :=
  @MkThresholdWitness R_star star_covering (fun _ => star_genus0_klein).

(** star_rigidity — one algebraic choice, the star RAAG on m+3 card
    positions, delivering both halves at once: the one-round fiber marginal
    bound, with no mixing certificate attached, and the genus-0 threshold
    witness.  The star sits between the abelian and Monster extremes: its
    group grows with m and stays non-abelian, so both halves move together as
    m does. *)
Definition star_rigidity : AlgebraicRigidity R R_star :=
  @MkAlgebraicRigidity R R_star
    (shuffle_bundle_of_bound (star_security_witness_1 R m))
    star_threshold_witness.

(* However long the words, no more group elements are reachable than the group
   holds. *)
Lemma star_complexity (L : nat) :
  (@search_space R_star L <= #|pgg_G R_star|)%N.
Proof. exact: search_space_leG. Qed.

(* The search space is squeezed between the trace count and the raw word
   count.  Read together with star_traces_lb, which puts m^L under the trace
   count, this places the search-space ceiling between m^L and (m+1)^L: the
   star graph's single center edge is all that separates this instance from
   the free case.  The chain is a property of the RAAG structure, so it is
   stated at the RAAGType view of the same PGG. *)
Let R_star_raag : RAAGType := @Gen_PGGTypes m m.+1 (star_gen_tuple m).

Lemma star_search_chain (L : nat) :
  ((@search_space R_star_raag L <= @n_traces R_star_raag L) &&
   (@n_traces R_star_raag L <= m.+1 ^ L))%N.
Proof. exact: search_space_chain. Qed.

(* The covering falls on one of two sides: at genus 0 the group obeys the
   Klein bound and reconstruction needs exactly the privacy threshold; at
   positive genus the gap is at most twice the genus.  This is the coupling
   the rigidity record exists to expose. *)
Lemma star_tradeoff :
  let cs := tw_covering (ar_threshold star_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_star| <= klein_genus0_bound R_star)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_star star_covering (fun _ => star_genus0_klein)).
Qed.

(******************************************************************************)
(*     CertifiedSolution (solver -> proof bridge)                             *)
(******************************************************************************)

(* The instance's epsilon is bounded by the rational number 2*(m+1)/(m+3)
   written as a ratio of two naturals.  A solver can only hand back a
   rational, so this is the form in which the analytic epsilon meets the
   numeric one. *)
Lemma star_eps_rational :
  (sw_bound_eps (star_security_witness_1 R m) <=
   (2 * m.+1)%:R / m.+3%:R)%O.
Proof.
rewrite /= /security_witness_fiber /= GRing.natrM.
exact: Order.POrderTheory.lexx.
Qed.

(** star_certified_1 — the star instance packaged as a certified solution:
    the marginal bound at one round together with a rational certificate
    2*(m+1)/(m+3) for its epsilon.  The certificate is what a search
    procedure can produce and check, so this is the record that turns a
    solver's parameter choice into a bound a protocol may quote. *)
Definition star_certified_1 : CertifiedSolution R R_star :=
  @certified_from_bound R R_star
    (star_security_witness_1 R m)
    (2 * m.+1) m.+3
    (ltn0Sn m.+2)
    star_eps_rational.

(******************************************************************************)
(*     Protocol Correctness (end-to-end bridge)                               *)
(******************************************************************************)

(* The seating of the protocol: which card position each player starts from. *)
Variable star_PI : PGGInterface R_star.

(* One share per seat: the covering's share count is the interface's player
   count, so the endpoints a run collects are exactly a share tuple. *)
Hypothesis star_HT :
  ts_T' (cs_scheme star_covering) = pi_T' star_PI.

(* A shuffle permutes the starting positions the same way it permutes the
   covering's share indices.  This is what makes the covering's algebra and
   the protocol's seating one structure rather than two: without it the
   coordinate permutation of the code and the monodromy on card positions
   could disagree, and reconstruction after a shuffle would read the wrong
   shares. *)
Hypothesis star_G_stable :
  forall g, g \in cs_recon_symmetry (tw_covering (ar_threshold star_rigidity)) ->
  forall i : 'I_(ts_T' (cs_scheme star_covering)).+1,
    @pgg_rho R_star g
      (tnth (cast_tuple (esym (congr1 S star_HT)) (pi_starts star_PI)) i) =
    tnth (cast_tuple (esym (congr1 S star_HT)) (pi_starts star_PI))
      (cs_monodromy star_covering g i).

(* Reconstructing from the endpoints of a run recovers the dealt secret, for
   every secret and every shuffle in the covering's symmetry group.  This is
   the correctness end of the instance: whatever the shuffle did to the deck,
   the shares still decode to what was dealt.  It says nothing about privacy,
   which is the marginal bound's business. *)
Lemma star_protocol_correct (s : 'I_(pgg_N' R_star).+1) (P : pgg_gT R_star) :
  P \in cs_recon_symmetry (tw_covering (ar_threshold star_rigidity)) ->
  ts_valid (cs_scheme star_covering) s
    (cast_tuple (esym (congr1 S star_HT)) (pi_starts star_PI)) ->
  pgg_recon_endpoints star_HT P = s.
Proof.
exact: (@ar_protocol_correct R R_star star_rigidity star_PI star_HT s P star_G_stable).
Qed.

(* The dealer of the star protocol, driven by a word of the length the
   certificate fixes.  Its word argument is a 1-tuple because
   star_certified_1 sets the round count to 1, so the number the security
   analysis chooses is the number the running protocol consumes. *)
Definition star_dealer
    (parties : seq 'I_(pi_T' star_PI).+1)
    (w : 1.-tuple 'I_m.+1)
    (P_idx : nat) :=
  exchange_dealer_from_words (M := R_star) star_PI 1 parties w P_idx.

End star_rigidity.
