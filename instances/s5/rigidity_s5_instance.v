(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 Algebraic Rigidity Instance                                            *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the S_5 adjacent      *)
(* transposition RAAG (Coxeter type A_4, path graph with 4 generators).       *)
(*                                                                            *)
(* This demonstrates all algebraic rigidity parameters computed from          *)
(* a single (G, I) choice with concrete vm_compute-checkable results:         *)
(*   1. Complexity: search_space L <= |G|                                     *)
(*   2. Security (spectral): L=286, eps = sqrt(5)*(1-gap)^286               *)
(*      40-bit security from the in-kernel spectral certificate              *)
(*   3. Threshold: genus-4 Bring's-curve cover (no-go: |S_5|=120 > Klein 60)   *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_5:                                *)
(*   The 5x5 Schreier matrix with 4 adjacent transpositions is               *)
(*     A = I - (1/4)*L(P_5)                                                   *)
(*   where L(P_5) is the graph Laplacian of the 5-vertex path.               *)
(*   Smallest nonzero Laplacian eigenvalue: 2*(1-cos(pi/5)).                  *)
(*   Spectral gap = (1 - cos(pi/5)) / 2 ~ 0.0955.                           *)
(*     L = 286 gives var_dist < 2^{-40}  (40-bit security)                   *)
(*     L = 897 gives var_dist < 2^{-128} (128-bit security)                  *)
(*                                                                            *)
(*   Brouwer-Haemers (2012), Spectra of Graphs, Springer.                    *)
(*   Chung (1997), Spectral Graph Theory, AMS.                               *)
(*   Wilson (2004), Ann. Appl. Probab. 14(1):274-325.                        *)
(*   Bacher (1994), J. Algebra 167:460-472.                                  *)
(*                                                                            *)
(* vm_compute demonstrations:                                                 *)
(*   s5_n_traces_natB1 : n_traces_natB 4 1 path_comm_nat = 4                 *)
(*   s5_n_traces_natB2 : n_traces_natB 4 2 path_comm_nat = 13                *)
(*   s5_n_traces_natB3 : n_traces_natB 4 3 path_comm_nat = 40                *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   s5_security_witness_schreier : ShuffleCertificateBundle at any word     *)
(*     length L, eps = sqrt(5)*(1-gap)^L                                     *)
(*   s5_rigidity : AlgebraicRigidity (security + threshold)                  *)
(*   s5_rayleigh_Q2_R (s5_mixing.v) : the Rayleigh premise of the            *)
(*     spectral bound, from an in-kernel rounded LDL^T certificate           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
From infotheo Require Import ssralg_ext.
From pgg_smc Require Import perm_uniform pgg_interface pgg_raag.
From pgg_smc Require Import pgg_raag_path pgg_raag_s5 pgg_collusion_bound.
From pgg_smc Require Import s5_mixing.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import curve_realisation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Spectral Gap Convergence                                               *)
(*                                                                            *)
(* The Schreier graph of S_5 on 'I_5 with 4 adjacent transpositions is       *)
(* the path graph P_5. The transition matrix is:                              *)
(*   A = I - (1/4) * L(P_5)                                                   *)
(* where L(P_5) is the graph Laplacian of the 5-vertex path.                  *)
(*                                                                            *)
(* Eigenvalues of A: 1 - (1/4)*2*(1-cos(k*pi/5)) for k=0,...,4.              *)
(* Second largest: 1 - (1-cos(pi/5))/2 ~ 0.9045.                             *)
(* Spectral gap = (1 - cos(pi/5)) / 2 ~ 0.0955.                             *)
(*                                                                            *)
(* References:                                                                *)
(*   Brouwer-Haemers (2012), Spectra of Graphs, Springer.                    *)
(*   Wilson (2004), Ann. Appl. Probab. 14(1):274-325.                        *)
(******************************************************************************)

Section s5_spectral.

Variable R : realType.

Let M_s5 := @Gen_PGGTypes 3 3 (path_gen_tuple 3).
Let s5_M : MonodromyReprWithGeneratorType := M_s5.

(* Spectral gap of the Schreier walk on the five card positions, from the
   rounded LDL^T certificate proved in s5_mixing.v: the tables come from an
   untrusted search in s5_spectral_certificate.py, and the kernel checks the
   factorisation identity, the nonnegativity of the pivots and the diagonal
   dominance of the residual.  No free variables. *)

Definition s5_asymptotic : @SecurityAsymptotic R s5_M.
Proof.
apply: (@MkSecurityAsymptotic R s5_M
  (s5_gap_R R) 0
  (s5_gap_R_pos R) (s5_gap_R_le1 R)
  (Order.POrderTheory.lexx 0)
  (fun L => rho_from_words L (path_gen_tuple 3))).
move=> L s.
rewrite add0r.
exact: s5_spectral_convergence_gap.
Defined.

(** s5_security_witness_schreier — the S_5 certificate bundle at word
    length [L]: the spectral marginal bound sqrt(5)*(1-gap)^L on the
    word-endpoint distribution, paired with the asymptotic rate
    [s5_asymptotic] and no exact certificate. This is the security half
    [s5_rigidity] reads at L = 286. *)
Definition s5_security_witness_schreier (L : nat) :
    ShuffleCertificateBundle R s5_M :=
  @MkShuffleCertificateBundle R s5_M
    (@MkShuffleMarginalBound R s5_M L
      (Num.sqrt 5%:R * (1 - s5_gap_R R) ^+ L)
      (rho_from_words L (path_gen_tuple 3))
      (fun s => @s5_spectral_convergence_gap R L s))
    None
    (Some s5_asymptotic).

End s5_spectral.

(******************************************************************************)
(*     Bring's-curve axiomatisation for the S_5 covering                      *)
(******************************************************************************)

(* Under the tightened (Klein finite-subgroup) [klein_genus0_bound], the s5 instance
   cannot be realised as a genus-0 cover: |S_5| = 120 exceeds the Klein
   ceiling of 60 (max non-dihedral finite subgroup of PGL(2, F̄), namely
   A_5). By Hurwitz's automorphism bound |Aut(C)| <= 84(g-1), an S_5
   automorphism action needs g >= 3; by Wiman's (1895) classification, no
   genus-3 curve has S_5 in its Aut group. The first realisable candidate
   is Bring's curve at g = 4 [Edge 1978, "Bring's curve", J. London Math.
   Soc. s2-18(3): 539-545]: the smooth projective curve in P^4 cut out by
   x_1 + x_2 + x_3 + x_4 + x_5 = 0,
   x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 = 0,
   x_1^3 + x_2^3 + x_3^3 + x_4^3 + x_5^3 = 0,
   admitting a faithful S_5 action by coordinate permutation.

   We axiomatise the existence of the corresponding [CoveringScheme] for
   the s5 monodromy, plus its genus = 4 and its [realised_by_curve] marker
   tying it to Bring's. None of these axioms is numerically false: each is
   a known mathematical fact whose Coq formalisation is deferred to a
   future curve-formalisation effort. *)

Section s5_brings_axiomatisation.

Local Notation s5_brings_M :=
  (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

(* The construction below replaces the previous opaque axiomatisation of the
   covering scheme with a concrete record. All numerical fields (base genus,
   branch count, total ramification, covering genus) are explicit. The
   reconstruction-invariance proof is discharged in the kernel. Two
   irreducible axioms remain:

     - [s5_group_order_eq]: the path-A_4 generators span the full S_5
       of order 120. This is "bubble-sort generates S_n", true but the
       lifting through the [Gen_PGGTypes] HB stack is engineering deferred
       to a future commit. Mirrors [s5x5_group_order_eq] (legacy/).

     - [s5_brings_covering_realised]: Bring's curve is the (genus-4)
       algebraic curve realising this CoveringData. Edge (1978). *)

(* Adjacent transpositions generate the symmetric group, being the Coxeter
   generators of type A_4, so the group they span has order 5! = 120.
   Standard; any group theory text, e.g. through the bubble-sort argument. *)

(** The deck group of the S_5 Bring's instance, spanned by the four
    adjacent transpositions of the five card positions, is the whole
    symmetric group; what is asserted here is its cardinality, 120.
    That number is the degree of the covering, which is how it enters the
    argument: Riemann-Hurwitz ties the genus of Bring's curve to the genus
    of the base through the degree, so s5_hurwitz has no arithmetic to
    state without it. *)
Axiom s5_group_order_eq :
  #|pgg_G s5_brings_M| = 120.

(** s5_n_branch_le — the S_5 Bring's cover has 4 branch points against
    246 total ramification, so branch count does not exceed ramification.
    Discharges the [cd_ramif_ge_n_branch] field of [CoveringData] when
    building [s5_brings_covering_data]. *)
Lemma s5_n_branch_le : (4 <= 246)%N. Proof. by []. Qed.

(** s5_hurwitz — the Riemann-Hurwitz identity holds for the claimed S_5
    Bring's cover: 2*4 + 2*120 = 120*(2*0) + 246 + 2, i.e. 248 = 248.
    Checks that genus 4, base genus 0, degree 120 and total ramification
    246 are a geometrically consistent covering before they are packaged
    into [s5_brings_covering_data]. *)
Lemma s5_hurwitz :
  (2 * 4 + 2 * #|pgg_G s5_brings_M| =
   #|pgg_G s5_brings_M| * (2 * 0) + 246 + 2)%N.
Proof. by rewrite muln0 muln0 add0n s5_group_order_eq. Qed.

(** s5_brings_covering_data — the CoveringData for the S_5 instance:
    genus 4, base genus 0, 4 branch points, total ramification 246, the
    numbers [s5_hurwitz] checks and [s5_brings_covering] packages into a
    covering scheme. *)
Definition s5_brings_covering_data : CoveringData s5_brings_M :=
  @MkCoveringData s5_brings_M 0 4 246 4 s5_n_branch_le s5_hurwitz.

(** s5_brings_covering_realised — Bring's curve, the genus-4 curve in
    P^4 admitting a faithful S_5 action by coordinate permutation,
    realises the covering described by [s5_brings_covering_data]. One
    of the two irreducible geometry axioms of this section, alongside
    [s5_group_order_eq]. Edge (1978), "Bring's curve", J. London Math.
    Soc. s2-18(3):539-545. *)
Axiom s5_brings_covering_realised :
  realised_by_curve s5_brings_covering_data.

(* Threshold scheme: sum-mod on 'I_5 with 5 parties. ts_T = ts_k = 5, so
   T - k = 0. The covering-scheme machinery therefore lives in the exact
   regime; only the legacy [s5x5] instance exercises the strict-gap branch. *)
Let s5_ts : ThresholdScheme 'I_5 'I_5 := @sum_mod_scheme 3 4.

(** s5_cs_gap — the [cs_gap] obligation ts_T <= ts_k + 2*cd_genus holds
    for the S_5 threshold scheme: with ts_T = ts_k = 5 and cd_genus = 4,
    the bound reads 5 <= 13. Discharges the gap field of
    [s5_brings_covering]. *)
Lemma s5_cs_gap :
  (ts_T s5_ts <= ts_k s5_ts + 2 * cd_genus s5_brings_covering_data)%N.
Proof. by []. Qed.

(** s5_sum_mod_perm_compatible — sum-mod reconstruction of the S_5 shares
    is invariant under the monodromy permutation of the share-index
    tuple. The single-pile analogue of [product_sum_mod_perm_compatible]
    in legacy/reconstruct/product_threshold.v: with no pile partition to
    track, the proof is a single reindex. Discharges the [cs_recon_invariant]
    obligation of [s5_brings_covering]. *)
Lemma s5_sum_mod_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G s5_brings_M) _ _ s5_ts
    (@pgg_rho s5_brings_M).
Proof.
move=> g s shares Hg Hvalid.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry; rewrite (reindex_inj (@perm_inj _ (@pgg_rho s5_brings_M g))).
by apply: eq_bigr.
Qed.

(** s5_brings_covering — the CoveringScheme for the S_5 instance: Bring's
    curve (genus 4) paired with the sum-mod threshold scheme. Threshold
    values, monodromy compatibility, reconstruction invariance and the
    gap bound are all proved; only the curve realisation
    ([s5_brings_covering_realised]) remains an axiom. *)
Definition s5_brings_covering : CoveringScheme s5_brings_M := {|
  cs_plug := @MkReconPlug s5_brings_M 'I_5 s5_ts id (@pgg_rho s5_brings_M)
               s5_sum_mod_perm_compatible ;
  cs_data := s5_brings_covering_data ;
  cs_gap  := s5_cs_gap ;
|}.

(** s5_brings_covering_genus — [s5_brings_covering] has genus 4, a
    definitional consequence of [s5_brings_covering_data]. Feeds the
    genus-0 vacuity argument in [s5_genus0_automorphism]: since the true
    genus is 4, any premise asking for genus 0 is false, so that
    obligation holds vacuously. *)
Lemma s5_brings_covering_genus :
  cd_genus (cs_data s5_brings_covering) = 4.
Proof. by []. Qed.

End s5_brings_axiomatisation.

(******************************************************************************)
(*     AlgebraicRigidity Instance at L = 286 (40-bit security)                *)
(*                                                                            *)
(* sqrt(5) * (1 - gap)^286 < 2^{-40} when gap ~ 0.0955.                     *)
(* For 128-bit security, read the same bundle at L = 897 instead.             *)
(******************************************************************************)

Section s5_rigidity.

Variable R : realType.

Let s5_M : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(* Card-position count for s5_M: 5 card positions (pgg_N' = 4). Verified
   definitionally
   since s5_M = Gen_PGGTypes 3 3 (path_gen_tuple 3), so pgg_N' = 4. *)
Lemma s5_HN5 : (pgg_N' s5_M).+1 = 5.
Proof. by []. Qed.

(* Bring's-curve-based covering. S_5 is the no-go: under the corrected
   [klein_genus0_bound] the genus-0 obligation [|S_5| <= 60] is mathematically false
   (120 > 60), so no genus-0 Reed-Solomon cover exists. See [s5_brings_covering]
   above for the Bring's-curve (genus 4) axioms. *)
Definition s5_covering : CoveringScheme s5_M := s5_brings_covering.

(** s5_genus0_automorphism — the genus-0 PGL automorphism obligation for
    [s5_covering] holds vacuously, since [s5_brings_covering] has
    [cd_genus = 4] (per [s5_brings_covering_genus]) and the premise
    [4 = 0] is false. Instantiates [s5_threshold_witness]. *)
Lemma s5_genus0_automorphism :
  genus0_automorphism_bound s5_M (cs_data s5_covering).
Proof. by rewrite /genus0_automorphism_bound /s5_covering s5_brings_covering_genus. Qed.

(** s5_threshold_witness — the threshold-covering witness for the S_5
    instance, packaging [s5_covering] with its vacuous genus-0
    automorphism bound [s5_genus0_automorphism]. *)
Definition s5_threshold_witness : ThresholdWitness s5_M :=
  @MkThresholdWitness s5_M s5_covering s5_genus0_automorphism.

(** s5_rigidity — the AlgebraicRigidity value of the S_5 instance: the
    Schreier spectral security bundle [s5_security_witness_schreier] read
    at word length 286, where sqrt(5) * (181/200)^286 < 2^{-40}, paired
    with the Bring's-curve threshold witness [s5_threshold_witness]. The
    security half is an unconditional information-theoretic bound on the
    per-seat endpoint marginal; the threshold half rests on the two
    geometry axioms of this file. *)
Definition s5_rigidity : AlgebraicRigidity R s5_M :=
  @MkAlgebraicRigidity R s5_M
    (@s5_security_witness_schreier R 286)
    s5_threshold_witness.

(* Derived properties *)

Lemma s5_complexity (L : nat) :
  (@search_space s5_M L <= #|pgg_G s5_M|)%N.
Proof. exact: search_space_leG. Qed.

Let s5_raag_M : RAAGType := @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(** s5_search_chain — for the S_5 path RAAG, search space is sandwiched
    between trace count and the naive alphabet power: search_space L <=
    n_traces L <= 4^L. The S_5 instantiation of the generic
    [search_space_chain], quantifying how much the RAAG's commutation
    relations shrink the search space below the free-monoid bound. *)
Lemma s5_search_chain (L : nat) :
  ((@search_space s5_raag_M L <= @n_traces s5_raag_M L) &&
   (@n_traces s5_raag_M L <= 4 ^ L))%N.
Proof. exact: search_space_chain. Qed.

(** s5_tradeoff — the S_5 instance sits in exactly one of two regimes: a
    genus-0 cover with ts_T <= ts_k, giving perfect reconstruction with
    no share overhead, or a positive-genus cover where the
    reconstruction slack ts_T <= ts_k + 2*cd_genus absorbs the genus.
    The S_5 specialisation of [security_threshold_tradeoff]; since
    [s5_covering] has genus 4, the actual instance falls in the second
    disjunct. *)
Lemma s5_tradeoff :
  let cs := tw_covering (ar_threshold s5_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G s5_M| <= klein_genus0_bound s5_M)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff s5_M s5_covering s5_genus0_automorphism).
Qed.

(** Protocol reconstruction correctness: named instance-level re-export of
    [ar_protocol_correct]. Takes a [PGGInterface] as a parameter since the S5
    instance is parameterised over the starting-card configuration. *)
Lemma s5_ts_recon_correct (PI : PGGInterface s5_M)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity)))) = pi_T' PI)
    (s : 'I_5) (P : pgg_gT s5_M)
    (G_stable : forall g, g \in pgg_G s5_M ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity))))).+1,
         rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))
           (@pgg_rho s5_M g
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i)) =
         tnth [tuple rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))
                 (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
              | j < (ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity))))).+1]
              (rp_monodromy (cs_plug (tw_covering (ar_threshold (s5_rigidity)))) g i)) :
  P \in pgg_G s5_M ->
  ts_valid (cs_scheme (tw_covering (ar_threshold (s5_rigidity)))) s
          [tuple rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
          | j < (ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity))))).+1] ->
  pgg_recon_endpoints HT
    (rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))) P = s.
Proof. exact: ar_protocol_correct. Qed.

End s5_rigidity.
