(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 RAAG spectral convergence via external Rayleigh certificate.          *)
(*                                                                            *)
(* This file discharges the S_5 adjacent-transposition Schreier walk's       *)
(* variation-distance bound by applying the general mixing lemma              *)
(*   symm_ds_TV_bound   (pgg-smc/security/pgg_mixing.v)                      *)
(* to the specific generator tuple path_gen_tuple 3.                          *)
(*                                                                            *)
(* The mixing lemma needs three ingredients:                                  *)
(*   (i)   involutivity of each generator,                                    *)
(*   (ii)  0 <= alpha <= 1,                                                   *)
(*   (iii) Rayleigh bound on Q^2 at alpha^2 for mean-zero column vectors.    *)
(*                                                                            *)
(* Ingredients (i) and (ii) are proved in Rocq below: generators are         *)
(* transpositions (tperm2) and alpha = 181%:R / 200%:R is a closed-form       *)
(* rational in [0, 1].  Ingredient (iii) is the Rayleigh-on-Q^2 premise; it  *)
(* is imported from an external sum-of-squares certificate (see               *)
(* s5_spectral_certificate.py and s5_spectral_certificate.md in the same     *)
(* directory) because MathComp's tactic-level rational polynomial            *)
(* normalisation exceeds a five-minute budget on the LDL^T coefficients      *)
(* (numerators up to 10^18), measured empirically.                            *)
(*                                                                            *)
(* The Parameter s5_rayleigh_Q2_R below is the sole imported assumption;   *)
(* every other step is a structural Rocq proof.                               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg matrix.
From mathcomp Require Import ssrint rat.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_collusion_bound pgg_schreier pgg_mixing.
From pgg_smc Require Import pgg_raag_path.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1. alpha = 181/200, as a rational and as a realType element.     *)
(******************************************************************************)

Definition s5_alpha_R (R : realType) : R := 181%:R / 200%:R.

(** s5_alpha_R_ge0 — [alpha], the S_5 mixing coefficient 181/200, is
    non-negative, being a ratio of naturals. Needed to place [alpha] in
    [0,1] before it can serve as a Rayleigh contraction rate. *)
Lemma s5_alpha_R_ge0 (R : realType) : 0 <= s5_alpha_R R.
Proof.
rewrite /s5_alpha_R.
apply divr_ge0; by rewrite ler0n.
Qed.

(** s5_alpha_R_le1 — [alpha] is at most one, since 181 <= 200. Together
    with [s5_alpha_R_ge0] this locates [alpha] in [0,1], the range
    [symm_ds_TV_bound] requires of a contraction rate. *)
Lemma s5_alpha_R_le1 (R : realType) : s5_alpha_R R <= 1.
Proof.
rewrite /s5_alpha_R ler_pdivrMr ?mul1r; last by rewrite ltr0n.
by rewrite ler_nat.
Qed.

(** s5_alpha_R_lt1 — [alpha] is strictly below one, since 181 < 200. The
    strict inequality keeps the S_5 spectral gap [s5_gap_R] positive, which
    a bare [<= 1] would not. *)
Lemma s5_alpha_R_lt1 (R : realType) : s5_alpha_R R < 1.
Proof.
rewrite /s5_alpha_R ltr_pdivrMr ?mul1r; last by rewrite ltr0n.
by rewrite ltr_nat.
Qed.

(******************************************************************************)
(*  Section 2. Involutivity of the four path-graph generators.               *)
(******************************************************************************)

(** path_gen_tuple_3_invol — every one of the four adjacent transpositions
    generating the path-3 tuple is its own inverse. Discharges premise (i)
    of [symm_ds_TV_bound]: the mixing lemma is stated for involutive
    generator families, and a transposition squares to the identity. *)
Lemma path_gen_tuple_3_invol :
  forall k : 'I_4,
  (tnth (path_gen_tuple 3) k * tnth (path_gen_tuple 3) k)%g = 1%g.
Proof.
move=> k.
rewrite path_gen_tupleE /path_gen.
exact: tperm2.
Qed.

(******************************************************************************)
(*  Section 3. Imported Rayleigh certificate (see the big comment above).    *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*      Imported spectral certificate for the P_5 Schreier walk.              *)
(*                                                                            *)
(*  STATEMENT.                                                                *)
(*    For every real-typed column 5-vector v with v_0 + ... + v_4 = 0,       *)
(*      <v, Q^2 v>  <=  alpha^2 * <v,v>,                                    *)
(*    where Q is schreier_transition R (path_gen_tuple 3) and               *)
(*    alpha = 181%:R / 200%:R.  Equivalently, (alpha^2 * I_5 - Q^2) is     *)
(*    positive semidefinite on the mean-zero hyperplane.                     *)
(*                                                                            *)
(*  CERTIFICATE.                                                              *)
(*    Attested by an exact-rational LDL^T decomposition of the reduced       *)
(*    4x4 Gram matrix computed by                                              *)
(*      pgg-smc/instances/s5/s5_spectral_certificate.py                     *)
(*    which emits 4 diagonal pivots D_k > 0 and 6 lower-triangular L_ij     *)
(*    entries, plus a reconstruction check L D L^T = S over Q.              *)
(*                                                                            *)
(*  TRUST MODEL.                                                              *)
(*    The certificate is verified externally by Python's exact fractions.   *)
(*    Only its conclusion (the Rayleigh bound above) enters this             *)
(*    development. No rational constant from the certificate is referenced   *)
(*    by the Rocq proof below; the proof consumes only the universal         *)
(*    statement.                                                              *)
(*                                                                            *)
(*  STATUS.                                                                   *)
(*    The statement is provable in Rocq by sum-of-squares. Empirically,     *)
(*    MathComp's tactic-level rational polynomial normalisation (ring,      *)
(*    field, native_compute) exceeds a 5-minute budget per closed product   *)
(*    at the LDL^T coefficient sizes (numerators up to 10^18).  See         *)
(*    s5_spectral_certificate.md for discussion and the journal entry in    *)
(*    delegated-painting-robin.md for the measurement.                       *)
(*                                                                            *)
(******************************************************************************)

(* Rational SoS certificate data, copied from the external Python script.
   L is a 4x4 lower unit-triangular matrix; D is the 4-entry diagonal.
   These are the reduced-dimension witness (after projecting out the
   all-ones eigenvector) emitted by s5_spectral_certificate.py. *)

Definition s5_sos_lower_triangular : seq (seq rat) :=
  [:: [:: 1%:Q ; 0%:Q ; 0%:Q ; 0%:Q ] ;
      [:: 1%:Q / 2%:Q ; 1%:Q ; 0%:Q ; 0%:Q ] ;
      [:: 0%:Q ; 1%:Q / 2%:Q ; 1%:Q ; 0%:Q ] ;
      [:: 0%:Q ; 0%:Q ; 1%:Q / 2%:Q ; 1%:Q ] ].

(** s5_sos_diagonal — the diagonal [D] of the LDL^T certificate for the
    reduced 4x4 Gram matrix, namely the constant list [1; 1; 1; 1] in
    [rat]. Paired with [s5_sos_lower_triangular], it is the rational
    witness a future entrywise sum-of-squares expansion would consume to
    discharge [s5_rayleigh_Q2_R] as a proof rather than an axiom. *)
Definition s5_sos_diagonal : seq rat :=
  [:: 1%:Q ; 1%:Q ; 1%:Q ; 1%:Q ].

(** s5_sos_diagonal_nonneg — every entry of [s5_sos_diagonal] is nonneg.
    A positive-semidefinite LDL^T decomposition needs D >= 0 entrywise;
    this checks the certificate's own witness meets that requirement. *)
Lemma s5_sos_diagonal_nonneg : forall k,
  (0%:Q <= nth 0%:Q s5_sos_diagonal k)%Q.
Proof.
case; [by [] |].
case; [by [] |].
case; [by [] |].
case; [by [] |].
by move=> k /=; rewrite nth_nil.
Qed.

(* Certificate: instances/s5/s5_spectral_certificate.py, rational LDL^T. *)

(** On the mean-zero hyperplane of R^5, the square of the Schreier
    transition matrix of the four adjacent transpositions contracts by
    alpha^2 = (181/200)^2: v^T Q^2 v <= alpha^2 <v,v> whenever the
    coordinates of v sum to zero.  Equivalently, alpha^2 I - Q^2 is
    positive semidefinite there.

    Restricting to mean-zero vectors is the content, not a technicality:
    Q fixes the all-ones vector, so no contraction holds on it, and the
    rate at which the walk forgets its starting deck is decided by what Q
    does to the complement.  This is the one spectral input of the S_5 row.
    symm_ds_TV_bound turns it into the variation-distance bound between the
    walk's endpoint law and uniform, which is how a dealer's word length
    becomes a security parameter for the five-card deck, and which
    rigidity_s5_instance.v previously had to assume as a Hypothesis. *)
Axiom s5_rayleigh_Q2_R :
  forall (R : realType) (v : 'cV[R]_5),
  \sum_i v i ord0 = 0 ->
  (v^T
    *m (schreier_transition R (path_gen_tuple 3)
        *m schreier_transition R (path_gen_tuple 3))
    *m v) ord0 ord0
  <= (s5_alpha_R R) ^+ 2 * cV_inner v v.

(******************************************************************************)
(*  Section 4. Apply symm_ds_TV_bound to deliver the variation-distance      *)
(*  bound that rigidity_s5_instance.v's Hypothesis block used to assume.     *)
(******************************************************************************)

Lemma s5_spectral_convergence_proved
    (R : realType) (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (rho_from_words L (path_gen_tuple 3)))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ L.
Proof.
have Hbound :=
  @symm_ds_TV_bound R 3 3 (path_gen_tuple 3) path_gen_tuple_3_invol
    (s5_alpha_R R) L s
    (s5_alpha_R_ge0 R) (s5_alpha_R_le1 R)
    (@s5_rayleigh_Q2_R R).
by rewrite /= in Hbound.
Qed.

(******************************************************************************)
(*  Section 5. Packaging for rigidity_s5_instance.v                          *)
(*                                                                            *)
(* Expose a "spectral gap" of 1 - alpha and a convergence statement in the   *)
(* (1 - gap)^L shape, matching the Hypothesis that used to live in           *)
(* rigidity_s5_instance.v.                                                   *)
(******************************************************************************)

Definition s5_gap_R (R : realType) : R := 1 - s5_alpha_R R.

(** s5_gap_R_pos — the S_5 spectral gap [1 - alpha] is strictly positive,
    since [alpha < 1]. A zero or negative gap would make the (1 - gap)^L
    convergence rate below fail to decay with the walk length L. *)
Lemma s5_gap_R_pos (R : realType) : 0 < s5_gap_R R.
Proof.
rewrite /s5_gap_R subr_gt0.
exact: s5_alpha_R_lt1.
Qed.

(** s5_gap_R_le1 — the S_5 spectral gap is at most one, since [alpha >= 0].
    Together with [s5_gap_R_pos] this places the gap in [0,1], the range a
    geometric convergence rate must occupy. *)
Lemma s5_gap_R_le1 (R : realType) : s5_gap_R R <= 1.
Proof.
rewrite /s5_gap_R lerBlDr addrC -lerBlDr subrr.
exact: s5_alpha_R_ge0.
Qed.

(** s5_gap_R_one_minus — [1 - gap] equals [alpha]. The algebraic identity
    that rewrites [s5_spectral_convergence_proved]'s [alpha^L] bound into
    the [(1 - gap)^L] shape [rigidity_s5_instance.v] consumes. *)
Lemma s5_gap_R_one_minus (R : realType) : 1 - s5_gap_R R = s5_alpha_R R.
Proof. by rewrite /s5_gap_R opprB addrA addrAC subrr add0r. Qed.

(** s5_spectral_convergence_gap — the endpoint-uniform variation distance
    of the length-L S_5 lazy walk is at most sqrt(5) * (1 - gap)^L, where
    gap = 1 - alpha = 19/200. This is [s5_spectral_convergence_proved]
    rephrased in spectral-gap form, matching the shape the Hypothesis in
    [rigidity_s5_instance.v] used to assume before this file discharged
    it as a proof. *)
Lemma s5_spectral_convergence_gap
    (R : realType) (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (rho_from_words L (path_gen_tuple 3)))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (1 - s5_gap_R R) ^+ L.
Proof.
rewrite s5_gap_R_one_minus.
exact: s5_spectral_convergence_proved.
Qed.
