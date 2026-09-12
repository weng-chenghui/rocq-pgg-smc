(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_mixing: an all-length endpoint mixing bound for the S_5 adjacent-       *)
(*            transposition shuffle, from an in-kernel Rayleigh certificate   *)
(*                                                                            *)
(* For every word length L and every card position s, the law of the card at  *)
(* s after a uniform L-letter word of the four adjacent transpositions of     *)
(* 'I_5 is within sqrt(5) * (181/200)^L of uniform in variation distance.     *)
(*                                                                            *)
(* The bound is delivered by the general mixing lemma symm_ds_TV_bound        *)
(* (security/pgg_mixing.v), which asks for three ingredients:                 *)
(*   (i)   every generator is an involution,                                  *)
(*   (ii)  0 <= alpha <= 1,                                                   *)
(*   (iii) <v, Q^2 v> <= alpha^2 <v, v> on the sum-zero subspace of R^5.      *)
(* (i) holds because the generators are transpositions, (ii) because alpha is *)
(* the rational 181/200, and (iii) is s5_rayleigh_Q2_R, which this file       *)
(* proves rather than assumes.                                                *)
(*                                                                            *)
(* THE CERTIFICATE.  alpha = 181/200, and the five literal tables below (the  *)
(* shifted matrix, the lower factor, the diagonal, the residual and its       *)
(* dominating bound) were produced by                                         *)
(*   instances/s5/s5_spectral_certificate.py                                  *)
(* by an untrusted search: an exact LDL^T of alpha^2 I - Q^2 + 11 J / 250     *)
(* rounded to thousandths, with the exact rounding error left in the          *)
(* residual.  The search is trusted for nothing.  What the kernel checks is   *)
(* the 25 entries of s5_shift_mxE, the 25 entries of s5_cert_identity, the    *)
(* nonnegativity of the five pivots, the entrywise bound on the off-diagonal  *)
(* residual and its row and column dominance, and those checks are the whole  *)
(* of the argument.                                                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_alpha_R    == the contraction rate 181/200                            *)
(*   s5_gap_R      == the spectral gap 19/200                                 *)
(*   s5_Q          == the 5x5 Schreier transition matrix as a literal table   *)
(*   s5_shift_mx   == alpha^2 I - Q^2 + 11 J / 250, positive semidefinite on  *)
(*                    all of R^5 and equal to alpha^2 I - Q^2 on sum-zero     *)
(*                    vectors                                                 *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_Q_E                          == the 25 Schreier entries are the table *)
(*   s5_shift_mxE                    == the shifted matrix is the table       *)
(*   s5_cert_identity                == the rounded LDL^T identity            *)
(*   s5_rayleigh_Q2_R                == <v, Q^2 v> <= (181/200)^2 <v,v> on    *)
(*                                      sum-zero vectors                      *)
(*   s5_spectral_convergence_proved  == the endpoint marginal bound at        *)
(*                                      every L                               *)
(*   s5_spectral_convergence_gap     == the same bound in (1 - gap)^L form    *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg matrix.
From mathcomp Require Import ssrint.
From mathcomp Require Import boolp reals lra.
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
(*  Section 1. alpha = 181/200, as a realType element.                        *)
(******************************************************************************)

(** s5_alpha_R — the contraction rate 181/200 of the S_5 word shuffle, the
    factor by which one letter shrinks the distance to uniform on the
    sum-zero subspace.  It overshoots the true second eigenvalue of the
    Schreier matrix, (1 + cos(pi/5))/2 = 0.9045085, by about 5e-4.  The
    certificate is correspondingly near-tight: its smallest pivot is 1/1000
    and its tightest dominance row has a slack of 1.1e-5. *)
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
(*  Section 2. Involutivity of the four path-graph generators.                *)
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
(*  Section 3. The Schreier transition matrix as a literal table.             *)
(******************************************************************************)

(** s5_letter_tbl — the permutation table of letter j: the image of each of
    the five card positions, read by position.  Describing the alphabet by
    five-element lists of naturals is what lets the Schreier counts be
    decided by computation instead of by reasoning about transpositions. *)
Definition s5_letter_tbl (j : nat) : seq nat :=
  nth [::] [:: [:: 1; 0; 2; 3; 4]
             ; [:: 0; 2; 1; 3; 4]
             ; [:: 0; 1; 3; 2; 4]
             ; [:: 0; 1; 2; 4; 3]] j.

(** s5_gen_val — letter j of the alphabet sends card position x to the entry
    of its own row of s5_letter_tbl at x.  The one point where the
    transposition tperm j (j+1) and the list view of the same permutation
    are identified. *)
Lemma s5_gen_val (j : 'I_4) (x : 'I_5) :
  val (tnth (path_gen_tuple 3) j x) = nth 0%N (s5_letter_tbl j) (val x).
Proof.
rewrite path_gen_tupleE /path_gen.
by case: j => -[|[|[|[|//]]]] jlt;
   case: x => -[|[|[|[|[|//]]]]] xlt; rewrite permE.
Qed.

(** s5_gen_countE — the number of letters carrying card position i to card
    position j, written as an unconditional four-term sum over the alphabet
    rather than as a set cardinality.  The form that reduces to a numeral
    once i and j are concrete, and hence the step that makes the 25 entries
    of the transition matrix decidable by computation. *)
Lemma s5_gen_countE (i j : 'I_5) :
  schreier_gen_count (path_gen_tuple 3) i j
  = \sum_(k < 4) (nth 0%N (s5_letter_tbl (val k)) (val i) == val j : nat).
Proof.
rewrite /schreier_gen_count cardsE -sum1_card big_mkcond /=.
apply: eq_bigr => k _.
by rewrite unfold_in /= s5_gen_val; case: eqnP => [->|];
   rewrite ?eqxx// => /eqP/negbTE ->.
Qed.

(** s5_Q_tbl — the numerators of the 5x5 Schreier transition matrix of the
    four adjacent transpositions: entry (i, j) counts the letters carrying
    card position i to card position j, out of four.  The random walk on the
    five card positions that the whole bound is about. *)
Definition s5_Q_tbl : seq (seq nat) :=
  [:: [:: 3; 1; 0; 0; 0 ];
      [:: 1; 2; 1; 0; 0 ];
      [:: 0; 1; 2; 1; 0 ];
      [:: 0; 0; 1; 2; 1 ];
      [:: 0; 0; 0; 1; 3 ] ].

(** s5_Q — the Schreier transition matrix of the alphabet as a real matrix
    read off s5_Q_tbl, each count divided by the four letters.  The literal
    form in which the certificate arithmetic is done; s5_Q_E identifies it
    with the definitional schreier_transition. *)
Definition s5_Q (R : realType) : 'M[R]_5 :=
  \matrix_(i, j) ((nth 0%N (nth [::] s5_Q_tbl i) j)%:R / 4%:R).

(** s5_Q_E — the Schreier transition matrix of the alphabet is the literal
    matrix s5_Q.  From here on the walk is a 5x5 array of rationals with
    denominator four, and no further reference to permutations is needed. *)
Lemma s5_Q_E (R : realType) :
  schreier_transition R (path_gen_tuple 3) = s5_Q R.
Proof.
apply/matrixP => i j; rewrite !mxE.
congr (_%:R / _).
rewrite s5_gen_countE !big_ord_recl big_ord0 /=.
by case: i => -[|[|[|[|[|//]]]]] ilt;
   case: j => -[|[|[|[|[|//]]]]] jlt; vm_compute.
Qed.

(******************************************************************************)
(*  Section 4. The rounded LDL^T certificate.                                 *)
(*                                                                            *)
(*  Every table below is a literal produced by                                *)
(*  instances/s5/s5_spectral_certificate.py and trusted for nothing:          *)
(*  s5_shift_mxE, s5_cert_identity and the five side conditions are what the  *)
(*  kernel checks, and together they are the whole of the argument.           *)
(******************************************************************************)

(* Two numeral hazards shape how the tables and the denominators below are
   written.  An int numeral is elaborated through a unary nat, so a table of
   six-digit int literals costs minutes to typecheck; each entry is
   therefore a nat numeral coerced by %:Z, which the Number Notation leaves
   as an unreduced Nat.of_num_uint application above 5001.  simpl would
   unfold that application into a Decimal spine that the algebra front end
   no longer reads as a constant, so the unfolding is switched off for the
   rest of the file.  Every denominator is instead written as a product of
   factors that stay below 5001 and so do reduce: over a single nat literal
   of 10^9, the mxE rewriting of s5_cert_identity runs into a search that
   does not finish. *)
Local Arguments Nat.of_num_uint : simpl never.

(** s5_shift_tbl — the numerators, over 160000, of alpha^2 I - Q^2 + 11 J /
    250, the matrix whose positive semidefiniteness carries the Rayleigh
    bound.  The all-ones term lifts the direction on which alpha^2 I - Q^2
    is negative far enough that the shifted matrix is positive semidefinite
    on all of R^5 and so admits a global factorisation. *)
Definition s5_shift_tbl : seq (seq int) :=
  [:: [:: 38084%:Z; -42960%:Z; -2960%:Z; 7040%:Z; 7040%:Z ];
      [:: -42960%:Z; 78084%:Z; -32960%:Z; -2960%:Z; 7040%:Z ];
      [:: -2960%:Z; -32960%:Z; 78084%:Z; -32960%:Z; -2960%:Z ];
      [:: 7040%:Z; -2960%:Z; -32960%:Z; 78084%:Z; -42960%:Z ];
      [:: 7040%:Z; 7040%:Z; -2960%:Z; -42960%:Z; 38084%:Z ] ].

(** s5_cert_lower_tbl — the numerators, over 1000, of the lower-triangular
    factor of the certificate.  It is the exact LDL^T factor of the shifted
    matrix rounded to thousandths, so it is not the true factor; the exact
    difference is carried by s5_cert_resid_tbl. *)
Definition s5_cert_lower_tbl : seq (seq int) :=
  [:: [:: 1000%:Z; 0%:Z; 0%:Z; 0%:Z; 0%:Z ];
      [:: -1130%:Z; 1000%:Z; 0%:Z; 0%:Z; 0%:Z ];
      [:: -78%:Z; -1233%:Z; 1000%:Z; 0%:Z; 0%:Z ];
      [:: 185%:Z; 170%:Z; -795%:Z; 1000%:Z; 0%:Z ];
      [:: 185%:Z; 509%:Z; 487%:Z; -619%:Z; 1000%:Z ] ].

(** s5_cert_diag_tbl — the numerators, over 1000, of the five pivots of the
    certificate, the exact pivots rounded down to thousandths.  Rounding
    down keeps every pivot nonnegative, which is the only property of the
    pivots the argument uses. *)
Definition s5_cert_diag_tbl : seq int :=
  [:: 237%:Z; 184%:Z; 206%:Z; 343%:Z; 1%:Z ].

(** s5_cert_resid_tbl — the numerators, over 10^9, of the exact residual of
    the rounded factorisation.  Rounding the factor and flooring the pivots
    leaves this matrix over, and the argument works because it is diagonally
    dominant rather than because it is small. *)
Definition s5_cert_resid_tbl : seq (seq int) :=
  [:: [:: 1025000%:Z; -690000%:Z; -14000%:Z; 155000%:Z; 155000%:Z ];
      [:: -690000%:Z; 1399700%:Z; -17180%:Z; -235150%:Z; -111150%:Z ];
      [:: -14000%:Z; -17180%:Z; 849916%:Z; -241850%:Z; 75758%:Z ];
      [:: 155000%:Z; -235150%:Z; -241850%:Z; 1398925%:Z; -459855%:Z ];
      [:: 155000%:Z; -111150%:Z; 75758%:Z; -459855%:Z; 961734%:Z ] ].

(** s5_cert_bound_tbl — the numerators, over 10^9, of the entrywise absolute
    value of the residual off the diagonal, zero on the diagonal.  Supplying
    the dominating matrix as data rather than as an absolute value keeps
    every side condition a linear inequality between literals. *)
Definition s5_cert_bound_tbl : seq (seq int) :=
  [:: [:: 0%:Z; 690000%:Z; 14000%:Z; 155000%:Z; 155000%:Z ];
      [:: 690000%:Z; 0%:Z; 17180%:Z; 235150%:Z; 111150%:Z ];
      [:: 14000%:Z; 17180%:Z; 0%:Z; 241850%:Z; 75758%:Z ];
      [:: 155000%:Z; 235150%:Z; 241850%:Z; 0%:Z; 459855%:Z ];
      [:: 155000%:Z; 111150%:Z; 75758%:Z; 459855%:Z; 0%:Z ] ].

(** s5_cert_mx — a 5x5 real matrix read off a table of integers over a
    common denominator.  The single point at which the certificate's integer
    literals become elements of the real field the bound is stated in. *)
Definition s5_cert_mx (R : realType) (t : seq (seq int)) (den : R)
    : 'M[R]_5 :=
  \matrix_(i, j) ((nth 0 (nth [::] t i) j)%:~R / den).

(* den has type R, so R would otherwise be inferred rather than written. *)
Arguments s5_cert_mx R t den : clear implicits.

(** s5_shift_mx — the matrix alpha^2 I - Q^2 + 11 J / 250 as a literal.  The
    object the certificate factorises, and the object whose nonnegative
    quadratic form gives the Rayleigh bound once the all-ones term is
    discarded on sum-zero vectors. *)
Definition s5_shift_mx (R : realType) : 'M[R]_5 :=
  s5_cert_mx R s5_shift_tbl (400%:R * 400%:R).

(** s5_cert_lower — the rounded lower-triangular factor as a real matrix,
    the A of psd_of_ldl. *)
Definition s5_cert_lower (R : realType) : 'M[R]_5 :=
  s5_cert_mx R s5_cert_lower_tbl 1000%:R.

(** s5_cert_diag — the floored pivots as a real row vector, the D of
    psd_of_ldl.  All of the certificate's positivity is carried here. *)
Definition s5_cert_diag (R : realType) : 'rV[R]_5 :=
  \row_k ((nth 0 s5_cert_diag_tbl k)%:~R / 1000%:R).

(** s5_cert_resid — the exact residual as a real matrix, the E of psd_of_ldl
    and of psd_of_dominant. *)
Definition s5_cert_resid (R : realType) : 'M[R]_5 :=
  s5_cert_mx R s5_cert_resid_tbl (1000%:R * (1000%:R * 1000%:R)).

(** s5_cert_bound — the dominating matrix as a real matrix, the A of
    psd_of_dominant. *)
Definition s5_cert_bound (R : realType) : 'M[R]_5 :=
  s5_cert_mx R s5_cert_bound_tbl (1000%:R * (1000%:R * 1000%:R)).

(** s5_shift_mxE — the literal table s5_shift_mx is the matrix alpha^2 I -
    Q^2 + 11 J / 250 it was written down as.  Twenty-five rational
    identities, each a five-term sum; this is where the certificate's own
    account of what it factorises is checked against the walk. *)
Lemma s5_shift_mxE (R : realType) :
  s5_shift_mx R
  = ((s5_alpha_R R) ^+ 2) *: 1%:M - s5_Q R *m s5_Q R
    + const_mx (11%:R / 250%:R).
Proof.
apply/matrixP => i j.
rewrite /s5_shift_mx /s5_cert_mx /s5_alpha_R !mxE.
rewrite !big_ord_recl big_ord0 /=.
rewrite !mxE.
by case: i => -[|[|[|[|[|//]]]]] ilt;
   case: j => -[|[|[|[|[|//]]]]] jlt; rewrite /=; lra.
Qed.

(** s5_cert_identity — the shifted matrix is exactly the rounded
    factorisation plus the residual.  This equality is the whole content of
    the untrusted search: once it is checked, no property of how the tables
    were found is used anywhere. *)
Lemma s5_cert_identity (R : realType) :
  s5_shift_mx R
  = s5_cert_lower R *m diag_mx (s5_cert_diag R)
      *m (s5_cert_lower R)^T
    + s5_cert_resid R.
Proof.
apply/matrixP => i j.
rewrite mul_mx_diag !mxE.
rewrite !big_ord_recl big_ord0 !mxE.
by case: i => -[|[|[|[|[|//]]]]] ilt;
   case: j => -[|[|[|[|[|//]]]]] jlt; rewrite /=; lra.
Qed.

(** s5_cert_diag_ge0 — every pivot of the certificate is nonnegative.  The
    hypothesis of psd_of_ldl, and the reason flooring rather than rounding
    the exact pivots was the right choice. *)
Lemma s5_cert_diag_ge0 (R : realType) :
  forall k, 0 <= s5_cert_diag R ord0 k.
Proof.
by move=> k; rewrite mxE; case: k => -[|[|[|[|[|//]]]]] klt;
   rewrite /=; lra.
Qed.

(** s5_cert_resid_le_bound — off the diagonal the residual is at most its
    dominating matrix.  One of the two halves of the absolute-value bound
    psd_of_dominant asks for, stated so that both halves are linear. *)
Lemma s5_cert_resid_le_bound (R : realType) :
  forall i j, i != j -> s5_cert_resid R i j <= s5_cert_bound R i j.
Proof.
move=> i j; rewrite !mxE.
(* The diagonal cases have a false antecedent.  Discharging them with
   discriminate rather than done saves the conversion between true and a
   concrete real inequality that done's trivial branch would attempt. *)
by case: i => -[|[|[|[|[|//]]]]] ilt;
   case: j => -[|[|[|[|[|//]]]]] jlt;
   rewrite /= => ne_ij; try discriminate; lra.
Qed.

(** s5_cert_resid_ge_neg_bound — off the diagonal the residual is at least
    minus its dominating matrix.  The other half of the absolute-value
    bound. *)
Lemma s5_cert_resid_ge_neg_bound (R : realType) :
  forall i j, i != j -> - s5_cert_resid R i j <= s5_cert_bound R i j.
Proof.
move=> i j; rewrite !mxE.
by case: i => -[|[|[|[|[|//]]]]] ilt;
   case: j => -[|[|[|[|[|//]]]]] jlt;
   rewrite /= => ne_ij; try discriminate; lra.
Qed.

(** s5_cert_bound_row_dominant — each row of the dominating matrix sums to
    at most the residual's diagonal entry in that row.  Row dominance; with
    column dominance it is what makes the residual's quadratic form
    nonnegative without any factorisation of the residual itself. *)
Lemma s5_cert_bound_row_dominant (R : realType) :
  forall i, \sum_(j | j != i) s5_cert_bound R i j <= s5_cert_resid R i i.
Proof.
move=> i.
rewrite big_mkcond !big_ord_recl big_ord0 !mxE.
by case: i => -[|[|[|[|[|//]]]]] ilt; rewrite /=; lra.
Qed.

(** s5_cert_bound_col_dominant — each column of the dominating matrix sums
    to at most the residual's diagonal entry in that column.  Column
    dominance, the second half of the budget psd_of_dominant spends. *)
Lemma s5_cert_bound_col_dominant (R : realType) :
  forall j, \sum_(i | i != j) s5_cert_bound R i j <= s5_cert_resid R j j.
Proof.
move=> j.
rewrite big_mkcond !big_ord_recl big_ord0 !mxE.
by case: j => -[|[|[|[|[|//]]]]] jlt; rewrite /=; lra.
Qed.

(******************************************************************************)
(*  Section 5. The Rayleigh bound on Q^2.                                     *)
(******************************************************************************)

(** s5_rayleigh_Q2_R — on the mean-zero hyperplane of R^5, the square of
    the Schreier transition matrix of the four adjacent transpositions
    contracts by alpha^2 = (181/200)^2: v^T Q^2 v <= alpha^2 <v,v> whenever
    the coordinates of v sum to zero.  Equivalently, alpha^2 I - Q^2 is
    positive semidefinite there.

    Restricting to mean-zero vectors is the content, not a technicality:
    Q fixes the all-ones vector, so no contraction holds on it, and the
    rate at which the walk forgets its starting deck is decided by what Q
    does to the complement.  This is the one spectral input of the S_5 row,
    and the only place the certificate tables are used.
    symm_ds_TV_bound turns it into the variation-distance bound between the
    walk's endpoint law and uniform, which is how a dealer's word length
    becomes a security parameter for the five-card deck. *)
Lemma s5_rayleigh_Q2_R :
  forall (R : realType) (v : 'cV[R]_5),
  \sum_i v i ord0 = 0 ->
  (v^T
    *m (schreier_transition R (path_gen_tuple 3)
        *m schreier_transition R (path_gen_tuple 3))
    *m v) ord0 ord0
  <= (s5_alpha_R R) ^+ 2 * cV_inner v v.
Proof.
move=> R v sum0.
have psd : forall w : 'cV[R]_5, 0 <= (w^T *m s5_shift_mx R *m w) ord0 ord0.
  apply: (@psd_of_ldl R 5 (s5_shift_mx R) (s5_cert_lower R)
            (s5_cert_resid R) (s5_cert_diag R)).
  - exact: s5_cert_identity.
  - exact: s5_cert_diag_ge0.
  - apply: (@psd_of_dominant R 5 (s5_cert_resid R) (s5_cert_bound R)).
    + exact: s5_cert_resid_le_bound.
    + exact: s5_cert_resid_ge_neg_bound.
    + exact: s5_cert_bound_row_dominant.
    + exact: s5_cert_bound_col_dominant.
move: (psd v); rewrite s5_shift_mxE rayleigh_of_shift//.
rewrite s5_Q_E mulmxBr mulmxBl mxE scalemx1 mul_mx_scalar -scalemxAl mxE.
rewrite /cV_inner [X in _ + X]mxE; lra.
Qed.

(******************************************************************************)
(*  Section 6. The endpoint bound.                                            *)
(******************************************************************************)

(** s5_spectral_convergence_proved — after a uniform L-letter word of the
    four adjacent transpositions, the law of the card at position s is
    within sqrt(5) * (181/200)^L of uniform in variation distance, at every
    L and every s.  This is the per-seat endpoint marginal bound: it
    averages over words and is worst case over the seat and over the length,
    it names no adversary and no computational assumption, and it says
    nothing about what several seats jointly see. *)
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
(*  Section 7. The bound in spectral-gap form.                                *)
(******************************************************************************)

(** s5_gap_R — the spectral gap 1 - alpha = 19/200 of the S_5 word shuffle.
    The form a SecurityAsymptotic states its convergence rate in: one letter
    of the word buys a factor 1 - gap. *)
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

(** s5_spectral_convergence_gap — after a uniform L-letter word the law of
    the card at position s is within sqrt(5) * (1 - gap)^L of uniform, with
    gap = 19/200.  The shape a SecurityAsymptotic and a spectral marginal
    bound are stated in, which is how one letter of a dealer's word acquires
    a price. *)
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
