(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_spectral: an all-length endpoint mixing bound for the PGL(2,7) word  *)
(*                 shuffle, from an in-kernel Rayleigh certificate            *)
(*                                                                            *)
(* For every word length L and every card position s, the law of the card at  *)
(* s after a uniform L-letter word of the symmetrized PGL(2,7) alphabet is    *)
(* within sqrt(8) * (7/8)^L of uniform in variation distance.                 *)
(*                                                                            *)
(* WHAT THIS BOUND IS.  It is the per-seat endpoint marginal bound, the       *)
(* quantity a single seat's view of one card is measured by.  It is not the   *)
(* coalition-view bound: pgl27_word_view_indist (instances/pgl27/             *)
(* pgl27_models.v), at the fixed length L = 200, remains the statement about  *)
(* what a coalition of seats jointly sees.  A coalition bound for every L     *)
(* would need mixing on the 336 group elements rather than on the 8 card      *)
(* positions, and is not proved here.                                         *)
(*                                                                            *)
(* Complementing pgl27_word_mixing (pgl27_mixing.v), which certifies a single *)
(* length L = 200 at 2^-40 by enumerating the walk, this bound holds at every *)
(* L and degrades geometrically.  At L = 200 it gives about 2^-37, weaker     *)
(* than the enumerated certificate, as a spectral bound with a sqrt(N)        *)
(* prefactor must be.  It is nontrivial from L >= 8 onwards: sqrt(8)*(7/8)^L  *)
(* is 1.1107 at L = 7 and 0.9719 at L = 8.                                    *)
(*                                                                            *)
(* WHAT IS PACKAGED.  weval_inj fails for the symmetrized alphabet at every   *)
(* L >= 2, since letter 1 is the inverse of letter 0 and the words (0,1) and  *)
(* (1,0) both evaluate to the identity.  security_witness_schreier of         *)
(* legacy/security/pgg_free_words.v, which                                    *)
(* takes a weval_inj premise, is therefore unavailable here, and only         *)
(* security_witness_schreier_asymptotic is packaged.                          *)
(*                                                                            *)
(* THE CERTIFICATE.  alpha = 7/8, and the five literal tables below (the      *)
(* shifted matrix, the lower factor, the diagonal, the residual and its       *)
(* dominating bound) were produced by                                         *)
(*   instances/pgl27/pgl27_spectral_certificate.py                            *)
(* by an untrusted search: an exact LDL^T of alpha^2 I - Q^2 + J/32 rounded   *)
(* to hundredths, with the exact rounding error left in the residual.  The    *)
(* search is trusted for nothing.  The kernel checks the identity             *)
(* (pgl27_cert_identity), the nonnegativity of the diagonal and the           *)
(* diagonal dominance of the residual, and those checks are what the bound    *)
(* rests on.                                                                  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_alpha_R  == the contraction rate 7/8                               *)
(*   pgl27_gap_R    == the spectral gap 1/8                                   *)
(*   pgl27_Q        == the 8x8 Schreier transition matrix as a literal table  *)
(*   pgl27_shift_mx == alpha^2 I - Q^2 + J/32, positive semidefinite on all   *)
(*                     of R^8 and equal to alpha^2 I - Q^2 on sum-zero        *)
(*                     vectors                                                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_Q_E                    == the 64 Schreier entries are the table    *)
(*   pgl27_cert_identity          == the rounded LDL^T identity               *)
(*   pgl27_rayleigh_Q2            == <v, Q^2 v> <= (7/8)^2 <v,v> on sum-zero  *)
(*   pgl27_spectral_convergence   == the endpoint marginal bound at every L   *)
(*   pgl27_schreier_cert          == the same as a SchreierCertificate        *)
(*   pgl27_security_asymptotic    == the asymptotic security witness          *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg ssrint matrix.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_collusion_bound pgg_schreier.
From pgg_smc Require Import pgg_mixing pgg_weighted_words.
From pgg_smc Require Import pgl27_group pgl27_mixing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1. The contraction rate alpha = 7/8 and the gap 1 - alpha.        *)
(******************************************************************************)

(** pgl27_alpha_R — the contraction rate 7/8 of the PGL(2,7) word shuffle,
    the factor by which one letter shrinks the distance to uniform on the
    sum-zero subspace.  It overshoots the true second eigenvalue of the
    Schreier matrix, 0.86265, by enough that a certificate with hundredths
    exists. *)
Definition pgl27_alpha_R (R : realType) : R := 7%:R / 8%:R.

(** pgl27_alpha_R_ge0 — alpha is nonnegative, being a ratio of naturals.
    One of the two facts that place alpha in the range a contraction rate
    must occupy. *)
Lemma pgl27_alpha_R_ge0 (R : realType) : 0 <= pgl27_alpha_R R.
Proof. by rewrite /pgl27_alpha_R divr_ge0// ler0n. Qed.

(** pgl27_alpha_R_lt1 — alpha is strictly below one, since 7 < 8.  The
    strictness is what makes the spectral gap positive, hence what makes the
    bound decay rather than merely fail to grow. *)
Lemma pgl27_alpha_R_lt1 (R : realType) : pgl27_alpha_R R < 1.
Proof. by rewrite /pgl27_alpha_R ltr_pdivrMr ?ltr0n// mul1r ltr_nat. Qed.

(** pgl27_gap_R — the spectral gap 1 - alpha = 1/8 of the PGL(2,7) word
    shuffle.  The form SchreierCertificate states its convergence rate in:
    one letter of the word buys a factor 1 - gap. *)
Definition pgl27_gap_R (R : realType) : R := 1 - pgl27_alpha_R R.

(** pgl27_gap_R_pos — the gap is strictly positive, since alpha < 1.  A
    nonpositive gap would leave the walk with no contraction to exhibit. *)
Lemma pgl27_gap_R_pos (R : realType) : 0 < pgl27_gap_R R.
Proof. by rewrite /pgl27_gap_R subr_gt0; exact: pgl27_alpha_R_lt1. Qed.

(** pgl27_gap_R_le1 — the gap is at most one, since alpha >= 0.  With
    pgl27_gap_R_pos this puts the gap in the half-open unit interval a
    SchreierCertificate requires. *)
Lemma pgl27_gap_R_le1 (R : realType) : pgl27_gap_R R <= 1.
Proof. by rewrite /pgl27_gap_R gerBl; exact: pgl27_alpha_R_ge0. Qed.

(** pgl27_gap_R_one_minus — one minus the gap is alpha.  The identity that
    rewrites a bound written with the contraction rate into the gap form the
    certificate record is stated in. *)
Lemma pgl27_gap_R_one_minus (R : realType) :
  1 - pgl27_gap_R R = pgl27_alpha_R R.
Proof. by rewrite /pgl27_gap_R opprB addrCA subrr addr0. Qed.

(******************************************************************************)
(*  Section 2. The symmetrized alphabet is closed under inversion.            *)
(******************************************************************************)

(* pgl27_mixing.v carries the pairing as pgl27_inv_letter : nat -> nat, the
   form its table computations run in.  The mixing bridge needs it as a
   self-inverse map of the five letter indices, so the ordinal-valued
   companion is defined here and tied back by pgl27_inv_letter_ordE. *)

(** pgl27_inv_letter_ord — the pairing of letter indices that sends each
    letter of the symmetrized alphabet to the letter inverting it, as a map
    of 'I_5.  This is the f of the inverse-closed Schreier bridge; PGL(2,7)
    is the case where f is not the identity, translation and scaling being
    paired with their inverses while inversion is paired with itself. *)
Definition pgl27_inv_letter_ord (k : 'I_5) : 'I_5 :=
  tnth [tuple (@Ordinal 5 1 isT); (@Ordinal 5 0 isT); (@Ordinal 5 3 isT);
              (@Ordinal 5 2 isT); (@Ordinal 5 4 isT)] k.

(** pgl27_inv_letter_ordE — pgl27_inv_letter_ord agrees with the nat-level
    pairing pgl27_inv_letter of pgl27_mixing.v.  The one point where the
    ordinal view used by the mixing bridge and the nat view used by the
    table computations are identified. *)
Lemma pgl27_inv_letter_ordE (k : 'I_5) :
  val (pgl27_inv_letter_ord k) = pgl27_inv_letter (val k).
Proof.
by case: k => -[|[|[|[|[|//]]]]] Hk;
   rewrite /pgl27_inv_letter_ord (tnth_nth (@Ordinal 5 0 isT)).
Qed.

(** pgl27_inv_letter_ordK — the letter pairing is an involution: the inverse
    of the inverse of a letter is that letter.  The hypothesis fK of the
    inverse-closed bridge, and the reason the five inverses are a
    permutation of the five letters rather than five new ones. *)
Lemma pgl27_inv_letter_ordK : involutive pgl27_inv_letter_ord.
Proof.
by case=> -[|[|[|[|[|//]]]]] Hk; apply/val_inj;
   rewrite /pgl27_inv_letter_ord !(tnth_nth (@Ordinal 5 0 isT)).
Qed.

(** pgl27_sym_sigmas_inv_closed — the letter paired with k by
    pgl27_inv_letter_ord is the inverse permutation of letter k, so the
    generator multiset of the shuffle is closed under inversion.  This is
    the structural hypothesis symm_ds_TV_bound_inv_closed needs, and the
    reason the Schreier transition matrix of the shuffle is symmetric even
    though only one of its five letters is an involution. *)
Lemma pgl27_sym_sigmas_inv_closed (k : 'I_5) :
  tnth pgl27_sym_sigmas (pgl27_inv_letter_ord k)
  = ((tnth pgl27_sym_sigmas k)^-1)%g.
Proof.
by apply: ptbl_inj; rewrite ptbl_sym ptbl_inv_letter pgl27_inv_letter_ordE.
Qed.

(******************************************************************************)
(*  Section 3. The Schreier transition matrix as a literal table.             *)
(******************************************************************************)

(** pgl27_Q_tbl — the numerators of the 8x8 Schreier transition matrix of the
    symmetrized alphabet: entry (i, j) counts the letters carrying card
    position i to card position j, out of five.  The random walk on the eight
    points of the projective line that the whole bound is about. *)
Definition pgl27_Q_tbl : seq (seq nat) :=
  [:: [:: 2; 1; 0; 0; 0; 0; 1; 1 ];
      [:: 1; 0; 1; 1; 0; 1; 1; 0 ];
      [:: 0; 1; 0; 3; 0; 0; 1; 0 ];
      [:: 0; 1; 3; 0; 1; 0; 0; 0 ];
      [:: 0; 0; 0; 1; 0; 3; 1; 0 ];
      [:: 0; 1; 0; 0; 3; 0; 1; 0 ];
      [:: 1; 1; 1; 0; 1; 1; 0; 0 ];
      [:: 1; 0; 0; 0; 0; 0; 0; 4 ] ].

(** pgl27_Q — the Schreier transition matrix of the symmetrized alphabet as a
    real matrix read off pgl27_Q_tbl, each count divided by the five letters.
    The literal form in which the certificate arithmetic is done; pgl27_Q_E
    identifies it with the definitional schreier_transition. *)
Definition pgl27_Q (R : realType) : 'M[R]_8 :=
  \matrix_(i, j) ((nth 0%N (nth [::] pgl27_Q_tbl i) j)%:R / 5%:R).

(** pgl27_letter_tbl — the permutation table of letter j: the image of each
    of the eight card positions, read by position.  pgl27_mixing.v holds the
    same table as a Local definition for its walk enumeration; the letter
    values of the alphabet are restated here so the transition matrix can be
    computed without reaching into that file's private names. *)
Definition pgl27_letter_tbl (j : nat) : seq nat :=
  nth [::] [:: [:: 1; 2; 3; 4; 5; 6; 0; 7]
             ; [:: 6; 0; 1; 2; 3; 4; 5; 7]
             ; [:: 0; 3; 6; 2; 5; 1; 4; 7]
             ; [:: 0; 5; 3; 1; 6; 4; 2; 7]
             ; [:: 7; 6; 3; 2; 5; 4; 1; 0]] j.

(* A permutation whose forward images are read off the table F sends x to the
   entry of Finv at x, whenever Finv is a right inverse of F on the eight
   codes.  The two inverse letters of the alphabet are given by tables this
   way, so no permutation is inverted inside a kernel computation. *)
Local Lemma pgl27_perm_inv_val (g : {perm 'I_8}) (F Finv : seq nat) (x : 'I_8) :
  (forall y : 'I_8, val (g y) = nth 0%N F (val y)) ->
  (forall k, (k < 8)%N -> nth 0%N F (nth 0%N Finv k) = k) ->
  (forall k, (k < 8)%N -> (nth 0%N Finv k < 8)%N) ->
  val ((g^-1)%g x) = nth 0%N Finv (val x).
Proof.
move=> Hfwd Hcomp Hrange.
have Hc8 : (nth 0%N Finv (val x) < 8)%N by apply: Hrange; exact: ltn_ord.
pose z : 'I_8 := Ordinal Hc8.
have Hgz : g z = x.
  by apply/val_inj; rewrite Hfwd /= Hcomp //; exact: ltn_ord.
have Hzx : (g^-1)%g x = z by rewrite -Hgz permK.
by rewrite Hzx.
Qed.

(* The three forward generators agree with their rows of pgl27_letter_tbl. *)
Local Lemma pgl27_gen_val0 (x : 'I_8) :
  val (tnth pgl27_gens (@Ordinal 3 0 isT) x)
  = nth 0%N (pgl27_letter_tbl 0) (val x).
Proof. by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hx; rewrite permE. Qed.
Local Lemma pgl27_gen_val1 (x : 'I_8) :
  val (tnth pgl27_gens (@Ordinal 3 1 isT) x)
  = nth 0%N (pgl27_letter_tbl 2) (val x).
Proof. by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hx; rewrite permE. Qed.
Local Lemma pgl27_gen_val2 (x : 'I_8) :
  val (tnth pgl27_gens (@Ordinal 3 2 isT) x)
  = nth 0%N (pgl27_letter_tbl 4) (val x).
Proof. by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hx; rewrite permE. Qed.

(** pgl27_gen_val — letter j of the symmetrized alphabet sends card position
    x to the entry of its own row of pgl27_letter_tbl at x.  The alphabet is
    thereby described entirely by eight-element lists of naturals, which is
    what lets the Schreier counts be decided by computation. *)
Lemma pgl27_gen_val (j : 'I_5) (x : 'I_8) :
  val (tnth pgl27_sym_sigmas j x) = nth 0%N (pgl27_letter_tbl j) (val x).
Proof.
case: j => -[|[|[|[|[|//]]]]] Hj; rewrite (tnth_nth 1%g) /=.
- exact: pgl27_gen_val0.
- apply: (pgl27_perm_inv_val (F := pgl27_letter_tbl 0)).
  + exact: pgl27_gen_val0.
  + by case=> [|[|[|[|[|[|[|[|k7]]]]]]]].
  + by case=> [|[|[|[|[|[|[|[|k7]]]]]]]].
- exact: pgl27_gen_val1.
- apply: (pgl27_perm_inv_val (F := pgl27_letter_tbl 2)).
  + exact: pgl27_gen_val1.
  + by case=> [|[|[|[|[|[|[|[|k7]]]]]]]].
  + by case=> [|[|[|[|[|[|[|[|k7]]]]]]]].
- exact: pgl27_gen_val2.
Qed.

(** pgl27_gen_countE — the number of letters carrying card position i to card
    position j, written as an unconditional five-term sum over the alphabet
    rather than as a set cardinality.  The form that reduces to a numeral
    once i and j are concrete, and hence the step that makes the 64 entries
    of the transition matrix decidable by computation. *)
Lemma pgl27_gen_countE (i j : 'I_8) :
  schreier_gen_count pgl27_sym_sigmas i j
  = \sum_(k < 5) (nth 0%N (pgl27_letter_tbl (val k)) (val i) == val j : nat).
Proof.
rewrite /schreier_gen_count cardsE -sum1_card big_mkcond /=.
apply: eq_bigr => k _.
by rewrite unfold_in /= pgl27_gen_val; case: eqnP => [->|];
   rewrite ?eqxx// => /eqP/negbTE ->.
Qed.

(** pgl27_Q_E — the Schreier transition matrix of the symmetrized alphabet is
    the literal matrix pgl27_Q.  From here on the walk is an 8x8 array of
    rationals with denominator five, and no further reference to permutations
    is needed. *)
Lemma pgl27_Q_E (R : realType) :
  schreier_transition R pgl27_sym_sigmas = pgl27_Q R.
Proof.
apply/matrixP => i j; rewrite !mxE.
congr (_%:R / _).
rewrite pgl27_gen_countE !big_ord_recl big_ord0 /=.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi;
   case: j => -[|[|[|[|[|[|[|[|//]]]]]]]] Hj; vm_compute.
Qed.

(******************************************************************************)
(*  Section 4. The rounded LDL^T certificate.                                 *)
(*                                                                            *)
(*  Every table below is a literal produced by                                *)
(*  instances/pgl27/pgl27_spectral_certificate.py and trusted for nothing:    *)
(*  pgl27_shift_mxE, pgl27_cert_identity and the four side conditions are     *)
(*  what the kernel checks, and together they are the whole of the argument.  *)
(******************************************************************************)

(** pgl27_shift_tbl — the numerators, over 1600, of alpha^2 I - Q^2 + J/32,
    the matrix whose positive semidefiniteness carries the Rayleigh bound.
    The J/32 term lifts the all-ones direction, on which alpha^2 I - Q^2 is
    negative, far enough that the shifted matrix is positive semidefinite on
    all of R^8 and so admits a global factorisation. *)
Definition pgl27_shift_tbl : seq (seq int) :=
  [:: [:: 827; -142; -78; -14; -14; -78; -142; -334 ];
      [:: -142; 955; -206; -142; -270; -14; -142; -14 ];
      [:: -78; -206; 571; -14; -206; -78; -14; 50 ];
      [:: -14; -142; -14; 571; 50; -206; -270; 50 ];
      [:: -14; -270; -206; 50; 571; -14; -142; 50 ];
      [:: -78; -14; -78; -206; -14; 571; -206; 50 ];
      [:: -142; -142; -14; -270; -142; -206; 955; -14 ];
      [:: -334; -14; 50; 50; 50; 50; -14; 187 ] ].

(** pgl27_cert_lower_tbl — the numerators, over 100, of the lower-triangular
    factor of the certificate.  It is the exact LDL^T factor of the shifted
    matrix rounded to hundredths, so it is not the true factor; the exact
    difference is carried by pgl27_cert_resid_tbl. *)
Definition pgl27_cert_lower_tbl : seq (seq int) :=
  [:: [:: 100; 0; 0; 0; 0; 0; 0; 0 ];
      [:: -18; 100; 0; 0; 0; 0; 0; 0 ];
      [:: -10; -24; 100; 0; 0; 0; 0; 0 ];
      [:: -2; -16; -10; 100; 0; 0; 0; 0 ];
      [:: -2; -30; -55; -4; 100; 0; 0; 0 ];
      [:: -10; -3; -19; -42; -26; 100; 0; 0 ];
      [:: -18; -18; -14; -58; -76; -103; 100; 0 ];
      [:: -41; -8; 0; 6; 8; 9; -16; 100 ] ].

(** pgl27_cert_diag_tbl — the numerators, over 100, of the eight pivots of
    the certificate, the exact pivots rounded down to hundredths.  Rounding
    down keeps every pivot nonnegative, which is the only property of the
    pivots the argument uses. *)
Definition pgl27_cert_diag_tbl : seq int := [:: 50; 57; 30; 32; 20; 25; 4; 1 ].

(** pgl27_cert_resid_tbl — the numerators, over 10^6, of the exact residual
    of the rounded factorisation.  Rounding the factor and flooring the
    pivots leaves this matrix over, and the argument works because it is
    diagonally dominant rather than because it is small. *)
Definition pgl27_cert_resid_tbl : seq (seq int) :=
  [:: [:: 16875; 1250; 1250; 1250; 1250; 1250; 1250; -3750 ];
      [:: 1250; 10675; -950; 650; 450; -650; -2350; -50 ];
      [:: 1250; -950; 19043; -1638; -5790; -854; -374; -194 ];
      [:: 1250; 650; -1638; 19083; -10; -3786; -5566; 654 ];
      [:: 1250; 450; -5790; -10; 14113; 394; 146; -1762 ];
      [:: 1250; -650; -854; -3786; 394; 20564; -8780; -894 ];
      [:: 1250; -2350; -374; -5566; 146; -8780; 27934; -987 ];
      [:: -3750; -50; -194; 654; -1762; -894; -987; 13696 ] ].

(** pgl27_cert_bound_tbl — the numerators, over 10^6, of the entrywise
    absolute value of the residual off the diagonal, zero on the diagonal.
    Supplying the dominating matrix as data rather than as an absolute value
    keeps every side condition a linear inequality between literals. *)
Definition pgl27_cert_bound_tbl : seq (seq int) :=
  [:: [:: 0; 1250; 1250; 1250; 1250; 1250; 1250; 3750 ];
      [:: 1250; 0; 950; 650; 450; 650; 2350; 50 ];
      [:: 1250; 950; 0; 1638; 5790; 854; 374; 194 ];
      [:: 1250; 650; 1638; 0; 10; 3786; 5566; 654 ];
      [:: 1250; 450; 5790; 10; 0; 394; 146; 1762 ];
      [:: 1250; 650; 854; 3786; 394; 0; 8780; 894 ];
      [:: 1250; 2350; 374; 5566; 146; 8780; 0; 987 ];
      [:: 3750; 50; 194; 654; 1762; 894; 987; 0 ] ].

(** pgl27_cert_mx — an 8x8 real matrix read off a table of integers over a
    common denominator.  The single point at which the certificate's integer
    literals become elements of the real field the bound is stated in. *)
Definition pgl27_cert_mx (R : realType) (t : seq (seq int)) (den : nat)
    : 'M[R]_8 :=
  \matrix_(i, j) ((nth 0%R (nth [::] t i) j)%:~R / den%:R).

(** pgl27_shift_mx — the matrix alpha^2 I - Q^2 + J/32 as a literal.  The
    object the certificate factorises, and the object whose nonnegative
    quadratic form gives the Rayleigh bound once the all-ones term is
    discarded on sum-zero vectors. *)
Definition pgl27_shift_mx (R : realType) : 'M[R]_8 :=
  pgl27_cert_mx R pgl27_shift_tbl 1600.

(** pgl27_cert_lower — the rounded lower-triangular factor as a real matrix,
    the A of psd_of_ldl. *)
Definition pgl27_cert_lower (R : realType) : 'M[R]_8 :=
  pgl27_cert_mx R pgl27_cert_lower_tbl 100.

(** pgl27_cert_diag — the floored pivots as a real row vector, the D of
    psd_of_ldl.  All of the certificate's positivity is carried here. *)
Definition pgl27_cert_diag (R : realType) : 'rV[R]_8 :=
  \row_k ((nth 0%R pgl27_cert_diag_tbl k)%:~R / 100%:R).

(** pgl27_cert_resid — the exact residual as a real matrix, the E of
    psd_of_ldl and of psd_of_dominant. *)
Definition pgl27_cert_resid (R : realType) : 'M[R]_8 :=
  pgl27_cert_mx R pgl27_cert_resid_tbl 1000000.

(** pgl27_cert_bound — the dominating matrix as a real matrix, the A of
    psd_of_dominant. *)
Definition pgl27_cert_bound (R : realType) : 'M[R]_8 :=
  pgl27_cert_mx R pgl27_cert_bound_tbl 1000000.

(* Rocq's nat Number Notation keeps a literal above 5001 as an unreduced
   Nat.of_num_uint application, which the algebra-tactics front end cannot
   read as a constant.  Splitting the 10^6 denominator once turns every
   certificate inequality back into a goal lra decides. *)
Local Lemma pgl27_den6_nat : (1000000 = 1000 * 1000)%N.
Proof. by []. Qed.

Local Lemma pgl27_den6R (R : realType) :
  (1000000%:R : R) = 1000%:R * 1000%:R.
Proof. by rewrite pgl27_den6_nat natrM. Qed.

(* Right multiplication by a diagonal matrix scales columns.  Used to keep
   the certificate identity a single 8-term sum per entry instead of two
   nested ones. *)
Local Lemma pgl27_mulmx_diag_r (R : realType) (p q : nat)
    (A : 'M[R]_(p, q)) (d : 'rV[R]_q) :
  A *m diag_mx d = \matrix_(i, j) (A i j * d ord0 j).
Proof.
apply/matrixP => i j; rewrite !mxE.
rewrite (bigD1 j)//= !mxE eqxx mulr1n big1 ?addr0// => k Hk.
by rewrite !mxE (negbTE Hk) mulr0n mulr0.
Qed.

(** pgl27_shift_mxE — the literal table pgl27_shift_mx is the matrix
    alpha^2 I - Q^2 + J/32 it was written down as.  Sixty-four rational
    identities, each an eight-term sum; this is where the certificate's own
    account of what it factorises is checked against the walk. *)
Lemma pgl27_shift_mxE (R : realType) :
  pgl27_shift_mx R
  = ((pgl27_alpha_R R) ^+ 2) *: 1%:M - pgl27_Q R *m pgl27_Q R
    + const_mx (1 / 32%:R).
Proof.
apply/matrixP => i j.
rewrite /pgl27_shift_mx /pgl27_cert_mx /pgl27_alpha_R !mxE.
rewrite !big_ord_recl big_ord0 /=.
rewrite !mxE.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi;
   case: j => -[|[|[|[|[|[|[|[|//]]]]]]]] Hj; rewrite /=; lra.
Qed.

(** pgl27_cert_identity — the shifted matrix is exactly the rounded
    factorisation plus the residual.  This equality is the whole content of
    the untrusted search: once it is checked, no property of how the tables
    were found is used anywhere. *)
Lemma pgl27_cert_identity (R : realType) :
  pgl27_shift_mx R
  = pgl27_cert_lower R *m diag_mx (pgl27_cert_diag R)
      *m (pgl27_cert_lower R)^T
    + pgl27_cert_resid R.
Proof.
apply/matrixP => i j.
rewrite pgl27_mulmx_diag_r !mxE pgl27_den6R.
rewrite !big_ord_recl big_ord0 !mxE.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi;
   case: j => -[|[|[|[|[|[|[|[|//]]]]]]]] Hj; rewrite /=; lra.
Qed.

(** pgl27_cert_diag_ge0 — every pivot of the certificate is nonnegative.
    The hypothesis of psd_of_ldl, and the reason flooring rather than
    rounding the exact pivots was the right choice. *)
Lemma pgl27_cert_diag_ge0 (R : realType) :
  forall k, 0 <= pgl27_cert_diag R ord0 k.
Proof.
by move=> k; rewrite mxE; case: k => -[|[|[|[|[|[|[|[|//]]]]]]]] Hk;
   rewrite /=; lra.
Qed.

(** pgl27_cert_resid_le_bound — off the diagonal the residual is at most its
    dominating matrix.  One of the two halves of the absolute-value bound
    psd_of_dominant asks for, stated so that both halves are linear. *)
Lemma pgl27_cert_resid_le_bound (R : realType) :
  forall i j, i != j -> pgl27_cert_resid R i j <= pgl27_cert_bound R i j.
Proof.
move=> i j; rewrite !mxE !pgl27_den6R.
(* The diagonal cases have a false antecedent.  Discharging them with
   discriminate rather than done saves about a hundred seconds: done's
   `apply: sym_equal; trivial` branch tries a conversion between true and
   the concrete real inequality. *)
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi;
   case: j => -[|[|[|[|[|[|[|[|//]]]]]]]] Hj;
   rewrite /= => Hij; try discriminate; lra.
Qed.

(** pgl27_cert_resid_ge_neg_bound — off the diagonal the residual is at least
    minus its dominating matrix.  The other half of the absolute-value
    bound. *)
Lemma pgl27_cert_resid_ge_neg_bound (R : realType) :
  forall i j, i != j -> - pgl27_cert_resid R i j <= pgl27_cert_bound R i j.
Proof.
move=> i j; rewrite !mxE !pgl27_den6R.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi;
   case: j => -[|[|[|[|[|[|[|[|//]]]]]]]] Hj;
   rewrite /= => Hij; try discriminate; lra.
Qed.

(** pgl27_cert_bound_row_dominant — each row of the dominating matrix sums to
    at most the residual's diagonal entry in that row.  Row dominance; with
    column dominance it is what makes the residual's quadratic form
    nonnegative without any factorisation of the residual itself. *)
Lemma pgl27_cert_bound_row_dominant (R : realType) :
  forall i, \sum_(j | j != i) pgl27_cert_bound R i j <= pgl27_cert_resid R i i.
Proof.
move=> i.
rewrite big_mkcond !big_ord_recl big_ord0 !mxE !pgl27_den6R.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi; rewrite /=; lra.
Qed.

(** pgl27_cert_bound_col_dominant — each column of the dominating matrix sums
    to at most the residual's diagonal entry in that column.  Column
    dominance, the second half of the budget psd_of_dominant spends. *)
Lemma pgl27_cert_bound_col_dominant (R : realType) :
  forall j, \sum_(i | i != j) pgl27_cert_bound R i j <= pgl27_cert_resid R j j.
Proof.
move=> j.
rewrite big_mkcond !big_ord_recl big_ord0 !mxE !pgl27_den6R.
by case: j => -[|[|[|[|[|[|[|[|//]]]]]]]] Hj; rewrite /=; lra.
Qed.

(******************************************************************************)
(*  Section 5. The Rayleigh bound on Q^2.                                     *)
(******************************************************************************)

(** pgl27_rayleigh_Q2 — on the sum-zero subspace of R^8 the square of the
    Schreier transition matrix of the symmetrized alphabet contracts by
    alpha^2 = (7/8)^2.  Restricting to sum-zero vectors is the content and
    not a technicality: the matrix fixes the all-ones vector and contracts
    nothing there, and the rate at which the shuffle forgets the deck it
    started from is decided by what it does to the complement.  This is the
    one spectral input of the PGL(2,7) row and the only place the
    certificate tables are used. *)
Lemma pgl27_rayleigh_Q2 (R : realType) (v : 'cV[R]_8) :
  \sum_i v i ord0 = 0 ->
  (v^T *m (schreier_transition R pgl27_sym_sigmas
           *m schreier_transition R pgl27_sym_sigmas) *m v) ord0 ord0
  <= (pgl27_alpha_R R) ^+ 2 * cV_inner v v.
Proof.
move=> Hv.
have Hpsd : forall w : 'cV[R]_8, 0 <= (w^T *m pgl27_shift_mx R *m w) ord0 ord0.
  apply: (@psd_of_ldl R 8 (pgl27_shift_mx R) (pgl27_cert_lower R)
            (pgl27_cert_resid R) (pgl27_cert_diag R)).
  - exact: pgl27_cert_identity.
  - exact: pgl27_cert_diag_ge0.
  - apply: (@psd_of_dominant R 8 (pgl27_cert_resid R) (pgl27_cert_bound R)).
    + exact: pgl27_cert_resid_le_bound.
    + exact: pgl27_cert_resid_ge_neg_bound.
    + exact: pgl27_cert_bound_row_dominant.
    + exact: pgl27_cert_bound_col_dominant.
move: (Hpsd v); rewrite pgl27_shift_mxE rayleigh_of_shift//.
rewrite pgl27_Q_E mulmxBr mulmxBl mxE scalemx1 mul_mx_scalar -scalemxAl mxE.
rewrite /cV_inner [X in _ + X]mxE; lra.
Qed.

(******************************************************************************)
(*  Section 6. The endpoint bound and its packaging.                          *)
(******************************************************************************)

(** pgl27_spectral_convergence — after a uniform L-letter word of the
    symmetrized alphabet, the law of the card at position s is within
    sqrt(8) * (7/8)^L of uniform in variation distance, at every L and every
    s.  This is the per-seat endpoint marginal bound: it averages over words
    and is worst case over the seat and over the length, it names no
    adversary and no computational assumption, and it says nothing about
    what several seats jointly see. *)
Lemma pgl27_spectral_convergence (R : realType) (L : nat) (s : 'I_8) :
  var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s)
             (rho_from_words L pgl27_sym_sigmas))
           (fdist_uniform (card_ord 8))
  <= Num.sqrt 8%:R * (pgl27_alpha_R R) ^+ L.
Proof.
apply: (symm_ds_TV_bound_inv_closed (f := pgl27_inv_letter_ord)).
- exact: pgl27_inv_letter_ordK.
- exact: pgl27_sym_sigmas_inv_closed.
- exact: pgl27_alpha_R_ge0.
- exact: pgl27_rayleigh_Q2.
Qed.

(** pgl27_spectral_convergence_gap — the endpoint bound written with the
    spectral gap, sqrt(8) * (1 - gap)^L with gap = 1/8.  The shape the
    sc_convergence field of SchreierCertificate is stated in, which is how
    one letter of the word acquires a price. *)
Lemma pgl27_spectral_convergence_gap (R : realType) (L : nat) (s : 'I_8) :
  var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s)
             (rho_from_words L pgl27_sym_sigmas))
           (fdist_uniform (card_ord 8))
  <= Num.sqrt 8%:R * (1 - pgl27_gap_R R) ^+ L.
Proof.
rewrite pgl27_gap_R_one_minus; exact: pgl27_spectral_convergence.
Qed.

(** pgl27_spectral_convergence_weighted — the endpoint bound at the weighted
    word law with uniform letter weights, the form pgl27_endpoint_mixing
    already states the fixed-length bound in.  The weighted construction
    generalises the uniform one and collapses back to it at Wuni, so the two
    fixed-length and all-length bounds of this shuffle are comparable
    without further transport. *)
Lemma pgl27_spectral_convergence_weighted (R : realType) (L : nat) (s : 'I_8) :
  var_dist (@endpoint_dist_weighted R 6 4 L pgl27_sym_sigmas (Wuni R) s)
           (fdist_uniform (card_ord 8))
  <= Num.sqrt 8%:R * (pgl27_alpha_R R) ^+ L.
Proof.
rewrite /endpoint_dist_weighted /Wuni rho_weighted_is_uniform.
exact: pgl27_spectral_convergence.
Qed.

(** pgl27_schreier_cert — the PGL(2,7) word shuffle as a SchreierCertificate
    with spectral gap 1/8.  The record carries the gap, its position in the
    unit interval and the convergence bound together, which is what lets a
    consumer of the Schreier interface use the shuffle without reading the
    certificate tables. *)
Definition pgl27_schreier_cert (R : realType) :
    SchreierCertificate R 4 6 pgl27_sym_sigmas :=
  @MkSchreierCertificate R 4 6 pgl27_sym_sigmas
    (pgl27_gap_R R)
    (pgl27_gap_R_pos R)
    (pgl27_gap_R_le1 R)
    (pgl27_spectral_convergence_gap R).

(** pgl27_security_asymptotic — the asymptotic security witness of the
    PGL(2,7) shuffle: the geometric endpoint bound with a zero additive
    floor.  Its non-asymptotic sibling security_witness_schreier, in
    legacy/security/pgg_free_words.v, takes a
    weval_inj premise, which the symmetrized alphabet fails at every L >= 2
    because the two-letter words (0,1) and (1,0) both evaluate to the
    identity, so this is the only witness this alphabet supports. *)
Definition pgl27_security_asymptotic (R : realType) :=
  security_witness_schreier_asymptotic (pgl27_schreier_cert R).
