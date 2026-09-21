# Variation-distance wording: proposed comment changes

Repository HEAD 7bd3bff, branch feat/tableau-extensions-probe. No `.v` file was
edited, nothing was compiled, no Rocq process was started.

## The fact this sheet enforces

infotheo defines `var_dist P Q := \sum_(a : A) `| P a - Q a |` with no factor
one half (`infotheo-itp/variation_dist.v:34`). A `var_dist` is therefore the sum
of absolute differences, valued in [0,2], and equals twice the total variation
distance of the literature. A distinguisher's advantage is at most half of a
`var_dist` bound. The tree's vocabulary: a `var_dist` is "the variation
distance" or "the sum of absolute differences"; "the total variation distance of
the literature" names the halved quantity only.

Identifiers are not renamed. `symm_ds_TV_bound`, `symm_ds_TV_bound_cV`,
`symm_ds_TV_bound_inv_closed`, `kim_w_tv` and every other identifier keep their
names; only the prose around them changes.

## Reading the replacement column

A replacement never contains the two-byte comment opener, the three-byte
documentation opener, or the two-byte closer. They are written as markers:

    <O>   the comment opener, two bytes
    <D>   the documentation-comment opener, three bytes
    <C>   the comment closer, two bytes

Each marker is one byte wider than the delimiter it stands for, so a replacement
line as printed here is one byte wider than the line to be written. The `width`
given on each replacement line is the true byte width of that line with the real
delimiters in place, already verified, and it is the authoritative number. A
boxed line is padded with spaces so that its total width equals the box width of
its own file.

---

# Part 1. Rows

Twenty-five rows over six files. Counts per file: `security/pgg_mixing.v` 14
(T1 to T14), `security/pgg_schreier.v` 3 (T15 to T17),
`instances/kim2025/kim_input_privacy.v` 5 (T18 to T22),
`instances/kim2025/five_card_kim.v` 1 (T23), `instances/pgl27/pgl27_mixing.v` 1
(T24), `instances/pgl27/pgl27_profile.v` 1 (T25). None is frozen.

---

## T1

**File** `security/pgg_mixing.v` **lines** 6

**Sits on** the file header box. The bound the file proves, displayed two lines
below at line 8:

    var_dist(Q^L e_s, U) <= sqrt(N) * alpha^L

**Current, byte for byte**

```
(* This file proves the generic total-variation-distance bound                *)
```

**Replacement** (one boxed line, box width 80)

```
<O> This file proves the generic variation-distance bound                      <C>
```
width 80.

**Reason** The displayed quantity is a `var_dist`, so the name carries a factor
of two against the literature's total variation distance.

---

## T2

**File** `security/pgg_mixing.v` **lines** 37

**Sits on** the `== Contents ==` index entry of the header box, whose next line
names `symm_ds_TV_bound`, a `var_dist` bound.

**Current, byte for byte**

```
(* Total-variation bound (main theorem):                                      *)
```

**Replacement** (one boxed line, box width 80)

```
<O> Variation-distance bound (main theorem):                                   <C>
```
width 80.

**Reason** Index entry for a `var_dist` bound. This is an index paragraph: edit
this line alone and leave the entry line below it untouched.

---

## T3

**File** `security/pgg_mixing.v` **lines** 118

**Sits on** the Section 2 banner. The section's lemma is

    Lemma var_dist_le_sqrtN_norm2 (R : realType) (A : finType)
        (P Q : R.-fdist A) :
      var_dist P Q
      <= Num.sqrt #|A|%:R * Num.sqrt (\sum_(a : A) (P a - Q a) ^+ 2).

**Current, byte for byte**

```
(*     Section 2: Bridge from variation distance to L^2 norm                  *)
```

**Replacement** (one boxed line, box width 80)

```
<O>     Section 2: Bridge from variation distance to the Euclidean norm        <C>
```
width 80.

**Reason** The name of the quantity is already right. The change removes the
barred letter-and-digit norm abbreviation. The same file already writes
"Euclidean norm" at lines 31, 435 and 441, so this is also the file's own word
for the concept. Note a deviation from the instruction to reuse
`pgg_schreier.v`'s "sum-of-squares": see Part 2, note N1.

---

## T4

**File** `security/pgg_mixing.v` **lines** 302

**Sits on** the Section 5 banner, whose own body displays the conclusion at line
307:

    var_dist(Q^L e_s, U) <= sqrt(N) * alpha^L.

**Current, byte for byte**

```
(*     Section 5: Total-variation bound                                       *)
```

**Replacement** (one boxed line, box width 80)

```
<O>     Section 5: Variation-distance bound                                    <C>
```
width 80.

**Reason** The section's conclusion is a `var_dist` bound, displayed five lines
below in the same banner.

---

## T5

**File** `security/pgg_mixing.v` **lines** 421 to 423

**Sits on**

    Lemma es_minus_U_norm_sq_le1 (s : 'I_N) :
      cV_inner (e_cV s - uniform_cV) (e_cV s - uniform_cV) <= 1.

**Current, byte for byte**

```
(** es_minus_U_norm_sq_le1 — the mean-zero witness e_s - U has squared norm
    1 - 1/N, so in particular at most 1: the starting slack the spectral
    contraction alpha^L multiplies down in the final TV bound. *)
```

**Replacement** (free-form documentation comment, four lines replacing three)

```
<D> es_minus_U_norm_sq_le1 — the mean-zero witness e_s - U has squared norm
    1 - 1/N, so in particular at most 1: the starting slack the spectral
    contraction alpha^L multiplies down in the final variation-distance
    bound. <C>
```
widths 74, 72, 71, 13.

**Reason** The bound this slack feeds is `symm_ds_TV_bound_cV`, a bare sum of
absolute differences with no factor one half. Line 421 is unchanged.

---

## T6

**File** `security/pgg_mixing.v` **lines** 431

**Sits on**

    Definition vec_norm2 (v : 'cV[R]_N) : R := Num.sqrt (cV_inner v v).

**Current, byte for byte**

```
(* The L^2 norm of a column vector. *)
```

**Replacement** (free-form single-line comment)

```
<O> The Euclidean norm of a column vector. <C>
```
width 44.

**Reason** Removes the barred letter-and-digit norm abbreviation. The
definition is a square root of an inner product, which is the Euclidean norm,
not a sum of squares.

---

## T7

**File** `security/pgg_mixing.v` **lines** 434 to 435

**Sits on**

    Lemma vec_norm2_ge0 (v : 'cV[R]_N) : 0 <= vec_norm2 v.

**Current, byte for byte**

```
(** vec_norm2_ge0 — the L^2 norm vec_norm2 v is non-negative, as any
    Euclidean norm must be. *)
```

**Replacement** (free-form documentation comment, two lines)

```
<D> vec_norm2_ge0 — the Euclidean norm vec_norm2 v is non-negative, as any
    norm must be. <C>
```
widths 76, 20.

**Reason** Removes the barred abbreviation and leaves one word per concept:
the paragraph already said "Euclidean norm" in its second line for the same
object it called an "L^2 norm" in its first.

---

## T8

**File** `security/pgg_mixing.v` **lines** 439 to 442

**Sits on**

    Lemma symm_ds_power_norm2_bound (L : nat) (v : 'cV[R]_N) :
      \sum_i v i ord0 = 0 ->
      vec_norm2 (Q ^+ L *m v) <= alpha ^+ L * vec_norm2 v.

**Current, byte for byte**

```
(** symm_ds_power_norm2_bound — the square root of
    symm_ds_power_norm_sq_bound: ||Q^L v|| <= alpha^L ||v|| whenever
    sum_i v_i = 0, the Euclidean-norm form the bridge from the sum of
    absolute values composes with to reach the total-variation bound. *)
```

**Replacement** (free-form documentation comment, four lines; only the last
line changes)

```
<D> symm_ds_power_norm2_bound — the square root of
    symm_ds_power_norm_sq_bound: ||Q^L v|| <= alpha^L ||v|| whenever
    sum_i v_i = 0, the Euclidean-norm form the bridge from the sum of
    absolute values composes with to reach the variation-distance bound. <C>
```
widths 46, 68, 69, 75.

**Reason** The bound it composes into is `symm_ds_TV_bound_cV`, a bare sum of
absolute differences. Lines 439 to 441 are unchanged.

---

## T9

**File** `security/pgg_mixing.v` **lines** 500

**Sits on**

    Lemma es_minus_U_norm2_le1 (s : 'I_N) :
      vec_norm2 (e_cV s - uniform_cV) <= 1.

**Current, byte for byte**

```
(* The L^2 norm of e_s - U is at most 1. *)
```

**Replacement** (free-form single-line comment)

```
<O> The Euclidean norm of e_s - U is at most 1. <C>
```
width 49.

**Reason** Removes the barred abbreviation. `vec_norm2` is a square root, so
the Euclidean norm is the accurate name.

---

## T10

**File** `security/pgg_mixing.v` **lines** 555

**Sits on** the Section 6 banner, whose bridges feed `symm_ds_TV_bound`, a
`var_dist` bound.

**Current, byte for byte**

```
(* general TV bound applies.                                                  *)
```

**Replacement** (one boxed line, box width 80)

```
<O> general variation-distance bound applies.                                  <C>
```
width 80.

**Reason** The bound the banner points at is a `var_dist` bound. This is a
banner paragraph wider than the one line changed: edit line 555 alone.

---

## T11

**File** `security/pgg_mixing.v` **lines** 615 to 619

**Sits on**

    Lemma schreier_endpoint_eq_Q_power (L : nat) (s a : 'I_N) :
      fdistmap (fun sigma : {perm 'I_N} => sigma s) (rho_from_words L sigmas) a
      = ((schreier_transition R sigmas) ^+ L *m \col_i (i == s)%:R) a ord0.

**Current, byte for byte**

```
(* The coalition's endpoint marginal probability at card position s (from
   fdistmap ... rho_from_words, the probabilistic picture) equals the
   (a, ord0) entry of the L-step Schreier transition matrix applied to the
   point mass at s (Q^L *m e_s, the linear-algebra picture this file's
   spectral TV bound operates in): the bridge between the two. *)
```

**Replacement** (free-form comment, six lines replacing five)

```
<O> The coalition's endpoint marginal probability at card position s (from
   fdistmap ... rho_from_words, the probabilistic picture) equals the
   (a, ord0) entry of the L-step Schreier transition matrix applied to the
   point mass at s (Q^L *m e_s, the linear-algebra picture this file's
   spectral variation-distance bound operates in): the bridge between the
   two. <C>
```
widths 73, 65, 75, 73, 73, 10.

**Reason** The spectral bound of this file is `symm_ds_TV_bound_cV`, a bare sum
of absolute differences. Lines 615 to 618 are unchanged.

---

## T12

**File** `security/pgg_mixing.v` **lines** 648

**Sits on** the Section 7 banner. The section's theorem is

    Lemma symm_ds_TV_bound (alpha : R) (L : nat) (s : 'I_N) : ...
      var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                 (rho_from_words L sigmas))
               (fdist_uniform (card_ord N))
      <= Num.sqrt (N%:R) * alpha ^+ L.

**Current, byte for byte**

```
(*     Section 7: Schreier-form total-variation bound                         *)
```

**Replacement** (one boxed line, box width 80)

```
<O>     Section 7: Schreier-form variation-distance bound                      <C>
```
width 80.

**Reason** The section's conclusion is literally a `var_dist` bound.

---

## T13

**File** `security/pgg_mixing.v` **lines** 650 to 652

**Sits on** the Section 7 banner body, three lines below T12, describing the
proof of `symm_ds_TV_bound`.

**Current, byte for byte**

```
(* Combines the column-vector TV bound, the bridge lemmas of Section 6, and  *)
(* the Rayleigh hypothesis on Q^2 to deliver the exact shape of              *)
(* `SchreierCertificate.sc_convergence`.                                     *)
```

**Replacement** (three boxed lines, box width 79; the paragraph rewraps, so all
three lines change and must be edited line by line)

```
<O> Combines the column-vector variation-distance bound, the bridge lemmas    <C>
<O> of Section 6, and the Rayleigh hypothesis on Q^2 to deliver the exact     <C>
<O> shape of `SchreierCertificate.sc_convergence`.                            <C>
```
widths 79, 79, 79.

**Reason** The column-vector bound is `symm_ds_TV_bound_cV`, a bare sum of
absolute differences. This banner's box is 79 bytes wide, not 80, and the
paragraph rewraps across its three lines.

---

## T14

**File** `security/pgg_mixing.v` **lines** 726

**Sits on** the Section 8 banner, whose conclusion is

    Lemma symm_ds_TV_bound_inv_closed (alpha : R) (L : nat) (s : 'I_N) : ...
      var_dist ... <= Num.sqrt (N%:R) * alpha ^+ L.

**Current, byte for byte**

```
(* total-variation bound.  Involutive alphabets are the case f = id.          *)
```

**Replacement** (one boxed line, box width 80; the two-space sentence spacing
after the full stop is kept)

```
<O> variation-distance bound.  Involutive alphabets are the case f = id.       <C>
```
width 80.

**Reason** The bound repeated under the weaker hypothesis is a `var_dist`
bound. This is one line of a wider banner paragraph: edit line 726 alone.

---

## T15

**File** `security/pgg_schreier.v` **lines** 277 to 282, with four lines added
after 282

**Sits on** the Section 3 banner, introducing the record field

    sc_convergence : forall (L : nat) (s : 'I_N),
      var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                         (rho_from_words L sigmas))
               (fdist_uniform (card_ord N))
      <= Num.sqrt (N%:R) * (1 - sc_lambda_gap) ^+ L

**Current, byte for byte**

```
(* The standard upper bound lemma (Diaconis 1988, Ch. 3B Proposition 2):     *)
(*   d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L             *)
(* where Q is the Schreier transition matrix and lambda_gap is its spectral  *)
(* gap. This requires the chain to be doubly stochastic (uniform stationary  *)
(* distribution), which holds for symmetric generator sets (S = S^{-1}).     *)
(* Each instance axiomatizes the bound and justifies it per-family.          *)
```

**Replacement** (six boxed lines unchanged, four boxed lines added after them;
box width 79, and the display line 278 is 78 bytes wide and stays as it is)

```
(unchanged, lines 277 to 282, byte for byte as above)
<O> sc_convergence bounds var_dist, the sum of absolute differences, which is <C>
<O> twice d_TV, so the field asks for half the number the display above gives <C>
<O> for d_TV. security/pgg_mixing.v proves that var_dist form from a Rayleigh <C>
<O> bound on Q^2, as symm_ds_TV_bound.                                        <C>
```
widths 79, 79, 79, 79.

**Reason** The displayed literature statement is in the literature's quantity
and its name is correct, so it is left as it is. The field below it bounds a
`var_dist`, which is twice `d_TV`, so the field is the bound
`d_TV <= sqrt(N) * (1 - lambda_gap)^L / 2` and asks for half the displayed
number. The factor was checked against the proof in `security/pgg_mixing.v`:
`symm_ds_TV_bound_cV` bounds the full sum `\sum_a |(Q^L e_s)_a - U_a|` by
`sqrt(N) * alpha^L` through `cV_l1_le_sqrtN_norm2`,
`symm_ds_power_norm2_bound` and `es_minus_U_norm2_le1`, so `sqrt(N) * alpha^L`
bounds the un-halved sum, not half of it. Whether the display's own constant
should read `sqrt(N) / 2` is a question about Diaconis's constant that the file
does not settle: see Part 2, unsure U1.

---

## T16

**File** `security/pgg_schreier.v` **lines** 322 to 323

**Sits on** the record field

    sc_convergence : forall (L : nat) (s : 'I_N),
      var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                         (rho_from_words L sigmas))
               (fdist_uniform (card_ord N))
      <= Num.sqrt (N%:R) * (1 - sc_lambda_gap) ^+ L

**Current, byte for byte**

```
     Applied to the Schreier graph (N vertices) instead of the
     Cayley graph (|G| vertices), giving prefactor sqrt(N). *)
```

**Replacement** (free-form comment indented five, four lines replacing two;
single-space sentence spacing, matching this comment)

```
     Applied to the Schreier graph (N vertices) instead of the
     Cayley graph (|G| vertices), giving prefactor sqrt(N). Both cited
     theorems bound d_TV. var_dist is twice d_TV, so the field asks for
     half the number they give for d_TV. <C>
```
widths 61, 70, 71, 43.

**Reason** The two citations two lines above, Diaconis 1988 Ch. 3B Proposition
2 and Saloff-Coste 1997 Theorem 2.6, are stated in the literature's total
variation distance and keep their names. The field's own statement is a
`var_dist` bound, so without this clause the comment attributes a
sum-of-absolute-differences bound to theorems about the halved quantity with
no factor stated. The citation labels at lines 320 and 321 are unchanged.

---

## T17

**File** `security/pgg_schreier.v` **lines** 379

**Sits on**

    Lemma schreier_epsilon_decreasing (sc : SchreierCertificate) (L L' : nat) :
      (L <= L')%N -> schreier_epsilon sc L' <= schreier_epsilon sc L.

**Current, byte for byte**

```
   IMPORTANT: the actual var_dist (exact variational distance) is NOT
```

**Replacement** (free-form comment indented three, one line of a longer
paragraph: edit line 379 alone)

```
   IMPORTANT: the actual var_dist, the exact variation distance, is NOT
```
width 71.

**Reason** "variational distance" is not the tree's word for a `var_dist`. The
numbers in the table four lines below, 0.8 and 1.2, exceed one and so are
un-halved sums, which the name must not contradict.

---

## T18

**File** `instances/kim2025/kim_input_privacy.v` **lines** 234 to 236

**Sits on**

    Fact kim_w_dev (k : 'I_5) : `|W k - 5%:R^-1| <= `|eps|.

**Current, byte for byte**

```
(** kim_w_dev — each Kim weight [W k] deviates from the uniform value 1/5 by
    at most the bias: `|W k - 1/5| <= |eps|. This is the per-letter
    deviation kim_w_tv sums into a total-variation bound. *)
```

**Replacement** (free-form documentation comment, three lines; only the last
line changes)

```
<D> kim_w_dev — each Kim weight [W k] deviates from the uniform value 1/5 by
    at most the bias: `|W k - 1/5| <= |eps|. This is the per-letter
    deviation kim_w_tv sums into a variation-distance bound. <C>
```
widths 78, 67, 63.

**Reason** The bound `kim_w_tv` states is `\sum_(k in 'I_5) |W k - 1/5| <= 2 |eps|`,
a bare sum with no factor one half. The identifier `kim_w_tv` keeps its name.

---

## T19

**File** `instances/kim2025/kim_input_privacy.v` **lines** 254 to 257

**Sits on**

    Fact kim_w_tv : \sum_(k in 'I_5) `|W k - 5%:R^-1| <= 2%:R * `|eps|.

**Current, byte for byte**

```
(** kim_w_tv — the Kim weight vector deviates from the uniform distribution
    on 'I_5, in total variation, by at most twice the bias:
    sum_k `|W k - 1/5| <= 2 |eps|. This is the total-variation ceiling
    kim_q_dev transports to the per-input view law. *)
```

**Replacement** (free-form documentation comment, four lines)

```
<D> kim_w_tv — the Kim weight vector deviates from the uniform distribution
    on 'I_5, in variation distance, by at most twice the bias:
    sum_k `|W k - 1/5| <= 2 |eps|. This is the variation-distance bound
    kim_q_dev transports to the per-input view law. <C>
```
widths 77, 62, 71, 54.

**Reason** The statement is a bare sum of absolute deviations with no factor
one half, so the bound of `2 |eps|` is twice what the literature's total
variation distance would carry. The number `2 |eps|` is unchanged. The third
line makes a second change, replacing the metaphor the paragraph used for a
bound by the word bound.

---

## T20

**File** `instances/kim2025/kim_input_privacy.v` **lines** 353 to 357

**Sits on**

    Fact kim_q_dev (A : seq nat) (x : bool * bool) :
      \sum_v `|kim_q A x v - kim_qctr A x v| <= 2%:R * `|eps|.

**Current, byte for byte**

```
(** kim_q_dev — the per-input view law kim_q A x deviates from the uniform
    reference kim_qctr A x, in total variation, by at most twice the bias:
    sum_v `|kim_q A x v - kim_qctr A x v| <= 2 |eps|. This transports
    kim_w_tv's per-letter bound to the level of a single input's view
    law. *)
```

**Replacement** (free-form documentation comment, five lines; only the second
line changes)

```
<D> kim_q_dev — the per-input view law kim_q A x deviates from the uniform
    reference kim_qctr A x, in variation distance, by at most twice the bias:
    sum_v `|kim_q A x v - kim_qctr A x v| <= 2 |eps|. This transports
    kim_w_tv's per-letter bound to the level of a single input's view
    law. <C>
```
widths 76, 77, 69, 69, 11.

**Reason** The statement is a bare sum of absolute differences with no factor
one half. The number `2 |eps|` is unchanged.

---

## T21

**File** `instances/kim2025/kim_input_privacy.v` **lines** 376 to 379

**Sits on**

    Fact kim_qbar_diff (A : seq nat) (x : bool * bool) :
      ~~ (x.1 && x.2) ->
      \sum_v `|kim_q A x v - kim_qbar A v| <= 4%:R * `|eps|.

**Current, byte for byte**

```
(** kim_qbar_diff — a false-fibre input's view law kim_q A x differs from the
    mixed reference kim_qbar A, in total variation, by at most four times
    the bias. This is the total-variation bound kim_chi2_bound squares and
    rescales into a chi-square bound. *)
```

**Replacement** (free-form documentation comment, four lines)

```
<D> kim_qbar_diff — a false-fibre input's view law kim_q A x differs from the
    mixed reference kim_qbar A, in variation distance, by at most four times
    the bias. This is the variation-distance bound kim_chi2_bound squares and
    rescales into a chi-square bound. <C>
```
widths 79, 76, 77, 40.

**Reason** The statement is a bare sum of absolute differences with no factor
one half. The number `4 |eps|` is unchanged.

---

## T22

**File** `instances/kim2025/kim_input_privacy.v` **lines** 525 to 529

**Sits on**

    Fact kim_chi2_bound (A : seq nat) (x : bool * bool) :
      ~~ (x.1 && x.2) ->
      \sum_v (kim_q A x v - kim_qbar A v) ^+ 2 / kim_qbar A v
        <= 16%:R * eps ^+ 2 / (5%:R^-1 - `|eps|).

**Current, byte for byte**

```
(** kim_chi2_bound — a false-fibre input's view law deviates from the mixed
    reference kim_qbar, in Pearson chi-square, by at most
    16 eps^2 / (1/5 - |eps|). This squares kim_qbar_diff's total-variation
    bound and floors the denominator with kim_qbar_ge, the two facts the
    chi-square-to-KL step kim_div_bound needs. *)
```

**Replacement** (free-form documentation comment, five lines; the tail rewraps,
so lines 527 to 529 must be edited line by line)

```
<D> kim_chi2_bound — a false-fibre input's view law deviates from the mixed
    reference kim_qbar, in Pearson chi-square, by at most
    16 eps^2 / (1/5 - |eps|). This squares kim_qbar_diff's
    variation-distance bound and floors the denominator with kim_qbar_ge,
    the two facts the chi-square-to-KL step kim_div_bound needs. <C>
```
widths 77, 57, 58, 73, 67.

**Reason** The bound being squared is `kim_qbar_diff`, a bare sum of absolute
differences with no factor one half. The number `16 eps^2 / (1/5 - |eps|)` is
unchanged. The verb "floors" is kept: it is this file's own word for a lower
bound, used the same way at line 247.

---

## T23

**File** `instances/kim2025/five_card_kim.v` **lines** 505 to 507

**Sits on**

    Definition fc_kim_security_bundle (L : nat) :
      ShuffleCertificateBundle R FiveCardKim_M := ...
        (Some (@MkSecurityExact R FiveCardKim_M
          (@rho_from_words_weighted R 3 4 L fc_kim_gens W)
          (2%:R * 4%:R / 5%:R * kim_lambda2 ^+ L)
          (kim_var_dist_exact L)))

**Current, byte for byte**

```
(** fc_kim_security_bundle — the certificate bundle at word length L, carrying
    the spectral marginal bound, the exact variational distance and the
    asymptotic convergence certificate. *)
```

**Replacement** (free-form documentation comment, three lines; only the second
line changes)

```
<D> fc_kim_security_bundle — the certificate bundle at word length L, carrying
    the spectral marginal bound, the exact variation distance and the
    asymptotic convergence certificate. <C>
```
widths 80, 69, 42.

**Reason** The exact value carried is `kim_var_dist_exact`, a `var_dist`, and
the file's own header at line 68 records it as `var_dist = 2 * d_TV`.
"variational distance" is not the tree's word for it.

---

## T24

**File** `instances/pgl27/pgl27_mixing.v` **lines** 13

**Sits on** the file header box. The checker it describes is

    Local Definition mixing_bound_ok : bool :=
      let D := (5 ^ 200)%num in
      ((2 ^ 40) * foldl (fun acc c => (acc + absdiffN (336 * c) D)%num) 0%num
                        (walkN 200)
       <=? 336 * D)%num.

**Current, byte for byte**

```
(* identity, and a scalar checker certifies its total-variation bound.        *)
```

**Replacement** (one boxed line, box width 80)

```
<O> identity, and a scalar checker certifies its variation-distance bound.     <C>
```
width 80.

**Reason** `mixing_bound_ok` sums `absdiffN (336 * c) D` over the 336 walk
counts with no factor one half, and the file's own index at line 29 already
reads "in variation distance". This is one line of a wider header paragraph:
edit line 13 alone.

---

## T25

**File** `instances/pgl27/pgl27_profile.v` **lines** 78 to 79

**Sits on**

    Lemma pgl27_se_exact (s : 'I_8) :
      var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist)
               (fdist_uniform (card_ord 8)) = 0%R.

**Current, byte for byte**

```
(** pgl27_se_exact — the single-card pushforward is at variational distance
    zero from uniform. *)
```

**Replacement** (free-form documentation comment, two lines; only the first
line changes)

```
<D> pgl27_se_exact — the single-card pushforward is at variation distance
    zero from uniform. <C>
```
widths 75, 25.

**Reason** The statement is a `var_dist` equality. "variational distance" is
not the tree's word for it. The value zero is the same under either
convention, so nothing else changes.

---

# Part 2. Left alone, unsure, frozen

## Left alone

These sites name the literature's halved quantity correctly, or mention an
identifier whose name the owner has decided to keep.

### Correct use of the literature's name for the halved quantity

Each of these says the tree's number is a sum of absolute differences and that
the literature's total variation distance is half of it. The name is attached
to the halved quantity, which is what the literature's name means.

| File | Line | What it says |
| --- | --- | --- |
| `lib/var_dist_supp.v` | 55 | the total variation distance of the literature is half of this quantity |
| `lib/var_dist_supp.v` | 182 | the literature's total variation distance is half of this |
| `instances/kim2025/five_card_kim.v` | 53 to 56, 68 | the convention paragraph: Kim uses `d_TV = (1/2) sum |P - Q|`, infotheo uses `var_dist = sum |P - Q|`, so `var_dist = 2 * d_TV` |
| `instances/kim2025/five_card_proximity.v` | 22 to 23 | bounds a sum of absolute differences, twice the total variation distance of the literature |
| `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | 50 | twice a total variation distance, advantage at most half the number |
| `instances/kim2025/tableau/five_card_tableau_sampled.v` | 254 | twice the total variation distance of the literature |
| `instances/pgl27/pgl27_proximity.v` | 22 | twice the total variation distance of the literature |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | 35 | twice a total variation distance |
| `instances/psl211/psl211_alldecks_input_distinguishability.v` | 155 | the sum of absolute differences being twice the total variation distance |
| `instances/psl211/psl211_word_proximity.v` | 17 | twice the total variation distance of the literature |
| `instances/s5/tableau/s5_tableau_sampled.v` | 95 | twice the total variation distance of the literature |
| `manifest/pgg_analysis_manifest.v` | 851 | twice the total variation distance of the literature |
| `manifest/pgg_tableau.v` | 715 | twice the total variation distance of the literature |
| `manifest/pgg_tableau.v` | 1641 | var_dist summing the absolute differences and so being twice the total variation distance |
| `manifest/pgg_tableau_marginal_bounds.v` | 75 | twice the total variation distance of the literature |
| `manifest/pgg_tableau_security_property_relations.v` | 629 | twice the literature's total variation distance |
| `security/var_dist_joint_law.v` | 10 | twice the total variation distance of the literature |
| `security/pgg_schreier.v` | 94 | the Literature index entry naming Saloff-Coste 1997 Theorem 2.6, "sum-of-squares to total variation conversion for reversible chains". The literature's theorem, in the literature's quantity, under the literature's name |
| `security/pgg_schreier.v` | 320, 321 | the two citation labels inside `sc_convergence`. The theorems are about `d_TV` and keep their names. T16 adds the factor clause beside them |

### Identifier mentions only, with no misnaming in the prose

The owner has decided identifiers are not renamed. At each of these the only
match is an identifier, and the surrounding prose is already right.

| File | Line | Identifier mentioned | Surrounding prose |
| --- | --- | --- | --- |
| `instances/s5/s5_mixing.v` | 11 | `symm_ds_TV_bound` | line 9 reads "in variation distance" |
| `instances/s5/s5_mixing.v` | 95 | `symm_ds_TV_bound` | about the range of alpha |
| `instances/s5/s5_mixing.v` | 117 | `symm_ds_TV_bound` | about involutive generators |
| `instances/s5/s5_mixing.v` | 421 | `symm_ds_TV_bound` | reads "the variation-distance bound" |
| `instances/pgl27/pgl27_spectral.v` | 169 | `symm_ds_TV_bound_inv_closed` | about the inverse-closure hypothesis |
| `security/pgg_mixing.v` | 513 | `symm_ds_TV_bound` | lines 511 to 512 read "the sum of absolute differences" |
| `security/pgg_mixing.v` | 665 | `symm_ds_TV_bound` | see note N2 |
| `security/pgg_mixing.v` | 809, 812 | `symm_ds_TV_bound_inv_closed`, `symm_ds_TV_bound` | see note N2 |

### Notes

**N1. "Euclidean norm" instead of "sum-of-squares" at T3, T6, T7, T9.** The
instruction was to carry `pgg_schreier.v`'s wording across. That wording,
"sum-of-squares to total variation conversion", names Saloff-Coste's theorem,
whose left-hand side is a chi-square, a sum of squares. In `pgg_mixing.v` the
object is `vec_norm2 v := Num.sqrt (cV_inner v v)`, the square root of a sum of
squares, so calling it a sum-of-squares would be type-dishonest. "Euclidean
norm" is also the word the same file already uses at lines 31, 435 and 441, so
it keeps one word per concept file-wide. If the owner prefers the uniform
wording anyway, T3, T6, T7 and T9 are the four lines to change again.

**N2. Two docstrings name no metric at all.** `symm_ds_TV_bound` at
`security/pgg_mixing.v:665` reads "is within sqrt(N) * alpha^L of the fully
uniform distribution", and `symm_ds_TV_bound_inv_closed` at line 809 reads
"lies within sqrt(N) * alpha^L of uniform". Both statements are `var_dist`
bounds. Neither misnames anything, so neither is a row here, but a reader
cannot tell from the "within" clause which of the two conventions the number is
in. Both paragraphs do say "the sum of absolute values" further down. Flagged
for the owner, not proposed.

**N3. The one non-frozen norm-abbreviation match outside `pgg_mixing.v` is a
false positive.** `security/pgg_schreier_weighted.v:349` matched only because a
table line puts `rho^L` and a following `2` in the same line:
`(*   Bound      sqrt(N) * rho^L           2(N-1)/N * |a-b|^L <= sqrt(N)*..   *)`.
There is no norm abbreviation there. Nothing to change.

## Unsure

**U1. `security/pgg_schreier.v:277 to 278`, the displayed Diaconis constant.**

Quoted byte for byte:

```
(* The standard upper bound lemma (Diaconis 1988, Ch. 3B Proposition 2):     *)
(*   d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L             *)
```

What I read. The field these two lines introduce, `sc_convergence` at lines 324
to 328, requires

    var_dist (fdistmap ... (rho_from_words L sigmas)) (fdist_uniform (card_ord N))
    <= Num.sqrt (N%:R) * (1 - sc_lambda_gap) ^+ L

Since `var_dist = 2 * d_TV`, that field is equivalent to
`d_TV <= sqrt(N) * (1 - lambda_gap)^L / 2`, which is half the number the
displayed line gives for `d_TV`. So the display as written does not, on its
own, yield the field.

What settles the tree's side. In `security/pgg_mixing.v`, `symm_ds_TV_bound_cV`
at lines 509 to 514 proves

    \sum_a `|(Q ^+ L *m e_cV s) a ord0 - uniform_cV a ord0|
    <= Num.sqrt (#|'I_N|%:R) * alpha ^+ L

that is, `sqrt(N) * alpha^L` bounds the un-halved sum. Its proof chains
`cV_l1_le_sqrtN_norm2`, then `symm_ds_power_norm2_bound`, then
`es_minus_U_norm2_le1`, with no factor one half anywhere. `symm_ds_TV_bound` at
line 674 then transports exactly that to `var_dist`. So the field's shape is
proved in-tree, and T15 and T16 state the factor from that side without
touching the display.

What I could not determine. Whether Diaconis 1988 Ch. 3B Proposition 2 states
`d_TV <= sqrt(N) * rate^L` or `2 * d_TV <= sqrt(N) * rate^L`, and therefore
whether line 278 should read `sqrt(N) / 2` or should keep `sqrt(N)` and be read
as the weaker of the two statements. That is a question about the cited book,
not about this file, and nothing in the repository answers it. T15 is written
so that it is correct either way: it states the field's own content and points
at the in-tree proof, and it does not assert a constant for Diaconis.

## Frozen, not touched

Six matches sit in files of `FROZEN_MODULES`. None is changed.

| File | Line | Text | Would it have been a row |
| --- | --- | --- | --- |
| `reconstruct/algebraic_rigidity.v` | 104 | "the variational distance converges to 0 geometrically in L." | Yes. `SecurityAsymptotic`'s bound is `var_dist (sigma s) uniform <= sa_eps_inf + sqrt(N) * (1 - gap)^L`, displayed at line 120 of the same file. "variational distance" is not the tree's word |
| `reconstruct/algebraic_rigidity.v` | 119 to 126 | "1 in infotheo's var_dist, the un-halved sum of absolute differences; 1/2 in the total variation distance of the literature" | No. Correct, and one of the vocabulary precedents |
| `reconstruct/algebraic_rigidity.v` | 157 | "the sum of absolute differences, which is twice the total variation distance of the literature" | No. Correct |
| `protocol/card_exchange_pismc.v` | 81 | "- Collusion bound: d_TV(adversary, uniform) <= eps + 2(T-1)/N." | Unsure, not a row. The header names `pgg_collusion_bound.v` and `pgg_schreier.v` as the source, both of which state their bounds on `var_dist`, so the `d_TV` name here may carry a factor of two against them. Both source files are frozen too |
| `security/pgg_security_solver.v` | 278 | "Is epsilon < 1? (i.e., d_TV < 1/2)" | No. `eps_lt1` tests `er.1 < er.2`, an epsilon in `var_dist` units below 1, which is `d_TV < 1/2`. The conversion is stated correctly |
| `security/pgg_security_solver.v` | 480 | "var_dist convention: sum |P(x) - Q(x)| (range 0..2, no 1/2 factor)." | No. Correct |

One further match, `smc/smc_interpreter.v:193`, is a comment quoting a
`disjoint` predicate applied to two list variables, whose names the
norm-abbreviation scan matched. It is a frozen file, and there is nothing to
change in it either way.

---

# Part 3. Reverse closure

Command run from the repository root:

    python3 scripts/comment_pass/closure.py security/pgg_mixing.v \
      security/pgg_schreier.v instances/kim2025/kim_input_privacy.v \
      instances/kim2025/five_card_kim.v instances/pgl27/pgl27_mixing.v \
      instances/pgl27/pgl27_profile.v

First three lines of its output:

```
touched 6, closure 82
frozen files met: none
security/pgg_schreier.v
```

The closure is 82 files and meets no frozen file, so the six changed files can
be recompiled without invalidating the endpoint file.
