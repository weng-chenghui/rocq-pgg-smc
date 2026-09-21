# Applied: the variation-distance wording pass (2026-09-21)

Base HEAD `f2897c4`, branch `feat/tableau-extensions-probe`. Comments only, by
hand, no compile, no commit, no identifier renamed. `RULINGS.md` was followed
where it replaces the sheet; `AUDIT.md` supplied W1, W5 and W8; `SHEET.md`
supplied the rest.

Six files changed, code token stream byte-identical to `git show HEAD:<file>`
for each one.

## Rows whose applied text differs from `SHEET.md`

### T13 — `security/pgg_mixing.v` 652 to 654 (W1's text, three boxed lines at 80)

```
(* Combines the column-vector variation-distance bound, the bridge lemmas     *)
(* of Section 6, and the Rayleigh hypothesis on Q^2 to deliver the exact      *)
(* shape of `SchreierCertificate.sc_convergence`.                             *)
```

The three lines were 79 bytes at HEAD and are 80 bytes now. The box frame at
651 and 655 was already 80.

### W5 (a) — `security/pgg_mixing.v` 670, inside the `symm_ds_TV_bound` docstring

Line 670 alone, 72 bytes, no rewrap:

```
    sqrt(N) * alpha^L of uniform in variation distance. The spectral gap
```

### W5 (b) — `security/pgg_mixing.v` 814 to 819, `symm_ds_TV_bound_inv_closed`

Re-laid by hand within the paragraph's own width (the widest line of the
paragraph at HEAD was 75; the widest here is 74). Lines 811 to 813 untouched.
Five lines became six.

```
    sqrt(N) * alpha^L of uniform in variation distance.  The conclusion of
    symm_ds_TV_bound under the weaker structural hypothesis: an alphabet
    that carries the inverse of each of its letters, rather than one whose
    letters are all involutions.  The bound is unconditional in the
    adversary and averages over words; alpha is the only quantity an
    instance must supply. *)
```

### RULINGS text 1 — `security/pgg_schreier.v` 277 to 281 and 287 to 294

Lines 277 and 278 became five lines, all 80 bytes. Lines 282 to 285 (the old
279 to 282) are untouched and keep their 79 bytes.

```
(* The standard upper bound lemma (Diaconis 1988, Ch. 3B, Lemma 1; for a      *)
(* reversible chain Levin-Peres-Wilmer 2017, Lemma 12.18) bounds 4 * d_TV^2   *)
(* by a sum over the non-trivial eigenvalues; when each of them is at most    *)
(* 1 - lambda_gap in modulus this gives                                       *)
(*   2 * d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L           *)
```

A blank boxed line at 286 (80 bytes, the separator this box already uses at
276 and at 295) opens the new paragraph at 287 to 294:

```
(* The left side is var_dist, the sum of absolute differences, d_TV being the *)
(* total variation distance of the literature, so sc_convergence states that  *)
(* bound with no factor lost. security/pgg_mixing.v proves the var_dist form  *)
(* from a Rayleigh bound on Q^2, as symm_ds_TV_bound for an alphabet of       *)
(* involutions under 0 <= alpha and alpha <= 1, and as                        *)
(* symm_ds_TV_bound_inv_closed for an alphabet each of whose letters is       *)
(* paired with its inverse by an involution of the letter index               *)
(* under 0 <= alpha alone.                                                    *)
```

The last sentence states the hypotheses as they are, which differs from the
form the ruling anticipated. See "Hypotheses read" below.

### RULINGS text 2 — `security/pgg_schreier.v` 332 and 334 to 337

Line 333, the Saloff-Coste label, is untouched.

```
       Diaconis (1988), Ch. 3B, Lemma 1 (upper bound lemma)
```

```
     Applied to the Schreier graph (N vertices) instead of the Cayley
     graph (|G| vertices), giving prefactor sqrt(N). The field bounds
     var_dist, which is 2 * d_TV, the left side of the bound displayed
     in the banner of this section. *)
```

Indent five, single sentence spacing, widths 69, 69, 70, 38, inside the
comment's own width (its widest line is 73).

### T17 — `security/pgg_schreier.v` 393 (W8's one-word form, 67 bytes)

```
   IMPORTANT: the actual var_dist (exact variation distance) is NOT
```

### W9 site 1 — `instances/kim2025/kim_input_privacy.v` 248, on `kim_w_ge`

Line 248 alone, 51 bytes; 246 and 247 untouched.

```
    bound a realised view's cut mass from below. *)
```

### W9 site 2 — `instances/kim2025/kim_input_privacy.v` 443 to 444, on `kim_q_ge_pos`

```
    bounds an individual input's realised view mass from below, the fact
    kim_qbar_ge averages across the false fibre. *)
```

### W9 site 3 with T22 — `instances/kim2025/kim_input_privacy.v` 527 to 530

T22's replacement carrying W9's tail; five lines became six.

```
    16 eps^2 / (1/5 - |eps|). This squares kim_qbar_diff's
    variation-distance bound and bounds the denominator from below with
    kim_qbar_ge, the two facts the chi-square-to-KL step kim_div_bound
    needs. *)
```

## Hypotheses read for the banner's last sentence

`symm_ds_TV_bound`, `security/pgg_mixing.v` 675 to 686, in
`Section schreier_TV_bound`:

- section hypothesis `sigmas_invol : forall k : 'I_Tg,
  (tnth sigmas k * tnth sigmas k)%g = 1%g`, every letter its own inverse
- premises `0 <= alpha`, `alpha <= 1`, and the Rayleigh bound on Q^2 for
  sum-zero column vectors

`symm_ds_TV_bound_inv_closed`, `security/pgg_mixing.v` 819 to 829, in
`Section schreier_inv_closed`:

- section hypotheses `fK : involutive f` and `sigmas_fV : forall k : 'I_Tg,
  tnth sigmas (f k) = ((tnth sigmas k)^-1)%g`, each letter paired with its
  inverse by an involution of the letter index
- premises `0 <= alpha` and the Rayleigh bound. There is no `alpha <= 1`.

The ruling listed `0 <= alpha` and `alpha <= 1` for both. Only the first lemma
carries `alpha <= 1`, so the applied sentence attaches it to
`symm_ds_TV_bound` alone and says `0 <= alpha alone` for the other. The
alphabet conditions are written in the wording the file's own Section 8 banner
already uses.

Statements read for the three W9 sites:

- `kim_w_ge` at 249, `5%:R^-1 - |eps| <= W k`, a lower bound; its consumer
  `kim_q_ge_pos` sums it (proof line 461) to a lower bound on `kim_q A x' v`
- `kim_q_ge_pos` at 445 to 446,
  `0 < kim_qctr A x' v -> 5%:R^-1 - |eps| <= kim_q A x' v`
- `kim_qbar_ge` at 468 to 469,
  `kim_qbar A v != 0 -> 5%:R^-1 - |eps| <= kim_qbar A v`, which is the
  denominator of the chi-square sum `kim_chi2_bound` states

Every ruled sentence was true of what was read, apart from the alpha
conditions noted above.

## Self-checks

- code token stream identical to HEAD for all six files: yes, six of six
- `git diff HEAD --stat`: the six files, plus `.claude/scheduled_tasks.lock`,
  which the harness rewrote before this pass began (it is `M` in the session's
  opening git status) and which was not touched here
- added lines over 80 bytes: none
- new or changed boxed lines not exactly 80 bytes: none
- word-boundary scan of the added lines for the barred, economic and history
  vocabulary, and for the norm abbreviation: no hits
- scan of the added lines for `total variation|total-variation|TV distance|
  variational`: one hit, `total variation distance of the literature`, the
  allowed name for the halved quantity
- whole-file scan of the six files for the same pattern: two hits,
  `security/pgg_schreier.v:94` (the Literature index entry naming
  Saloff-Coste 1997 Theorem 2.6, a citation) and `security/pgg_schreier.v:288`
  (the allowed phrase)
- `git grep -n -w "floors\|floor" -- instances/kim2025/kim_input_privacy.v`:
  no match

## Done differently, and why

1. The banner's last sentence carries the alpha conditions per lemma rather
   than as one shared pair, because the two statements differ.
2. A blank boxed line was inserted at `security/pgg_schreier.v:286` so that
   the added text is a paragraph of the box in the box's own convention, as
   the ruling asks for a new paragraph.
3. W5's second docstring and T22 each grew by one line, because the added
   words do not fit the paragraph's own width otherwise.
