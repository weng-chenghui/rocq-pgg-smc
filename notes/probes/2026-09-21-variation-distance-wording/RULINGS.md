# Rulings on the audit of the variation-distance sheet (2026-09-21)

Sheet `SHEET.md` (one Opus writer, 25 rows), audit `AUDIT.md` (one Opus
auditor, read-only, GO-WITH-CHANGES, W1 to W12), literature check `LOOKUP.md`
(a Sonnet retrieval, audited by the main session against the two sources).
Owner's decision: fix the wording, rename NO identifier. Rulings by the main
session. Rows T1 to T12, T14, T18 to T25 are accepted as the sheet has them,
with W8's one-word form for T17.

| finding | ruling |
|---|---|
| W1 | ACCEPT: T13's three boxed lines at exactly 80 bytes (the auditor's text) |
| W2, W3, W7, W12, U1 | SUPERSEDED by the literature check, which the audit did not have. The texts to land are in the section below |
| W4 | the pass is applied BY HAND; `apply_tsv.py` and `check_pass.py` are not used (one row inserts lines). The main session checks code tokens instead |
| W5 | ACCEPT both: `symm_ds_TV_bound` line 668 as the auditor wrote it; `symm_ds_TV_bound_inv_closed` (about lines 809-816) re-laid BY HAND with "in variation distance" after "of uniform", within the docstring's own width |
| W6, W10, W11 | noted; no applied text is affected |
| W8 | ACCEPT the one-word form |
| W9 | ACCEPT INTO THIS PASS: the three uses of "floors" for a lower bound in `instances/kim2025/kim_input_privacy.v` (about lines 248, 443, 528) become "bounds ... from below", each after reading the statement it sits on (`kim_qbar_ge` is a lower bound on the denominator); the verb "floor" for the integer part, if any occurs, is untouched |
| N1 | ACCEPT: "Euclidean norm" in `pgg_mixing.v` (the object is a square root of a sum of squares); "sum-of-squares" stays in `pgg_schreier.v` for Saloff-Coste's conversion |

## The texts for `security/pgg_schreier.v` (replace T15 and T16)

What the sources say is in `LOOKUP.md`: Diaconis 1988, Chapter 3, Section B,
LEMMA 1 (Upper bound lemma), p. 24, has the constant 4 on the squared total
variation distance (`||.|| = (1/2) sum |.|`); Levin-Peres-Wilmer 2017, Lemma
12.18, has `4 ||P^t(x,.) - pi||_TV^2 <= sum_{j>=2} f_j(x)^2 lambda_j^{2t}` for
a reversible chain. So the literature bounds `2 * d_TV`, which is `var_dist`,
by `sqrt(N) * rate^L`, and the display of line 278 lacks the factor two; the
label "Proposition 2" is wrong.

1. Banner of the section, lines 277 to 282. New words, in a box whose NEW or
   CHANGED lines are exactly 80 bytes (the untouched neighbours keep their
   widths):

   "The standard upper bound lemma (Diaconis 1988, Ch. 3B, Lemma 1; for a
   reversible chain Levin-Peres-Wilmer 2017, Lemma 12.18) bounds 4 * d_TV^2
   by a sum over the non-trivial eigenvalues; when each of them is at most
   1 - lambda_gap in modulus this gives"
   then the display line
   "  2 * d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L"
   then the three existing lines 279 to 281 unchanged, then line 282
   unchanged, then a new paragraph:
   "The left side is var_dist, the sum of absolute differences, d_TV being
   the total variation distance of the literature, so sc_convergence states
   that bound with no factor lost. security/pgg_mixing.v proves the var_dist
   form from a Rayleigh bound on Q^2, as symm_ds_TV_bound for an alphabet of
   involutions and as symm_ds_TV_bound_inv_closed for an alphabet closed
   under inverses."
   The prover checks the last sentence against the two statements and their
   section hypotheses (`0 <= alpha`, `alpha <= 1`, which alphabet condition
   each lemma has) and writes the hypotheses as they are if they differ.
2. The field comment, lines 320 to 323:
   line 320 becomes "Diaconis (1988), Ch. 3B, Lemma 1 (upper bound lemma)";
   line 321 unchanged; lines 322-323 become
   "Applied to the Schreier graph (N vertices) instead of the Cayley graph
   (|G| vertices), giving prefactor sqrt(N). The field bounds var_dist, which
   is 2 * d_TV, the left side of the bound displayed in the banner of this
   section."
   laid out at the comment's own indent of five, single sentence spacing.
