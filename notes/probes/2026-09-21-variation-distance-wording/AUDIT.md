GO-WITH-CHANGES

Read-only audit. Nothing was edited, nothing compiled, no Rocq process started. All 25 "Current, byte for byte" quotes were re-read from the files at HEAD 7bd3bff and every one matches byte for byte. The factor-two fact is confirmed from the source: `/Users/cheng-huiweng/Projects/coq/infotheo-itp/variation_dist.v:34` defines `var_dist P Q := \sum_(a : A) `| P a - Q a |` with no one half, and the file's own title at line 8 is "The Variation Distance", so "variation distance" is infotheo's own name for the un-halved sum.

Three MUST, two SHOULD, seven NOTE. The MUSTs are two mechanical width failures that would make the applied pass fail the repository's own checker, and one sentence that asserts what two cited books state.

## Findings

| id | class | sheet row | finding | evidence |
| --- | --- | --- | --- | --- |
| W1 | MUST | T13 | The three boxed replacement lines are 79 bytes. The tree's rule is that a boxed line is exactly 80 bytes, delimiters included, with a space before the closer, and `check_pass.py` fails any new box line of width at least 78 that is not exactly 80. The three lines would be reported as `BOX security/pgg_mixing.v:650: 79 bytes, not 80`. | `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/scripts/comment_pass/README.md:78`, `.../check_pass.py:115-122`, `.../common.py:20`; the box frame at `security/pgg_mixing.v:647` and `:653` is 80 bytes |
| W2 | MUST | T15 | Same failure on the four added boxed lines, all 79 bytes. | as W1; frame at `security/pgg_schreier.v:290` is 80 bytes |
| W3 | MUST | T16 | The replacement says "Both cited theorems bound d_TV" and "the number they give for d_TV". Both sentences assert the convention of Diaconis 1988 Ch. 3B Proposition 2 and Saloff-Coste 1997 Theorem 2.6. The sheet's own U1 states that the repository does not settle this and that T15 was written so as not to assert it. T16 undoes that restraint on the same question. | `security/pgg_schreier.v:320-321`; SHEET.md T16 and U1 |
| W4 | SHOULD | T15 | The addition is an insertion of four new paragraphs, not a substitution. `apply_tsv.py` replaces the words of exactly one paragraph and has no insert form, and `check_pass.py` compares the paragraph sequence and would print an `insert` opcode. The segment at 277 to 282 parses as five one-line paragraphs, so four more appear. | `.../apply_tsv.py:1-8` and `:52-58`, `.../check_pass.py:23-41` and `:104-107` |
| W5 | SHOULD | note N2 | N2 says both paragraphs "do say the sum of absolute values further down". True of `symm_ds_TV_bound` at `security/pgg_mixing.v:670`. False of `symm_ds_TV_bound_inv_closed` at `security/pgg_mixing.v:809-816`, which names no metric anywhere, so its "lies within sqrt(N) * alpha^L of uniform" is unreadable in either convention. | `security/pgg_mixing.v:665-672` against `:809-816` |
| W6 | NOTE | T5, T8, T11, T16 | Six of the declared widths are wrong, although the sheet calls them authoritative and already verified. T5 line 1 claimed 74, real 77. T8 line 1 claimed 46, real 52. T11 lines 2 to 4 claimed 65, 75, 73, real 69, 74, 70. T16 line 1 claimed 61, real 62. Every one of these is an unchanged line, and every changed line's claimed width is correct, so no applied text is affected. | measured with `common.bw` against the sheet's own blocks |
| W7 | NOTE | U1 | Answered below from the repository alone. | `security/pgg_schreier.v:277-278` against `:324-328` |
| W8 | NOTE | T17 | The replacement also removes the parentheses and adds two commas. One word is enough. Both versions are true and grammatical. | `security/pgg_schreier.v:379` |
| W9 | NOTE | T22 | Keeping "floors" is the right call for this pass, because the file uses it at three places and changing one creates drift. It remains a metaphor for a lower bound and it collides with the standard floor function, so it deserves a pass of its own over `instances/kim2025/kim_input_privacy.v:248`, `:443` and `:528`. `kim_qbar_ge` at `:468-469` is indeed a lower bound on the denominator. | `instances/kim2025/kim_input_privacy.v:248, 443, 468-469, 528` |
| W10 | NOTE | Part 2 | The "left alone" table is incomplete. A paragraph-level scan finds five more sites that say the correct thing and are not tabulated. None is a missed change. | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:515-516`, `manifest/pgg_tableau.v:761-762`, `manifest/pgg_tableau_marginal_bounds.v:13-14`, `manifest/pgg_tableau_reading.v:28-29`, `manifest/pgg_tableau_security_property_relations.v:32-33` |
| W11 | NOTE | Part 2 | The identifier-mention table omits two sites, both correct as they stand. | `security/pgg_mixing.v:38` and `:45`, the Contents entries naming `symm_ds_TV_bound` and `symm_ds_TV_bound_inv_closed` |
| W12 | NOTE | T15 | The pointer says pgg_mixing.v proves the var_dist form "from a Rayleigh bound on Q^2". `symm_ds_TV_bound` also needs `0 <= alpha`, `alpha <= 1` and the section hypothesis that every letter is its own inverse, and the weaker alphabet case is a second lemma. An instance author reading only this clause could take the Rayleigh bound to be sufficient. Line 4 has forty spare columns. | `security/pgg_mixing.v:662-663` and `:673-684`, `:817` |

## Exact replacements

W1, `security/pgg_mixing.v` lines 650 to 652. One space added before each closer. Verified 80, 80, 80 bytes.

```
(* Combines the column-vector variation-distance bound, the bridge lemmas     *)
(* of Section 6, and the Rayleigh hypothesis on Q^2 to deliver the exact      *)
(* shape of `SchreierCertificate.sc_convergence`.                             *)
```

W2, `security/pgg_schreier.v`, the four lines added after 282. One space added before each closer. Verified 80, 80, 80, 80 bytes.

```
(* sc_convergence bounds var_dist, the sum of absolute differences, which is  *)
(* twice d_TV, so the field asks for half the number the display above gives  *)
(* for d_TV. security/pgg_mixing.v proves that var_dist form from a Rayleigh  *)
(* bound on Q^2, as symm_ds_TV_bound.                                         *)
```

W3, `security/pgg_schreier.v` lines 322 to 323, four lines replacing two, indent five, single-space sentence spacing to match the comment. Verified 62, 69, 70, 40 bytes. No double quote, no comment opener or closer, no barred word. It states the factor from the field's own side, which is proved in the tree, and says nothing about which convention either book uses. It is also three words shorter than the sheet's version.

```
     Applied to the Schreier graph (N vertices) instead of the
     Cayley graph (|G| vertices), giving prefactor sqrt(N). The field
     bounds var_dist, twice d_TV, so a source stated in d_TV must give
     half the bound the field states. *)
```

W4, `security/pgg_schreier.v`. Two ways to make T15 expressible as a sheet row. Either fold the four sentences into the paragraph at line 282, so the row becomes a substitution whose old text is "Each instance axiomatizes the bound and justifies it per-family." and whose new text is that sentence followed by the four, which `reflow.py` then lays out at 80 bytes; or apply T15 by hand with the W2 lines and record that `check_pass.py` will report one insert for it. The first is the safer one, because it keeps the whole pass inside the toolkit.

W5, `security/pgg_mixing.v` line 668 alone, replacing "the fully uniform distribution" by "uniform" so the metric fits without a rewrap. Verified 72 bytes.

```
    sqrt(N) * alpha^L of uniform in variation distance. The spectral gap
```

For `symm_ds_TV_bound_inv_closed` there is no one-line edit: lines 811 and 812 are 63 and 75 bytes and the paragraph is packed to 816, so inserting "in variation distance" after "of uniform" on line 812 cascades through to the end of the paragraph. That one needs a re-lay of 811 to 816, which is what `reflow.py` does when the words change.

W8, `security/pgg_schreier.v` line 379, the one-word version. Verified 67 bytes.

```
   IMPORTANT: the actual var_dist (exact variation distance) is NOT
```

W9, wording for a later pass over the three "floors" sites, shown here for T22's tail. Verified 71, 70, 13 bytes.

```
    variation-distance bound and bounds the denominator from below with
    kim_qbar_ge, the two facts the chi-square-to-KL step kim_div_bound
    needs. *)
```

W12, an optional replacement for the last added line of W2. Verified 80 bytes.

```
(* bound on Q^2, as symm_ds_TV_bound and symm_ds_TV_bound_inv_closed.         *)
```

## Rows accepted unchanged

T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T14, T17, T18, T19, T20, T21, T22, T23, T24, T25. Twenty-two of twenty-five. T13, T15 and T16 carry the three MUSTs.

Each accepted row was re-read against the statement its comment sits on. Type honesty holds throughout: every `<=` site says "bound" or "by at most", and the two equality sites say "the exact variation distance" at T23, where `kim_var_dist_exact` at `instances/kim2025/five_card_kim.v:464-467` is an equality, and "at variation distance zero" at T25, where `pgl27_se_exact` at `instances/pgl27/pgl27_profile.v:80-82` is `= 0`. Numbers are unchanged everywhere: `2 |eps|` at T18 to T20, `4 |eps|` at T21, `16 eps^2 / (1/5 - |eps|)` at T22. The vocabulary matches `lib/var_dist_supp.v:51-56` and `:180-184` and `security/pgg_collusion_bound.v:41, 67, 115`, which read "variation distance" and "the sum of absolute differences", with "the total variation distance of the literature" reserved for the halved quantity.

## The factor-two clauses, checked against the proofs

`symm_ds_TV_bound_cV` at `security/pgg_mixing.v:515-517` bounds the full sum `\sum_a `|(Q ^+ L *m e_cV s) a ord0 - uniform_cV a ord0|` by `Num.sqrt (#|'I_N|%:R) * alpha ^+ L`. Its proof chains `cV_l1_le_sqrtN_norm2` at `:474-475`, which is Cauchy-Schwarz against the constant one, then `symm_ds_power_norm2_bound` at `:443-445`, then `es_minus_U_norm2_le1` at `:501-502`. No factor one half occurs at any step. `symm_ds_TV_bound` at `:673-684` unfolds `var_dist` at line 696 and closes with that same lemma at line 713. So `sqrt(N) * alpha^L` bounds the un-halved sum, and the sheet's factor claim is right. T15's added clause speaks only about `sc_convergence`, the display four lines above it, and the in-tree proof, so it asserts nothing about the cited book. T16's does, which is W3.

## N1, Euclidean norm against sum-of-squares

N1 is correct and should stand. In `pgg_mixing.v` the object is `vec_norm2 v := Num.sqrt (cV_inner v v)` at `:432`, a square root of a sum of squares, so "Euclidean norm" is the type-honest name and "sum-of-squares" would not be. The same file already says "Euclidean norm" at `:31`, `:435` and `:441`, and after T3 the Section 2 banner reads exactly like the Contents entry at `:30-31`. In `pgg_schreier.v:94` the phrase "sum-of-squares to total variation conversion" labels Saloff-Coste's theorem, whose left side is a chi-square, a genuine sum of squares. The two phrases name two different objects, so carrying one across would have been the error. A loose scan of every tracked `.v` comment outside `notes/` and `legacy/` for the letter L followed by an optional caret or underscore and a digit returns exactly four hits, all in `pgg_mixing.v` at 118, 431, 434 and 500, which are T3, T6, T7 and T9. After the pass that vocabulary is gone from the tree, and N3's two reported false positives do not match a tight pattern at all.

## W7, the answer on U1

What is inconsistent, from the repository alone. Line 277 introduces the display as "The standard upper bound lemma", line 278 displays `d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L`, and line 282 says each instance axiomatizes that bound. The field those lines introduce, `sc_convergence` at `security/pgg_schreier.v:324-328`, requires `var_dist ... <= Num.sqrt (N%:R) * (1 - sc_lambda_gap) ^+ L`. The tree states `var_dist = 2 * d_TV` at `instances/kim2025/five_card_kim.v:55` and `security/pgg_security_solver.v:480`, so the field is equivalent to `d_TV <= sqrt(N) * (1 - lambda_gap)^L / 2`, which is strictly stronger than the display. The display as written therefore does not yield the field, while the text says it is the field.

Two candidate one-line fixes for line 278, both padded to 80 bytes so a new box line passes the checker. Which one is right depends on what Diaconis states, which the repository does not answer.

```
(*   2 * d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L           *)
```

```
(*   var_dist(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L           *)
```

The second reads the display in the tree's own quantity and makes the line match the field exactly. The first keeps the literature's symbol and states the same content. Either changes the mathematical claim of the display, so neither should be applied before the book check lands.

## Delimiter, quote and barred-word check

No replacement contains a double quote, a comment opener or a comment closer inside its body. No replacement matches `common.BARRED`, which covers the barred vocabulary and the letter L followed by a digit. No new line exceeds 80 bytes. The only rule breach is the box width at W1 and W2.

## Completeness and Part 3

My own case-insensitive scan of the comments of every tracked `.v` outside `notes/` and `legacy/`, run at paragraph granularity so that a phrase split across two box lines is still caught, gives 49 paragraphs holding `total variation`, `total-variation`, `TV`, `statistical distance`, `variational` or `d_TV`, plus 14 identifier mentions. Every one is either a sheet change, a Part 2 entry, or one of the five sites in W10 and the two in W11, all of which say the correct thing. No site that needs changing is missing from Part 1. Note that `reconstruct/algebraic_rigidity.v:119-126` is caught only at paragraph granularity, because the phrase breaks across lines 124 and 125, and the sheet already lists it.

Part 3 confirmed. Running `python3 scripts/comment_pass/closure.py` over the six files from the repository root prints `touched 6, closure 82` and `frozen files met: none`, exactly as the sheet reports.

## Paragraph boundaries, and what must be edited line by line

Measured with `scripts/comment_pass/common.py` `paragraphs`.

Paragraph wider than the change: T2, whose paragraph is 37 to 38, the index heading plus its entry line. T3, whose paragraph is 117 to 119, a banner that includes its two star lines. T10, 553 to 555. T14, 722 to 726. T16, 319 to 323, which also holds the two citation labels at 320 and 321 as separate lines that a re-lay would run together into prose. T17, 379 to 386, which holds the two-column table at 383 and 384 that a re-lay would destroy. T24, 7 to 13.

Paragraph equal to the change: T1, T4, T5, T6, T7, T8, T9, T11, T12, T13, T18, T19, T20, T21, T22, T23, T25.

T15 is not a paragraph edit at all. Lines 277 to 282 parse as five one-line paragraphs, and the addition makes four more.

Must be edited line by line rather than re-laid: every row except T1, T4 and T12. For the seven rows with a wider paragraph the reason is the index, the banner, the citation labels or the table. For the free-form rows the reason is width: `reflow.py` fills to 80 bytes, while these docstrings are hand-wrapped between about 60 and 78, so a re-lay would rewrite the lines the sheet marks unchanged. `README.md:163-166` says this in the tool's own words. For T13 and T15 the reason is that the surrounding box lines are 79 bytes today and a re-lay would pad untouched neighbours to 80. T1, T4 and T12 are single-line box paragraphs already at 80 bytes and are safe either way, and are simplest as line edits too.
