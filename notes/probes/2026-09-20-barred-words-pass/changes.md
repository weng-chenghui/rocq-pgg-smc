# Two barred words out of the production comments (2026-09-20)

Branch `feat/tableau-extensions-probe`, base HEAD `376b64b`. Comments only:
no code token changed in any file (checked, see "Verification").

## Legend for the quoted old lines

This report does not spell the two barred words. In every OLD block the
barred token is replaced by a placeholder and nothing else is altered:

- `[CW]` = the circuit word for a logical relation, in whatever inflection
  the old line had (`[CW]`, `[CW]s`, `[CW]d`, `[CW] 2` for the uppercase
  plan-task label in den Boer).
- `[NA]` = the two-character abbreviation for the sum of absolute
  differences, including its hyphenated forms (`full-[NA]`, `[NA]-to-[EA]`)
  and its caret spelling.
- `[EA]` = the matching two-character abbreviation for the Euclidean norm.

NEW blocks are verbatim: they contain no placeholder.

Line numbers are the HEAD numbers of the old text.

## Group A. The feasibility predicate: which word is true of it

`cs_gap_feasible` **is not an identifier anywhere in the tree**. A grep over
`reconstruct/` finds it only in these three comments. The two real objects
the name is built from are:

- `reconstruct/covering_scheme.v:146-151`. `cs_gap` is a **field of the
  `CoveringScheme` record**, and its type is the inequality
  `ts_T (rp_scheme cs_plug) <= ts_k (rp_scheme cs_plug) + 2 * cd_genus cs_data`.
  It is a proof obligation carried by the record, discharged at each
  instance (for example `instances/s5/rigidity_s5_instance.v:223`,
  `s5_cs_gap`), and consumed as a premise (`covering_scheme.v:173,194`:
  `have := cs_gap cs`).
- `reconstruct/invariant_profiler.v:74-75`. `feasible` is a
  **`Definition ... : Prop`**, `exists d, d \in window /\ secret_inv_dim d`.

Neither is a boolean test, and neither reduces: both live in `Prop`. The
word that is true of the pair is **condition**, and I used that single word
in all three files. Where the old text said "the [CW]'s required
dimensions" I wrote "the dimensions the condition requires", so that the
noun stays the dimensions and the condition is what imposes them.

### A1. `reconstruct/invariant_profiler.v:16`

OLD
```
(*   feasible window   : some dimension required by the [CW] (a member of      *)
```
NEW
```
(*   feasible window   : some dimension the condition requires (a member of   *)
```
Line 17 is untouched, so the sentence still reads "... (a member of window)
is achievable as a secret-encoding invariant."

Read: `Definition feasible (window : seq nat) : Prop := exists d, d \in
window /\ secret_inv_dim d` (`invariant_profiler.v:74`). The window is the
list the condition requires a dimension from, so "the dimensions the
condition requires" names the same set the old phrase named.

### A2. `reconstruct/invariant_profiler.v:19-23`

OLD
```
(* supplies the available secret-encoding dimensions; the cs_gap_feasible [CW] *)
(* rejects an instance when the two are disjoint. The Maschke lemma records     *)
(* the regime (coprime characteristic) in which the available dimensions are    *)
(* closed under complementation, i.e. the simple subset-sum reasoning is valid; *)
(* the s5_nogo.v instance is precisely the MODULAR regime where it fails.       *)
```
NEW
```
(* supplies the available secret-encoding dimensions; the cs_gap_feasible     *)
(* condition rejects an instance when the two are disjoint. The Maschke lemma *)
(* records the regime (coprime characteristic) in which the available         *)
(* dimensions are closed under complementation, i.e. the simple subset-sum    *)
(* reasoning is valid; the s5_nogo.v instance is precisely the MODULAR regime *)
(* where it fails.                                                            *)
```
The paragraph is one line longer because the replacement is four characters
longer and the box lines I touch are exactly 80 bytes (HEAD had them at
81-82). Line 18 is untouched. Every word other than the one replaced is
preserved in order.

### A3. `reconstruct/invariant_profiler.v:49`

OLD
```
    feasibility [CW] consumes. *)
```
NEW
```
    feasibility condition consumes. *)
```
Read: the docstring is on `inv_dim` (`:50`), whose refinement
`secret_inv_dim` (`:63`) is what `feasible` quantifies over, so the thing
that consumes the profile is the `Prop` named above.

### A4. `reconstruct/invariant_profiler.v:57`

OLD
```
    this at the [CW]'s required dimensions, proving the wired instance
```
NEW
```
    this at the dimensions the condition requires, proving the wired instance
```
Read: `reconstruct/s5_nogo.v:421`, `Theorem s5_gap_window_infeasible :
~ feasible rG_secret e0 [:: 3; 4]`, together with
`reconstruct/gap_dimension.v:35-38`, `gap_dim_window`, which produces
`[/\ 0 < g, 1 < k & k < n - 1]`, that is the required dimensions 3 and 4 at
n = 6. The refutation is at those dimensions, which is what the old
possessive said.

### A5. `reconstruct/invariant_profiler.v:68-73`

OLD
```
    which secret_inv_dim d holds. This is the [CW] side of early rejection:
    gap_dimension.v computes the window of dimensions a feasible covering
    scheme would need, and feasible window asserts at least one of them is
    realised by a secret-encoding invariant submodule. The no-go theorem
    proves ~ feasible rG e0 [:: 3; 4] for the S_5 instance, so the [CW]
    rejects it before any code is built. *)
```
NEW
```
    which secret_inv_dim d holds. This is the condition's side of early
    rejection: gap_dimension.v computes the window of dimensions a feasible
    covering scheme would need, and feasible window asserts at least one of
    them is realised by a secret-encoding invariant submodule. The no-go
    theorem proves ~ feasible rG e0 [:: 3; 4] for the S_5 instance, so the
    condition rejects it before any code is built. *)
```
Same six lines, re-flowed; no word other than the two replacements changed.

### A6. `reconstruct/gap_dimension.v:15-17`

OLD
```
(* arithmetic; the invariant-submodule profiler and the cs_gap_feasible [CW]   *)
(* intersect this band with the available invariant dimensions to reject       *)
(* mathematically impossible instances before any code is constructed.        *)
```
NEW
```
(* arithmetic; the invariant-submodule profiler and the cs_gap_feasible       *)
(* condition intersect this band with the available invariant dimensions to   *)
(* reject mathematically impossible instances before any code is constructed. *)
```
Same three lines, all exactly 80 bytes.

### A7. `reconstruct/s5_nogo.v:438`

OLD
```
   cs_gap_feasible [CW] is meant to reject before any code is built. *)
```
NEW
```
   cs_gap_feasible condition is meant to reject before any code is built. *)
```
One word; the comment keeps its three-space continuation indent and stays
under 80 bytes (76).

## Group B. The two parity-shift lemmas

I read both statements before choosing the direction words.

`sumn_shift_even_to_odd_gen` (`groups/pgg_raag_clique.v:692-695`):
the left side is `sumn [seq (if ~~ odd k then g k.-1 else 0) | k <- iota
m.+1 M]`, so its summand survives at **even** k; the right side is
`sumn [seq (if odd j then g j else 0) | j <- iota m M]`, surviving at
**odd** j. Even on the left, odd on the right.

`sumn_shift_odd_to_even_gen` (`:701-704`): `if odd k` on the left,
`if ~~ odd j` on the right. Odd on the left, even on the right.

### B1. `groups/pgg_raag_clique.v:689-691`

OLD
```
(** Shifting the index down by one turns an even-[CW]d sum into an odd-[CW]d
    one.  Parity alternates under k |-> k-1, which is how the second summand
    produced by Pascal's rule lands in the opposite half. *)
```
NEW
```
(** Shifting the index down by one turns a sum restricted to even indices
    into one restricted to odd indices.  Parity alternates under k |-> k-1,
    which is how the second summand produced by Pascal's rule lands in the
    opposite half. *)
```

### B2. `groups/pgg_raag_clique.v:700`

OLD
```
(** The same index shift in the other direction, odd-[CW]d to even-[CW]d. *)
```
NEW
```
(** The same index shift in the other direction, from odd indices to
    even ones. *)
```
Two lines because the one-line form would be 82 bytes.

## Group C. The plan-task label in den Boer

### C1. `instances/denboer1989/den_boer_profile.v:162-168`

OLD
```
(* encode_bool, as a PGG_sheet ([CW] 2 — the fc_dtype FCCommit cannot be      *)
(* reused, so the existing pgg_data alphabet carries the commit). The two      *)
(* input parties commit at process ids 7 and 8, above the dealer (0),         *)
(* verifier (1) and the five players (2..6). The dealing body is the          *)
(* unchanged exchange_dealer, so the player/verifier wire is identical to the *)
(* uncommitted den Boer dealer; only the dealer gains the two-receive         *)
(* prologue.                                                                   *)
```
NEW
```
(* encode_bool, as a PGG_sheet (the fc_dtype FCCommit cannot be reused, so    *)
(* the existing pgg_data alphabet carries the commit). The two input parties  *)
(* commit at process ids 7 and 8, above the dealer (0), verifier (1) and the  *)
(* five players (2..6). The dealing body is the unchanged exchange_dealer, so *)
(* the player/verifier wire is identical to the uncommitted den Boer dealer;  *)
(* only the dealer gains the two-receive prologue.                            *)
```
The label and its dash are gone, the reason is kept word for word, and the
paragraph is one line shorter. All six lines are exactly 80 bytes; lines
159-161 above and 169 onward are untouched and keep their HEAD widths.

Read: the commit is carried by `pgg_commit` at process ids 7 and 8
(`den_boer_profile.v:204,209`), which is what the parenthetical explains.

## Group D. The norm

In this repository `var_dist` is the sum of absolute differences, that is
twice the total variation distance of the literature. Every rewritten
sentence below states that fact in the place where the old one stated it,
so each rewrite carries the full phrase rather than a short back-reference:
none of these paragraphs mentions the convention twice.

### D1. `instances/kim2025/five_card_kim.v:54-56`

OLD
```
(*   variation). Infotheo uses var_dist = sum |P - Q| (full [NA] norm),       *)
(*   so var_dist = 2 * d_TV.  The table below normalises to Kim's d_TV      *)
(*   convention for an apples-to-apples comparison.                          *)
```
NEW
```
(*   variation). Infotheo uses var_dist = sum |P - Q| (the sum of absolute    *)
(*   differences, with no factor one half), so var_dist = 2 * d_TV.  The      *)
(*   table below normalises to Kim's d_TV convention for a                    *)
(*   like-for-like comparison.                                                *)
```
The equation `var_dist = 2 * d_TV` and the preceding sentence naming Kim's
`d_TV = (1/2) sum |P - Q|` (line 53, untouched) are unchanged, so the
doubling is still stated twice, once as a formula and once in words.

The idiom at line 56 was replaced as the brief permitted. It claimed only
that the table's two columns are brought to one convention before being
compared; "for a like-for-like comparison" claims exactly that and nothing
more. The table itself (lines 60-65) is untouched.

### D2. `instances/s5/s5_analysis.v:274-278`

OLD
```
(* L cuts, in the repository's full-[NA] convention. It quantifies over one     *)
(* position, mentions no coalition view and no second secret, and is          *)
(* rests on the in-kernel Rayleigh certificate s5_rayleigh_Q2_R. It is        *)
(* neither exact nor approximate privacy, and is recorded as an endpoint      *)
(* marginal bound in the analysis manifest.                                   *)
```
NEW
```
(* L cuts, in the repository's convention, the sum of absolute differences    *)
(* with no factor one half. It quantifies over one position, mentions no      *)
(* coalition view and no second secret, and is rests on the in-kernel         *)
(* Rayleigh certificate s5_rayleigh_Q2_R. It is neither exact nor approximate *)
(* privacy, and is recorded as an endpoint marginal bound in the analysis     *)
(* manifest.                                                                  *)
```
Read: the alias at `:286` is `@s5_word_endpoint_bound`, whose statement
(`instances/s5/s5_models.v:297-301`) is a `var_dist` between a position
pushforward of `sa_cut_dist` and `fdist_uniform (card_ord 5)`, bounded by
`Num.sqrt 5%:R * (s5_alpha_R R) ^+ L`. `var_dist` is the unhalved sum, so
the new clause is true of it.

**Point to decide (not mine to fix).** The words "and is rests on" are in
the HEAD text; the stray "is" is preserved verbatim, so the re-flowed lines
still read "and is rests on the in-kernel Rayleigh certificate". Deleting
that one word is outside the rule this pass applies, so I left it and flag
it here.

### D3. `instances/s5/s5_analysis.v:288`

OLD
```
    s5_rayleigh_Q2_R: the variation distance, in the full-[NA] convention,
```
NEW
```
    s5_rayleigh_Q2_R: the variation distance, in the repository's
    convention, the sum of absolute differences with no factor one half,
```
The appositive sits where the old one sat, between "the variation distance"
and "between sa_seat_dist ...", so the sentence structure is unchanged. The
word "repository's" is added so that this file says the same thing the same
way in both places (D2 already said "the repository's").

Read: `s5_exec_endpoint_bound` (`s5_models.v:391-396`) is
`var_dist (sa_seat_dist ...) (s5_ideal_reading secretP) <= Num.sqrt 5%:R *
(s5_alpha_R R) ^+ L`.

### D4. `instances/s5/s5_models.v:293-296`

OLD
```
    repository's full-[NA] convention. This is the S_5 spectral mixing
    bound (s5_spectral_convergence_proved) transported to the sample
    layer; it rests on the in-kernel Rayleigh certificate s5_rayleigh_Q2_R
    and bounds one seat's endpoint marginal only, not a coalition view. *)
```
NEW
```
    repository's convention, the sum of absolute differences with no factor
    one half. This is the S_5 spectral mixing bound
    (s5_spectral_convergence_proved) transported to the sample layer; it
    rests on the in-kernel Rayleigh certificate s5_rayleigh_Q2_R and bounds
    one seat's endpoint marginal only, not a coalition view. *)
```
Read: `Lemma s5_word_endpoint_bound` immediately below, a `var_dist`
against `fdist_uniform (card_ord 5)`.

### D5. `instances/s5/s5_models.v:309-315`

OLD
```
    repository's full-[NA] convention, between the finite-word adapter's
    cut distribution on the group carrier {perm 'I_5} and a reference
    distribution on that same carrier. The landed spectral theorem
    (s5_spectral_convergence_proved) bounds a position pushforward on
    'I_5, a different carrier, so it does not discharge this premise:
    s5_word_transfer_conditional below stays conditional on a hypothesis
    this file supplies no proof of. *)
```
NEW
```
    repository's convention, the sum of absolute differences with no factor
    one half, between the finite-word adapter's cut distribution on the
    group carrier {perm 'I_5} and a reference distribution on that same
    carrier. The landed spectral theorem (s5_spectral_convergence_proved)
    bounds a position pushforward on 'I_5, a different carrier, so it does
    not discharge this premise: s5_word_transfer_conditional below stays
    conditional on a hypothesis this file supplies no proof of. *)
```
Read: `Definition s5_word_base_premise (Q : R.-fdist {perm 'I_5}) (delta :
R) : Prop := (var_dist (@sa_cut_dist R mpS s5_exec_plug s5_word_sample) Q
<= delta)%R`, a `var_dist` on the group carrier, so the convention clause
applies to the same quantity as before.

### D6. `instances/s5/s5_models.v:322-325`

OLD
```
    each other, in the repository's full-[NA] convention. The premise is a
    hypothesis, not a fact this file proves (see s5_word_base_premise):
    this lemma is the generic transfer machinery kept ready for whichever
    future proof discharges that premise. *)
```
NEW
```
    each other, in the repository's convention, the sum of absolute
    differences with no factor one half. The premise is a hypothesis, not a
    fact this file proves (see s5_word_base_premise): this lemma is the
    generic transfer machinery kept ready for whichever future proof
    discharges that premise. *)
```
Read: `s5_word_transfer_conditional`'s conclusion is
`var_dist (fdistmap fx ...) (fdistmap fy ...) <= delta + delta`, the same
unhalved quantity as the premise it consumes.

### D7. `instances/s5/s5_models.v:383-388`

OLD
```
    under the repository's full-[NA] convention. This is
    s5_spectral_convergence_proved transported through the executed
    interpreter, so it rests on the in-kernel Rayleigh certificate
    s5_rayleigh_Q2_R. It bounds one seat's endpoint marginal only: the
    ideal reading is neither uniform nor secret-independent, and no
    coalition, privacy, secrecy, or leakage conclusion follows from it. *)
```
NEW
```
    under the repository's convention, the sum of absolute differences with
    no factor one half. This is s5_spectral_convergence_proved transported
    through the executed interpreter, so it rests on the in-kernel Rayleigh
    certificate s5_rayleigh_Q2_R. It bounds one seat's endpoint marginal
    only: the ideal reading is neither uniform nor secret-independent, and
    no coalition, privacy, secrecy, or leakage conclusion follows from it. *)
```
Read: `Lemma s5_exec_endpoint_bound` below it, `var_dist (sa_seat_dist ...)
(s5_ideal_reading secretP) <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ L`.

### D8. `security/pgg_mixing.v:30`

OLD
```
(* Bridge from variation distance ([NA]) to [EA] norm:                            *)
```
NEW
```
(* Bridge from variation distance (the sum of absolute differences) to the    *)
(* Euclidean norm:                                                            *)
```
Read: the heading names `var_dist_le_sqrtN_norm2` on the next line, whose
statement (`:124-127`) is
`var_dist P Q <= Num.sqrt #|A|%:R * Num.sqrt (\sum_(a : A) (P a - Q a) ^+ 2)`.
The left side is the sum of absolute differences, the right the Euclidean
norm of the difference vector, so both halves of the heading are true of it.

### D9. `security/pgg_mixing.v:440-441`

OLD
```
    sum_i v_i = 0, the [EA]-norm form the [NA]-to-[EA] bridge composes with to
    reach the total-variation bound. *)
```
NEW
```
    sum_i v_i = 0, the Euclidean-norm form the bridge from the sum of
    absolute values composes with to reach the total-variation bound. *)
```
Read: `cV_l1_le_sqrtN_norm2` (`:472-473`) is
`\sum_a `|w a ord0| <= Num.sqrt (#|'I_N|%:R) * vec_norm2 w`. Its left side
is a column vector's sum of absolute **values**, not of differences, which
is why this and D10, D11 and D13 say "values" while D1, D2 and D12 say
"differences".

### D10. `security/pgg_mixing.v:471` (beyond the listed sites)

OLD
```
(* [NA] to [EA] bridge for column vectors. *)
```
NEW
```
(* Bridge from the sum of absolute values to the Euclidean norm, for
   column vectors. *)
```
This is the caret spelling of the same abbreviation, sitting directly on the
lemma whose description D9, D11 and D13 rewrite. Leaving it would have left
the file naming one lemma two ways. It is the only site I changed that the
brief did not list, and reverting it is a single edit.

### D11. `security/pgg_mixing.v:509-512`

OLD
```
(* The mixing bound in raw column-vector form: the [NA] distance between the
   Q^L-iterated point mass at s and the uniform column is at most
   sqrt(N) * alpha^L. The fdist-level statement (symm_ds_TV_bound, Section
   7) is this same bound read through fdistmap and var_dist. *)
```
NEW
```
(* The mixing bound in raw column-vector form: the sum of absolute differences
   between the Q^L-iterated point mass at s and the uniform column is at most
   sqrt(N) * alpha^L. The fdist-level statement (symm_ds_TV_bound, Section 7)
   is this same bound read through fdistmap and var_dist. *)
```
Read: `symm_ds_TV_bound_cV` (`:513-515`) states
`\sum_a `|(Q ^+ L *m e_cV s) a ord0 - uniform_cV a ord0| <= Num.sqrt
(#|'I_N|%:R) * alpha ^+ L`, a sum of absolute **differences** of two
columns, so "differences" is the true word here.

### D12. `security/pgg_mixing.v:517-518`

OLD
```
(* Chains the [NA]-to-[EA] bridge (cV_l1_le_sqrtN_norm2), the sqrt'd spectral
   power bound (symm_ds_power_norm2_bound), and ||e_s - U||_2 <= 1
```
NEW
```
(* Chains the bridge from the sum of absolute values to the Euclidean
   norm (cV_l1_le_sqrtN_norm2), the sqrt'd spectral power bound
   (symm_ds_power_norm2_bound), and ||e_s - U||_2 <= 1
```
The two lines that follow are untouched. This one sits inside a proof body,
so it keeps its strategy content.

### D13. `security/pgg_mixing.v:667-669`

OLD
```
    sqrt(N) prefactor coming from the [NA]-to-[EA] bridge rather than the
    sqrt(|G|) blowup a group-level DPI bound would incur
    (pgg_collusion_bound.v Section 2). *)
```
NEW
```
    sqrt(N) prefactor coming from the bridge from the sum of absolute
    values to the Euclidean norm rather than the sqrt(|G|) blowup a
    group-level DPI bound would incur (pgg_collusion_bound.v Section 2). *)
```
Read: `symm_ds_TV_bound` (`:670-681`) concludes on
`var_dist (fdistmap ... (rho_from_words L sigmas)) (fdist_uniform (card_ord
N))`, and its `Num.sqrt #|'I_N|%:R` factor enters through
`symm_ds_TV_bound_cV`, which applies `cV_l1_le_sqrtN_norm2`. The citation
and the comparison with the group-level bound are unchanged.

## Verification

1. **Code unchanged.** For each of the nine files, HEAD and the working
   tree were parsed with a nested-comment stripper and the remaining
   non-comment tokens compared: identical, all nine
   (164/127/1683/4949/635/1930/680/1178/4605 tokens, unchanged on both
   sides).
2. **Widths.** No added line exceeds 80 bytes (measured on the encoded
   bytes, so the em-dash that is gone from den Boer counted as three).
   Every added boxed line is exactly 80 bytes with a space before the
   closing delimiter. Untouched ragged lines were left ragged.
3. **No barred vocabulary in the new text.** The added lines were scanned
   for both words, for `apex`, for `posit` and its inflections, for any
   abbreviation of indistinguishability, and for a capital L adjacent to a
   digit with or without a caret: no hit.
4. **Finishing scan.** 127 tracked `.v` files, excluding `notes/`,
   `legacy/` and the 36-file frozen closure of
   `instances/psl211/psl211_endpoints.v` (computed from the `Require`
   graph, which confirms none of the nine edited files is in it). Comment
   text only, nested comments handled. The circuit word: **zero hits**.
   The norm abbreviation: **10 hits, all in the two schreier files**
   (`security/pgg_schreier.v:59,60,376,394` and
   `security/pgg_schreier_weighted.v:202`, each line matching twice), where
   the two tokens are word lengths and mirror the code variables. This is
   the expected residue.
   The scan treats a match preceded by an underscore as part of an
   identifier and does not report it: that suppresses
   `instances/s5/pgg_raag_s5.v:59` and
   `instances/s5/rigidity_s5_instance.v:31`, which cite the lemma name
   `s5_nt_[NA]` (word length one). Those are code tokens and were not
   touched.

## Things the owner may want to decide

1. **`reconstruct/algebraic_rigidity.v:155`** holds one more occurrence, in
   the field comment of `sw_bound_eps` inside `ShuffleMarginalBound`
   ("the stated full-[NA] upper bound on one endpoint marginal"), and
   `:125` holds the caret spelling ("un-halved [NA] var_dist convention;
   1/2 in standard TV"). That file is in the frozen closure of
   `psl211_endpoints.v`, so it was not edited and the finishing scan
   excludes it. Suggested text for `:155`, when the closure is next
   unfrozen: "sw_bound_eps is the stated upper bound on one endpoint
   marginal, in the sum of absolute differences with no factor one half."
2. **The stray "is"** in `instances/s5/s5_analysis.v` (D2), preserved
   verbatim. Resolved by ruling F2 below.
3. **`security/pgg_mixing.v:430` and `:498`** still read "The [EA] norm of
   a column vector" and "The [EA] norm of e_s - U is at most 1", in the
   caret spelling. These name the Euclidean norm, not the barred
   abbreviation for the sum of absolute differences, and they are outside
   the listed sites, so I left them. If the owner wants the caret spelling
   gone from the file as well, both are one-word edits.
4. **`groups/pgg_raag_clique.v` says "half"** for this concept elsewhere
   ("even-index half", "the odd half", at `:592,597,602,724,739,794,805,
   816`). The two rewritten comments use "restricted to even indices" as
   instructed, and B1 still ends with the file's own word ("the opposite
   half"), so the two vocabularies now sit side by side in one file. If
   one word is wanted, "the even-index half" and "the odd-index half"
   would match the rest of the file.
5. **The gloss is repeated** at each of the six norm sites in the s5 pair
   of files, because each sentence that stated the doubling must keep
   stating it. If the owner prefers it once per file, five of the six can
   fall back to "in the repository's convention".

# Follow-up (same day, rulings from the coordinating session)

Four further comment edits, same rules: comments only, nothing compiled, no
git write. No barred token appears in the old lines quoted in this section,
so no placeholder is needed here.

## F1. A comment must not name an object that does not exist

The finding that `cs_gap_feasible` names no identifier was accepted. At the
three sites the real object is now named: the predicate `feasible` of
`reconstruct/invariant_profiler.v`. The name `cs_gap_feasible` no longer
occurs anywhere in the tree, in code or in comments. The other sites in
`invariant_profiler.v` that say "the condition" and "the feasibility
condition" are unchanged.

### F1a. `reconstruct/invariant_profiler.v:19-24`

OLD (as this pass first left it)
```
(* supplies the available secret-encoding dimensions; the cs_gap_feasible     *)
(* condition rejects an instance when the two are disjoint. The Maschke lemma *)
(* records the regime (coprime characteristic) in which the available         *)
(* dimensions are closed under complementation, i.e. the simple subset-sum    *)
(* reasoning is valid; the s5_nogo.v instance is precisely the MODULAR regime *)
(* where it fails.                                                            *)
```
NEW
```
(* supplies the available secret-encoding dimensions; the condition feasible  *)
(* rejects an instance when the two are disjoint. The Maschke lemma records   *)
(* the regime (coprime characteristic) in which the available dimensions are  *)
(* closed under complementation, i.e. the simple subset-sum reasoning is      *)
(* valid; the s5_nogo.v instance is precisely the MODULAR regime where it     *)
(* fails.                                                                     *)
```
Six lines, re-flowed, each exactly 80 bytes. Nothing but the subject
changed. The two things whose disjointness rejects the instance are still
the required dimensions (line 18, untouched) and the available
secret-encoding dimensions named in the same clause.

### F1b. `reconstruct/gap_dimension.v:15-17`

OLD (as this pass first left it)
```
(* arithmetic; the invariant-submodule profiler and the cs_gap_feasible       *)
(* condition intersect this band with the available invariant dimensions to   *)
(* reject mathematically impossible instances before any code is constructed. *)
```
NEW
```
(* arithmetic; the invariant-submodule profiler's condition feasible          *)
(* intersects this band with the available invariant dimensions to reject     *)
(* mathematically impossible instances before any code is constructed.        *)
```
The old sentence had two subjects, the profiler and the name that does not
exist; the new one has the single subject that does exist, so the verb is
singular.

Checked against the definition, as asked. `reconstruct/invariant_profiler.v:74-75`:
`Definition feasible (window : seq nat) : Prop := exists d, d \in window /\
secret_inv_dim d`. `feasible window` holds exactly when the window shares a
member with the dimensions that carry a secret-encoding invariant submodule
(`secret_inv_dim`, `:63-65`), and the window is the band this file computes
(`gap_dim_window`, `:35-38`, `[/\ 0 < g, 1 < k & k < n - 1]`). So
"intersects this band with the available invariant dimensions" is true of
it: the predicate asserts that the intersection is inhabited, and its
negation, which `reconstruct/s5_nogo.v:421` proves for the S_5 instance, is
that the intersection is empty. One shorthand is carried over unchanged
from the old sentence: the set the band is met with is the
**secret-encoding** invariant dimensions `secret_inv_dim`, a refinement of
`inv_dim`, and both the old and the new text write "available invariant
dimensions" for it.

### F1c. `reconstruct/s5_nogo.v:438`

OLD (as this pass first left it)
```
   cs_gap_feasible condition is meant to reject before any code is built. *)
```
NEW
```
   condition feasible is meant to reject before any code is built. *)
```
Line 437, untouched, still ends "the dead end the", so the sentence reads
"the dead end the condition feasible is meant to reject before any code is
built." 69 bytes, three-space continuation indent kept.

## F2. `instances/s5/s5_analysis.v:276-279`

OLD (as this pass first left it)
```
(* coalition view and no second secret, and is rests on the in-kernel         *)
(* Rayleigh certificate s5_rayleigh_Q2_R. It is neither exact nor approximate *)
(* privacy, and is recorded as an endpoint marginal bound in the analysis     *)
(* manifest.                                                                  *)
```
NEW
```
(* coalition view and no second secret, and rests on the in-kernel Rayleigh   *)
(* certificate s5_rayleigh_Q2_R. It is neither exact nor approximate privacy, *)
(* and is recorded as an endpoint marginal bound in the analysis manifest.    *)
```
The stray word is gone and the paragraph re-flows from four lines to three,
each exactly 80 bytes. Lines 274-275 above are untouched. No claim changed:
the bound still rests on `s5_rayleigh_Q2_R`, still quantifies over one
position, still claims neither exact nor approximate privacy.

## F3. Nothing else changed

B1 and B2 keep "restricted to even indices" and "from odd indices to even
ones"; the six norm glosses stay as written; the caret spelling of the
Euclidean norm at `security/pgg_mixing.v:430` and `:498` stays;
`reconstruct/algebraic_rigidity.v` is frozen and its two occurrences go to
the owner's list.

## Re-verification after the follow-up

1. **Code unchanged.** All nine files re-parsed against HEAD with the
   nested-comment stripper: token streams identical
   (164 / 127 / 1683 / 4949 / 635 / 1930 / 680 / 1178 / 4605).
2. **Widths.** No added line over 80 bytes; the boxed lines added here are
   exactly 80 with a space before the closing delimiter.
3. **No barred vocabulary** in any added line, and no capital L adjacent to
   a digit with or without a caret.
4. **Finishing scan**, same scope as before (127 files; `notes/`,
   `legacy/` and the 36-file frozen closure excluded; comments only):
   circuit word **zero hits**; norm abbreviation **10 hits, all in
   `security/pgg_schreier.v:59,60,376,394` and
   `security/pgg_schreier_weighted.v:202`**, the word-length usages.
   Unchanged from the first run.
5. **`cs_gap_feasible`** now returns nothing from a tree-wide grep over
   `reconstruct/`, `instances/`, `security/`, `groups/`, `protocol/`,
   `smc/` and `lib/`.
