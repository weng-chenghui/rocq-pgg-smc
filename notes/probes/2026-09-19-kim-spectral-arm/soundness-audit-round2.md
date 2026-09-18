# Soundness audit, round 2: the fix pass on the Kim spectral arm probe

Independent adversarial audit of the delta between
`history/*.2026-09-19-before-fix` and the current five `.v` files and
`STATUS.md`, of `rename_map.tsv`, and of the claims `STATUS.md` now makes.
2026-09-19. Round 1 is `soundness-audit.md`; its mathematics is not re-audited.

**VERDICT: NO-GO** for folding the spec and reporting the result as it stands.
The mathematics is sound and round 1's blocking finding F1 is fully and
correctly remedied: both biased spectral programs are now published at
`IdealFinite`, and I confirmed in the kernel that the published row differs
from the manifest's `five_card_row_biased` in `apr_transfer` and in no other
field. What is not sound is the landing plan. S8's change list and S10's
homes-and-costs section contain four checkable statements that are false, and
a landing executed from them does not compile: three `erefl` status pins
inside `manifest/pgg_analysis_manifest.v` become errors and are not listed,
and the new `lib/` file S10 proposes is not built, because `_CoqProject`
enumerates every `.v` file and S10 says no `_CoqProject` edit is needed. The
remedy is again narrow: extend one table, rewrite three sentences, and correct
one number. No proof changes and no re-proving.

I recompiled the five probe files from source in my own directory
(`scratchpad/b3_audit2/build`, rc=0 for each, wall 4.5 / 4.2 / 6.1 / 4.2 /
11.0 s, matching `STATUS.md`'s compile table) and compiled three audit files
of my own, `audit2.v`, `audit3.v` and `audit4.v`, all rc=0. Eighteen
`Print Assumptions` blocks across the five files report the three boolp axioms
or `Closed under the global context` and nothing else, which reproduces the
counts `STATUS.md` states. No repository file was edited; this file is the
only one written.

## Findings

| ID | Severity | Claim audited | Evidence | Recommended change |
|---|---|---|---|---|
| G1 | BLOCKING | `STATUS.md`'s fix table for N6/F3: the S8 change list "now carries both manifest rows, the compile breakage at `five_card_rows.v:456`, and **every** header and docstring passage a landing makes false". The S8 table's "fields to change" column names, for the two manifest rows, only `apr_transfer`, `apr_completion` and the two docstrings. | Three further declarations inside `manifest/pgg_analysis_manifest.v` become compile errors at the landing values, and the manifest's own header announces them: ":67-72, restatusing a row makes its pin fail". They are `Check (erefl : apr_transfer five_card_row_biased = StaticExecutedOnly)` (`:1779-1780`), `Check (erefl : apr_completion five_card_row_repeated = Sampled)` (`:1787`) and `Check (erefl : apr_transfer five_card_row_repeated = NoModelComparison)` (`:1788-1789`). My `audit4.v` wraps each pin at the landing value in `Fail` and every one of the three `Fail`s succeeds, so each is an error and not a warning; the unwrapped pin at today's value compiles, so a failing `Check` is a hard error in this file. Separately, the manifest's header tables for Row 4 (`:301-310`, `:322-328`) and Row 5 (`:355-364`, `:374-380`) record "model transfer \| none claimed", "missing premise \| the ideal distribution equality", "bound or certificate \| none", "final bridge theorem \| NONE", "transfer status", "completion level", and the level-justification sentence "The row is NOT AnalysisBridged". All of these become false and none is in the list. | Extend the S8 manifest table with a third column naming the three `erefl` pins as compile breakages, and add the Row 4 and Row 5 header-table lines to the prose list. Withdraw the word "every" from the fix table's N6/F3 row, or make it true. |
| G2 | BLOCKING | S10: "both directories are covered by a `-R` line in `_CoqProject`, so no `_CoqProject` edit is needed either way." | False. `_CoqProject` has the `-R` lines and then enumerates 194 `.v` files by name; all 133 production files are listed and none is missing. `Makefile` regenerates `Makefile.rocq` from `_CoqProject` by `rocq makefile -f _CoqProject`, so a new `lib/var_dist_supp.v` that is not listed is never built. The `-R` line supplies the logical path, not the build target. | Replace the sentence: a landing adds one line to `_CoqProject` for the new file, which regenerates `Makefile.rocq`; out-of-date targets alone rebuild, so the regeneration costs nothing further. |
| G3 | SHOULD-FIX | S10's dependency table row `manifest/pgg_analysis_manifest.v` \| 5, and the sentence "a landing recompiles three files plus those five". | The reverse closure of `manifest/pgg_analysis_manifest.vo` computed from `.Makefile.rocq.d` is **7**, not 5: `pgg_tableau`, `pgg_tableau_syntax`, `pgg_analysis_client`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`. `manifest/pgg_tableau.v:92` requires `pgg_analysis_manifest` directly, and so does `pgg_tableau_syntax.v:110`. My script reproduces all eleven other rows of the S10 table exactly (105, 107, 102, 41, 39, 24, 20, 20, 10, 9, 0), so the method agrees and this row alone is wrong. The true cost is 9 compiles, not 8: the new `lib/` file, the manifest, and the manifest's seven dependants, of which `five_card_rows.v` is one. `instances/psl211/psl211_endpoints.vo` is in none of these closures, so the freeze rule is respected. | Correct the table row to 7 and restate the cost as nine files, naming `pgl27_rows.v`, `s5_rows.v` and `psl211_rows.v`, which the current sentence does not lead a reader to expect. |
| G4 | SHOULD-FIX | S10 sends `kim_centi_cut_mixing`, `kim_biased_cut_mixing` and `five_card_static_obs_const` to `instances/kim2025/five_card_rows.v`. | That home makes the manifest's own convention for an `IdealFinite` row unmeetable. `five_card_rows.v` requires `pgg_analysis_manifest`, which requires `five_card_analysis.v`, so a theorem in `five_card_rows.v` is strictly above the manifest and above the facade. The precedent the probe cites works the other way: `pgl27_word_mixing` lives in `instances/pgl27/pgl27_mixing.v`, below the facade; `pgl27_analysis.v:267` aliases it as `word_mixing`; the manifest's Row 2 table names `PGL27Analysis.word_mixing` at `:173` and `:182` and pins it by spelled type at `:1048`. A five-card row at `IdealFinite` whose justification names no checked alias breaks the convention the manifest header states at `:67-72`. Putting the mixing and invariance theorems below `five_card_analysis.v` instead costs 11 compiles rather than 9, since `five_card_analysis.vo` has 8 reverse dependants, and still excludes `psl211_endpoints`. | Say which of the two the landing chooses, and price it. Either name the conflict and leave the manifest's five-card tables without an alias, or move the two theorems below `five_card_analysis.v` and carry the extra two compiles. |
| G5 | NOTE | `STATUS.md:288`: the repeated row's form-1 bound `2 * sqrt 5 * (1/80)^7` is "about `1.6e-13`". | It is `2.1325e-13`. The figure is also inconsistent with the probe's own comparison: `2^-39 = 1.819e-12` is 8.53 times that value, which is the "about eight and a half times weaker" round 1 records, and would be 11.4 times `1.6e-13`. The error predates the fix pass; `history/STATUS.2026-09-19-before-fix.md:271` carries it too. | Write `2.13e-13`. |
| G6 | NOTE | `kim_spectral_rows_probe.v:286-287`, the comment on the recorded `Fail five_card_row_repeated39_bare`: "the reprice obligation is one identity per real field and per index, and `five_card_pow2_39_split` alone is an identity at one field". | The first clause is right and the second is not. `About` gives `five_card_pow2_39_split : forall R : realType, ((2 : R) ^- 40 + 2 ^- 40)%R = (2 ^- 39)%R`, an identity at every field. The rejection message names the real reason: the payload type is `forall idx : amf_index ... R, match ab_port ... with ... end` and the supplied term is the `match` branch without the `idx` abstraction. | Restate as "is an identity at every real field but not one per index". `STATUS.md`'s own sentence, which says the `Fail` is the version "without the `fun R _ =>`", is already correct. |
| G7 | NOTE | F8 of round 1, the undefended `sw_L` field, and F7, the single mutation on the support hypothesis, are recorded as "Notes, no change asked" and are unchanged. | Confirmed unchanged and still correct as observations. | No change. |

Nothing I found is a kernel-level unsoundness, and nothing in the delta
weakens a statement. No `Admitted`, `Axiom`, `admit`, `Abort`, `Parameter`,
`Hypothesis` or `Conjecture` occurs in any of the five files.

## Q1 F1: are all biased programs published at IdealFinite, and do the Fails fail for the right reason

Yes on both, and the second half is proved rather than inferred.

Every `publish` in the file now carries `IdealFinite`: the two `|>` programs at
`:102` and `:112`, the two `;;;` programs at `:284` and `:360`, and the
recorded `Fail` at `:294`. `StaticExecutedOnly` survives only in three prose
comments describing what the manifest records. The pre-fix file's third biased
program `kim_row_biased_spectral_static`, which published at
`StaticExecutedOnly`, and its `rowE` are gone, as `rename_map.tsv` records
with `-`.

The two publishing syntaxes put the transfer status in different argument
positions, `|> publish IdealFinite BaselineClassicalOnly` against
`;;; publish BaselineClassicalOnly of IdealFinite`, and both reach
`apr_transfer`. I checked this rather than reading it off the notation:
`A1b_inv25_only_transfer` closes by `erefl` for the `;;;` program.

The recorded `Fail`s fail on the status and on nothing else. `publish` builds
`MkAnalysisPathRow (ab_obs q) AnalysisBridged (ab_f q) t a`
(`manifest/pgg_tableau.v:691-695`), so a row equation compares five fields and
the rejection message names only the two sides. I closed the gap by kernel
equations instead:

    A1_biased_only_transfer :
      published_row five_card_row_biased_ideal_tableau
      = @MkAnalysisPathRow (apr_observed five_card_row_biased)
          (apr_completion five_card_row_biased)
          (apr_model five_card_row_biased)
          IdealFinite
          (apr_assumptions five_card_row_biased)
      := erefl.

It closes, and so does the same equation for `five_card_row_biased_inv25`. So
the one-cut programs' published rows are the manifest's biased row with
`apr_transfer` replaced and nothing else replaced, and both recorded `Fail`s
fail exactly on the transfer status. `A2_repeated_two_fields` does the same for
the repeated row at `AnalysisBridged` and `IdealFinite`, so its `Fail` fails on
exactly the two fields its comment names. The model slot survives the level
change because `AnalysisModelSlot observed Sampled` and
`... AnalysisBridged` are one type (`A3_slot_type_same`, `erefl`), which is
also why `five_card_row_repeated_modelE` keeps its statement after a landing.

`five_card_row_biased_ideal_publishedE` therefore states the published fields
truthfully, and its comment, "the transfer status is the one field a landing
changes", is exactly `A1_biased_only_transfer`.
`five_card_row_repeated_spectral_publishedE` and its comment are likewise
exact.

`five_card_row_biased_forms_publishedE` says only what it proves. Its
statement is an equality of two `AnalysisPathRow` values; its comment states
that the record holds descriptive metadata and no `Prop`, which I confirmed
against `manifest/pgg_analysis_manifest.v:707-725`, five fields and none in
`Prop`, and concludes that such an equation "cannot say which transfer status
is the honest one". It makes no security claim and does not present the
equation as evidence about a certificate. The one loose phrase is "their
certificates carry different numbers, `sqrt 5` over forty against one
twenty-fifth": `kim_biased_cert_exact` carries `1/50 + 1/50` and `1/25` is the
repriced name for it, though the two are equal as reals.

## Q2 S8, the landing change list

The half about `instances/kim2025/five_card_rows.v` is accurate and complete.
I checked every cited line. Item 1, the ascription at `:456-458`, is a genuine
compile breakage: `five_card_row_repeated_tableau : Tableau Sampled` and my
`Fail Definition A6_repeated_at_bridged : Tableau AnalysisBridged := ...`
succeeds as a `Fail`. Items 2, 3 and 4 quote the header at `:29-33`, `:39-42`
and `:42-50` correctly; one refinement, the sentence at `:30-33`, "The
repeated row stops there because the manifest does", becomes false rather than
merely obsolete, since the manifest would no longer stop there. Items 5 and 6
quote the two docstrings correctly and both become false. Items 7 and 8 are
right that `five_card_row_biased_levelE` and the recorded
`Fail five_card_row_biased_at_manifest_level` both survive: only the biased
row's transfer status moves and its completion level is already
`AnalysisBridged`. The closing list of theorems that stay true is right;
`five_card_row_repeated_endpoint_lt` and `five_card_row_biased_leak_bound`
both typecheck unchanged beside the certified programs (`audit2.v`, A7), and
neither mentions a manifest row. The endpoint lemma stays the readable form of
what `kim_centi_marginal_bound40` consumes, and the leakage bound stays the
only statement about the full reveal, so both keep their place.

The half about `manifest/pgg_analysis_manifest.v` is incomplete; that is G1.
`manifest/pgg_analysis_client.v` is safe: its only mentions are
`Check five_card_row_biased.` and `Check five_card_row_repeated.` at `:149-150`,
which survive any restatusing. No file anywhere counts or pattern-matches
manifest rows by level or status; the manifest holds no sequence of rows, and
a whole-tree grep for the two row names outside the manifest returns only
`five_card_rows.v` and those two `Check` lines. No lemma anywhere states
`apr_completion` or `apr_transfer` of either row except
`five_card_row_biased_levelE`, which is about completion and stays true.

The recompile cost is wrong; that is G3, with G2 and G4 beside it.

## Q3 var_dist_le2

Correct, and I checked that it is tight rather than merely true.
`var_dist P Q = \sum_a |P a - Q a|`, both laws sum to one, so
`2%:R = \sum_a (P a + Q a)` and `ler_normB` gives the summand bound; six
lines, `Qed`, boolp axioms only. My `B6_var_dist_two` proves
`var_dist (fdist1 true) (fdist1 false) = 2%:R`, so 2 is attained and the
ceiling cannot be lowered.

Every "below the ceiling" sentence now rests on the lemma and says nothing
stronger. The three in the probe comments (`kim_spectral_rows_probe.v:159-162`
and `:378-379`) and the four in `STATUS.md` (`:272`, `:288`, `:350`, `:390`)
all name `var_dist_le2`, and each of the percentages is right: `sqrt 5 / 40`
is 2.795 per cent of 2, "about three percent"; `1/25` is exactly 2 per cent.
The one number that is wrong is the absolute value at `:288`, which is G5, not
the comparison it is used in.

## Q4 The two split identities

Both are correct and both sit where an equality is required, which I checked
by supplying each as the obligation itself:

    A4_reprice39_obligation (R : realType) (idx : unit)
      : cert_eps (kim_centi_cert40 R idx)
      = odflt (cert_eps (kim_centi_cert40 R idx)) (five_card_reprice39 R)
      := five_card_pow2_39_split R.

and the same for `five_card_inv50_split` against `five_card_reprice_inv25`.
Both close. `RepricePayload` (`pgg_tableau.v:610-615`) is an equality
`cert_eps cert = odflt (cert_eps cert) (c R)` and not an inequality, so a
reprice cannot weaken a bound, and `port_reprice` (`:622-631`) rewrites with
it rather than transiting through it. The obligation is genuinely checked: my
`A5_wrong_constant`, the same program at `2%:R ^- 38`, is rejected, and in the
repl `five_card_inv50_split R` offered against the `2^-39` obligation is
rejected with the two sides printed.

`five_card_row_repeated39_bare` still fails, and for the reason `STATUS.md`
gives. The message is a type mismatch between
`forall R : realType, (2 ^- 40 + 2 ^- 40)%R = (2 ^- 39)%R` and
`forall idx : amf_index ... R, match ab_port ... with ... end`, that is, the
missing per-index abstraction. The in-file comment misnames it; that is G6.

## Q5 The deletion of five_card_ideal_distE

Harmless. Both call sites in `five_card_rotation_probe.v` (`:113-115` and
`:127-129`) open with

    have Hid : sa_cut_dist (five_card_sample R)
        = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)).
      exact: five_card_sample_cut_distE.

`five_card_sample_cut_distE` (`instances/kim2025/five_card_exec.v:756-759`) is
that equation at the folded left side `five_card_sample_cut_dist`, and `exact:`
closes the `have` by conversion. So the deleted name was an alias and nothing
else; no hypothesis is added, no statement is weakened, both lemmas still end
in `Qed`, and their `Print Assumptions` blocks are unchanged. The `have` is
local, so the probe no longer introduces a second public name for a library
equation, which is what N2 asked for.

## Q6 Disposition of round 1's F2 to F9

- **F2, SHOULD-FIX, fixed.** `five_card_row_biased_forms_publishedE` is added
  and S8 carries a subsection saying a row equation compares descriptive
  metadata and cannot decide a transfer status. Verified above.
- **F3, SHOULD-FIX, partly fixed.** The `five_card_rows.v` half is complete
  and accurate. The manifest half is not, and the fix table claims it is.
  That is G1.
- **F4, SHOULD-FIX, fixed.** `var_dist_le2` is proved and every ceiling
  sentence cites it. Verified above.
- **F5, NOTE, fixed.** The comment on `kim_biased_exact_le_eps`
  (`kim_sc_close_probe.v:124-127`) now names one fiftieth against `sqrt 5`
  over eighty and points at no file header.
- **F6, NOTE, fixed.** `fc_sigma_pow5_eq1`'s comment
  (`five_card_rotation_probe.v:34-37`) claims order dividing five and no
  longer that the group has exactly five elements. The claim as written is
  true: the rotation group is generated by `fc_sigma`, so its order is the
  order of `fc_sigma`, which divides five.
- **F7, NOTE, not applied, acceptable.** The second mutation on the support
  hypothesis is still absent. The one mutation present fixes the boundary that
  matters for the field it fills.
- **F8, NOTE, not applied, acceptable.** `sw_L` is still undefended: it is 7 in
  `kim_centi_marginal_bound40` and 1 in `kim_biased_marginal_bound_exact`, both
  correct, and it enters neither `cert_eps` nor `SpectralPropAt`.
- **F9, NOTE, applied although the fix table says no change was asked.**
  `STATUS.md:549-553` now states that `sa_cut_dist sa` is the cut marginal and
  that the reading as a conditional law rests on `kim_input_dist` being a
  product, a property of these adapters.

## Q7 The certified proposition, and whether S9 and the paper material still match

In one sentence: *at every real field and every index of the model family, for
every coalition of at most one of the five seats and every two committed
pairs, the sum of absolute differences between the law of that coalition's
static endpoint reading at the first pair and its law at the second pair, both
taken under the row's own biased cut law, is at most the row's published
number.*

I did not take this from the prose. `B1_inv25_statement` and
`B2_repeated39_statement` write the proposition out in full and derive it from
`published_thm` of the two repriced rows, at `1 / 25` and at `2%:R ^- 39`
respectively, and both close. The cut law is the row's own:
`B3_biased_cut_is_biased` is `sa_cut_dist (amf_sample kim_biased_family R tt)
= sw_rho_dist (kim_biased_marginal_bound R)`. The threshold is definitional,
`A10_threshold : profile_k (instance_profile five_card_algebra) = 2` by
`erefl`, so "at most one seat" is exact.

`STATUS.md`'s S9 matches it with no discrepancy, and its citation of
`SpectralPropAt` at `manifest/pgg_tableau.v:331` is right. Three things S9
gets right that are easy to get wrong, and I checked each. The uniform
rotation law is the ideal and the ideal does **not** appear in the certified
proposition; it enters only through the certificate's fields, and the
statement compares two readings of the biased cut with each other. The two run
arguments range over all four committed pairs, so pairs with different values
of the conjunction are covered. A seat reads a colour: the reading lands in
`'I_5` but `den_boer_layout` is `map_tuple encode_bool ...`, so only two of
the five values occur. S9's four "it is NOT" bullets are all accurate, and the
first of them, that this is not independence of the reading from the secret,
is the one a reader is most likely to overclaim.

Round 1's "what a paper may and may not say" material still matches after the
fix pass, and one of its bullets is now consistent with the probe rather than
against it: "may not say that the biased row's status is unchanged" is what
the probe now says itself. The numbers in that material check out, `1/25` at 2
per cent of the ceiling and `2^-39` at 8.53 times the spectral expression,
with the single exception that the spectral expression is `2.13e-13` and not
the `1.6e-13` `STATUS.md` prints (G5).

## Q8 The rest of the delta

The five files hold 56 declarations with no duplicate name. I reran the
collision scan independently: whole-word search of all 56 over the 133
production `.v` files, the 62 under `legacy/` and the 1153 under
`_opam/lib/coq/user-contrib` returns zero hits in all three corpora, which
reproduces S10's claim exactly. Every `Print Assumptions` block reports the
three boolp axioms or `Closed under the global context`, eighteen blocks in
the distribution `STATUS.md` states, five, four, three, two and four. My wall
times reproduce the compile table to within a tenth of a second.
