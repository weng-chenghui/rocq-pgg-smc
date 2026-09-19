# NO-GO

Verdict on "these names, homes and comments may be carried into a landing plan
as they are": **NO-GO**.

Round 3 of the naming, style and statement-comment audit of
`notes/probes/2026-09-19-kim-spectral-arm/`. The second fix pass applied every
blocking finding of round 2 and every SHOULD-FIX, and applied them correctly:
"constancy" is restored everywhere, `kim_centi_cert40`'s comment now names both
fields that change, and the reverse-dependency figures are not merely corrected
but recomputed and published with their script. On the three places where the
fix pass says it checked an audit claim against the source and declined to
follow it, **the fix pass is right in all three** and round 2 was wrong.

What blocks a landing plan is text this pass wrote. Four sentences in
`STATUS.md` are false or wrong by a number, and all four sit in the two
sections a landing plan is written from: one says the freeze rule is respected
by every home on the page while the table four lines above marks four homes as
violating it; one describes a home arrangement that cannot compile, because
the lemmas the three moved theorems call are left in the file above them; one
reports a whole-tree grep as returning one site where it returns fourteen; and
one counts three lemmas where the file has two, inside a list presented as
exhaustive that omits eight declarations.

Independent checks run for this audit, none of which invoked a Rocq compiler
and none of which edited an existing file: a line-by-line diff of every `.v`
file and `STATUS.md` against its `history/*.2026-09-19-before-fix2` copy; a
whole-word Python `\b` scan of all 56 declaration names plus every right-hand
entry of `rename_map.tsv` over 133 production, 62 legacy, 1153 installed, 355
earlier-probe and 169 worktree `.v` files; a byte length check; a banned-word
scan; an independent recomputation of every reverse-dependency closure, every
landing total and every forward cone from `.Makefile.rocq.d`; and a reading of
each of the 60-odd `file:line` citations of `STATUS.md` against the source.

---

## 1. Disposition of every round 2 finding

### Blocking

| ID | Disposition | Evidence |
|---|---|---|
| B1 | **fixed** | "constancy" replaces "invariance" at all five `.v` sites (`five_card_sc_const_probe.v:89`; `kim_spectral_rows_probe.v:63`, `:77`, `:108`, `:256`) and all six `STATUS.md` sites. Zero occurrences of `invarian` remain in the five files or in `STATUS.md`. The four replacement comments round 2 supplied are applied verbatim. `:658-659` reads "where the constancy field is false for a reason no proof removes", as B1 asked. One residue: the count in the disposition row is wrong. See S-1. |
| B2 | **fixed**, verbatim and accurate | `kim_spectral_rows_probe.v:254-259` carries round 2's replacement unchanged. Checked field by field against `kim_centi_cert`: `sc_b` and `sc_close` differ, `sc_Hd`, `sc_ideal` and `sc_const` are the same terms. "the mixing statement differs only in the number it bounds by" is exact: `sw_rho_dist (kim_centi_marginal_bound40 R)` is the same law as `sw_rho_dist (scb_bound (kim_security_bundle_centi R))` by the record's fourth field, so only the right-hand side moves. |
| B3 | **fixed differently, acceptable and better** | Round 2 gave a replacement paragraph; the fix pass instead rebuilt the whole home analysis around a published script. I recomputed every figure independently and every one agrees: the manifest's closure is **7** and its members are the seven named; `five_card_analysis.v` 8; `den_boer_encoding.v` 16; `pgl27_mixing.v` 20; `five_card_rows.v` 0; the eleven older rows 105, 107, 102, 41, 39, 24, 20, 20, 10, 9, 0. The landing totals 9, 10, 11, and the `card_tnth_count` branch 18 and 19, all reproduce exactly, as does the "direct requirers" block. The text this rebuild introduced carries two blocking defects of its own: B-1 and B-2 below. |

### Should fix

| ID | Disposition | Evidence |
|---|---|---|
| S1 | **fixed**, verbatim | `five_card_sc_const_probe.v:49-53` now reads "this is that census read as the law of the card drawn". |
| S2 | **fixed**, verbatim, and accurate | `kim_spectral_rows_probe.v:94-99`. `manifest/pgg_analysis_status.v:63-73` does define `IdealFinite` as covering "a cut-carrier transfer whose base premise is discharged", and `publish` (`manifest/pgg_tableau.v:691`) takes the status as a plain argument. |
| S3 | **fixed differently, acceptable and better** | Round 2 wrote "quantified over the field alone"; the file has "quantified over every real field but not over the family index". Checked: `RepricePayload` (`manifest/pgg_tableau.v:610-614`) is `forall (R : realType) (idx : amf_index (ab_f q) R), ...`, so the missing binder is the family index and the fix pass names it. |
| S4 | **fixed** | The N4 row reads "The four row programs ... Round 1's fifth program is deleted by F1." Counted in the file: four. |
| S5 | **fixed**, verbatim | `kim_spectral_rows_probe.v:161-165`. |

### Notes

| ID | Disposition | Evidence |
|---|---|---|
| a | **fixed**, and the count is right | `history/kim_spectral_rows_probe.2026-09-19-before-fix.v` has three `Fail`s, the current file four, so "the other three recorded `Fail`s existed in round 1 under their round-1 names" is exact. The sentence acquired a false clause in the rewrite: see S-5. |
| b | **fixed** | `var_dist_le2`'s proof runs `:44-52`, nine lines between `Proof.` (`:43`) and `Qed.` (`:53`). |
| c | **half applied, and the fix pass is right on both halves** | Read in the source: `five_card_row_repeated_tableau`'s docstring is `five_card_rows.v:383-389`, so round 2's `:382-388` is wrong and `STATUS.md` was already right. `five_card_row_biased_tableau`'s docstring is `:394-400`, so round 1's `:396-400` and round 2's `:393-399` are both wrong and the corrected range is what the file has. |
| d | **not applied, acceptable** | Recorded for the landing plan. |
| e | **fixed differently, NOT acceptable** | The duplicated clause is gone, but the replacement is proof narration. See S-2. |
| f | **recorded, acceptable** | Carried into "Audit findings not applied" at `:1191-1196`. |
| g | **no change needed, none made** | Correct. |
| h | **not applied, acceptable** | A `Section` rename is a code change and this pass changed no code. Recorded for the landing. |
| i | **fixed** | `STATUS.md:1179` reads `b \in codom f`. |
| j | **fixed** | The N7-and-N20 bullet is split, and the section now carries six bullets for the six deviations: N10 second half, N4 one name, N7, N20, N3 last row, N24. |
| k | **no change asked, none made** | Correct. |

### The three places where the fix pass overruled an audit claim

All three were checked against the source for this audit. **The fix pass is
right in all three, and round 2 was wrong.**

1. `five_card_row_repeated_tableau`'s docstring is `five_card_rows.v:383-389`.
   Round 2's `:382-388` is off by one; `:382` is blank and `:389` carries the
   closing `*)`.
2. `five_card_row_biased_tableau`'s docstring is `:394-400`. Round 2's
   `:393-399` is off by one in the other direction, and round 1's `:396-400`
   is short by two lines.
3. "constancy" as the tree's word for the fifth certificate field occurs in
   **six** production files, not seven: `manifest/pgg_tableau.v:37,126,129,557`,
   `manifest/pgg_tableau_syntax.v:140`, `instances/pgl27/pgl27_rows.v:244`,
   `instances/s5/s5_rows.v:66`, `instances/psl211/psl211_rows.v:41`,
   `instances/kim2025/five_card_rows.v:41`. Round 2 wrote "seven files" and
   then listed six. `reconstruct/s5_nogo.v:53` is the seventh file carrying the
   word and is about a different object, exactly as the fix pass says.

---

## 2. New findings

Replacement text for a `.v` file is at most 80 columns. Replacement text for
`STATUS.md` follows that file's own convention: prose wrapped at 76, and a
Markdown table row on one line, as every row of those tables already is.

### Blocking

**B-1. `STATUS.md` says the freeze rule is respected by every home on the page;
its own table four lines above marks four homes as violating it.**
BLOCKING. `STATUS.md:747-749`.

The sentence reads "and `instances/psl211/psl211_endpoints.vo` is in none of
the closures on this page, so the freeze rule is respected by every home
considered here". The table at `:723-739` marks `psl211_endpoints` **YES** for
`security/pgg_collusion_bound.v`, `lib/perm_uniform.v`,
`reconstruct/algebraic_rigidity.v` and `reconstruct/transitivity_privacy.v`. I
recomputed all fifteen rows and those four are correct. The very next
paragraph, `:751-755`, then says `pgg_collusion_bound.v` "is below
`psl211_endpoints`, so the rule forbids it", which contradicts the sentence
directly. This is new text in this revision.

The true claim, and the one the home argument needs, is about the homes the
landing proposes, not about the page.

Replacement for `:746-749`:

```
(`manifest/pgg_tableau.v:695`). Every other row of the table is confirmed by
the rerun. `instances/psl211/psl211_endpoints.vo` is in the closures of the
first four rows, which is why none of those four is proposed as a home, and
in none of the closures of the other eleven.
```

**B-2. Option 2 as described does not compile: the lemmas the three moved
theorems call are left in the file above them.**
BLOCKING. `STATUS.md:790-794` and `:827-906`, and the dagger marks at `:815`
and `:816`.

The section argues the placement from the three theorems' statement types
alone: "Their statements mention no manifest type ... Both can therefore sit
anywhere at or above `five_card_exec.v`." It never asks what their proofs
call. The S10 table then sends every one of those callees to
`instances/kim2025/five_card_rows.v`, which under option 2 sits above the new
`instances/kim2025/five_card_mixing.v`.

- `kim_centi_cut_mixing` and `kim_biased_cut_mixing` are proved by
  `five_card_cut_mixing_of_supp_pow` from `kim_centi_cut_supp_pow` and
  `kim_single_cut_supp_pow`; those in turn call `fc_kim_rho_supp_pow`,
  `fc_kim_word_eval_powE`, `five_card_ideal_supp_pow`,
  `five_card_ideal_point_uniform`, `fc_sigma_pow_point_inj` and
  `fc_sigma_pow5_eq1`. Table home for every one of them: `five_card_rows.v`.
- `kim_biased_cut_mixing`'s **statement** mentions `kim_biased_marginal_bound`,
  which the table carries in the "bounds and the certificates" row, also to
  `five_card_rows.v`.
- `five_card_static_obs_const` is proved from `den_boer_layout_law_const`,
  `fc_arrange_countE` and `five_card_ideal_point_uniform`. Same home in the
  table, same inversion.

So "under option 2 the three theorems marked with a dagger move one file down"
understates the move by thirteen declarations, and taken literally it
describes an arrangement the kernel rejects. The recompile figure 11 is
unaffected, because everything that must move lands in the new file, which is
already counted; what is wrong is the instruction a landing plan would follow.

Replacement for `:790-794`:

```
The generic lemmas go in one new `lib/` file. Where the instance-specific
lemmas go is an open decision, set out under "The home of the mixing and
constancy theorems" below. The table that follows records the second home as
`instances/kim2025/five_card_rows.v`, which is option 1 there; under option 2
every row marked with a dagger moves to the new file below the facade.
```

and the dagger moves from two rows to fourteen: the eleven rows from
`fc_sigma_pow5_eq1` through `the generic distance transfer`, the two mixing
fields, the constancy field, and `kim_biased_marginal_bound`, which must be
split out of the "bounds and the certificates" row because a mixing statement
names it. Add at `:841`, after "so those stay in `five_card_rows.v` under
either option":

```
Their proofs do not travel alone. `kim_centi_cut_mixing` and
`kim_biased_cut_mixing` are proved by `five_card_cut_mixing_of_supp_pow` from
the two Kim supports, and `five_card_static_obs_const` from
`den_boer_layout_law_const` and `five_card_ideal_point_uniform`; the chain
closes at `fc_sigma_pow5_eq1` and `fc_kim_word_eval_powE`. Under option 2 all
of those, and `kim_biased_marginal_bound`, which a mixing statement names, go
in the new file too. Only the certificates and the row programs stay above.
```

**B-3. The landing list reports a whole-tree grep as returning one site where
it returns fourteen.**
BLOCKING. `STATUS.md:626-631`.

The sentence reads: a grep for `single_biased_sample`, `repeated_sample`,
`centi_sample`, `biased_family` and `centi_family` "returns their declarations
in `five_card_analysis.v:202-222`, their names in the manifest's Row 4 and Row
5 header tables and row definitions, and one spelled-type `Check` at
`five_card_analysis.v:402`".

The grep over the twelve production directories also returns
`manifest/pgg_analysis_client.v:41`, `:43`, `:44`, and
`manifest/pgg_analysis_manifest.v:1177`, `:1182`, `:1187`, `:1210`, `:1217`,
`:1225`, `:1229`, `:1235`, `:1248`, `:1253`, together with the facade's own
alias table at `five_card_analysis.v:45-47`. Ten of those are spelled-type
`Check`s in the manifest's section 4 and its bridge block, which is the same
class of pin whose omission was round 2's G1.

The conclusion drawn from the grep survives: I checked each of the fourteen and
none states a completion level or a transfer status, so no name there moves
with a restatusing. But this sentence exists because the round-1 claim to cover
"every" passage was withdrawn and replaced by a statement of what was searched,
and that statement is wrong about what the search returned.

Replacement for `:626-631`:

```
family names, `single_biased_sample`, `repeated_sample`, `centi_sample`,
`biased_family` and `centi_family`, returns their declarations and alias
table in `five_card_analysis.v:45-47` and `:202-222`, their names in the
manifest's Row 4 and Row 5 header tables and row definitions, three bare
`Check`s in `manifest/pgg_analysis_client.v:41,43,44`, one spelled-type
`Check` at `five_card_analysis.v:402`, and ten more spelled-type `Check`s in
`manifest/pgg_analysis_manifest.v:1177,1182,1187,1210,1217,1225,1229,1235,
1248,1253`. None of the fourteen states a level or a status, so none moves
with a restatusing.
```

**B-4. "the three `prefixE` ... lemmas": the file has two, and the list
presented as exhaustive omits eight declarations.**
BLOCKING. `STATUS.md:680-685`.

`instances/kim2025/five_card_rows.v` declares `five_card_row_repeated_prefixE`
(`:418`) and `five_card_row_biased_prefixE` (`:428`) and no third. The
paragraph opens "Every other theorem in that file stays true:" and then
enumerates; the enumeration omits `five_card_viewS_nth` (`:216`),
`five_card_static_obsE` (`:234`), `five_card_viewS_indep` (`:270`),
`five_card_exact_viewE` (`:286`), `five_card_static_obs_indep` (`:299`),
`five_card_FE` (`:558`), the recorded `Fail five_card_F_or` (`:571`) and
`five_card_realises_expected` (`:579`). Each of those does stay true, so the
claim is sound and the list is not.

Replacement for `:680-685`:

```
Every other declaration in that file stays true. Named for the landing:
`five_card_row_repeated_endpoint_lt`, `kim_centi_small`,
`five_card_row_biased_leak_bound`, `five_card_row_uniform_tableau` and its
`rowE`, `five_card_exact_view_secrecy`, the two `prefixE` and two `modelE`
lemmas, `five_card_committed_paramsE`, and the recorded
`Fail five_card_row_s5_family`. The five static-reading lemmas at `:216`,
`:234`, `:270`, `:286` and `:299` and the functionality block at `:558-579`
mention no manifest row and are untouched.
```

### Should fix

**S-1. The B1 disposition row counts ten sites and lists nine.**
SHOULD-FIX. `STATUS.md:1219`.

"It is the tree's word for that field at ten sites in six files" is followed by
a list of nine line numbers, and the same row then calls
`reconstruct/s5_nogo.v:53` "the only other 'constancy' in the tree". A
whole-tree grep returns ten occurrences in production files in all: the nine
listed plus `s5_nogo.v:53`. The "ten" double-counts.

```
| B1 | blocking | "constancy" replaces "invariance" as the prose name of the `sc_const` field at all eleven sites, five in the `.v` files and six here. It is the tree's word for that field at nine sites in six files, `manifest/pgg_tableau.v:37,126,129,557`, `manifest/pgg_tableau_syntax.v:140`, `instances/pgl27/pgl27_rows.v:244`, `instances/s5/s5_rows.v:66`, `instances/psl211/psl211_rows.v:41` and `instances/kim2025/five_card_rows.v:41`, all read for this pass. The audit says seven files and lists six; six is what a whole-tree grep returns. The only other "constancy" in the tree, `reconstruct/s5_nogo.v:53`, is about a different object and is not a name for this field. `invariant by` as a Tableau surface keyword is untouched, and it does not occur in this probe. |
```

**S-2. `fc_kim_rho_supp_pow`'s new comment replaces the domain position with
proof narration.**
SHOULD-FIX. `five_card_rotation_probe.v:90-94`.

The second sentence now reads "It reads fc_kim_word_eval_powE off the support
of the pushforward that defines the shuffle, and adds the quantifier over the
weighting, which is what makes every Kim cut law comparable with the uniform
rotation law on one group." That is the proof: the script is
`rewrite /rho_from_words_weighted => /fdistmap_neq0_codom [w Hw]` followed by
`rewrite -Hw fc_kim_word_eval_powE`. It also pins the comment to a sibling
declaration, so it does not survive a reproof, and "on one group" loses the
referent "the rotation group" that the previous version carried.

Round 2's note e asked for the second comment to say what it adds. What it
adds, in the domain's frame, is that one statement covers Kim's three cut laws
at once, which is why a single support fact puts all of them and the ideal on
the same carrier.

```
(* Every cut the weighted word shuffle gives mass to is a power of the
   five-cycle, at every word length and every letter weighting. The
   quantifier over the weighting is what lets one statement cover all of
   Kim's cut laws, so each of them and the uniform rotation law live on one
   group and a variation distance between them is a distance on that
   group. *)
```

**S-3. "Neither round-2 audit names this file" is false.**
SHOULD-FIX. `STATUS.md:568`.

`soundness-audit-round2.md:38`, finding G4, names
`instances/kim2025/five_card_analysis.v` three times: as the file the manifest
requires, as the file the option-2 home sits below, and as the file whose eight
reverse-dependants set the 11-compile figure. What no round-2 audit reached is
the file's typed transfer statuses and their pins, which is a narrower and true
claim.

```
Neither round-2 audit reaches this file's typed transfer statuses. It states
both rows' transfer statuses a second time, and those statements are pinned
by four further `erefl`s, two in the facade itself and two more inside the
manifest.
```

**S-4. The N6/F3 row credits round 2 with findings round 2 did not make, and
contradicts the G1 row.**
SHOULD-FIX. `STATUS.md:1123`.

It says "round 2 found the list missing five `erefl` pins, the manifest's Row 4
and Row 5 header tables, and the whole of the five-card facade's section 7".
`soundness-audit-round2.md`'s G1 names three pins, `:1779-1780`, `:1787` and
`:1788-1789`, and the Row 4 and Row 5 tables, and does not mention the facade.
The G1 disposition row at `:1226` says so itself: "The further search the fix
pass was asked to run found what both audits missed: the five-card facade's two
typed transfer statuses".

```
| N6, F3 | The landing change list in S8 is rewritten and carries both manifest rows and the compile breakage at `five_card_rows.v:456`. Its round-1 claim to carry "every" header and docstring passage a landing makes false is withdrawn: round 2 found the list missing three `erefl` row pins and the manifest's Row 4 and Row 5 header tables, and the further search this pass ran added two more pins in the manifest and the whole of the five-card facade's section 7. What the list states now is the result of a whole-tree grep for the two row names, for the facade's two typed transfer statuses, and for the manifest's status vocabulary at those rows, each result read in the source. |
```

**S-5. The compile-table sentence says the kernel rejects an `erefl` that
`Qed`s.**
SHOULD-FIX. `STATUS.md:58-61`.

"that new comparison is one part and one new `Fail`,
`five_card_row_biased_inv25_rowE`, is another, each of which elaborates a
published row before the kernel rejects the `erefl`". The new comparison is
`five_card_row_biased_forms_publishedE`, a `Lemma` closed by `Proof. by [].
Qed.` Nothing is rejected there. Only the `Fail` fits the clause.

```
`kim_spectral_rows_probe.v` was 7.72 s; of the 3.3 s added, the new
comparison `five_card_row_biased_forms_publishedE` is one part, and the new
`Fail five_card_row_biased_inv25_rowE` is another, which elaborates a
published row before the kernel rejects its `erefl`. The other three
recorded `Fail`s existed in round 1 under their round-1 names and account
for none of the added time. The rest is the two lemmas added,
`five_card_row_biased_ideal_publishedE` and
`five_card_row_biased_forms_publishedE`, less the two deleted.
```

**S-6. The Row 5 quote is called the paragraph's ending, and the sentence that
actually ends it is the one a landing most directly falsifies.**
SHOULD-FIX. `STATUS.md:562`.

The cell quotes the level justification "ending" at "neither has the shape of
an indistinguishability or leakage statement", which is `:379`. The paragraph
runs to `:380` and ends "A ShuffleCertificateBundle exists for both models and
does not raise the level." A landing makes that sentence false in the sharpest
way available: the certificate that raises the level is built from that
bundle's `scb_bound`. The cited range `:374-380` already covers it, so a
landing editor will see it, but the list does not name it.

```
| `:374-380` | the level justification, which says `The row is NOT AnalysisBridged. endpoint_bound and deal_centi_lt bound the distance from uniform of ONE seat's endpoint distribution: neither quantifies over a coalition, neither mentions a second secret, and neither has the shape of an indistinguishability or leakage statement.` and closes at `:379-380` with `A ShuffleCertificateBundle exists for both models and does not raise the level.` | the certified proposition quantifies over every coalition below the threshold, compares two committed pairs, and has exactly the shape the paragraph says is absent; and the certificate that raises the level is built from that same bundle's `scb_bound` |
```

### Notes

| ID | Location | Observation |
|---|---|---|
| a | `STATUS.md:659` | Cites `instances/s5/s5_rows.v:60-72` for the constancy field being false at S5. The sentence that says so runs `:65-72`; `:60-64` is about the missing distance. The range is a superset and finds the passage. |
| b | `STATUS.md:647` | Cites `:29-33` for "both Kim rows stop at `Sampled`". That sentence is `five_card_rows.v:28-30`; `:30-33` for the second half is exact. |
| c | `STATUS.md:723-739` | The three rows appended for this revision are placed after `manifest/pgg_analysis_manifest.v`, so the table is no longer in descending order of reverse-dependants. Cosmetic; every figure is right. |
| d | `kim_spectral_rows_probe.v:65` | "the ideal cut and the constancy field are exact." `sc_ideal` is a distribution and "exact" is a word for a number or an equality. `sc_Hd` is exact too. The preceding clause, "the only inexact quantity in the row is the bundle's spectral number", already carries the content without the type wobble. Round 2's wording; no change needed. |
| e | `STATUS.md:794` | "move one file down" for a move to a new file below the facade. Superseded by B-2's replacement. |
| f | `five_card_sc_const_probe.v:46`, `:91` | `Section five_card_static_obs_const` still encloses `Lemma five_card_static_obs_const`, as round 2's note h recorded. Deliberately not applied, because this pass changed no code. Still a one-line edit for the landing. |
| g | `five_card_rotation_probe.v:76-79` | The clause round 2's note e flagged as duplicated is now carried here alone, which is the right half to keep: this is the declaration the alphabet fact is about. |
| h | `kim_spectral_rows_probe.v:76-79` | "the two rows differ only in the shuffle and its number" while three fields differ. The sentence is at the domain level, not a field count, and the preceding clause names the two fields that are shared, so a reader can count. Distinguish from B2, which was a field count. No change. |

---

## 3. Mechanical results

| check | result |
|---|---|
| whole-word collision scan, 57 identifiers (56 declarations plus `rename_map.tsv` right-hand entries), 133 production `.v` | **0 hits** |
| same, 62 `legacy/` | **0 hits** |
| same, 1153 installed under `~/Projects/coq/_opam/lib/coq/user-contrib` | **0 hits** |
| same, 355 earlier-probe `.v` | **0 hits** |
| same, 169 `.claude/worktrees/` `.v` | **0 hits** |
| lines over 80 bytes, five `.v` files | **none** |
| the three banned words of the account-wide vocabulary list, with all their inflections, whole-word and case-insensitive, over the five `.v` files, `STATUS.md` and `rename_map.tsv` | **0 hits** |

`STATUS.md:34`'s count of 56 declaration names is exact: 55 distinct
`Lemma`/`Definition`/`Fact` names plus `five_card_static_obs_const`, which is
also a `Section` name. Every scan used Python `re` with `\b`; the
`grep -E '[[:<:]]'` trap was avoided throughout.

---

## 4. What was checked and found correct

Recorded so that a later pass does not re-audit it.

- Every `file:line` in the S8 landing list and the S10 home sections, opened in
  the source: the manifest rows `:766-768` and `:776-778` with docstrings
  `:760-765` and `:770-775`; the header quote `:67-72`; the six `erefl` row
  pins `:1777-1778`, `:1779-1780`, `:1781-1782`, `:1787`, `:1788-1789`,
  `:1790-1791`; the facade-status pins `:1385-1386`, `:1388-1389` under the
  comment `:1381-1383`; every Row 4 line `:301-302`, `:303`, `:305`, `:306`,
  `:307`, `:308`, `:310`, `:322-328`; every Row 5 line `:351-354`, `:355`,
  `:357`, `:358-360`, `:361`, `:362`, `:364`, `:374-380`; the pgl27 precedent
  `:173`, `:182`, `:1048` and `pgl27_analysis.v:267`; the client `:48-49` and
  `:149-150`; `pgg_tableau.v:691` and `:695`; `AnalysisPathRow` `:707-725` with
  "It stores no theorem" at `:702`; `SpectralPropAt` at `pgg_tableau.v:331`;
  `pgg_analysis_status.v:63-73`; `five_card_exec.v:756`. All correct.
- The facade `five_card_analysis.v`: `:351-358`, `:361-363`, `:364`,
  `:366-367`, `:368`, `:402`, `:433-436`, `:202-222`. All correct, and the
  quoted section-header text is verbatim.
- `five_card_rows.v` items 1, 3, 4, 7 and 8 of the landing list: `:456-458`,
  `:39-42`, `:42-50`, `:460-464`, `:465-467`, `:469-472`, `:473-475`. All
  correct.
- `_CoqProject` enumerates exactly 194 `.v` files after its `-R` lines;
  `reconstruct/dealer_privacy.v` is at `:172`; the five `lib/` lines are
  `:30-34`.
- The S7 arithmetic: `2*sqrt(5)*(1/80)^7 = 2.1325e-13`, `2^-39 = 1.8190e-12`,
  ratio `8.5299`; `soundness-audit.md:338-339` does carry "about eight and a
  half times weaker"; `1.6e-13` would have given `11.37`. `sqrt 5 / 40 =
  0.0559`, about three per cent of the ceiling 2; `sqrt 5 / 80 = 0.02795`;
  `1/25 = 0.04`.
- The forward cones: `pgl27_word_privacy.v`'s is 32 files plus itself, all 33
  inside `five_card_rows.v`'s 98, so the "build cost of the edge is zero"
  sentence at `:340-342` is exact.
- Eighteen `Print Assumptions` commands, distributed 5/4/3/2/4, and the
  sixteen-name list at `:1084-1091` plus the two closed declarations accounts
  for all eighteen.
- Vocabulary, across all five files: "card position" for an `'I_5` in a
  marginal bound everywhere; "seat" only in `five_card_sc_const_probe.v`, where
  the object is an index of `pi_starts`; "reading" for `static_coalition_obs`
  with no "view" or "observation" anywhere as a synonym; `pow` for powers of
  `fc_sigma` with no bare `rot`; "constancy" for the fifth field with zero
  occurrences of `invarian`.
- `kim_sc_close_probe.v` and `var_dist_injective_probe.v` are byte-identical to
  their `before-fix2` copies, and re-reading them against the changes elsewhere
  found no sentence made false.
- No `Admitted`, `Axiom`, `admit` or `Abort` in any of the five files.

---

## 5. What a landing plan must carry, beyond rounds 1 and 2

1. B-1: the corrected freeze-rule sentence.
2. B-2: the corrected option-2 description, with the dagger on every
   declaration whose proof or statement the three theorems reach, and
   `kim_biased_marginal_bound` split out of the "bounds and the certificates"
   row.
3. B-3: the corrected grep result, all fourteen sites.
4. B-4: the corrected `prefixE` count and the eight unnamed declarations.
5. S-1 through S-6.
6. Round 2's note d, the `(**` and `(*` split at `five_card_pow2_39_split`, and
   note f, the instance prefix moving with the two identities: both still open
   and both correctly recorded.
7. Note f of this round: the `Section five_card_static_obs_const` rename.
