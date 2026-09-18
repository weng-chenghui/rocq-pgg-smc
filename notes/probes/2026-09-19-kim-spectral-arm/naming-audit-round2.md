# NO-GO

Verdict on "these names, homes and comments may be carried into a landing plan
as they are": **NO-GO**.

Round 2 of the naming, style and statement-comment audit of
`notes/probes/2026-09-19-kim-spectral-arm/`. The fix pass applied every one of
round 1's six blocking findings and every SHOULD-FIX it accepted. The renames
are correct, the identifiers no longer carry record-field abbreviations, `rot`
is gone, the `_bad` suffix is gone, no line exceeds 80 bytes, no collision
exists in any corpus, and no banned word occurs anywhere. What blocks a landing
plan is three sentences the fix pass wrote or carried: one word substituted
repository-wide in the wrong direction, one claim about a certificate that is
false about the term, and one recompile figure that is wrong by two files and
is the figure the plan's home choice rests on.

Independent checks run for this audit, none of which invoked a Rocq compiler
and none of which edited an existing file: a whole-word Python `\b` scan of all
56 declaration names plus every right-hand entry of `rename_map.tsv` over 133
production, 62 legacy, 1153 installed and 349 earlier-probe `.v` files; a byte
length check of all five files; a banned-word scan of the five files,
`STATUS.md` and `rename_map.tsv`; a reverse-dependency recomputation of the
whole S10 table from `.Makefile.rocq.d`, cross-checked against a direct grep of
`Require` lines; and a line-by-line diff of every file against its
`history/*.2026-09-19-before-fix` copy.

Audited text: the five `.v` files, `STATUS.md`, `rename_map.tsv`, and for
comparison `history/` and `naming-audit.md`.

---

## 1. Round 1 disposition, N1-N27

| ID | Round 1 verdict | Disposition | Evidence |
|---|---|---|---|
| N1 | BLOCKING | **fixed** | `fc_rot_pow_faithful` is `fc_sigma_pow_point_inj`. Replacement comment C2 applied verbatim at `five_card_rotation_probe.v:45-49`. No occurrence of `faithful` or `regular` survives in any of the five files. |
| N2 | BLOCKING | **fixed** | `five_card_ideal_distE` is gone. Both sites, `five_card_ideal_supp_pow` and `five_card_ideal_point_uniform`, now open with `have Hid : <unfolded type>. exact: five_card_sample_cut_distE.` The tree's lemma is at `instances/kim2025/five_card_exec.v:756`, as claimed. |
| N3 | BLOCKING | **fixed for identifiers, regressed for prose** | The eight abbreviation names carry domain words and neither `sc_close` nor `sc_Hd` occurs as an identifier fragment anywhere. But the prose word for the `sc_const` field moved from the tree's "constancy" to "invariance". See B1. |
| N4 | BLOCKING | **fixed differently, acceptable** | The row programs are `five_card_row_*`. Four programs remain, not five, because F1 deleted the `StaticExecutedOnly` one. The disposition table's own wording is now stale: see S4. |
| N5 | BLOCKING | **fixed** | No `_bad` anywhere. `five_card_row_biased_ideal_rowE` and `five_card_row_repeated_spectral_rowE` are named after what is attempted and both stay recorded `Fail`s. |
| N6 | BLOCKING | **fixed** | `STATUS.md:477-523` now carries both manifest rows, the compile breakage at `five_card_rows.v:456-458`, and eight numbered items covering every header and docstring passage a landing makes false. I verified the manifest rows, the status vocabulary and the breakage independently. Two cited line ranges are off by one and by three: see NOTE c. |
| N7 | SHOULD-FIX | **fixed differently, acceptable** | Reciprocals are spelled `inv50`, `inv25`. A numeral suffix now reads as an exponent of two in `pow2_39`, `40`, `39`, and as a reciprocal only behind `inv`. The `_lt2` and `_le2` suffixes carry a third reading, the number compared against, but the comparison word immediately precedes the numeral, so no ambiguity arises. Deviation on the prefix is judged at section 2(a). |
| N8 | SHOULD-FIX | **fixed** | No `\brot\b` token in any of the five files. Every group element is `pow`. |
| N9 | SHOULD-FIX | **fixed** | `den_boer_layout_law_const`. |
| N10 | SHOULD-FIX | **fixed** (first half) / **not applied, acceptable** (second half) | Name is `fdistmap_neq0_codom`. The `b \in codom f` restatement is declined because the conclusion is consumed through a destructuring view at two call sites; that is three proof scripts for a rename pass, and the name states the fact either way. Acceptable. |
| N11 | SHOULD-FIX | **fixed** | `lib/var_dist_supp.v`, with `card_tnth_count` left open between `lib/` and `den_boer_encoding.v`. That openness interacts with the recompile figure: see B3. |
| N12 | SHOULD-FIX | **fixed** | C1 applied verbatim. See NOTE g: the file in fact proves the stronger fact the old comment claimed, so the new comment is honest and understates. |
| N13 | SHOULD-FIX | **fixed** | C7 applied verbatim. The pointer at a nonexistent file header is gone and both numbers are named. |
| N14 | SHOULD-FIX | **fixed, with one residue** | "seat" now occurs only in `five_card_sc_const_probe.v`, where the quantified object is a set of `pi_starts` indices, which is correct. The residue is a carrier ambiguity at `den_boer_layout_law_const`: see S1. |
| N15 | SHOULD-FIX | **fixed** | The script narration is gone; the recorded `Fail` carries a declarative sentence. |
| N16 | SHOULD-FIX | **fixed** | Every occurrence of "below" in the five files is numeric ("below two"). No positional pointer, no "used by", no roadmap clause survives. |
| N17 | SHOULD-FIX | **fixed** | Zero lines over 80 bytes across all five files, measured in bytes. |
| N18 | SHOULD-FIX | **fixed** | `fc_kim_word_eval_powE`, `fc_kim_rho_supp_pow`. |
| N19 | SHOULD-FIX | **fixed** | `kim_biased_marginal_bound`, `kim_biased_epsE`, `kim_biased_exact_le_eps`, `kim_biased_cut_mixing`. |
| N20 | SHOULD-FIX | **fixed differently, acceptable** | Route chosen: local reproof as `five_card_pow2_39_split`, the `pgl27_word_privacy` Require removed, no cross-instance edge created. `STATUS.md:320-328` records the trade and leaves the reuse open to the user. I confirm no file under `instances/kim2025` or `instances/denboer1989` now requires anything under `instances/pgl27`. |
| N21 | NOTE | **applied** | The comment on `fdistmap_inj_uniform_id` now says how it differs from `fdistmap_inj_uniform`. The clause is accurate: the existing lemma at `security/pgg_collusion_bound.v:572` concludes `fdist_uniform_supp (f @: setT)`. |
| N22 | NOTE | n/a | No change asked, none made. |
| N23 | NOTE | n/a | Four numeric goal selectors remain, at `kim_sc_close_probe.v:132-133` and `kim_spectral_rows_probe.v:169-170`. Unchanged, as the note allows. |
| N24 | NOTE | **not applied, acceptable** | The probe keeps `(* ... *)`; the landing matches the target's `(** ... *)`. One mechanical consequence the landing plan must carry: see NOTE d. |
| N25 | NOTE | **addressed, but the replacement figure is wrong** | The S10 spread over six files is withdrawn and replaced by two homes. The honest recompile number that replaces it is itself wrong. See B3. |
| N26 | NOTE | n/a | Import audit unchanged and still accurate: `Lia` and `zify` in `kim_sc_close_probe.v:6-7` in `five_card_kim.v`'s order, `lra` in `kim_spectral_rows_probe.v:9`. |
| N27 | NOTE | **confirmed** | Zero hits for `apex`, `gate`/`gates`/`gated`/`gating`, `posit`/`posits`/`posited`/`positing` across the five `.v` files, `STATUS.md` and `rename_map.tsv`, case-insensitive, whole-word. |

### Collision scan, rerun

Python `re` with `\b`, over all 56 declaration names and every right-hand entry
of `rename_map.tsv`, 60 distinct identifiers in all.

| corpus | files | hits |
|---|---|---|
| production, the twelve `_CoqProject` directories | 133 | none |
| `legacy/` | 62 | none |
| installed, all `.v` under `~/Projects/coq/_opam/lib/coq/user-contrib` | 1153 | none |
| earlier probe directories | 349 | none |

The two round-1 collisions with `notes/probes/2026-09-19-kim-tableau-sampled/`
are gone, because both names were renamed. `STATUS.md:34`'s count of 56
declaration names is exact.

### Line length

Zero lines over 80 bytes in the five files. The `[[:<:]]` trap was avoided
throughout; every scan in this audit used Python `re` with `\b`.

---

## 2. The recorded deviations

`STATUS.md`'s "Audit findings not applied" carries five bullets, not six. The
sixth is presumably the second identity in the third bullet, which covers both
`five_card_inv50_split` and `five_card_pow2_39_split`. Judgements follow.

### (a) The instance prefix on two pure identities

`five_card_pow2_39_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39` and
`five_card_inv50_split : (1 / 50 : R) + 1 / 50 = 1 / 25` are identities over a
`realType` with no five-card content. Round 1 was internally inconsistent here:
N20 objected that `fifty_split` is "a bare unprefixed name that would land in a
file where every other name carries an instance prefix", and the rename table
then prescribed the bare `inv50_split`. The fix pass resolved the
inconsistency in the direction N20 argued.

**Acceptable.** Three reasons. The landing target prefixes every name. The
two identities would land in the same file and should read alike, which the
bare-and-prefixed pair would not. And `instances/pgl27/pgl27_word_privacy.v`
already exports a bare `pow2_split` into the `pgg_smc` logical path, so a
second and third bare arithmetic name in the same path is a real hazard rather
than a stylistic one.

The prefix is a home marker and not a claim about a five-card object, which is
how a reader of `five_card_rows.v` will take it. If a later pass moves the
generic lemmas to `lib/var_dist_supp.v`, these two belong there too under
neutral names, and the prefix should go with the move. Recorded as NOTE f.

### (b) `five_card_static_obs_const` against `pgl27_word_view_const`

The recorded reason is that "view" at this instance already means `ViewS`, the
leakage space's colour tuple.

**The reason is good enough, and the name is right.** Three facts support it,
all checked. `ViewS` is defined at `instances/denboer1989/five_card_leakage.v:676`
as the view at a set of card positions, valued in a colour tuple, and
`five_card_rows.v` uses it at `:219,238,270,291,309`. The landing target
already names the statements about the carrier of this very field
`five_card_static_obsE` (`:234`) and `five_card_static_obs_indep` (`:299`), so
`five_card_static_obs_const` completes a triple in one file and pairs the
exact arm's `indep` with the spectral arm's `const` on one carrier. And the two
objects genuinely differ: `ViewS` is indexed by `{set 'I_5}` of card positions,
while the certificate's field is indexed by `{set 'I_(pi_T' ...).+1}` of seats.
Naming them alike would assert a correspondence that holds at this instance
only because `pi_starts` is the identity.

The two instances therefore name one certificate field with two heads, and
that is the right call. It has a consequence the fix pass did not draw: when
the identifier diverges, the prose is the only thing left that lets a reader
find the concept across instances, so the prose must use the repository's word.
It now uses a different one. That is B1.

---

## 3. New findings

### Blocking

**B1. "invariance" replaces the repository's "constancy" for the `sc_const`
field.**
BLOCKING.
Sites: `five_card_sc_const_probe.v:89`; `kim_spectral_rows_probe.v:63`, `:77`,
`:106`, `:253`; `STATUS.md:5`, `:179`, `:417`, `:502`, `:621`, `:708`.

The repository's word for the fifth field of `SpectralCert` is **constancy**,
in seven files: `manifest/pgg_tableau.v:37,126,129,557`, which is where the
record is declared; `manifest/pgg_tableau_syntax.v:140`, which is where the
surface clause is declared; `instances/pgl27/pgl27_rows.v:244`;
`instances/s5/s5_rows.v:66`; `instances/psl211/psl211_rows.v:41`; and
`instances/kim2025/five_card_rows.v:41`, which is the landing target. The
Tableau surface's clause keyword is `invariant by`, which is a keyword and not
prose, and round 1 read the keyword as licence to change the prose word.

Round 1's replacement text C9 introduced "invariance", the fix pass applied it,
and then propagated it to four further comments and to six places in
`STATUS.md`, including one sentence at `kim_spectral_rows_probe.v:63` that had
said "constancy" before the fix. The pre-fix file was right and the post-fix
file is wrong.

The drift is not cosmetic here. `kim_centi_cert`'s comment is a deliberate
mirror of `pgl27_word_cert`'s docstring at `pgl27_rows.v:236-246`, sentence for
sentence, and the one word that now differs between them is the name of the
field they both fill. A reader who has both open will ask whether two different
fields are meant. A landing makes it worse: the header of `five_card_rows.v` at
`:41` says "the constancy of a coalition's reading of that ideal", N6 requires
that header to be rewritten rather than deleted, and the probe's comments would
then sit ten lines below it saying "invariance" about the same field.

Replacement texts, all at most 80 columns.

`five_card_sc_const_probe.v:84-90`, whole comment:

```
(* The privacy threshold is two, so a coalition below it is empty or holds
   one seat. At every such coalition the static endpoint reading of the
   uniform rotation law has the same law at both committed pairs. One seat
   reads one card of a deck whose colour census den Boer's encoding fixes
   at three hearts and two clubs, so the reading cannot separate the pairs.
   This is the constancy field of the spectral certificate, and it is
   exact. It spends no mixing bound. *)
```

`kim_spectral_rows_probe.v:59-65`, whole comment:

```
(* The spectral certificate of the repeated row. Its five fields are the
   seven-cut bundle's marginal bound; the identification of that bound's law
   with the law the repeated adapter draws its cut from; the uniform rotation
   law as the ideal cut; the distance of the seven-cut law from that ideal;
   and the constancy of a coalition's reading of the ideal cut in the
   committed pair. The only inexact quantity in the row is the bundle's
   spectral number; the ideal cut and the constancy field are exact. *)
```

`kim_spectral_rows_probe.v:76-79`, whole comment:

```
(* The spectral certificate of the one-cut row, with the same five fields at
   word length one. The ideal cut and the constancy of a coalition's
   reading of it are the same two terms as in the repeated row's
   certificate, so the two rows differ only in the shuffle and its number. *)
```

`kim_spectral_rows_probe.v:104-107`, whole comment:

```
(* Kim's one-cut row certified by the same arm and published at the same
   transfer status. Its certificate has the shape the repeated row's has,
   over the same ideal cut and with the same constancy field, so the same
   status is the honest one for it. *)
```

`kim_spectral_rows_probe.v:251-254` is also B2; the combined replacement is
given there.

In `STATUS.md`, replace "invariance" by "constancy" at `:5`, `:179`, `:417`,
`:502`, `:621` and `:708`. At `:502` the sentence becomes "where the constancy
field is false for a reason no proof removes", which is what
`instances/s5/s5_rows.v:66-72` says.

**B2. `kim_centi_cert40`'s comment says only one field changes; two do.**
BLOCKING. `kim_spectral_rows_probe.v:251-254`.

The comment reads "The repeated row's certificate with the constant in the
marginal-bound field. Only that field changes: the ideal cut, the tying
equation and the invariance of a coalition's reading are the same terms as in
the certificate at the spectral number."

`SpectralCert` has five fields. Comparing the two terms:

| field | `kim_centi_cert` | `kim_centi_cert40` |
|---|---|---|
| `sc_b` | `scb_bound (kim_security_bundle_centi R)` | `kim_centi_marginal_bound40 R` |
| `sc_Hd` | `esym (kim_centi_cut_distE R)` | same |
| `sc_ideal` | `sa_cut_dist (five_card_sample R)` | same |
| `sc_close` | `@kim_centi_cut_mixing R` | `@kim_centi_cut_mixing40 R` |
| `sc_const` | `@five_card_static_obs_const R` | same |

Two fields change, `sc_b` and `sc_close`. The mixing field must change, because
`sc_close`'s type mentions `sw_bound_eps sc_b` and the epsilon is now the
constant, which is exactly why `kim_centi_cut_mixing40` exists thirteen lines
above. The comment's own enumeration lists three unchanged fields out of four
and is silent about the fourth, so a reader counting fields is told something
false by the sentence and told nothing by the list. This is a new sentence: the
pre-fix comment was the single line "The repeated row's certificate at the
constant bound."

Replacement, which also carries the B1 word:

```
(* The repeated row's certificate with the constant in the marginal-bound
   field. That field and the mixing statement proved against it are the two
   that change. The ideal cut, the tying equation and the constancy of a
   coalition's reading are the same terms as in the certificate at the
   spectral number, and the mixing statement differs only in the number it
   bounds by. *)
```

**B3. The recompile figure the home choice rests on is wrong.**
BLOCKING. `STATUS.md:574` and `STATUS.md:628-635`.

`STATUS.md:574` gives `manifest/pgg_analysis_manifest.v` seven reverse-
dependants as five, and `:628-635` builds the landing's recompile estimate on
that number: "`manifest/pgg_analysis_manifest.v`, which a landing must also
edit, has five. So a landing recompiles three files plus those five".

The transitive reverse closure of `manifest/pgg_analysis_manifest.vo` over
`.Makefile.rocq.d` is **seven**: `manifest/pgg_tableau.vo`,
`manifest/pgg_tableau_syntax.vo`, `manifest/pgg_analysis_client.vo`,
`instances/kim2025/five_card_rows.vo`, `instances/pgl27/pgl27_rows.vo`,
`instances/s5/s5_rows.vo`, `instances/psl211/psl211_rows.vo`. A direct grep of
`Require` lines gives the same seven files and no others. The two files the
round-1 count missed are `pgg_tableau.v` and `pgg_tableau_syntax.v`, which
require the manifest because `publish` builds an `@MkAnalysisPathRow`
(`manifest/pgg_tableau.v:695`).

Every other figure in the S10 table is exact. I recomputed all twelve rows and
only this one disagrees: 105, 107, 102, 41, 39, 24, 20, 20, 10, 9 and 0 all
confirm, together with every `psl211_endpoints` column.

The derived total is also wrong. The three edited files are the new
`lib/var_dist_supp.v`, `instances/kim2025/five_card_rows.v` and
`manifest/pgg_analysis_manifest.v`. `five_card_rows.v` is itself one of the
seven, so the landing recompiles **nine** distinct files, not eight.

This is the number the whole S10 home argument rests on, it is presented as the
honest replacement for a withdrawn round-1 claim, and a corrected figure that
is itself wrong is worse than an uncorrected one. It also has a second branch
the paragraph does not price: `STATUS.md:594-596` leaves `card_tnth_count`
between `lib/` and `den_boer_encoding.v`, and the latter has 16 reverse-
dependants, which I confirm.

Replacement for `STATUS.md:574`:

```
| `manifest/pgg_analysis_manifest.v` | 7 | no |
```

Replacement for `STATUS.md:628-635`:

```
That home is chosen for the recompile cost, which this makes honest:
`five_card_rows.v` has no reverse-dependants, the new `lib/` file has none
by construction, and `manifest/pgg_analysis_manifest.v`, which a landing
must also edit, has seven: `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v`, `manifest/pgg_analysis_client.v` and the
four `*_rows.v` files. `five_card_rows.v` is one of those seven, so a
landing recompiles nine files in all, and no figure in the
reverse-dependency table above applies to it. That figure holds on the
branch where `card_tnth_count` goes to `lib/`; sending it to
`den_boer_encoding.v` instead adds that file and its 16 reverse-dependants.
The round-1 text spread thirteen declarations over six files with
reverse-dependency counts of 24, 20, 20, 16, 10 and 9 while claiming the
cost of one file; that claim is withdrawn.
```

### Should fix

**S1. `den_boer_layout_law_const` names the wrong carrier.**
SHOULD-FIX. `five_card_sc_const_probe.v:49-53`.

"this is that census read as a distribution on card positions". The statement
is `fdistmap (tnth (den_boer_layout x)) (fdist_uniform (card_ord 5))`, whose
domain is the five deck positions and whose value is the card at the drawn
position, an element of the image of `encode_bool`. The law is on the cards,
not on the positions. Both carriers are literally `'I_5`, so the kernel cannot
separate them, and the probe uses "card position" for the index everywhere
else, including two lines above in the same comment ("at a uniformly chosen
position"). The tree does call `encode_bool`'s value a card position at
`instances/denboer1989/five_card_program.v:138`, so the clause is not flatly
false, but it obscures the one thing the sentence exists to say, which is that
the reader ends up looking at the colour census and not at a position.

```
(* The card at a uniformly chosen position has the same law at every
   committed pair. The arrangement moves with the two bits and the colour
   census does not, and this is that census read as the law of the card
   drawn. It is the level at which the spectral arm's two run arguments
   become indistinguishable to a single seat. *)
```

**S2. "what pgg_analysis_status.v admits at that transfer status" claims a
check that does not exist.**
SHOULD-FIX. `kim_spectral_rows_probe.v:94-97`.

`publish` takes the `TransferStatus` as a plain argument
(`manifest/pgg_tableau.v:691-696`) and nothing relates it to the certificate.
The status is claimed against a criterion stated in prose at
`manifest/pgg_analysis_status.v:63-73`, which is the honest description and the
one the whole S8 argument turns on. "admits" reads as an admission rule the
elaborator enforces.

```
(* Kim's repeated row certified by the spectral arm and published at
   IdealFinite. The status is a parameter of publish and nothing checks it,
   so it is claimed against the criterion pgg_analysis_status.v states for
   IdealFinite: a cut-carrier transfer whose base premise is discharged,
   which is what a certificate comparing a finite shuffle with a named
   ideal cut supplies. *)
```

**S3. The `_bare` comment misdescribes what the `Fact` lacks.**
SHOULD-FIX. `kim_spectral_rows_probe.v:287-288`.

"five_card_pow2_39_split alone is an identity at one field" is inherited from
`pow2_split` and is wrong about the declaration it now names.
`Fact five_card_pow2_39_split (R : realType)` is quantified over every real
field. What it lacks against `conclude`'s expected type is the index argument,
which is why `fun R _ =>` closes it.

```
(* The reprice obligation is one identity per real field and per index.
   five_card_pow2_39_split is quantified over the field alone, so it does
   not have the shape conclude asks for. *)
```

**S4. "The five row programs" is now four.**
SHOULD-FIX. `STATUS.md:709`.

The N4 row of the disposition table says "The five row programs are
`five_card_row_*`". F1 deleted `kim_row_biased_spectral_static`, as
`STATUS.md:746-747` and `:770-774` both record, so four remain. The two
sections contradict each other.

```
| N4 | The four row programs are `five_card_row_*`, matching the three programs already in `five_card_rows.v`. Round 1's fifth program is deleted by F1. |
```

**S5. `kim_biased_cert_eps_lt2` says the row excludes readings.**
SHOULD-FIX. `kim_spectral_rows_probe.v:159-162`.

"The row therefore excludes readings that the trivial bound permits". What the
row bounds is a variation distance between the law of one coalition's reading
at one committed pair and its law at another. It excludes pairs of laws that
are far apart, which is a statement about distinguishability and not about
readings. The number itself is right: `sqrt 5 / 40` is 0.0559, which is 2.8 per
cent of the ceiling 2.

```
(* The one-cut row's bound is below two, the ceiling var_dist_le2 gives for
   a variation distance. The row therefore rules out a coalition telling the
   two committed pairs apart with certainty, which a bound at the ceiling
   would not. At about three percent of the ceiling it is not a strong
   statement. *)
```

### Notes

| ID | Location | Observation |
|---|---|---|
| a | `STATUS.md:55-57` | "the 3.3 s added are that new comparison and the two `Fail`s". Round 1 had three recorded `Fail`s and round 2 has four, so exactly one `Fail` is new, `five_card_row_biased_inv25_rowE`. The other two row-equation `Fail`s existed before under their round-1 names and cannot account for added time. The rest of the added time is the two new lemmas, `five_card_row_biased_ideal_publishedE` and `five_card_row_biased_forms_publishedE`, less the two deleted ones. |
| b | `STATUS.md:92` | "the proof is six lines". The proof of `var_dist_le2` in the file runs nine lines between `Proof.` and `Qed.` The six is the soundness auditor's figure for `A4_var_dist_le2`, carried across. |
| c | `STATUS.md:504`, `:506` | Two cited ranges are off. The docstring of `five_card_row_repeated_tableau` is `five_card_rows.v:382-388`, not `:383-389`; the docstring of `five_card_row_biased_tableau` is `:393-399`, not `:396-400`. The other six items in that list, including `:456-458`, `:460-464` and `:469-475`, are exact. |
| d | `kim_spectral_rows_probe.v:118-125` | Two comment blocks sit between the section banner and `five_card_pow2_39_split`: the statement comment, then a note that the `mulr_natl` and `mulr_natr` routes fire inside the numeral. The split is the right shape and the note is accurate. The landing plan must carry the consequence of N24: the first block becomes `(** ... *)` and the second must stay `(* ... *)`, or a coqdoc pass renders proof strategy as part of the statement. Moving the note below `Proof.` removes the hazard. |
| e | `five_card_rotation_probe.v:76-79` and `:90-94` | The clause "the alphabet is the five powers of one five-cycle, so a word shuffle never leaves the rotation group however long the word is" appears in both comments, nearly verbatim, on two adjacent declarations. One of the two should carry it and the other should say what it adds. |
| f | `kim_spectral_rows_probe.v:126`, `:344` | `five_card_pow2_39_split` and `five_card_inv50_split` are identities over a `realType` carrying an instance prefix. Accepted at section 2(a) as a home marker. If a later pass moves them to `lib/var_dist_supp.v` the prefix must go with the move, since nothing in either statement is about five cards. |
| g | `five_card_rotation_probe.v:34-37` | The comment now claims only that the order of the rotation group divides five, which is what `fc_sigma ^+ 5 = 1` gives on its own. `fc_sigma_pow_ord_inj`, twenty lines below, gives injectivity of `k |-> (fc_sigma ^+ k) s` on `'I_5`, hence `fc_sigma ^+ 0 <> fc_sigma ^+ 1`, hence order exactly five. Round 1's N12 said nothing in the file proves it; the file does. The weakened comment is honest and no change is needed, but a landing that wants the exact order has it. |
| h | `five_card_sc_const_probe.v:46` and `:91` | `Section five_card_static_obs_const` encloses `Lemma five_card_static_obs_const`. It compiles, and the same shape existed before the fix under the old name, but a section and a lemma with one name is avoidable. `Section five_card_static_obs` reads better. |
| i | `STATUS.md:766` | `b \\in codom f`, a double backslash left by escaping. Should be `b \in codom f`. |
| j | `STATUS.md:765-787` | The remit names six deviations; the section carries five bullets. The third covers two identities, which is presumably the sixth. Worth splitting so the count is checkable. |
| k | `kim_sc_close_probe.v:48` and `:96` | Two orientation observations, neither needing a change. `kim_biased_sample_cut_witnessE` states `sw_rho_dist ... = sa_cut_dist ...`, the reverse of the tree's `den_boer_sample_cut_witnessE` at `five_card_exec.v:991`, but the orientation is forced by `sc_Hd`'s type. `kim_biased_marginal_bound`'s comment describes `sw_bound` exactly as `reconstruct/algebraic_rigidity.v:149` documents it. |

---

## 4. What was checked and found correct

Recorded so that a later pass does not re-audit it.

- Every renamed declaration's comment was read in full against the pre-fix
  text. The replacements C1 through C11 of round 1 are applied verbatim where
  round 1 supplied them.
- `cert_eps = sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)`
  (`manifest/pgg_tableau.v:345-347`), and the transfer proof at `:562-570`
  spends `sw_bound_eps (sc_b cert)` once per run argument through
  `var_dist_fdistmap_transfer` and the ideal. So `kim_biased_epsE`'s "the
  triangle inequality through the ideal spends the number once for each of the
  two committed pairs" and `five_card_pow2_39_split`'s "publishes its marginal
  bound twice" are both exact.
- `kim_one_cut_centiE` (`five_card_kim.v:661`) is an equality to `1 / 50`, so
  `kim_one_cut_centi_le`'s comment is accurate and the name says which equation
  it weakens.
- `five_card_row_biased_forms_publishedE`'s numbers are right:
  `kim_biased_cert` publishes `sqrt 5 / 40` and `kim_biased_cert_exact`
  publishes `1 / 25`. `AnalysisPathRow` has five fields and no `Prop`
  (`manifest/pgg_analysis_manifest.v:707-725`, "It stores no theorem" at
  `:702`), so the sentence about what a row equation cannot say is correct.
- Both `publishedE` lemmas' comments match the manifest: `five_card_row_biased`
  (`:766-768`) is `AnalysisBridged`, `StaticExecutedOnly`,
  `BaselineClassicalOnly`, and `five_card_row_repeated` (`:776-778`) is
  `Sampled`, `NoModelComparison`, `BaselineClassicalOnly`. The docstring
  descriptions at `STATUS.md:483-484` are accurate quotes.
- `publish` always builds at `AnalysisBridged`
  (`manifest/pgg_tableau.v:691-696`), as `STATUS.md:448-450` says.
- `fc_arrange_countE` is true for every `pred bool`, and the census is three
  and two at all four committed pairs, matching `STATUS.md:192-199`.
- "static endpoint reading" is the tree's own phrase for `static_coalition_obs`
  (`protocol/pgg_instance.v:73,476`). "reading" is used consistently; "view"
  and "observation" do not appear as prose synonyms for it anywhere in the five
  files.
- `fdistmap_inj_uniform`'s conclusion is `fdist_uniform_supp (f @: setT)`
  (`security/pgg_collusion_bound.v:572`), so N21's clause is exact.
- The `StaticExecutedOnly` story is consistent end to end: the third program and
  its `rowE` are deleted, both row equations against the manifest are recorded
  `Fail`s, and no sentence in `STATUS.md` or the five files still claims the
  biased row needs no manifest change.
- Eighteen `Print Assumptions` commands, distributed 5/4/3/2/4 as
  `STATUS.md:686-689` states.
- No `Admitted`, `Axiom`, `admit`, `Abort`, bare `auto`, `intuition`, `tauto`
  or `omega` in any of the five files.

---

## 5. What a landing plan must carry, beyond round 1's list

1. B1: "constancy" everywhere, in the five files and in `STATUS.md`, and in the
   rewritten header of `five_card_rows.v` that N6 already requires.
2. B2: the corrected `kim_centi_cert40` comment.
3. B3: the corrected reverse-dependency figure, the nine-file total, and the
   second branch for `card_tnth_count`.
4. S1 through S5.
5. NOTE d: the `(**` and `(*` split at `five_card_pow2_39_split` when the
   comments are converted to the target file's shape.
6. NOTE f: if the two identities move to `lib/`, the instance prefix moves with
   them.
