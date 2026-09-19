# Soundness audit, round 5: the fourth fix pass, delta only

Independent audit, 2026-09-19. Round 1 is `soundness-audit.md` (F1-F9), round 2
`soundness-audit-round2.md` (G1-G7), round 3 `soundness-audit-round3.md`
(H1-H10), round 4 `soundness-audit-round4.md` (I1-I8). No Rocq compiler was run
in this round, on the coordinator's instruction: the main session recompiled all
five probe files from source after the fourth fix pass with real exit status 0
and verified that, comments stripped, the five files are identical to the
versions round 4 audited. I re-verified that identity myself with a
comment-stripping script: all five are byte-identical to their `before-fix4`
copies once comments are removed. Every other claim below is checked against the
source at this revision with Python and `grep`. No repository file was edited.
This file is the only one written. I wrote none of what I audit.

Scope is the delta: `diff history/STATUS.2026-09-19-before-fix4.md STATUS.md`,
380 lines, and every changed or added passage in it. The mathematics was
confirmed sound in all four previous rounds and is not re-audited.

**VERDICT: NO-GO** for "the probe's claims are true as stated, STATUS.md
contains no false landing item and no claim of completeness, and the result may
be folded into the spec and reported to the user".

One blocking finding, J1. It is not a new defect: it is the sentence round 4
raised as I1, corrected in the paragraph round 4 quoted and left standing in a
second place, the H4 disposition row at `STATUS.md:1899`. That row now
contradicts the corrected paragraph at `:801-814` and the I1 disposition row at
`:1956`. It is a text fix of one clause. No proof changes and no re-proving.

Everything else in the delta that I could check against a source checks out, and
several of the additions are stronger than they needed to be. In particular the
twenty-nine-declaration enumeration matches, member for member, a set I computed
independently from the `.glob` and `.v` files, and the cone numbers 12, 13, 6 and
union 17 reproduce exactly.

---

## 1. Disposition of I1-I8, S4-1 to S4-4 and B4-2 to B4-4

| ID | Round-4 severity | Disposition | Evidence checked this round |
|---|---|---|---|
| I1 | BLOCKING | **Applied in the paragraph, NOT applied in the H4 disposition row. See J1.** | Section 2 below. The replacement account at `STATUS.md:779-814` is right in all six of its parts and every citation in it holds. |
| I2 | BLOCKING | **Applied, correct.** | Section 3. The four added propositions are at `manifest/pgg_analysis_manifest.v:301-302`, `:351-354`, `:355` and `:379-380`, each verbatim, and the closing sentence at `:972-981` opens the list instead of closing it. |
| I3 = B4-1 | should-fix / blocking | **Applied, and the numbers reproduce.** | Section 4. 56 declarations, cones of 12, 13 and 6, union 17, same members, same file attributions. One overstatement about the published listing, J4. |
| I4 = S4-4 | SHOULD-FIX | **Applied, correct, and exact.** | Section 5. The twenty-nine are the twenty-nine. The four added S10 rows cover the eight declarations that had none. The form-2 rule is right against PGL(2,7). |
| B4-2 | BLOCKING | **Applied, correct.** | `STATUS.md:696-699` now says section 7 "has three theorems to alias: `kim_centi_cut_mixing` and `kim_biased_cut_mixing` for the two models' mixing fields, and `five_card_static_obs_const` for the constancy field they share". Three is what the aliases count: the two mixing fields are `kim_spectral_rows_probe.v:73` and `:87`, the constancy field is shared, `:74` and `:88`. |
| B4-3 | BLOCKING | **Applied, correct.** | `STATUS.md:911-917`. I grepped `instances/kim2025/five_card_rows.v` for `StaticExecutedOnly`, `IdealFinite`, `NoModelComparison`, `AnalysisBridged`, `apr_completion`, `apr_transfer` and `published_row` over code lines. Outside the five declarations already in the list above (`:390`, `:401`, `:456`, `:465`, `:473`), the only hits are `:348`, the body of `five_card_row_uniform_rowE`, and the `publish StaticExecutedOnly BaselineClassicalOnly` at `:342` inside `five_card_row_uniform_tableau` (`:338`). Both are about the uniform row. `:175` and `:409` carry `Tableau Observed` and `Tableau Sampled`, which are a program's own level and not a manifest row's, so the sentence's restriction is the right one. |
| B4-4 | BLOCKING | **Applied, correct, and the new comment is true of the lemma.** | The one `.v` change, `five_card_rotation_probe.v:91-95`. The lemma at `:96-99` quantifies over `L` and over `W`. The two derived laws are `kim_single_cut_supp_pow` (`:145-149`), whose bundle is `fc_kim_security_bundle R (1 / 100) (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1`, and `kim_centi_cut_supp_pow` (`:154-157`), whose bundle is `kim_security_bundle_centi R`, pinned by `manifest/pgg_analysis_manifest.v:1238-1243` to `rho_from_words_weighted 7 fc_kim_gens (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))`. So the two do share the bias one hundredth and differ only at lengths 1 and 7, and the length quantifier is what carries one to the other. |
| S4-1 | should-fix | **Applied, correct, and exact.** | Section 6. All eleven lines verified, and a whole-word grep over the twelve production directories returns no twelfth. |
| S4-2 = I5 | should-fix / note | **Applied, correct.** | `manifest/pgg_analysis_manifest.v:753` ends with the word "reaching", so `:753-755` is the range the quotation needs. The body citation at `STATUS.md:639` and the H1 disposition row at `:1897` both now read `:753-755`. One new citation of the same class was introduced this pass, J8. |
| S4-3 = I7 | should-fix / note | **Applied, correct.** | The superseded paragraph is `history/STATUS.2026-09-19-before-fix3.md:680-685`. It names eight declarations individually and covers four more by the suffixes `prefixE` and `modelE`, which is twelve of the twenty-six. `STATUS.md:917-919` now says exactly that. |
| I6 | note | **Applied, correct.** | Item 5 at `STATUS.md:846-856`. Both clauses of the docstring are named and each gets its own reason. The second reason is right: `five_card_rows.v:384-385` asserts agreement between the program's level and the manifest's, and a landing moves the manifest's while the program keeps `Sampled`. This is correctly distinguished from item 2 at `:822-829`, where `five_card_rows.v:28-30` claims only that the programs stop at `Sampled`, which stays true. Citation overhang, J8. |
| I8 | note | **Applied, correct.** | `STATUS.md:932-934`, "one per compile: `coqc` halts at the first error, so the pass is an iteration and not a single run that lists them all". True of `coqc`. |
| vocabulary | owner's rule | **Applied, correct.** | `STATUS.md:1675-1677` now reads "the sum of absolute differences, `\sum_a \|P a - Q a\|`, twice the total variation distance, so the ceiling is 2. That ceiling is `var_dist_le2`." infotheo defines `var_dist P Q := \sum_(a : A) `\|P a - Q a\|` (`probability/variation_dist.v:33`) and `var_dist_injective_probe.v:41-42` states `var_dist P Q <= 2%:R`. A whole-word grep for the Lebesgue-exponent spelling returns nothing in STATUS.md or in the five `.v` files. |

---

## 2. J1. BLOCKING. The H4 disposition row still makes T0 an obligation

### 2.1 What the corrected paragraph now says, and it is right

`STATUS.md:779-814` is the replacement I1 asked for, and it is correct in every
part I could check.

The landing ADDS four programs and KEEPS the two `Tableau Sampled` values
(`:779-784`). The four programs are full chains from `five_card_committed`, and
the four citations hold: `kim_spectral_rows_probe.v:100-104` is
`five_card_row_repeated_spectral_tableau`, `:110-114`
`five_card_row_biased_ideal_tableau`, `:284-289` `five_card_row_repeated39`,
`:360-366` `five_card_row_biased_inv25`, and each opens with
`five_card_committed`.

The reason given for the four surviving lemmas is now the type of the two kept
values (`:784-789`), not what the certified programs continue from. The four
lemmas are `five_card_row_repeated_prefixE` (`five_card_rows.v:418-425`),
`five_card_row_biased_prefixE` (`:428-435`), `five_card_row_repeated_modelE`
(`:441-444`) and `five_card_row_biased_modelE` (`:447-450`), each applying
`tableau_at` or `sp_f (tableau_at ...)` to one of the two values, as the source
shows. The recorded `Fail five_card_row_biased_at_manifest_level` (`:473-475`)
keeps its present reason, the level gap. `five_card_row_repeated_at_manifest_level`
(`:456-458`) still breaks, and item 1 at `STATUS.md:816-821` says so and says
why, independently of the decision.

The replacement universal at `:803-811` is true. Every certified program in the
production tree chains from its own instance's prefix at a level below
`Sampled`. I enumerated them: `pgl27_row_exact_tableau`
(`instances/pgl27/pgl27_rows.v:270`) and `pgl27_row_word_tableau` (`:295`) from
`pgl27_dealt` (`:124`, `Tableau Observed`); `pgl27_row_word39` (`:378`) also from
`pgl27_dealt`; `s5_row_rand_tableau` (`instances/s5/s5_rows.v:275`) from
`s5_supplied` (`:166`, `Tableau Observed`); `psl211_row_alldecks_tableau`
(`instances/psl211/psl211_rows.v:175`) from `psl211_alldecks_prefix` (`:126`,
`Tableau Observed`); `five_card_row_uniform_tableau`
(`instances/kim2025/five_card_rows.v:338`) from `five_card_committed` (`:175`,
`Tableau Observed`). Four distinct prefixes, all `Tableau Observed`, which is
what `:810-811` says. The enumeration omits one program, J9 below, and the
universal survives the omission.

The T0 citation is right. `notes/20260919-tableau-three-extensions-probe-design.md:169`
is row T0 and reads "Two programs can continue from one named `Tableau Sampled`
value", with "Nothing in the tree does this today" in its own evidence column,
which is what `STATUS.md:812-814` reports.

### 2.2 The sentence that was not corrected

`STATUS.md:1899`, the H4 row of the "Round 3 audits and what changed" table,
closes:

> The list also records that no program in the tree continues from a named
> `Tableau Sampled` value today, so the construction is unverified and is row T0
> of `notes/20260919-tableau-three-extensions-probe-design.md:169`.

"The construction" in that row is the construction the H4 decision asks for,
which in the superseded paragraph
(`history/STATUS.2026-09-19-before-fix4.md:792-799`) was writing the four
certified programs as continuations of the two named `Tableau Sampled` values.
The fourth fix pass removed that construction from the decision: the four are
full chains from `five_card_committed`, and the landing performs no continuation
from a named `Tableau Sampled` value at all.

So the row asserts three things that the document no longer supports.

1. That the list "also records" the construction as unverified. It does not.
   `:811-814` records that the landing does not need T0.
2. That "the construction is unverified". The construction the landing performs
   is the one the probe compiled, four times, and the file records the four
   programs' line ranges.
3. That the construction "is row T0". `:811-814` says T0 is another design and
   no obligation of this landing, and `:1956` says "T0 is recorded as no
   obligation of this landing."

`:1899` and `:1956` cannot both be true, which is the standard's clause (e), and
`:1899` states a wrong reason for what a landing must do, which is clause (b).

This is not a frozen historical record. The same table was edited by this pass:
the H1 row at `:1897` had its citation changed from `:754-755` to `:753-755`. The
table is maintained as live present-tense prose about the state of this document
("The decision is stated at the head of the `five_card_rows.v` list", "The list
also records that ..."), so a reader is entitled to read the H4 row against the
current list.

**Exact correction.** Replace the final sentence of `STATUS.md:1899` with:

> The list also records that no program in the tree continues from a named
> `Tableau Sampled` value today, which is row T0 of
> `notes/20260919-tableau-three-extensions-probe-design.md:169`; the four
> certified programs are full chains from `five_card_committed`, so the landing
> does not perform that construction and T0 is no obligation of it.

Nothing else in the row changes. The type argument in it is right and was
checked in round 4.

I grepped STATUS.md for every other mention of T0, of
`20260919-tableau-three-extensions`, of "`Tableau Sampled` value" and of
"continue from". `:812-813` and `:1956` are the only other sites and both are
correct. `:1899` is the single remaining one.

---

## 3. I2: the four added propositions

The four bullets at `STATUS.md:960-970` are each verified against
`manifest/pgg_analysis_manifest.v` at this revision.

| bullet | cited | source | verdict |
|---|---|---|---|
| the biased path carries no shuffle certificate | `:301-302` | `:301` `\| bound or certificate \| none; kim_leak_bound is the numeric constant of` and `:302` `the bridge theorem, not a shuffle certificate \|` | verbatim; Row 4, whose typed row at `:310` is `five_card_row_biased` |
| the repeated path's bound-or-certificate list is those four bundles and bounds | `:351-354` | `:351` opens `\| bound or certificate \| FiveCardAnalysis.kim_bundle,` and `:352-354` carry `centi_bundle`, `endpoint_bound`, `deal_centi_lt \|` | verbatim, and four is the count |
| the repeated path has no final bridge theorem | `:355` | `\| final bridge theorem \| NONE \|` | verbatim |
| the existing certificate bundle does not raise the level | `:379-380` | `:379` ends `A ShuffleCertificate-` and `:380` is `Bundle exists for both models and does not raise the level.` | the quotation rejoins the identifier across the source's line break, which the file's own conventions make unambiguous |

The list is eleven bullets: the original seven at `:945-959` and these four. The
closing paragraph at `:972-981` now reads "Those eleven propositions are the ones
found so far. The list of propositions is no more complete than the list of
places, and it is open." That withdraws the completeness claim I2 was raised
about, and the instruction to extend the list from the Row 3, Row 4 and Row 5
tables and the facade's section 7 before searching is a rebuild instruction that
works.

The claim that "the seven before them reached none of the four" holds: none of
the seven bullets contains the words "shuffle certificate", "bound or
certificate", "final bridge theorem" or "raise the level", and bullet 4's "no
transfer-layer result exists" is a different form of words from
`final bridge theorem | NONE`.

I grepped STATUS.md for "complete", "every", "all of", "full list", "nothing
else", "no other", "exhaust" and "the ones" over the landing material and the
propositions list. No surviving sentence claims or implies that either list is
complete. `:23`, `:531-532`, `:972-973` and `:1049` all disclaim explicitly.

The four back-references in that paragraph are stale, J2.

---

## 4. I3: the cone script and its numbers

The added paragraph at `STATUS.md:1351-1366` is correct in its substance. The
`.glob` files beside the probe carry modification times of 2026-09-19 10:01 and
10:02, after the last `.v` edit at 09:59, so they do match the sources.

I ran the published listing against them. Filling `G` with the probe directory
and adding a driver that calls the listing's own `closure` on the three roots, I
get, byte for byte, the output printed at `STATUS.md:1447-1508`:

    declarations found: 56
    cone of kim_centi_cut_mixing: 12
    cone of kim_biased_cut_mixing: 13
    cone of five_card_static_obs_const: 6
    union of the three cones: 17

Same members, same file attributions, in the same order. The union is the four
generic lemmas `var_dist_fdistmap_supp_inj`, `fdistmap_inj_uniform_id`,
`fdistmap_neq0_codom` and `card_tnth_count` together with thirteen
instance-specific ones; adding the three theorems themselves gives the sixteen
that move, which is the fourteen dagger rows of the S10 table
(`STATUS.md:1141-1154`) counted by declaration.

The claim that both round-4 auditors reproduced 12, 13 and 6 from the sources
alone is borne out by their files.

The historical claim about the stale run printing 0, 1, 6 and a union of 7 cannot
be checked, since those `.glob` files were overwritten. It is consistent with
round 4's I3.

One overstatement, J4: the listing as published cannot print anything.

---

## 5. I4: the twenty-nine, the four added S10 rows, and the form-2 rule

### 5.1 The counts

I enumerated every top-level declaration in the five files with a
comment-stripping script, excluding the five `Variable R` section variables:

    kim_spectral_rows_probe.v      31
    kim_sc_close_probe.v            6
    five_card_sc_const_probe.v      3
    five_card_rotation_probe.v      9
    var_dist_injective_probe.v      7
                                   --
                                   56

which is the "declarations found: 56" the cone script prints. Five of the 56 are
recorded `Fail`s, four in `kim_spectral_rows_probe.v` and
`var_dist_const_reader_mutation` in `var_dist_injective_probe.v`, leaving 51 real
declarations. Sixteen move, six are the generic lemmas of
`var_dist_injective_probe.v`, and twenty-nine stay. Every count in
`STATUS.md:1191-1195` and `:1249-1251` is right.

### 5.2 The enumeration

I computed the set of twenty-nine independently: the 51 real declarations minus
the six generic ones minus the transitive cone of the three theorems. The result
matches `STATUS.md:1252-1274` member for member, all twenty-nine, with no
declaration in one and not the other:

    kim_centi_cert, kim_biased_cert, kim_centi_cert40, kim_biased_cert_exact,
    kim_biased_sample_cut_witnessE, kim_centi_marginal_bound40,
    kim_biased_marginal_bound_exact, five_card_row_repeated_spectral_tableau,
    five_card_row_biased_ideal_tableau, five_card_row_repeated39,
    five_card_row_biased_inv25, kim_centi_cert_epsE, kim_centi_cert_eps_lt,
    kim_biased_cert_epsE, kim_biased_cert_eps_lt2, kim_centi_cert40_epsE,
    five_card_row_repeated_spectral_publishedE,
    five_card_row_biased_ideal_publishedE,
    five_card_row_biased_forms_publishedE, five_card_pow2_39_split,
    five_card_inv50_split, five_card_reprice39, five_card_reprice_inv25,
    five_card_reprice_inv25_lt2, kim_biased_epsE, kim_biased_exact_le_eps,
    kim_one_cut_centi_le, kim_centi_cut_mixing40, kim_biased_cut_mixing_exact

The internal counts in the sentence hold too: four certificates, one tying field,
two form-2 marginal bounds, four row programs, eight number and published-field
lemmas, two repricing identities, three repricing definitions and bounds, two
bundle-number lemmas, one per-card-position bound, two form-2 mixing statements,
which sums to 29.

The accompanying no-cycle claim is right. Running the listing's own edge relation,
there is no edge from any of the sixteen that move to any of the twenty-nine that
stay. Fourteen edges run the other way, which is the expected direction.

### 5.3 The four added S10 rows

Before this pass, eight of the twenty-nine appeared in no row of the S10 table:
`five_card_reprice39`, `five_card_reprice_inv25`, `five_card_reprice_inv25_lt2`,
`kim_biased_epsE`, `kim_biased_exact_le_eps`, `kim_one_cut_centi_le`,
`kim_centi_cut_mixing40` and `kim_biased_cut_mixing_exact`. The four rows added
at `STATUS.md:1156-1159` cover exactly those eight, three plus two plus one plus
two. After the addition every one of the 51 real declarations has a row.

### 5.4 The form-2 rule

`STATUS.md:1276-1288` states the rule: what the facade aliases is the mixing
field of the certificate a landed row publishes, which the manifest then names as
that row's base premise, so the two form-1 rows written above publish
`kim_centi_cert` and `kim_biased_cert`, whose mixing fields
(`kim_spectral_rows_probe.v:73`, `:87`) are the two that move; publish a form-2
row instead and the form-2 mixing statement takes the dagger and the form-1 one
loses it.

This is right against PGL(2,7), which is the precedent the coordinator named.
`pgl27_row_word_tableau` (`instances/pgl27/pgl27_rows.v:295-304`) builds its
certificate inline with `mixing by pgl27_word_mixing R` at `:302`, and
`pgl27_word_mixing` is aliased in the facade at `instances/pgl27/pgl27_analysis.v:267`.
The second published PGL row, `pgl27_row_word39` (`:378-383`), carries
`pgl27_word_cert`, whose mixing field is the same `pgl27_word_mixing` (`:255`),
so PGL(2,7) has one mixing statement serving both forms and offers no
counterexample to the rule.

The rule is stated the same way everywhere it appears. `:1191-1195` lists the two
form-2 statements as staying; S10 row `:1159` gives them no dagger, which means
staying under the convention set at `:1130-1131`; `:1959`, the I4 disposition,
repeats the rule in the same words. The swap the rule describes preserves both
counts, 29 staying and 16 moving, under either form choice, so no other sentence
in the file needs adjusting for it. One overreach in the wording, J11.

---

## 6. S4-1: the nine spelled-type `Check`s at eleven lines

Every citation added at `STATUS.md:749-764` is verified in the source.

    manifest/pgg_analysis_client.v:41  Check FiveCardAnalysis.centi_sample.
    manifest/pgg_analysis_client.v:43  Check FiveCardAnalysis.biased_family.
    manifest/pgg_analysis_client.v:44  Check FiveCardAnalysis.centi_family.
    instances/kim2025/five_card_analysis.v:402  Timeout 60 Check (FiveCardAnalysis.centi_sample : ...)
    manifest/pgg_analysis_manifest.v:1177  Check (FiveCardAnalysis.single_biased_sample : ...)
    manifest/pgg_analysis_manifest.v:1182  Check (FiveCardAnalysis.repeated_sample : ...)
    manifest/pgg_analysis_manifest.v:1187  Check (FiveCardAnalysis.centi_sample : ...)

and five further spelled-type `Check`s in the manifest opened at `:1207`,
`:1214`, `:1221`, `:1233` and `:1245`, carrying the searched names at seven
lines: `single_biased_sample` at `:1210`; `repeated_sample` at `:1217`, at
`:1225` and `:1229` inside `repeated_seat_distE`, and at `:1248` and `:1253`
inside `centi_repeated_seat_distE`; `centi_sample` at `:1235`. That is nine
spelled-type `Check`s, eight of them in the manifest, with the names on eleven
lines, which is what the sentence says.

A whole-word grep for `single_biased_sample`, `repeated_sample`, `centi_sample`,
`biased_family` and `centi_family` over `lib protocol groups security smc
reconstruct instances manifest` returns 29 lines and no site outside the ones the
sentence names: the facade's header table at `:45-47` and its aliases at
`:202-222`, the manifest's header-table lines `:293`, `:315`, `:322`, `:340`,
`:341` and `:370`, the row definitions at `:768` and `:778`, the three client
`Check`s, and the eleven `Check` lines above. `pgg_analysis_client.v:42` is
`uniform_family`, correctly excluded.

---

## 7. The three audit numbers the fix pass corrected

All three corrections are right, and in each case the audit was wrong.

**Row 5 cells.** Round 4's I2 cited `STATUS.md:606` and `:607` for the Row 5
bound-or-certificate cell and the final-bridge-theorem cell. In the file round 4
read, `history/STATUS.2026-09-19-before-fix4.md`, those cells are at `:605` and
`:606`; `:606` there is the final-bridge cell and `:607` the model-transfer cell.
The fix pass's correction is correct against that file. It is stale against the
current one, J3.

**Eight declarations with no S10 row.** Round 4's I4 named five. Counting the
twenty-nine against the S10 table as it stood, eight had no row; I4's five plus
`kim_biased_epsE`, `kim_biased_exact_le_eps` and `five_card_reprice_inv25_lt2`.
`kim_biased_epsE` is the one that turns on a reading: it ends in `epsE`, and the
S10 row for the rows and the numbers covers "their `epsE` ... declarations",
where "their" is the four row programs. `kim_biased_epsE` is the one-cut bundle's
number (`kim_sc_close_probe.v:119`) and is not one of theirs, so the strict
reading, which is the one the naming audit also took, is right and eight is the
count. The four added rows make the question moot.

**Eleven outside the prose enumerations.** Round 4's naming audit S4-4 named ten.
Subtracting from the twenty-nine the four certificates, the four row programs,
the eight number and published-field lemmas and the two repricing identities
leaves eleven, and the eleventh is `kim_biased_sample_cut_witnessE`, exactly as
the fix pass says. It does have an S10 row, at `:1160`.

---

## 8. Findings

| ID | Severity | Site |
|---|---|---|
| J1 | BLOCKING | `STATUS.md:1899` |
| J2 | should-fix | `STATUS.md:974-975` |
| J3 | should-fix | `STATUS.md:1971-1973` |
| J4 | should-fix | `STATUS.md:1359-1361`, `:1958` |
| J5 | should-fix | `STATUS.md:532` against `:24` |
| J6 | should-fix | `STATUS.md:14-19` |
| J7 | should-fix | `STATUS.md:1950` |
| J8 | should-fix | `STATUS.md:850-851` |
| J9 | note | `STATUS.md:805-811` |
| J10 | note | `STATUS.md:1249-1251` against `:1292-1294` |
| J11 | note | `STATUS.md:1276-1277` |
| J12 | note | `STATUS.md:1282-1284` |

### J1. BLOCKING. The H4 disposition row still makes T0 an obligation

Section 2 above carries the finding and the exact correction.

### J2. SHOULD-FIX. The four back-references in the propositions paragraph are pre-fix4 line numbers

`STATUS.md:973-976`:

> The last four were added in round 4 from this document's own cells, `:589`,
> `:605`, `:606` and `:611`, each of which already records the proposition as
> falsified

Those are the line numbers in `history/STATUS.2026-09-19-before-fix4.md`. At this
revision the file has shifted by two lines at that point: `:589` is the Row 4
table's header row, `:605` the Row 5 table's header row, `:606` its separator,
and `:611` the Row 5 completion-level cell rather than the level-justification
cell. Three of the four now point at table furniture, so "each of which already
records the proposition as falsified" does not hold at the cited lines.

**Exact correction.** Replace "`:589`, `:605`, `:606` and `:611`" with "`:591`,
`:607`, `:608` and `:613`".

### J3. SHOULD-FIX. The correction sentence is right about the old file and stale against the new one

`STATUS.md:1971-1973`:

> Line numbers the audits cite that the source does not bear, corrected while
> applying: I2's citations of this file's Row 5 cells are `:605` and `:606`, not
> `:606` and `:607`.

The correction is right against the file round 4 read. Against "this file" as it
now stands, the Row 5 cells are at `:607` and `:608`, so a reader checking `:605`
and `:606` finds a header row and a separator and would conclude the correction
is itself wrong.

**Exact correction.** "I2's citations of this file's Row 5 cells were `:605` and
`:606` in the revision round 4 read, not `:606` and `:607`; in this revision they
are `:607` and `:608`."

### J4. SHOULD-FIX. The published listing cannot print the output attributed to it

`STATUS.md:1359-1361` says "the script as published reproduces the output below
against them", and `:1958` says "the script as published then prints 12, 13, 6
and union 17".

The listing at `:1369-1442` sets `G = "<directory holding the five .v files and
their .glob files>"`, a placeholder, and ends at the definition of `closure`. It
never calls `closure`, never opens a root, and contains no `print`. As published
it produces no output at all.

The numbers are not in doubt: I reproduced all of them exactly, in the same order
with the same members, by substituting the probe directory for `G` and adding a
nine-line driver over the three roots. Only the attribution is wrong.

**Exact correction.** At `:1359-1361`, "and the listing below, with `G` set to
this directory and a driver calling `closure` on the three roots, reproduces the
output that follows it against them". At `:1958`, the same qualification. Or add
the driver to the listing, which is the better fix, since the point of I3 was
that a later reader can rerun it.

### J5. SHOULD-FIX. Three rounds against four rounds

`STATUS.md:532` opens "Three rounds of audit have each added items the round
before missed", and the enumeration in the next sentence, extended by this pass
at `:539-540`, now names round 2, the search after it, round 3 and round 4.
`STATUS.md:24`, which this pass rewrote, says "Each of four audit rounds added
items the round before missed". The pass updated the count in one place and left
it in the other.

**Exact correction.** At `:532`, "Four rounds of audit have each added items the
round before missed". Or, if round 1 is meant to be excluded from both, change
`:24` to three and say which rounds are counted.

### J6. SHOULD-FIX. The provenance paragraph stops at the third revision

`STATUS.md:14-19` says the file was rewritten after the round-1 audits, revised
again after the round-2 audits, "and revised a third time after two round-3
audits", and points the reader at "Round 1 audits and what changed", "Round 2
audits and what changed" and "Round 3 audits and what changed". This pass is the
fourth revision and added a "Round 4 audits and what changed" section at `:1939`.
A reader following the pointer misses it.

**Exact correction.** Add ", and a fourth time after two round-4 audits" and name
the fourth section in the "See" list.

### J7. SHOULD-FIX. "One `.v` character changed" understates the edit

`STATUS.md:1950-1952`:

> One `.v` character changed in this pass, the statement comment of
> `fc_kim_rho_supp_pow`. Comments stripped, the five files are byte-identical to
> their `before-fix4` copies, and all five recompile with return code 0.

The edit is a five-line rewrite of `five_card_rotation_probe.v:91-95`, not one
character. The second sentence is the load-bearing one and is true: I verified the
comment-stripped identity of all five files myself.

**Exact correction.** "One `.v` comment changed in this pass, the statement
comment of `fc_kim_rho_supp_pow`, five lines of `five_card_rotation_probe.v`."

### J8. SHOULD-FIX. A new citation of the class S4-2 just corrected

`STATUS.md:850-851`:

> The opening clause at `:384`, "The program stops at Sampled, the level the
> manifest records for this row"

In `instances/kim2025/five_card_rows.v`, `:384` ends with "the level the manifest
records" and `:385` opens with "for this row." The quoted clause spans `:384-385`.
This is the same overhang the pass corrected this round for the
`five_card_row_uniform` docstring, `:754-755` to `:753-755`.

**Exact correction.** "The opening clause at `:384-385`".

### J9. NOTE, further seed item. The universal's enumeration omits one certified program

`STATUS.md:805-811` supports its universal with five programs. A sixth exists,
`pgl27_row_word39` (`instances/pgl27/pgl27_rows.v:378-383`), a
`PublishedRowAt pgl27_reprice39` that also chains from `pgl27_dealt`. The
universal at `:803-805` is therefore true and the "all four prefixes" count is
right, since the sixth program adds no new prefix. Naming it would make the
enumeration exhaustive over the production tree, which is what the universal
claims.

### J10. NOTE. "named below" names four of the six

`STATUS.md:1249-1251` says the six that are not among the twenty-nine are "the
generic lemmas of `var_dist_injective_probe.v` named below". Six is right:
`var_dist_le2`, `var_dist_fdistmap_supp_inj`, `var_dist_fdistmap_const_neq`,
`fdistmap_inj_uniform_id`, `fdistmap_neq0_codom` and `card_tnth_count`. The next
sentence at `:1292-1294` names four of them, the four the cone reaches. The other
two are named eighty lines further on, at `:1347-1348`, in the paragraph about the
span cut.

### J11. NOTE. The facade aliases more than mixing fields

`STATUS.md:1276-1277`, "what the facade aliases is the mixing field of the
certificate a landed row publishes", is true of the alias that names a row's base
premise, which is the sense the trailing clause fixes and the sense the rule
needs. Read as a universal about the facade it is too wide:
`instances/pgl27/pgl27_analysis.v` also aliases `pgl27_view_mixing` (`:263`),
`exec_view_indist` (`:256`), `marginal_bound` (`:279`) and others that no
published certificate carries as a mixing field.

### J12. NOTE. A certificate cited at its mixing-field line

`STATUS.md:1282-1284` writes "`five_card_row_repeated39` carrying
`kim_centi_cert40` (`:267`)" and "`five_card_row_biased_inv25` carrying
`kim_biased_cert_exact` (`:344`)". Both lines are the mixing-field lines inside
those certificates, parallel to the `:73` and `:87` citations in the preceding
sentence, rather than the certificates' own opening lines `:260` and `:337`. Both
lines do fall inside the certificate they are attached to, so nothing is wrong;
the parallel is just easier to see if it is stated.

---

## 9. What this round did not re-audit

The mathematics of the five `.v` files, confirmed sound in rounds 1 to 4 and
unchanged at this revision by the comment-stripped identity check. The passages
of STATUS.md outside the fourth-pass delta. The compile times at `:1983-1985`,
which need a compiler.
