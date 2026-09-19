# Soundness audit, round 4: is the probe true and is STATUS.md's landing account free of false items?

Independent audit, 2026-09-19. Round 1 is `soundness-audit.md` (F1-F9), round 2
`soundness-audit-round2.md` (G1-G7), round 3 `soundness-audit-round3.md`
(H1-H10). No Rocq compiler was run in this round, on the coordinator's
instruction: all five probe files were recompiled from source after the third
fix pass with real exit status 0, and, comments stripped, the only code change
since round 3 is one deleted `Require` line in `kim_sc_close_probe.v`. Every
claim below is checked against the source at this revision with Python and
`grep` over the repository. No repository file was edited. This file is the
only one written.

**VERDICT: NO-GO** for "the probe's claims are true as stated, STATUS.md
contains no false landing item and no claim of completeness, and the result may
be folded into the spec and reported to the user".

The mathematics is unchanged and unchallenged, as in all three previous rounds.
The withdrawal of the completeness claim is done properly: S8 is reheaded, the
disclaimers at `:21-31`, `:48`, `:530-541` and `:998-1003` are explicit, and
the `five_card_rows.v` enumeration and the family-name grep are now reported in
full and reproduce exactly against my own scripts. H1, H2, H3, H5, H6, H7, H8,
H9 and H10 are all correctly applied and every line number the fix pass added
checks out.

Two blocking findings remain, both introduced by this fix pass.

- **I1.** H4's decision states a construction that contradicts the probe's own
  compiled programs. All four certified programs in `kim_spectral_rows_probe.v`
  continue from `five_card_committed`, not from the two `Tableau Sampled`
  values, and STATUS.md prints them that way in S6 and S7. The paragraph also
  gives a wrong reason for the four `prefixE`/`modelE` lemmas surviving, and
  supports itself with a universal claim about the tree that is false.
- **I2.** The rebuild instruction closes its own list. "The seven propositions
  above are the ones a spectral landing falsifies" is a completeness claim, and
  at least four propositions that STATUS's own Row 4 and Row 5 tables record as
  falsified are not among the seven.

Both are text fixes. No proof changes and no re-proving.

---

## 1. Disposition of H1-H10, against the source

| ID | Round-3 severity | Disposition | Evidence checked this round |
|---|---|---|---|
| H1 | BLOCKING | **Applied, correct.** | The new S8 subsection "Three further manifest passages about the development, not about a row" (`STATUS.md:615-661`). All three passages read verbatim in the source: `manifest/pgg_analysis_manifest.v:244-248` is the Row 3 `missing premise` cell, word for word as quoted; `:669-673` is the "Five-card development" paragraph of "Absent capabilities", word for word; `:754-755` is the tail of the `five_card_row_uniform` docstring. The anchor claim is right: Row 4 `:306` reads `missing premise | the ideal distribution equality, as in row 3 |` and Row 5 `:358-360` reads `... as in row 3, and in addition ...`, both pointing at `:244-248`. The clause-by-clause reading of `:669-673` is right on all three clauses. See I5 for a one-word citation overhang. |
| H2 | BLOCKING | **Applied, correct, and this is the finding that mattered.** | `security/pgg_collusion_bound.v:977-981` opens `Section var_dist_transfer` and declares `Hypothesis PQ_close : var_dist P Q <= delta.` at `:980` and `Hypothesis ideal_eq : fdistmap fx Q = fdistmap fy Q.` at `:981`, in that order. `spectral_tail` (`manifest/pgg_tableau.v:561-571`) applies `var_dist_fdistmap_transfer` at `:566-568` and discharges `:569` `by rewrite -(sc_Hd cert); exact: (sc_close cert)` then `:570` `exact: (@sc_const _ _ _ _ cert C HC x x')`. So mixing answers the first and constancy IS the second. STATUS's new paragraph at `:455-469` states exactly this with correct citations. Full sweep in section 2. |
| H3 | BLOCKING | **Applied, correct.** | Item 9 of the `five_card_rows.v` list (`STATUS.md:857-867`). `instances/kim2025/five_card_rows.v:78-83` indexes both programs as "stopping at Sampled"; `:84-86` indexes `five_card_row_repeated_at_manifest_level`; `:119-122` says the manifest's level for the biased row is one "which its program does not reach"; `:4` reads "five_card_rows: the five-card instance's three rows, written as programs". All four verbatim. |
| H4 | BLOCKING | **Decided, but the decision as written is wrong. See I1.** | The decision to keep `five_card_row_repeated_tableau` and `five_card_row_biased_tableau` at `Tableau Sampled` is sound and its type argument is right (section 3). What is wrong is the sentence about what the certified programs continue from, the reason it gives for the four lemmas, and the universal claim offered as its evidence. |
| H5 | SHOULD-FIX | **Applied, correct.** | Item 6 of the facade list (`STATUS.md:715-722`). `instances/kim2025/five_card_analysis.v:16-17` reads "Section 7 is empty for this development and is documented as empty rather than omitted." verbatim; `:30-57` is the phase-H1 check table; `manifest/pgg_analysis_manifest.v:67-72` says every identifier in the tables is `Check`ed against its spelled type and every row pinned, which is the pinning obligation STATUS names. |
| H6 | NOTE | **Applied, correct.** | `STATUS.md:883-884` now says "the two `prefixE` lemmas (`:418`, `:428`) and the two `modelE` lemmas (`:441`, `:447`)". The file has exactly two of each, at those lines. |
| H7 | NOTE | **Applied, correct.** | Item 2 is `:28-30` and item 3 is `:33-42`. Read in the source: the sentence "The manifest's two further five-card rows ... both stop at Sampled." occupies `:28-30`; "The repeated row stops there because the manifest does: ... inside it." occupies `:30-33`; "The biased row stops there although ... at this instance." occupies `:33-42`, of which `:39-42` is the spectral-arm clause. All three ranges are what STATUS now states. |
| H8 | NOTE | **Applied, and the rerun reproduces exactly.** | Section 4 below. |
| H9 | NOTE | **Applied, correct.** | Item 2 (`STATUS.md:807-814`) says the sentence is obsolete rather than false, gives the reason under the decision, and marks the next sentence false outright. That matches the decision H4 settles. |
| H10 | SHOULD-FIX | **Applied as a code change, correct.** | `diff history/kim_sc_close_probe.2026-09-19-before-fix3.v kim_sc_close_probe.v` is exactly one deleted line, `From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.` at `:21`. The four cone-bearing probe files now import none of `pgg_analysis_status`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `five_card_analysis` or `five_card_rows`, so the option-2 cycle is closed at the file level as well as at the reference level. |

The second `.v` change this pass, `fc_kim_rho_supp_pow`'s comment
(`five_card_rotation_probe.v:90-95`), is the naming audit's replacement text
verbatim, no line exceeds 80 bytes, and the comment is true of the lemma it
sits on: the statement is quantified over `L` and over `W`, and the conclusion
places every supported cut in the cyclic group generated by `fc_sigma`.

---

## 2. H2 in full: every occurrence of the hypothesis vocabulary

Ground truth, read this round:

    security/pgg_collusion_bound.v:977   Section var_dist_transfer.
    security/pgg_collusion_bound.v:980   Hypothesis PQ_close : var_dist P Q <= delta.
    security/pgg_collusion_bound.v:981   Hypothesis ideal_eq : fdistmap fx Q = fdistmap fy Q.

    manifest/pgg_tableau.v:566-568  apply: (var_dist_fdistmap_transfer R _ _ (sa_cut_dist sa) (sc_ideal cert) ...).
    manifest/pgg_tableau.v:569      - by rewrite -(sc_Hd cert); exact: (sc_close cert).
    manifest/pgg_tableau.v:570      - exact: (@sc_const _ _ _ _ cert C HC x x').

A grep of `STATUS.md` and the five `.v` files for "first hypothesis", "second
hypothesis", "base premise", "missing premise", "ideal distribution equality",
"discharg" returns twenty-four sites. Every one says the right thing.

| site | what it says | verdict |
|---|---|---|
| `STATUS.md:10` | "a cut-carrier comparison with its base premise discharged is `IdealFinite`" | right; `manifest/pgg_analysis_status.v:63-73` defines `IdealFinite` as covering "a cut-carrier transfer whose base premise is discharged" |
| `STATUS.md:206` | "The generic lemma's hypothesis is discharged by S2 before the field is filled" | right; `five_card_cut_mixing_of_supp_pow` carries the support hypothesis and S2's support lemmas discharge it |
| `STATUS.md:443` | quotes `pgg_analysis_status.v` on the base premise | quotation, verbatim |
| `STATUS.md:455-469` | the new paragraph | correct in every clause, citations `:980`, `:981`, `:561-570`, `:569`, `:570` all right |
| `STATUS.md:590` | Row 4 `:305` cell, "the mixing field discharging the inequality's first hypothesis and the constancy field being its second" | correct, and the reverse of what the previous revision said |
| `STATUS.md:591` | Row 4 `:306` cell, "the constancy field `five_card_static_obs_const` is that equality; the mixing field supplies the cut-carrier distance the inequality's first hypothesis asks for" | correct |
| `STATUS.md:608` | Row 5 `:358-360` cell | quotation of the manifest, verbatim |
| `STATUS.md:627`, `:651` | the Row 3 cell and the "Absent capabilities" paragraph | quotations, verbatim, and both call the ideal equality the second hypothesis, which is right |
| `STATUS.md:686-687` | the facade's section header | quotation, verbatim; "no ideal distribution equality to discharge its second hypothesis" is right |
| `STATUS.md:693` | facade item 1, "The constancy field is the ideal distribution equality that discharges the second hypothesis, and the mixing field is the cut-carrier bound the first asks for" | correct |
| `STATUS.md:916-922` | the spellings bullet | quotations |
| `STATUS.md:1152` | "the base premise of the row's own `IdealFinite` status" | right |
| `STATUS.md:1784` | the H2 disposition row | correct, and its closing claim that every "first"/"second hypothesis" was re-read is borne out by this sweep |
| `kim_spectral_rows_probe.v:97`, `:186`, `:370` | "base premise ... discharged" as the criterion for `IdealFinite` | right, against `pgg_analysis_status.v:63-73` |
| `var_dist_injective_probe.v:121` | "The support hypothesis is not discharged at a constant reader" | right; that is what the recorded `Fail` there shows |

No site states the roles backwards. H2 is fully closed.

---

## 3. H4: the decision, its type argument, and what is wrong with it

### 3.1 What is right

The type argument is correct, verbatim against the source.

    manifest/pgg_tableau.v:411-414
      Record TableauAt (b : CompletionLevel) (Q : StackAt b -> Prop) :=
        MkTableau { tableau_at : StackAt b ; tableau_thm : Q tableau_at }.
    manifest/pgg_tableau.v:678-681
      Record PublishedRowAt (c : Reprice) := MkPublishedRow {
        published_at : StackAt AnalysisBridged ; published_row : AnalysisPathRow ;
        published_thm : BridgedProp c published_at }.

`PublishedRowAt` has no `tableau_at` projection, so retyping the two programs
in place would break `five_card_row_repeated_prefixE` (`:418-425`),
`five_card_row_biased_prefixE` (`:428-435`),
`five_card_row_repeated_modelE` (`:441-444`) and
`five_card_row_biased_modelE` (`:447-450`), each of which applies `tableau_at`
or `sp_f (tableau_at ...)`. Read in the source: `:419`, `:421`, `:423` apply
`projT1 (tableau_at ...)` and `sp_obs (tableau_at ...)`; `:442` and `:448`
apply `sp_f (tableau_at ...)`. Under the decision to keep the type, all four go
on compiling. Correct.

The consequences stated for the other items are right too.

- Item 1, `five_card_row_repeated_at_manifest_level` (`:456-458`), ascribes
  `five_card_row_repeated_tableau` at `Tableau (apr_completion
  five_card_row_repeated)`. Moving that manifest row to `AnalysisBridged`
  breaks it, and STATUS is right that this does not depend on the decision.
- Item 7, `five_card_row_biased_levelE` (`:465-467`), states only
  `apr_completion five_card_row_biased = AnalysisBridged` and names no program,
  so it survives. Its docstring at `:461` does say "The program above reaches
  Sampled". Both correct.
- Item 8, the recorded `Fail five_card_row_biased_at_manifest_level`
  (`:473-475`), goes on failing for the level gap, since the biased manifest
  row keeps `AnalysisBridged` and the program keeps `Tableau Sampled` while
  only the transfer status moves. Correct.

The closing enumeration is correct and I reproduced it. `five_card_rows.v` has
31 top-level declaration commands: 28 `Definition`/`Lemma`/`Theorem` and 3
recorded `Fail`s (`:409`, `:473`, `:571`). Four of the 28 and one of the 3 are
in the list, at `:390`, `:401`, `:456`, `:465`, `:473`. The other 24 and 2 are
named individually and every one of the 26 line numbers matches the source.

### 3.2 I1. BLOCKING. The decision states a construction the probe did not build, and supports it with a false claim about the tree

`STATUS.md:774-776`:

> and the certified programs are
> added beside them under the names of S6 and S7. **They become the named values
> the certified programs continue from**, so `five_card_row_repeated_prefixE`
> (`:418-425`) ... go on compiling for their present reasons

`STATUS.md:792-794`:

> The construction the decision asks for is unverified. No program in the tree
> continues from a named `Tableau Sampled` value today: **every certified program
> is written as one chain from `five_card_committed`.**

Three things are wrong here.

**(a) The four certified programs do not continue from those two values.** All
four are written as full chains from `five_card_committed`, and STATUS.md
prints them that way itself:

    kim_spectral_rows_probe.v:100-104   five_card_row_repeated_spectral_tableau
    kim_spectral_rows_probe.v:110-114   five_card_row_biased_ideal_tableau
    kim_spectral_rows_probe.v:284-289   five_card_row_repeated39
    kim_spectral_rows_probe.v:360-366   five_card_row_biased_inv25

each opening `five_card_committed` and then `sample`/`sample_step`. The same
four appear in STATUS.md at `:282-292`, `:344-349` and `:412-417`, in that
form. So the sentence at `:775-776` asserts, as the content of the decision, a
construction the probe compiled nothing for and does not need, and it
contradicts the document's own S6 and S7 sections.

**(b) The reason given for the four lemmas is wrong.** They go on compiling
because `five_card_row_repeated_tableau` and `five_card_row_biased_tableau`
keep the type `Tableau Sampled`, which the preceding clause already says. What
any other program continues from is irrelevant to them. The "so" at `:776`
attaches the right conclusion to the wrong premise.

**(c) The supporting universal is false.** Every certified program in the tree
is written as one chain from **its own instance's prefix**, not from
`five_card_committed`:

    instances/pgl27/pgl27_rows.v:270-275      pgl27_row_exact_tableau  from pgl27_dealt
    instances/pgl27/pgl27_rows.v:295-304      pgl27_row_word_tableau   from pgl27_dealt
    instances/s5/s5_rows.v:275-279            s5_row_rand_tableau      from s5_supplied
    instances/psl211/psl211_rows.v:175-179    psl211_row_alldecks_tableau from psl211_alldecks_prefix
    instances/kim2025/five_card_rows.v:338-342 five_card_row_uniform_tableau from five_card_committed

Only the last chains from `five_card_committed`. The first clause of the
sentence, that no program continues from a named `Tableau Sampled` value, is
true and I confirmed it: the only two named `Tableau Sampled` values in the
tree are `five_card_rows.v:390` and `:401`, and nothing continues from either
(the other `Tableau Sampled` occurrences are two recorded `Fail`s at
`s5_rows.v:192` and `pgl27_rows.v:362`, one `Fail` at `five_card_rows.v:409`,
one `Check` at `s5_rows.v:191`, one `Fail` at `psl211_rows.v:293`, and
`pgg_tableau.v:503-504` where the notation is defined). It is the explanation
after the colon that is false. `five_card_committed` is a `Tableau Observed`
(`five_card_rows.v:175`), so it is not evidence about `Tableau Sampled` values
in either direction.

**Why it is blocking.** The sentence invents a probe obligation the compiled
evidence already makes unnecessary. `notes/20260919-tableau-three-extensions-probe-design.md:169`
records T0 as unverified, which is true, but the landing does not reach T0 if
it copies the four programs the probe compiled. A landing batch reading
`:792-799` as written would either probe T0 first, or copy the wrong shape, and
would carry away a false belief about how the other three instances' rows are
written.

**Exact correction.** Replace `STATUS.md:775-783` with: "The two named values
keep their type, so `five_card_row_repeated_prefixE` (`:418-425`),
`five_card_row_biased_prefixE` (`:428-435`),
`five_card_row_repeated_modelE` (`:441-444`) and
`five_card_row_biased_modelE` (`:447-450`) go on compiling for their present
reasons, each applying `tableau_at` or `sp_f (tableau_at ...)` to a
`Tableau Sampled`, and the recorded `Fail five_card_row_biased_at_manifest_level`
(`:473-475`) goes on failing for its present reason, the level gap between that
program and the manifest's row." Replace `STATUS.md:792-799` with: "The four
certified programs are copied from the probe as they stand, each a full chain
from `five_card_committed` (`kim_spectral_rows_probe.v:100-104`, `:110-114`,
`:284-289`, `:360-366`), which is how every certified program in the tree is
written: from its own instance's prefix, at a level below `Sampled`. The
landing therefore does not need T0 of
`notes/20260919-tableau-three-extensions-probe-design.md:169`, which asks
whether two programs can continue from one named `Tableau Sampled` value.
Nothing in the tree does that today and this landing does not start."

---

## 4. Completeness language, and I2

### 4.1 What is now correct

Every hit of "every", "all of", "complete", "full list", "nothing else", "no
other" and "exhaust" near the landing material was read in place. The
withdrawal is done properly and no sentence claims the **change list** is
complete:

- `:21-31`, the standing-of-the-account block: "They are not claimed complete
  and a landing plan must not be written from them alone."
- `:48`, the S8 ledger row: "as the items known so far and not as a complete
  list".
- `:530-541`, the S8 subsection head: "**This list is not claimed to be
  complete, and a landing plan must not treat it as complete.**"
- `:998-1003`, S10: "the list of sentences a landing makes false is the one
  known so far and is not claimed complete."
- `:762-763`, on the two name-keyed searches: "they say what the search found,
  not that no sentence anywhere says the same thing in words."
- `:1621`, the N6/F3 row: "the claim to completeness is withdrawn altogether
  rather than restated".

Two remaining "every"-shaped claims are narrow and true. `:869` "Every other
declaration in that file stays true" is a claim about one file backed by a full
enumeration I reproduced. `:739` "returns no other site" is a claim about what
one grep returns, and I reran it: outside the manifest, `five_card_row_biased`
and `five_card_row_repeated` occur only in `instances/kim2025/five_card_rows.v`
and at `manifest/pgg_analysis_client.v:149-150`. Correct.

### 4.2 I2. BLOCKING. The rebuild instruction closes its own list

`STATUS.md:932-934`:

> **The seven propositions above are the ones a spectral landing falsifies.** The
> list in this section names where each is stated today; a landing batch must
> assume there are more places and search for the words, not for the names.

The second sentence keeps the places open. The first closes the propositions,
and it is false: at least four propositions that STATUS's own Row 4 and Row 5
tables record as falsified are outside the seven bullets, and none of the seven
bullets' words would find them.

| proposition | stated at | STATUS's own change list says | in the seven bullets? |
|---|---|---|---|
| the biased path carries no shuffle certificate | `manifest/pgg_analysis_manifest.v:301-302`, `bound or certificate \| none; kim_leak_bound is the numeric constant of the bridge theorem, not a shuffle certificate` | `STATUS.md:589`, "the row then carries a `SpectralCert`" | **no** |
| the repeated path's bound-or-certificate list is those four bundles and bounds | `:351-354` | `STATUS.md:606`, "incomplete: the row then also carries a `SpectralCert`" | **no** |
| the repeated path has no final bridge theorem | `:355`, `final bridge theorem \| NONE` | `STATUS.md:607`, "the certified proposition is the bridge theorem" | **no**; bullet 4's "no transfer-layer result exists" is a different form of words |
| the existing certificate bundle does not raise the level | `:379-380`, `A ShuffleCertificate-Bundle exists for both models and does not raise the level.` | `STATUS.md:611`, "the certificate that raises the level is built from that same bundle's `scb_bound`" | **no** |

I searched the twelve production directories for each of these spellings.
"shuffle certificate" returns `manifest/pgg_analysis_manifest.v:302` and
`instances/pgl27/pgl27_analysis.v:281`, the latter about PGL and not falsified.
"raise the level" returns `manifest/pgg_analysis_manifest.v:380` alone. So no
**further place** is missed today, and the change list is unaffected. What is
wrong is the enumeration of propositions, which is what the rebuild pass is
keyed to. A landing batch told that the seven are "the ones" would search seven
strings and stop, and the class of item every round has found is precisely the
one no listed string reaches.

The failure mode is the one this revision was written to close. Rounds 1, 2 and
3 each found a new class of item, `:531-538` says so, and the very next
subsection then asserts the class list is now closed.

**Exact correction.** Replace `STATUS.md:932-934` with: "Those seven
propositions are the ones found so far, and the list of propositions is no more
complete than the list of places. Four more the tables above already record are
outside it: that the biased path carries no shuffle certificate
(`manifest/pgg_analysis_manifest.v:301-302`), that the repeated path's bound
list is those four bundles and bounds (`:351-354`), that it has no final bridge
theorem (`:355`), and that the existing `ShuffleCertificateBundle` does not
raise the level (`:379-380`). A landing batch must extend this list from the
Row 4 and Row 5 cells above before it searches, and must assume that both the
propositions and their places are undercounted."

### 4.3 The rest of the rebuild instruction works

The compile half (`:900-909`) is sound. `Check` is not `Fail Check`, so a
failing `Timeout 60 Check (erefl : ...)` is a hard error that stops `coqc`, and
`manifest/pgg_analysis_manifest.v:67-72` says exactly that, verbatim as STATUS
paraphrases it. Copying the three named files and their reverse-dependants and
compiling the copies does find every pin, every spelled-type `Check` and every
ascription mechanically. One practical qualification, not a fault in the
instruction: `coqc` halts at the first error, so the pass is iterative rather
than a single run that lists them all. See I8.

---

## 5. The family-name grep, rerun independently

`STATUS.md:739-755`. I rebuilt the search from `_CoqProject`: the twelve
non-legacy directories hold **133** `.v` files, and 195 in all with `legacy/`.
A whole-word search for `single_biased_sample`, `repeated_sample`,
`centi_sample`, `biased_family` and `centi_family` over the 133 returns
exactly what STATUS reports and nothing else:

    instances/kim2025/five_card_analysis.v  45 46 47 202 204 206 207 209 210 216 218 220 222 402
    manifest/pgg_analysis_client.v          41 43 44
    manifest/pgg_analysis_manifest.v        293 315 322 340 341 370 768 778
                                            1177 1182 1187 1210 1217 1225 1229 1235 1248 1253

Read in place: `:45-47` is the phase-H1 alias table, `:202-222` the four sample
and three family declarations, `:402` a spelled-type `Check`; the client's
three are bare `Check`s at `:41`, `:43`, `:44`; the manifest's `:293`, `:315`,
`:322`, `:340-341`, `:370` are Row 4 and Row 5 table lines, `:768` and `:778`
the two row definitions, and the remaining ten spelled-type `Check`s. Eleven
spelled-type `Check`s in all, as STATUS says. STATUS's judgement that only the
two row definitions and `:322` are already in the list and that none of the
others states a level or a status is right.

The client is safe as STATUS describes: `:48-49` and `:149-150` are bare
`Check`s, and `:126` "The typed status vocabulary and the nine rows" counts
rows and not levels.

---

## 6. The dependency cone, recomputed independently

I did not use STATUS's method. I stripped comments from the five `.v` files,
cut each declaration's body at `Qed`/`Defined`/`Admitted` or the next top-level
command, took the probe-local identifiers occurring in each body, and closed
transitively. My result is identical to the one STATUS reports:

| cone | STATUS | mine |
|---|---|---|
| `kim_centi_cut_mixing` | 12 | **12** |
| `kim_biased_cut_mixing` | 13 | **13** |
| `five_card_static_obs_const` | 6 | **6** |
| union | 17 | **17** |

The membership matches name for name in all four sets. The arithmetic around it
is right: 17 less the four generic lemmas is 13, plus the three theorems is 16,
and the S10 table carries exactly 14 dagger rows holding those 16 declarations
(twelve rows of one, two rows of two). STATUS's `declarations found: 56` is
right for its own counting: the `.glob` files emit a `def` entry for each of the
five recorded `Fail`s, and 51 succeeded declarations plus 5 is 56.

"Nothing in the cone reaches the manifest, the Tableau files or the facade" is
true, and stronger than the `.glob` check STATUS ran shows: after the H10
deletion, none of `var_dist_injective_probe.v`, `five_card_rotation_probe.v`,
`kim_sc_close_probe.v` or `five_card_sc_const_probe.v` **imports**
`pgg_analysis_status`, `pgg_analysis_manifest`, `pgg_tableau`,
`pgg_tableau_syntax`, `five_card_analysis` or `five_card_rows`, so no reference
into them is possible. Option 2 is not a cycle.

Option 2 is described the same way in all four places it appears (`:1083-1084`,
`:1138-1146`, `:1175-1219`, `:1243-1402`): a new
`instances/kim2025/five_card_mixing.v` below the facade, holding the whole
sixteen-declaration cone, eleven files recompiled.

### I3. SHOULD-FIX. The published cone script does not reproduce its printed output

`STATUS.md:1250-1325` prints the script and `:1327-1390` its output. I ran the
script verbatim in the probe directory as it stands. It exits cleanly and
prints:

    declarations found: 56
    cone of kim_centi_cut_mixing: 0
    cone of kim_biased_cut_mixing: 1
    cone of five_card_static_obs_const: 6
    union: 7

not 12, 13, 6 and 17. The cause is that the script reads declaration and
reference positions as byte offsets from the `.glob` files and the span
boundaries from the `.v` files, and the `.glob` files in the directory
(timestamped 08:59) predate the third fix pass's two `.v` edits (09:20 and
09:21). Deleting `kim_sc_close_probe.v:21` moved every later byte in that file
by 62, and the rewritten comment in `five_card_rotation_probe.v` moved that
file's too, so the spans no longer align with the recorded positions. Nothing
warns; the answer is simply smaller.

The reported output is correct, as my independent recomputation confirms, and
the conclusion drawn from it stands. What fails is reproducibility: a reader or
a landing batch that reruns the published script to check the cone gets seven
declarations and would conclude the page is wrong, or would move seven and
leave `five_card_rows.v` calling lemmas that are no longer in scope.

**Exact correction.** Regenerate the five `.glob` files from the current
sources, or add one sentence above the script: "The script reads byte offsets
from the `.glob` files against line boundaries in the `.v` files, so the two
must come from the same compile. The `.glob` files committed beside this probe
predate the third fix pass's two source edits; recompile the five files before
rerunning it, or the cone comes out short with no error."

### I4. SHOULD-FIX. Option 2's "keeps only" sentence and the S10 table leave five declarations unplaced

`STATUS.md:1195-1198`:

> `instances/kim2025/five_card_rows.v` keeps **only** the
> certificates, the four row programs, their `epsE`, `eps_lt`, `publishedE` and
> `rowE` lemmas, and the two repricing identities
> `five_card_pow2_39_split` and `five_card_inv50_split`.

Five declarations fit none of those four descriptions and appear in no row of
the S10 table at `:1086-1110`:

    kim_spectral_rows_probe.v:246   kim_centi_cut_mixing40
    kim_spectral_rows_probe.v:328   kim_biased_cut_mixing_exact
    kim_spectral_rows_probe.v:310   kim_one_cut_centi_le
    kim_spectral_rows_probe.v:277   five_card_reprice39
    kim_spectral_rows_probe.v:354   five_card_reprice_inv25

The first two are mixing statements of exactly the shape that sends
`kim_centi_cut_mixing` and `kim_biased_cut_mixing` to the new file, and they
are the mixing fields of the form-2 certificates, so under option 2 they belong
below the facade with the others. `kim_one_cut_centi_le` is the per-position
bound `kim_biased_marginal_bound_exact` is built from. The two `Reprice`
definitions are data the row programs consume.

This is an omission rather than a false item, so under the standard in force it
does not change the verdict. The word "only" is what makes it worth correcting:
as written the sentence says the split is exhaustive, and it is not.

**Exact correction.** Add the five to the S10 table, `kim_centi_cut_mixing40`
and `kim_biased_cut_mixing_exact` as dagger rows beside the two mixing fields
and `kim_one_cut_centi_le` as a dagger row beside the one-cut marginal bound,
the two `Reprice` definitions in the "rows and the numbers" row; and change
"keeps only the certificates" to "keeps the certificates".

---

## 7. Numbers and the certified proposition: nothing regressed

Every figure recomputed in Python at this revision.

| quantity | value | STATUS | verdict |
|---|---|---|---|
| `2*sqrt(5)*(1/80)^7` | `2.132480599880019e-13` | `:318` "about `2.13e-13`", `:324` "`2.1325e-13`" | unchanged, correct |
| `2^-39` | `1.8189894035458565e-12` | `:325` "`1.8190e-12`", `:1723` "`1.82e-12`" | unchanged, correct |
| ratio | `8.529922399520068` | `:322` "a factor of 8.53", `:325` "`8.5299`" | unchanged, correct |
| `sqrt(5)/40` | `0.05590169943749475` | `:385` "about `0.0559`" | unchanged, correct |
| `sqrt(5)/80` | `0.027950849718747374` | `:432` "`sqrt 5 / 80 = 0.02795`" | unchanged, correct |
| `1/25` | `0.04` | `:424` "`1 / 25 = 0.04`" | unchanged, correct |

The two ceiling comparisons in the probe comments are still right.
`kim_spectral_rows_probe.v:164` "at about three percent of the ceiling":
`(sqrt5/40)/2 = 2.795%`. `:384-385` "One twenty-fifth is below two": `0.04 < 2`.

S9 still matches the definition. `SpectralPropAt` (`manifest/pgg_tableau.v:331-339`)
quantifies over `C` and two `x x' : ex_inputT E` under `#|C| < profile_k
(instance_profile A)`, and bounds `var_dist` of the two pushforwards of
`static_coalition_obs` along `sa_cut_dist sa`. STATUS's S9 sentence at `:968-972`
is that statement, its four "it is NOT" bullets are accurate, and its two
closing remarks are right. The citation `manifest/pgg_tableau.v:331` is the
first line of the definition.

The S10 reverse-dependency table is unchanged and I reran all fifteen rows from
`.Makefile.rocq.d` with my own script: 105, 107, 102, 41, 39, 24, 20, 20, 10, 9,
0, 7, 8, 16, 20, all matching. The five landing totals reproduce: option 1 at
**9**, option 1 corrected at **10**, option 2 at **11**, and with
`card_tnth_count` to `den_boer_encoding.v`, **18** and **19**.
`instances/psl211/psl211_endpoints.vo` is in the closures of the first four
rows and of none of the other eleven, and in none of the five landing sets, so
B-1's rewritten sentence at `:1033-1039` is exactly right.

---

## 8. Notes

- **I5. NOTE.** `STATUS.md:641-644` cites `manifest/pgg_analysis_manifest.v:754-755`
  for a quotation that begins "reaching AnalysisBridged". "reaching" is the last
  word of `:753`. The range is `:753-755`, or the quotation should start at
  "AnalysisBridged". Carried over from round 3's own citation.
- **I6. NOTE, a further seed item.** Item 5 (`STATUS.md:831-834`) names the
  docstring of `five_card_row_repeated_tableau` (`:383-389`) for its closing
  clause "so no security payload follows it". The same docstring opens at
  `:384` with "The program stops at Sampled, **the level the manifest records
  for this row**", and the manifest's level for that row moves to
  `AnalysisBridged`, so a second clause in the same range goes false for a
  second reason. The item and its range are right; only its reason is partial.
- **I7. NOTE.** `STATUS.md:890-892` says the previous form of the paragraph
  "named nine declarations out of the twenty-six". It named eight declarations
  individually and one group of five by description. Twenty-six is right.
- **I8. NOTE.** `STATUS.md:904-906` "Every `erefl` pin, every spelled-type
  `Check` and every ascription that moves shows up as an error with a line
  number." True of the pass, but `coqc` stops at the first error, so the batch
  finds them one per compile and must iterate. Worth one clause so nobody plans
  a single run.
- **Further seed items: none beyond I6 and the four propositions of I2.** I
  searched the twelve production directories independently for the two row
  names, the five facade model and family names, "shuffle certificate", "raise
  the level", "no certificate", "none claimed", "no theorem", "ShuffleCertificate"
  and "constancy". Every result is either already in STATUS's list or is about
  another instance and is not falsified. The B1 disposition row's "nine sites in
  six files" for "constancy" reproduces exactly: `manifest/pgg_tableau.v:37,126,129,557`,
  `manifest/pgg_tableau_syntax.v:140`, `instances/pgl27/pgl27_rows.v:244`,
  `instances/s5/s5_rows.v:66`, `instances/psl211/psl211_rows.v:41`,
  `instances/kim2025/five_card_rows.v:41`, with `reconstruct/s5_nogo.v:53` the
  tenth occurrence about a different object.

---

## Findings, by ID

| ID | Severity | What | Where |
|---|---|---|---|
| I1 | **BLOCKING** | H4's decision states that the certified programs continue from the two `Tableau Sampled` values; all four continue from `five_card_committed`. The reason given for the four `prefixE`/`modelE` lemmas is wrong, and "every certified program is written as one chain from `five_card_committed`" is false about the tree | `STATUS.md:775-776`, `:792-794` against `kim_spectral_rows_probe.v:100-104`, `:110-114`, `:284-289`, `:360-366`, `STATUS.md:282-292`, `:344-349`, `:412-417`, `instances/pgl27/pgl27_rows.v:270,295`, `instances/s5/s5_rows.v:275`, `instances/psl211/psl211_rows.v:175` |
| I2 | **BLOCKING** | "The seven propositions above are the ones a spectral landing falsifies" claims the proposition list is complete; four propositions STATUS's own Row 4 and Row 5 tables record as falsified are outside it | `STATUS.md:932` against `manifest/pgg_analysis_manifest.v:301-302`, `:351-354`, `:355`, `:379-380` and `STATUS.md:589`, `:606`, `:607`, `:611` |
| I3 | SHOULD-FIX | The published cone script does not reproduce its printed output in the directory as it stands, and fails silently with a union of 7 instead of 17, because the `.glob` files predate the fix pass's two source edits | `STATUS.md:1250-1390` |
| I4 | SHOULD-FIX | Option 2's "keeps only" is not exhaustive and the S10 table has no row for five declarations | `STATUS.md:1195-1198`, `:1086-1110` against `kim_spectral_rows_probe.v:246,277,310,328,354` |
| I5 | NOTE | Quotation range short by one line at the head | `STATUS.md:641-644` against `manifest/pgg_analysis_manifest.v:753-755` |
| I6 | NOTE | Item 5's docstring has a second clause that goes false, for a second reason | `STATUS.md:831-834`, `instances/kim2025/five_card_rows.v:384` |
| I7 | NOTE | "nine declarations" was eight declarations and one group | `STATUS.md:890-892` |
| I8 | NOTE | The compile pass is iterative; `coqc` stops at the first error | `STATUS.md:904-906` |

Nothing found here is a kernel-level unsoundness. No `Admitted`, `Axiom`,
`admit`, `Abort`, `Parameter`, `Hypothesis` or `Conjecture` was introduced into
the five files, and no statement, proof or number the kernel checks is
disputed. Both blocking findings are sentences in `STATUS.md` that a landing
executed from `STATUS.md` would act on and that are false against the probe's
own compiled evidence.
