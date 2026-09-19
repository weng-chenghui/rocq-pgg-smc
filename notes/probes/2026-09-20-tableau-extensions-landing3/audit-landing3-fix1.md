# Adversarial audit of fix pass 1, landing 3 (PGL(2,7))

Read-only. Commits `0c4a4ef` (before) to `538862a` (after). No repository file
was edited except this one. Nothing was compiled; the rocq lock was left alone.
Paths below are relative to
`notes/probes/2026-09-20-tableau-extensions-landing3/`, and line numbers are
those of the frozen text at `538862a`.

## Verdict: NO-GO, on one MUST

`F1` is in `staged/instances/pgl27/pgl27_proximity.v`, one of the seven files
the copy would move into production, and the sentence it names is false of the
declarations of this development. Everything else below is SHOULD or NOTE and
does not block the copy. `F3` is in `landing_fidelity.v`, which is not copied,
but it is the pass's own evidence file and the pass is what made it stale.

The pass is otherwise accurate. Twenty-three comment passages were rewritten
against their declarations, the two renames and the one move are clean, no
occurrence of either old name survives anywhere, both header tables index
exactly their files, no landed line exceeds 80 bytes, and no word of the
project's banned vocabulary list appears in any added line.

## Findings

| id | class | file:line | quoted text | problem, with the declaration's type | replacement |
|---|---|---|---|---|---|
| F1 | MUST | `staged/instances/pgl27/pgl27_proximity.v:611-613` | "The `Fail` rejects the one term written here, on that mismatch of index types, and **the mismatch is what separates the two models of this instance**." | False, and it reintroduces at a third site the error `N17` and `N18` removed from the manifest. An index type separates two *families*, never two models. The two models this file is about carry the **same** index type: `pgl27_prior_exact_family` and `pgl27_word_family` are both indexed by `R.-fdist bool` (`staged/instances/pgl27/pgl27_models.v`), and `pgl27_word_proximity_close (R : realType) (secretP : R.-fdist bool) (C : …) : (#\|C\| < profile_k …)%N -> var_dist … <= 2%:R^-40` is the statement that they are two models at one index. In the other direction one model is reached from two families: the soundness audit compiled `amf_sample pgl27_exact_family R tt = amf_sample pgl27_prior_exact_family R (fdist_uniform (R := R) card_bool)` closed `by []`, rc 0 (`pos_checks.v`, recorded at `L3-6`). What the `Fail` at `:614-616` establishes is a type mismatch between `unit` and `{fdist bool}` in one written term, which is what the sentence before it already says. | "The `Fail` rejects the one term written here, on that mismatch of index types, and rules out no other term." This is guard 2's own wording at `:591-592` and is what `L3-1` asked the three guards to agree on. If a positive clause about the index types is wanted, the true one is "and what the index types separate is the two families, not the two models". |
| F2 | SHOULD | `staged/instances/pgl27/pgl27_proximity.v:383-384` | "**The number** is spent once, against the input-indistinguishability row's twice." | The nearest antecedent of "the number" is 2^-39, set two sentences earlier by "concluded at 2^-39" and "is within that number". At 2^-39 the sentence is false: 2^-39 is exactly the quantity the other row spends twice. What is spent once is the certificate's number, `ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40` (`pgl27_word_proximity_cert_epsE`), against `cert_eps (pgl27_word_cert secretP) = ipc_eps (…) + ipc_eps (…)` (`pgl27_word_proximity_eps_halfE`). The sentence is verbatim from production `instances/kim2025/five_card_proximity.v:356`, where the row publishes its certificate's own number and no ambiguity arises; the pass rewrote the line carrying it without re-reading the antecedent. | "The certificate's number is spent once, against the input-indistinguishability certificate's twice." (See `F7` on "spent".) |
| F3 | SHOULD | `landing_fidelity.v:5-11` | "Each declaration landing 3 adds is restated here at the statement the probe proved, modulo **the two edits the landing forces**: the R7 rename of `pow2_40_ge1` and `pow2_40_gt0` …, and the replacement of the four-branch first `[…]` of `var_dist_fdist1_uniform` …" | The pass added two more forced substitutions and did not update the count or the list. The restatements at `:207` and `:253` are now `f_pgl27_row_word_families_sampledE` and `f_pgl27_word_uniform_ideal_close_false`, against the probe's `pgl27_row_word_arms_sampledE` and `pgl27_word_uniform_ideal_not_close`. STATUS.md's own verification paragraph says `verify.py` prints "the four `RENAMED` substitutions", so the file's header and its checker disagree on the count. | "… modulo the four edits the landing forces: the R7 rename of `pow2_40_ge1` and `pow2_40_gt0` to `pgl27_pow2_40_ge1` and `pgl27_pow2_40_gt0`, the renames of `pgl27_row_word_arms_sampledE` to `pgl27_row_word_families_sampledE` and of `pgl27_word_uniform_ideal_not_close` to `pgl27_word_uniform_ideal_close_false`, and the replacement of the four-branch first `[…]` of `var_dist_fdist1_uniform` by the one branch that fires." Re-box to column 80. |
| F4 | SHOULD | `staged/lib/var_dist_supp.v:12-15` | "Beside it sit the scale a published variation distance is read against, the invariance of a uniform law under an injective endomap, and the fact that a pushforward charges only the image." | The header prose enumerates the companions of `var_dist_fdistmap_supp_inj` one by one, and the arriving `var_dist_fdist1_uniform` was added to the index table at `:24-25` but not to this enumeration. Three are listed where the file now holds four besides the main lemma: `var_dist_le2`, `fdistmap_inj_uniform_id`, `fdistmap_neq0_codom`, `var_dist_fdist1_uniform`. | "… and the fact that a pushforward charges only the image, and the distance between a point mass on the booleans and the uniform law there." Re-box to column 80. |
| F5 | SHOULD (non-blocking) | `staged/instances/pgl27/pgl27_proximity.v:28` (changed), and `:221`, `:324` (unchanged) | "which rests on **pgl27_word_mixing, the distance between** the word walk and the uniform cut on the group" | `pgl27_word_mixing : var_dist (@rho_from_words_weighted R 6 4 200 pgl27_moves Wuni) (`U pgl27_G_pos) <= 2%:R^-40` (`instances/pgl27/pgl27_mixing.v:1048-1051`) is an upper bound, not the distance. The appositive types a `<=` statement as a quantity. The auditor's proposed text for `N1` carries the same appositive, and two unchanged sites in the same file do too (`:221` "The cut group's own distance, pgl27_word_mixing"; `:324` "Both are read off pgl27_word_mixing, the one distance on the cut group"), so the phrasing is a file-wide idiom, not a slip introduced here. Fixing one site alone would break "one word per concept, file-wide". | At `:28`: "which rests on pgl27_word_mixing, which bounds by that same number the distance between the word walk and the uniform cut on the group." If the owner takes it, take all three sites in one pass. |
| F6 | NOTE | `staged/instances/pgl27/pgl27_proximity.v:33-34` | "so the two rows over this model are **published at one constant**" | `N27`'s ruling, which the pass applied at the index entry `:54` ("the proximity claim, concluded at 2^-39"), is to keep "concluded at" for the terminal and "publishes" for the number a finished row carries. Both rows reach their constant through `conclude pgl27_reprice39` (`:390` and `instances/pgl27/pgl27_rows.v:496`), so the header uses the verb the same pass replaced ten lines below. `:32` "the constant pgl27_row_word_branch39 publishes for the other arm" is the allowed use and needs no change. | "so the two rows over this model conclude at one constant". |
| F7 | NOTE, for a later pass over both sites | `staged/instances/pgl27/pgl27_proximity.v:383` and production `instances/kim2025/five_card_proximity.v:356` | "The number is **spent** once, against the input-indistinguishability row's twice." | "Spent" is a currency metaphor for the relation "the certificate's number enters the accumulated bound once". Read against the rule barring narrative and metaphor words for mathematical results, it is a metaphor. Read against the project's own vocabulary it is established: `instances/pgl27/pgl27_rows.v:264` says "The two currencies are visible in the fields" and `instances/pgl27/pgl27_word_privacy.v:89` "the number a word row's spectral arm spends", and the owner's own guidance on hopping arguments asks for a priced step and a named currency. The pass kept it because production carries the identical sentence, which is the right call for this pass. | None here. One finding covering both sites for a later pass: either "used once" / "enters once", applied to every carrier of the metaphor at once, or an explicit ruling that "spend" is the project's word for this relation. Not a blocker. |
| F8 | NOTE | `staged/instances/pgl27/pgl27_proximity.v:23-24` and `:70-71` | "and that **the witness it carries for that model is the row's own port**" / "== the certificate's ideal and **witness** are the model and the **port** the ideal row publishes" | Type slip. The second conjunct of `pgl27_word_proximity_cert_idealE` is `ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP)) = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP` (`:309-310`). A witness is an `ExactWitness`; a port is the arm payload. They are equal only after the constructor is applied. The auditor's proposed text for `N10` has the same slip, and the declaration's own comment at `:300-301` says "the witness it carries for it, are the model and the witness of the published ideal row", giving a third wording of one lemma. | Index entry: "== the certificate's ideal is the model the ideal row publishes, and its witness wrapped as an exact-independence port is that row's port". Header `:23-24`: "and that its witness, wrapped as an exact-independence port, is the row's own port". Then align `:300-301` to the same words. |
| F9 | NOTE | `staged/lib/var_dist_supp.v:159` | section banner "**A point mass** against the uniform law on the booleans" | `N22` asked for "the point mass at true" in the index entry because the statement is at `fdist1 true`, and the pass applied it at `:24`. The banner six lines below keeps the indefinite article for the same lemma, the only one in the section. | "The point mass at true against the uniform law on the booleans". |
| F10 | NOTE | `STATUS.md:723-754` | — | `N18` (SHOULD) is absent from the per-finding table, from the declined table and from the deviations table, yet it was applied: `staged/manifest/pgg_analysis_manifest.v:985-988` now carries the auditor's proposed replacement word for word. Nothing vanished from the text; the record vanished. `N18`'s replacement text should be added as a row so the coverage argument is complete. | Add the row: "N18 — 'It differs from pgl27_row_exact in its model family, whose index is the law of the dealt secret where the other's is the unit type …' — checked against `pgl27_row_exact` and `pgl27_row_prior_exact`." |

## Answers to the named questions

**1a. The three recorded guards.** Guard 1's added sentences are true and are
readable from the types, not only from the `Fail`: the ideal field written is
`amf_sample pgl27_exact_family R secretP` where `amf_index pgl27_exact_family R`
is `unit`, so the term is refused at the index and no distance is reached; and
the same family at `tt` is well typed as an ideal, with the mismatch moving to
the distance field, whose written proof `pgl27_word_proximity_close secretP HC`
is stated against `pgl27_prior_sample secretP` and not against `pgl27_sample R`.
The soundness audit's un-`Fail`ed compiles (`unfail_unit.v`, `unfail_uniform.v`)
agree. The file records only `Fail` and not the two error messages, so a reader
takes the *which field* on the comment's word; that is the tree's existing
practice and not a defect of this pass. Guard 2 is unchanged and correct. Guard
3's last clause is `F1`: the separation claim is neither supported by the `Fail`
nor readable from the index types, and it is false of this instance's two
models.

**1b. Header paragraph three.** Checked against every declaration it names.
`pgl27_word_marginal_bound = @MkShuffleMarginalBound R pgl27_M 200 (2%:R^-40)
rho_word (@pgl27_endpoint_mixing R)` (`instances/pgl27/pgl27_word_privacy.v:90-92`),
whose `sw_bound` field is the per-position bound, so "single-card marginal
number 2^-40" is right; `pgl27_endpoint_mixing` is proved
`apply: le_trans pgl27_word_mixing` (`pgl27_mixing.v:1070`), so "rests on" is
right; `pgl27_view_mixing` is correctly no longer named. The two deviations
hold. "Carries it added to itself" is exact: `cert_eps` is defined as
`sw_bound_eps (ic_b …) + sw_bound_eps (ic_b …)` (`manifest/pgg_tableau.v:470`)
and `ic_b (pgl27_word_cert …) = pgl27_word_marginal_bound R`
(`pgl27_rows.v:271`), and `pgl27_word_proximity_eps_halfE` states exactly that
sum. "Published at one constant" is factually right, both rows being
`PublishedRowAt pgl27_reprice39` with `pgl27_reprice39 = fun R => Some (2%:R^-39 : R)`
(`pgl27_rows.v:417`), but it uses the verb `N27` had just replaced (`F6`). The
closing sentence is sound: the row concludes at 2^-39, `var_dist` is twice the
total variation distance, so a distinguisher's advantage against the published
row is at most 2^-40. The one defect is `F5`.

**1c. `pgl27_row_prior_exact_rowE`.** True throughout. The lemma is
`published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact`, closed
`exact: erefl`; the manifest's `Definition pgl27_row_prior_exact :=
@MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
PGL27Analysis.prior_exact_family StaticExecutedOnly BaselineClassicalOnly` has
exactly the five coordinates the sentence lists, in that order, written in the
facade's aliases where the program uses this file's names, and conversion is
what decides the equation. The closing clause is `pgl27_rows.v:342-344`'s own
wording, as `L3-3` asked.

**1d. The scope sentence on `pgl27_word_uniform_ideal_close_false`.** Correct.
The statement is `forall (C : {set 'I_(…).+1}), ~ (var_dist … <= 2%:R^-40)`,
with no cardinality premise, so "stated at every coalition and not only below
four seats" is what the binder says, and "refutes more than the field asks" is
right, the field asking the bound only below the threshold. The sentence does
say what is refuted: the preceding sentences name the ideal (the uniform-secret
member of the unit-indexed family, `pgl27_sample R`), the actual model (the word
walk at `P1 = fdist1 true`) and the number 2^-40, all of which the statement
carries.

**1e. `var_dist_fdist1_uniform` at its new home.** The docstring's first
sentence is an equality and is stated as one, at the point mass at true, which
is what `N22` asked. The added sentence is true and its mechanism is the right
one: the pushforward along the secret coordinate is the secret marginal
(`fdist_prod1`, used twice in the proof at `:566` and `:574` of
`pgl27_proximity.v`), and `var_dist_fdistmap` gives
`var_dist (fdistmap f P) (fdistmap f Q) <= var_dist P Q`, so pushing forward can
only shorten. "Distance" is type-honest here: it names `var_dist` between two
joint laws, a quantity, not a bound, and `var_dist` is a genuine metric, twice
the literature's total variation. The conclusion "a proximity number … is at
least one" follows: `1 = var_dist(marginals) <= var_dist(joints) <= eps`. The
domain vocabulary in a `lib/` file is consistent with that file's own header,
which already presents itself as the home of the distance facts a certificate's
number is read against.

**1f. Manifest Row 10.** True. `pgl27_row_exact` and `pgl27_row_prior_exact`
agree in `observed`, `AnalysisBridged`, `StaticExecutedOnly` and
`BaselineClassicalOnly` and differ in the family alone, so "agree in their other
four coordinates" is exact. The final clause is a term equation that no landed
file states as a lemma; the soundness audit compiled it `by []`, rc 0, and
recorded it under `L3-6`. It is the verified form the auditor offered, so it
stands, but its evidence lives in the probe and not in the artifact.

**1g. The "at most 2^-39" sites and the index entries.** All correct.
`pgl27_word_proximity_le39` concludes `<= 2%:R^-39`, so "at most" replaces
"under" rightly at `:347` and `:80`; the added "the obligation is met strictly"
is a true statement about the two numbers and not a claim about the lemma's
relation. `L3-4`: the premise `(#|C| < profile_k (instance_profile pgl27_algebra))%N`
is restored in the entry, and the threshold is four, which the proof's
`have H3 : (#|C| <= 3)%N := HC` settles by conversion. `N10`: see `F8`. `N11`:
`pgl27_word_proximity_eps_halfE` is exactly "twice". `N13`:
`pgl27_word_view_proximity` concludes `<= 2%:R^-39`. `N14`:
`pgl27_word_proximity_cert_epsE` is `= 2%:R^-40`, an equality, and the entry
says "is 2^-40".

**2. Deviations and declines.** All four recorded deviations are justified and
their texts are true, with the two qualifications already raised: `N1`'s
"published at one constant" (`F6`) and `L3-7`'s "can only shorten the distance",
which is correct. `N6`'s deviation is right, the lemma being a conjunction,
subject to `F8` on how the second half is worded. The four declines are sound.
`N23` is correctly declined: the replacement would edit a proof body and add a
fourth token difference from the probe, for two one-line `have`s. `N25` and
`N26` are correctly kept; both timing comments sit inside `Proof` and name the
tactic, the goal shape and the alternative. `N28` correctly touches nothing,
Row 1's capability column not being landing 3's to change. On `N5`: production
`five_card_proximity.v:356-359` does carry the replacement word for word, so the
pass copied it correctly; the metaphor is `F7`, one finding over both sites for
a later pass, and the antecedent defect the copy exposes is `F2`.

**3. Completeness.** Every id of both reports is accounted for in the text.
`L3-1` to `L3-11`: all applied. `N1`, `N2`, `N3`, `N4`: applied. `N5` to `N15`,
`N17`, `N19`, `N20`, `N21`, `N22`, `N24`, `N27`: applied. `N16`: resolved by
ruling (b), the move to `lib/var_dist_supp.v`. `N23`, `N25`, `N26`, `N28`:
declined with reasons. `N29` to `N35`: clean in the audit, nothing to apply.
`N33`: satisfied as a consequence of the move. **`N18` is applied in the text
but recorded nowhere in STATUS.md** (`F10`). Nothing else is missing. The stale
reference the audits missed is indeed fixed: header paragraph one at `:17` now
names `pgl27_word_uniform_ideal_close_false`. A scan of the seven landed files
and `landing_fidelity.v` finds **zero** occurrences of `arms_sampledE` and zero
of `uniform_ideal_not_close`, and no passage placing `var_dist_fdist1_uniform`
in the instance file: the eight remaining occurrences of that name are the
declaration and index entry in `lib/var_dist_supp.v`, the `rewrite` at
`pgl27_proximity.v:575`, and five in `landing_fidelity.v`, of which
`:55` is `Check var_dist_supp.var_dist_fdist1_uniform`.

**4. Unrequested changes.** None. Every changed passage maps to a finding or to
a consequence one forces: the `Require` and `Check` lines and the provenance
banner of `landing_fidelity.v` to `N16(b)`, the additions banner and the fifth
`Check` to `L3-9`, the six renamed sites to `N3` and `N15`, and each comment
passage to the id STATUS.md names for it.

**5. Header tables.** `staged/instances/pgl27/pgl27_proximity.v` declares 23
non-`Fail` objects and three `Fail`s; the Definitions block indexes five and the
Key results block eighteen, every declared name appears exactly once, and no
`Fail` name appears, which is the tree's precedent. Spelling matches in all 23.
`staged/lib/var_dist_supp.v` declares five lemmas and its table has five
entries, the new one among them, spelled correctly. Descriptions match their
declarations everywhere, subject to `F8` on the `idealE` entry.

**6. Discipline in the changed text.** No line of any landed file exceeds 80
bytes. No box-comment line among the changed passages has its closing `*)` off
column 80; the off-column lines the scan reports are inline and section markers
in chain copies this landing does not own, unchanged from before the pass. No
added line contains any word of the project's banned vocabulary list. No meta
narration in any of the seven staged files: the one hit for a staging word is
`landing_fidelity.v:47`, which is a probe file whose subject is exactly the
staged-against-production question. "Indistinguishability" is spelled in full at
every occurrence. "Reading" is the prose word throughout and "view" occurs only
inside identifiers (`pgl27_view`, `pgl27_prior_viewE`, `pgl27_word_view_proximity`,
`sa_coalition_view`), including at `:59` and `:135` where `N12` asked for it.
Proof strategy stays inside `Proof` in plain `(* *)` comments: the threshold
sentence added at `:243-245` and the `exact: erefl` note moved to `:401-402`
under `N24` are both inside their proofs. The one metaphor is `F7`.

## Coverage list

Read in full: the 604-line diff hunk by hunk; the frozen
`staged/instances/pgl27/pgl27_proximity.v` (616 lines),
`staged/lib/var_dist_supp.v`, `landing_fidelity.v`, the changed regions of
`staged/manifest/pgg_analysis_manifest.v`, the additions to
`staged/instances/pgl27/pgl27_exec.v`, and STATUS.md's "Fix pass 1".
Declarations opened and quoted from production: `pgl27_word_marginal_bound`,
`pgl27_endpoint_mixing`, `pgl27_word_mixing`, `pgl27_view_mixing`,
`ShuffleMarginalBound` and its fields, `pgl27_word_cert`, `pgl27_reprice39`,
`pgl27_row_word_branch39`, `pgl27_row_word_rowE`, `pgl27_row_exact`,
`pgl27_row_word`, `pgl27_sample`, `cert_eps`, and the Kim sentences at
`five_card_proximity.v:311-314` and `:351-359` and `:394-396`. Audit entries
read in full: `L3-1`, `L3-3`, `L3-6`, `L3-7`, `L3-8`, `N1`, `N2`, `N5`, `N10`,
`N15`, `N16`, `N17`, `N18`, `N20`, `N21`, `N27`, `N35`, and the one-line summary
of every other id.

Not re-checked, as instructed: the code-token diff, the compiles, and
`Print Assumptions`. Two claims in the changed text rest on evidence outside the
seven files and were not re-run here: the Row 10 family equation, compiled by
the soundness auditor in `pos_checks.v`, and the attribution of guard 2's
rejection to the distance field, compiled in `unfail_uniform.v`.
