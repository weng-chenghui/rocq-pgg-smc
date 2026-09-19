# Adversarial audit of fix pass 1, landing 4 (PSL(2,11))

Read-only audit of `833acaf` -> `a3095fc`, of the frozen text at
`land4_fix1_frozen/notes/probes/2026-09-20-tableau-extensions-landing4/`. No
repository file other than this report was written, nothing was compiled, and
`make` was never run. The code-token facts the main session established by
script were taken as given and not redone.

## VERDICT: NO-GO on one MUST

The MUST is not the fix pass's work. Every sentence the pass wrote or changed
is true against the declaration it describes, and the two renames and their
mentions are right; the pass's own text carries four SHOULD-level defects
(F1, F3, F4, F5), three of them wordings the two audit reports themselves
proposed. The MUST (F2) is a sentence of `psl211_word_proximity.v`'s header
that both audits of `833acaf` passed over: it states a universal about
input-indistinguishability certificates where the theorem it names is about
certificates over one sample adapter, and landing 4 is the landing that adds
the second adapter over that same execution. One qualifier fixes it.

GO after F2, and preferably after F1 and F3 to F5, all of which are one
sentence each.

## Findings

| id | class | file:line | quoted text | problem, with the declaration's type | replacement |
|---|---|---|---|---|---|
| F1 | SHOULD | `staged/instances/psl211/psl211_reading_constancy.v:778-780` (S3+S4 text) | "…carries a proximity certificate, which has no constancy field for this refutation to touch, so this refutation rules out no proximity row." | Defect class (i). The premise is about the one row named in the clause before it; the conclusion quantifies over every proximity row. What supports the universal is the record type, not that row: `Record IdealProximityCert (R) (A) (E) (sa) := MkIdealProximityCert { ipc_ideal : SampleAdapter R (instance_exec E) ; ipc_witness : ExactWitness ipc_ideal ; ipc_secret : {RV (sa_sampleP sa) -> ew_secretT ipc_witness} ; ipc_eps : R ; ipc_close : … }` (`staged/manifest/pgg_tableau.v:215-232`), five fields and no constancy field, against `ic_const` as the fifth field of `IndistinguishabilityCert` (`:196-200`). The rest of the merged text is exact: `psl211_alldecks_constancy_false_word584 (R) (ideal : R.-fdist cutT) (eps : R) : var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R)) ideal <= eps -> (2%:R^-40 + eps) + (2%:R^-40 + eps) < (#\|pgg_G psl211_M\|%:R)^-1 -> ~ coalition_reading_constancy psl211_alldecks_params ideal` does quantify over every law within eps of that cut, and the `ic_close`/`ic_Hd` route is the one `psl211_alldecks_cert_ideal_close` (`:679-688`) takes, `ic_Hd : sw_rho_dist ic_b = sa_cut_dist sa` composed with `ic_close : var_dist (sw_rho_dist ic_b) ic_ideal <= sw_bound_eps ic_b`. | "…carries a proximity certificate, and IdealProximityCert has no constancy field, so this refutation denies no field of that row's certificate." |
| F2 | MUST | `staged/instances/psl211/psl211_word_proximity.v:28-30` (header; text inherited from `833acaf`, not edited by this pass) | "and psl211_alldecks_no_small_eps_cert excludes every input-indistinguishability certificate whose shuffle bound is strictly below 1/1320." | Defect class (i), and landing 4 is what makes it live. The theorem is `psl211_alldecks_no_small_eps_cert (R : realType) (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) : sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#\|pgg_G psl211_M\|%:R)^-1 -> False` (`staged/instances/psl211/psl211_reading_constancy.v:709-712`): the certificate argument is typed at one adapter, `psl211_alldecks_sample`. Until this landing that adapter was the only one over this execution (`MkSampleAdapter` occurs once in production's `instances/psl211/`, at `psl211_models.v:222-227`); landing 4 adds a second, `psl211_word_sample (R : realType) : SampleAdapter R (instance_exec psl211_alldecks_params)`, and the sentence sits in the header of the file that publishes over it. A certificate over the word adapter is not excluded by this theorem at all; it is excluded instead by `psl211_alldecks_constancy_false_word584` read with `ic_close` and `ic_Hd`, and over the smaller range eps < 1/1320 - 2^-40, which the same file's own paragraph at `:26-32` gets right for the refutations and wrong for the exclusion. The declaration's own docstring keeps the scope: "no input-indistinguishability certificate over the all-decks run of the twelve-card chirality instance" (`:690-692`). | "and psl211_alldecks_no_small_eps_cert excludes every input-indistinguishability certificate over the all-decks model whose shuffle bound is strictly below 1/1320." (One phrase; the box lines re-wrap mechanically.) |
| F3 | SHOULD | `staged/instances/psl211/psl211_word_proximity.v:290-291` (N33 text), and the same wording at `staged/manifest/pgg_analysis_manifest.v:1094-1096` | "Its transfer status is IdealFinite: the cut is a shuffle of 584 letters where psl211_row_alldecks draws it uniformly from the group." | Defect class (v). `psl211_row_alldecks : AnalysisPathRow := @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged PSL211Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly` (`pgg_analysis_manifest.v:1070-1072`) is five descriptive coordinates and draws nothing; the draw belongs to the model it names, whose adapter has law `psl211_alldecksP R = (\`U psl211_alldecks_gt0) \`x (\`U psl211_G_pos)` (`instances/psl211/psl211_models.v:200-202`). The same docstring uses the same name as a record two sentences later, "It differs from psl211_row_alldecks in the model family and in the transfer status", so one name carries two kinds inside one comment. This is the manifest's own N25 discipline, "the object that has an arm is the published program; the row is the record that does not", applied to a draw. | "Its transfer status is IdealFinite: the cut is a shuffle of 584 letters where the model of psl211_row_alldecks draws it uniformly from the group." |
| F4 | SHOULD | `staged/instances/psl211/psl211_word_proximity.v:202-204` (S10 text, as the auditor proposed it) | "The bit is not a constant either: psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v reads it as the value the run recovers at every sample point." | The cited lemma carries no non-constancy. `psl211_alldecks_secret_expectedE (R : realType) (u : psl211_inputT * pgg_gT psl211_M) : psl211_alldecks_secret R u = ex_expected psl211_alldecks_params ((psl211_alldecks_sample R).(sa_arg) u)` (`psl211_models.v:449-453`) is an identity at every sample point, and a constant secret satisfies it whenever `ex_expected` is constant. What makes the bit non-constant is `psl211_alldecks_secret R : {RV (psl211_alldecksP R) -> bool} := fun u => u.1.1` (`:207-208`) at a law uniform over `#\|{: psl211_inputT}\| = 2 * 132 * 6\`! * 6\`!` (`psl211_alldecks.v:174`), and no landed declaration states that. The clause asserts the conclusion and cites a lemma that does not reach it. | "The secret is also the one the protocol reconstructs: psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v reads it as the value the run recovers, at every sample point." |
| F5 | SHOULD | `staged/instances/psl211/psl211_word_model.v:22-24` (N17 text, as the auditor proposed it) | "That both laws are written as products is a premise about how the shuffle is performed and not a theorem about the execution: it says the dealer draws the word without seeing the deck." | The subject is both laws and the gloss fits one. `psl211_alldecksP R := (\`U psl211_alldecks_gt0) \`x (\`U psl211_G_pos)` draws a group element and no word; only `psl211_wordP R := (\`U psl211_alldecks_gt0) \`x (psl211_word_cutP R)` draws a word. The probe's text had the clause attached to `psl211_wordP`'s own docstring, where it was right; the pass lifted it to a sentence about both. | "…: it says the dealer draws the cut without seeing the deck." |
| F6 | NOTE | `staged/instances/psl211/psl211_reading_constancy.v:125-127` (inherited, unchanged by this pass) | header entry "psl211_alldecks_constancy_false_word584 == the field is false at every ideal within eps of the 584-letter word shuffle's cut law" | Defect class (vi): the entry drops the declaration's second hypothesis `(2%:R^-40 + eps) + (2%:R^-40 + eps) < (#\|pgg_G psl211_M\|%:R)^-1`, where the neighbouring entry for `psl211_alldecks_constancy_false_close` keeps its own ("once eps + eps < 1/660", `:112-114`). STATUS's whole-file re-read records this entry as true; it is true only with the side condition. Inherited production text, so a later pass. | "== the field is false at every ideal within eps of the 584-letter word shuffle's cut law, once twice the sum of eps and 2^-40 stays below 1/660" |
| F7 | NOTE | `STATUS.md` section A, and N28 | "Two inherited sentences of production carry an economic metaphor and were left … beside the `:16` the ruling names. All three belong to a later pass over production." | The inventory is short by two. `psl211_reading_constancy.v` carries the metaphor at `:16` ("would cost it"), `:748`/`:751` ("the price … pays both"), `:770` ("the whole information-theoretic price"), and also at `:518` ("the form a support hypothesis is spent in") and `:1013` ("has to spend a nonempty coalition"). All five are production text unchanged by this landing, and the two new files carry none, so N28 is applied exactly where it was ruled to apply. Recorded so the later production pass has the full list. | Record five occurrences, not three. |
| F8 | NOTE | `staged/instances/psl211/psl211_word_proximity.v:374`, `:255`, `:155` | lines of 24, 10 and 50 bytes in the middle of rewritten docstrings | Re-wrap artifacts of the pass: `:374` is "    about. A certificate", `:255` is "    bound.", `:155` ends "…the word walk's number 2^-40; and" where the next token would fit. Surrounding lines fill to 72-78. Nothing false; every line is under 80 and every box line closes at column 80. | Re-fill the three paragraphs. |
| F9 | NOTE | `STATUS.md`, "Fix pass 1" sections B and C | the remit's "four deviations" | STATUS labels three: S1 (the auditor's text named a file where an adapter was meant), S6 (no count of refutations given), N28 (a bound on the distance, not the distance). All three reasons are right and all three texts are true, checked in the coverage list below. Two further departures from the reports' proposed wording are recorded as merges rather than deviations: S3+S4 ("covered at its own shuffle bound" became "reached at"), and S5+N8 (S5's "a distance to that independent model" became N8's "a bound on the distance"). Both changes are improvements and both are true. | State three labelled deviations plus the two recorded merges. |

Every replacement above was checked against the declaration it describes and
against the campaign's list (i) to (x). None quantifies over a class where the
declaration is about one object, none calls a bound a distance, none attributes
an impossibility to a `Fail`, none calls a witness a port or a model a row.
None needs a compile: F2, F3, F4 and F5 are comment text, and F1's replacement
names only the record `IdealProximityCert`, which is already in the file's
vocabulary and in no `Require`-dependent position.

## Coverage

### 1. Every sentence the pass wrote or changed

Walked hunk by hunk, skipping the Row 10 block and the `pgl27_row_prior_exact`
docstring, which are landing 3's production text.

- **S1, the banner** (`psl211_reading_constancy.v:742`). True and 80 bytes.
  `psl211_word_sample (R : realType) : SampleAdapter R (instance_exec
  psl211_alldecks_params)` is the word model's adapter and the only one besides
  `psl211_alldecks_sample`; `psl211_word_cut_distE` makes its cut
  `psl211_word_cutP R := @rho_from_words_weighted R 10 2 584 psl211_moves
  (psl211_Wuni R)`, the term the lemma under the banner is stated on. The
  deviation from the auditor's text, naming the declaration instead of the
  file, is the right call.
- **S2** (`:45`). True: `psl211_row_word_proximity_armE … =
  IdealProximityArm`, so "through the proximity arm" names the arm the row
  carries; the anaphora defect (viii) is gone.
- **S3+S4** (`:772-780`). The `ic_close`/`ic_Hd` route and the eps restriction
  check out as quoted in F1; the closing clause is F1.
- **S5+N8** (`pgg_analysis_manifest.v:845-850`). True on every coordinate.
  Row 9 is `psl211_row_alldecks` (`:634`, `:676`), whose model is
  `PSL211Analysis.exact_family` and whose transfer status is
  `StaticExecutedOnly`; Row 11's is `psl211_row_word`,
  `PSL211Analysis.word_family` and `IdealFinite` (`:1070-1072`, `:1100`). Two
  of five coordinates differ, which is what the text now says, and the other
  three (`PSL211Analysis.observed`, `AnalysisBridged`, `BaselineClassicalOnly`)
  agree. "The two models differ in the law of the cut alone" is exact against
  `psl211_alldecksP` and `psl211_wordP`, which share the first factor and its
  law. "a bound on the distance" rather than "a distance" is N20 applied.
- **S6** (`:850-856`). True clause by clause. The refuted propositions are
  instances of `coalition_reading_constancy` (`psl211_reading_constancy.v:198-205`),
  a standalone `Definition`; `indistinguishability_cert_reading_constancy … :
  coalition_reading_constancy E (ic_ideal cert)` is proved `exact: ic_const
  cert`; `ic_const` is the fifth field of `IndistinguishabilityCert`, after
  `ic_b`, `ic_Hd`, `ic_ideal`, `ic_close` (`pgg_tableau.v:191-200`); and
  `IdealProximityCert` has no counterpart. "Those refutations stay true" fixes
  the earlier "propositions which are refuted stay true". Dropping the count
  "three" is right: the file proves five refutations of the field, of which the
  row docstring cites three.
- **S7** (`psl211_word_proximity.v:21-24`). True once restricted to security
  statements: of the file's fourteen declarations, only
  `psl211_word_proximity_close` (premise `#\|C\| < profile_k (instance_profile
  psl211_algebra)`) and `psl211_word_view_proximity` (premise `#\|C\| <= 5`)
  quantify over a coalition, and six is the threshold
  (`profile_k_psl211_algebra`, `psl211_exec.v:132`).
- **S8+N10** (`:244-245`). True and about one term. The `Fail`'s body is
  `var_dist_le2 _ _`, and `var_dist_le2 (R : realType) (A : finType) (P Q :
  R.-fdist A) : var_dist P Q <= 2%:R` (`lib/var_dist_supp.v:53-54`) gives the
  bound two, which is not 2^-40. No universal over a class of facts remains.
- **S9** (`:373`). True: the `Fail` is `erefl` at an equation between two
  adapters, so what fails is convertibility.
- **S10** (`:202-204`). F4.
- **S11** (`pgg_analysis_manifest.v:795-799`). True.
  `psl211_word_view_proximity` is stated at `@sa_coalition_view R
  (instance_profile psl211_algebra) (instance_exec psl211_alldecks_params)
  (amf_sample psl211_word_family R tt) 0 C`, and `psl211_word_sample` and
  `psl211_alldecks_sample` are both `@MkSampleAdapter … ((psl211_inputT *
  pgg_gT psl211_M)%type : finType) … fst snd`, so the reader is one function at
  the two models and only the law differs.
- **S12+N11** (`pgg_analysis_client.v:7`). 80 bytes, checked.
- **N1** (`:313-316`). The adopted sibling wording is
  `pgl27_proximity.v:189-197` verbatim, and the two-coordinate difference it is
  followed by is the one checked under S5+N8. "Its five coordinates" matches
  `AnalysisPathRow`'s five fields.
- **N2** (`:298-300`). The paper's-table sentence is gone; what remains is the
  sibling's docstring (`pgl27_proximity.v:411-413`) with "ideal" dropped, which
  the mathematics forces.
- **N3, N4** (`:47-50`, `:171-175`). Both now say "the port built from its
  witness", against the second conjunct `ExactIndependence (ipc_witness
  (psl211_word_proximity_cert R idx)) = ab_port (published_at
  psl211_row_alldecks_tableau) R idx` and the constructor `ExactIndependence of
  ExactWitness sa` (`pgg_tableau.v:241`). Defect class (v) closed.
- **N5** (`:70-71`), **N6** (`:57`, `:213`), **N7** (`:44-46`), **N23**
  (`:60-65`), **N26** (`:116`), **N24** (`:250-251`). All six checked against
  their declarations: `psl211_word_view_proximity … <= 2%:R^-40`;
  `ipc_eps … = 2%:R^-40`; `psl211_word_proximity_close`'s premise `#\|C\| <
  profile_k …` with `profile_k … = 6`, so "below the six-seat threshold" and
  "a coalition's reading"; `psl211_word_law_le2 … <= 2%:R` and
  `psl211_word_proximity_cert_eps_lt2 … < 2%:R`, both now naming the number two
  and `var_dist_le2` inside their own entries; "the distance field" is the
  manifest's own word for `ipc_close`; "a sum of absolute differences" agrees
  with the file header.
- **N9, N13** (the two renames). See section 2.
- **N12** (`psl211_analysis.v:43`). 80 bytes with `->` in the same column as
  the other thirteen rows of the table, checked mechanically.
- **N14** (`idealized`), **N15** ("the third to publish through that arm"),
  **N16** (paragraph deleted), **N17** (F5), **N18/N27** (decimals dropped; no
  `9.09…` remains anywhere in the six files), **N19**, **N20**, **N21**
  (timing sentence gone), **N22** (comment now inside `Proof.`), **N25**,
  **N28** (no economic metaphor in either new file), **N33** (F3), **N34**
  (`2^-41` at `:36`, `:279` and `pgg_analysis_manifest.v:845`), **N36**. All
  present in the frozen text and all true against their declarations.
- **Metaphor sweep of the two new files**: zero occurrences of price, cost,
  pay, spend, beat, ceiling or earn. The `psl211_reading_constancy.v`
  occurrences are F7 (NOTE, inherited).

### 2. The two renames

`psl211_word_law_le40 (R : realType) : var_dist (psl211_wordP R)
(psl211_alldecksP R) <= 2%:R^-40` states a `<=` at 2^-40: the suffix is right
where `E` was wrong. Every mention moved: the declaration, the `Key results:`
entry of `psl211_word_model.v`, the `exact:` closing
`psl211_word_proximity_close`, the guard comment, Row 11's model-transfer cell
and `landing_fidelity.v`'s restatement and `Print Assumptions` line. A walk over
the whole frozen directory finds `psl211_word_lawE` and `psl211_word_law_tauto`
only in `STATUS.md`, the two audit reports and `verify.py`'s `RENAMED` map,
which is where the probe's names belong.

`psl211_word_law_by_var_dist_le2` names the route the rejected term takes: the
`Fail`'s body is `:= var_dist_le2 _ _`, and the rejection quoted above it is
about `var_dist_le2 ?P ?Q`. The tree's precedent for naming a recorded `Fail`
after subject and route holds.

### 3. The dealt-mode sentences, and the 24-row table

**Verified true.** `psl211_word_sample` is typed `SampleAdapter R
(instance_exec psl211_alldecks_params)`, the all-decks execution parameters,
where the dealt-mode statements are about `psl211_dealt_params`
(`psl211_dealt_constancy_false : ~ coalition_reading_constancy
psl211_dealt_params ((\`U psl211_G_pos) : R.-fdist cutT)`). A walk over every
`.v` file of the tree outside `notes/` finds no `MkSampleAdapter` at
`instance_exec psl211_dealt_params` and none anywhere in `instances/psl211/`
besides `psl211_alldecks_sample` in production and `psl211_word_sample` in the
staged text. So both "this tree carrying no dealt-mode sample adapter"
sentences (`:55-56` and `:962-963`) stand.

Five further rows spot-checked:

- `:32-45` quantitative form. True: `psl211_alldecks_cert_ideal_close` derives
  the distance against the group-uniform law from `ic_Hd` composed with
  `psl211_alldecks_cut_distE`.
- `:207-216`. True: `indistinguishability_cert_reading_constancy` gives
  `coalition_reading_constancy E (ic_ideal cert)` for every certificate, so a
  refutation at a law rules out every certificate holding that law as its ideal
  cut.
- `:690-739`. True: both theorems take `cert : IndistinguishabilityCert
  (psl211_alldecks_sample R)`, so the scope claim is exactly the type. This row
  is also the evidence for F2, where the file header drops that scope.
- `:994-1025`. True: `psl211_alldecks_constancy_set0` proves the constancy
  equation at `set0` for every `ideal : R.-fdist cutT`.
- `:93-134` index blocks, "twelve entries". The count is right, two
  `Definitions:` and ten `Key results:`. The `_word584` entry is F6.

### 4. Deviations, completeness, unrequested changes

**Deviations**: F9. Three labelled, all with the right reason and true text;
two further wording merges, both improvements.

**Completeness**: every id of both reports is disposed of. S1 to S14 appear in
STATUS's table B, with S13 and S14 in their own subsections. N1 to N37 appear in
table C-D-E except N8, N10 and N11, which are disposed of in table B as S5+N8,
S8+N10 and S12+N11. Nothing silently vanished, nothing was declined, and the
four passages the naming report asked a fix pass not to lose are all still in
the frozen text: `psl211_word_law_le2`'s "A proximity certificate carrying two
would be a certificate about nothing", `_cert_secretTE`'s one-point-carrier
sentence, `psl211_word_law_le40`'s "unconditional and information-theoretic …
counts the 3^584 words", and the row docstring's "once twice the sum of eps and
2^-40 stays below 1/660".

**Unrequested changes**: none. Every hunk of the diff outside the Row 10 block
maps to a finding: `landing_fidelity.v` to N13, `psl211_analysis.v:43` to N12,
`psl211_reading_constancy.v` to S1, S2 and S3+S4, `psl211_word_model.v` to N13,
N16, N17, N18/N27 and N28, `psl211_word_proximity.v` to N1 to N7, N9, N13, N14,
N15, N19 to N26, N28, N33, N34, N36 and S7 to S10,
`pgg_analysis_manifest.v` to N13, N14, N25, S5+N8, S6 and S11, and
`pgg_analysis_client.v` to N11/S12.

### 5. Header index blocks, and the three siblings

`psl211_word_model.v`: seven declarations, seven indexed, four under
`Definitions:` and three under `Key results:`, no `Fail` in the file, every
spelling exact after the rename, every description checked.

`psl211_word_proximity.v`: fourteen non-`Fail` declarations, fourteen indexed,
two under `Definitions:` and twelve under `Key results:`; the three recorded
`Fail`s are not indexed, and `psl211_word_law_by_var_dist_le2` appears nowhere
in the header. Spellings exact, mechanically compared against the declaration
heads. Descriptions all match their declarations after N3, N5, N6, N7 and N23.

The three files now read alike where the mathematics is shared: same section
order, same shape of `_close`, `_cert`, `_cert_idealE`, `_cert_epsE`,
`_cert_eps_lt2`, `_rowE`, `_armE` and `_view_proximity`, and the same currency
paragraph in the header. Divergences the mathematics does not force:

1. `five_card_proximity.v:10` still calls an instance "the first carrier of the
   arm", the word sense N15 removed from `psl211_word_proximity.v:9`, which now
   reads "the third to publish through that arm". `pgl27_proximity.v` uses
   neither. Production text.
2. `five_card_proximity.v:271-272` still has the loose "the witness it carries
   … are the model and the witness of" that N4 corrected here and landing 3
   corrected at PGL(2,7). Production text; the naming report already flagged it
   for the owner.
3. The proof comment on the `exact: erefl` row equation: `pgl27_proximity.v:406-407`
   ends at "two rows' coordinates", `psl211_word_proximity.v:182-183` adds
   "where exact: erefl decides it at once". Same placement, different length.
4. `psl211_word_proximity.v` carries the comment on `_cert_idealE` where
   `pgl27_proximity.v` carries it on `_rowE`, because the psl211 `_rowE` closes
   on a manifest row and the pgl27 one on two rows' coordinates. Half forced.

Divergences the mathematics does force, and which are correct here: no
`conclude`, so no `Reprice`, no `_le39`-shaped obligation, no `PublishedRowAt`
and no sentence about a number "concluded at"; no input-indistinguishability
certificate over the word model, so no `_eps_halfE` and no `_arm_neq`; no
ideal-row section, the ideal row being `psl211_rows.v`'s. Checked
mechanically: neither new file contains "conclude", "2^-39" or "half".

### 6. Mechanical

In the six landed files and `landing_fidelity.v`: no line over 80 bytes; every
padded box line closes at column 80, including `pgg_analysis_client.v:7` and
`psl211_analysis.v:43`, the two the reports flagged, and the table row's `->`
sits in the column the other thirteen rows use. No entry of the project's
banned vocabulary list occurs in any of the six files. "Indistinguishability" is
never abbreviated and no `_indist` segment occurs. "View" occurs in no prose of
either new file, only inside `sa_coalition_view` and
`psl211_word_view_proximity`, and the prose says "reading". "Idealised" occurs
nowhere; "idealized" is the spelling in all four places. The only mechanical
defect is the wrapping of F8.
