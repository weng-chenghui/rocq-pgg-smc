# Naming and style audit: terminals below AnalysisBridged (2026-09-20)

Read-only audit, before a landing plan. No repository file was edited except
this one. Nothing was compiled and no Rocq process was started.

Audited: the spec
`notes/20260920-terminals-below-analysis-bridged-probe-design.md`; the probe
`notes/probes/2026-09-20-terminals-below-analysis-bridged/` (`LEDGER.md`,
`t_framework.v`, `t_s5.v`, `t_pgl27.v`, `t_syntax.v`, and `t6_alt_split.v`
where T6 depends on it). Read as landing homes and as the authority on the
existing scheme: `manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v`,
`manifest/pgg_analysis_status.v`, `manifest/pgg_analysis_manifest.v`,
`instances/s5/tableau/s5_tableau_observed.v`,
`instances/s5/tableau/s5_tableau_checks.v`,
`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`,
`instances/s5/tableau/s5_tableau_analysis_bridged.v`, and
`notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md`.

Findings are Z1..Z26. Where a finding overlaps the soundness audit
(`audit-soundness.md`), its Y id is named; nothing here contradicts it.

## Verdict

**NO-GO under these names. GO after Z1 to Z13 are applied.**

Nothing found is a defect of the design. Every name the probe introduces is
free: 46 candidate identifiers were searched across the 225 tracked `.v`
files outside `notes/`, and across the 388 `.v` files of mathcomp and
infotheo under
`/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib/`. Not one is
taken, in the repository or in either library.

What blocks a landing is three things a reader would have to be told, and a
name may not need telling.

1. Two instance names claim in the existing vocabulary what the values do not
   hold. `_published` means, in all seventeen existing values, a program that
   certified a security property at `AnalysisBridged`; these certify none
   (Z2). And `pgl27_word_published_sampled` plus the tree's `E` suffix is
   letter for letter the existing lemma `pgl27_word_published_sampledE`,
   which says something else entirely (Z1).
2. Four statement comments assert the opposite of the statement they sit on,
   or assert something false about the framework (Z4, Z5, Z6, Z7).
3. Two header facts of the landing homes go stale on the same edit (Z12,
   Z13).

The type-level question the owner raised is a SHOULD, not a blocker: the two
"At" do collide, and the better pair is `PublishedAtBound c` beside
`PublishedAtLevel l` (Z14), at a measured cost of 21 lines in 6 files.

## Findings

| id | class | file:line | the name or sentence | rule and problem | replacement |
|---|---|---|---|---|---|
| Z1 | MUST | `t_pgl27.v:34` | `pgl27_word_published_sampled` | One name, one thing. `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:420` already declares `pgl27_word_published_sampledE`, which says that the top-level published value is the named `Sampled` program with its payload and terminal adjoined. The new value's own equations carry the `E` suffix, so `pgl27_word_published_sampled` + `E` is an existing name with an unrelated meaning. The symbol is free; the reading is not, and every instance holding a `Sampled` program reproduces the clash. | `pgl27_word_sampled_published`, under the scheme of Z2. Free. See also Z20: do not land this value at all. |
| Z2 | MUST | `t_s5.v:39`, `t_pgl27.v:34` | `s5_det_published`, `pgl27_word_published_sampled` | `_published` as the last token means, in all seventeen existing values (`pgl27_exact_published`, `five_card_uniform_published`, `psl211_alldecks_published`, `s5_rand_published`, and the rest), a value of type `Published`: a program that certified a security property at `AnalysisBridged`. These two certify none. A name must state what the thing is; here it states what the thing is not. | One scheme, three lines, no existing value renamed: **`<inst>_<discriminator>_<phase>_published`, the phase word written at `Observed` and at `Sampled` and elided at `AnalysisBridged`.** Gives `s5_dealt_observed_published`, `pgl27_word_sampled_published`, and leaves the seventeen exactly as they are. At `Sampled` the discriminator plus the phase word is already the program's own name (`pgl27_word_sampled`), so the value reads as that program handed over. Both free. |
| Z3 | MUST | `t_s5.v:39,45,52,65`; `t_syntax.v:90,100,106` | the `s5_det_` prefix | One word per concept, file-wide. The five-seat dealer-dealt run is `dealt` in every instance file: `s5_dealt`, `s5_dealt_executable`, `s5_dealt_terminates`, `s5_dealt_endpoints`, `s5_dealt_recon`, `s5_dealt_path_observedE`, `s5_dealt_executableE`. Measured: `s5_det` occurs in exactly one declaration in the whole tree, the manifest path `s5_det_path`, and in one comment line. A second identifier family under `s5_det_` makes one run look like two. | `s5_dealt_`, as in Z2. The path equation still reads `s5_dealt_observed_published_pathE : ... = s5_det_path`, which is where the two words meet and is the one place they should. |
| Z4 | MUST | `t_syntax.v:42-45` on the notation at `t_syntax.v:46` | "Two payloads, written transfer first, in the order the manifest column headings run and against the argument order of the terminal itself, as the existing publish rule is." | A statement comment must describe the statement it sits on. The rule is `"s \|> 'publish' 'sampled' a t" := (publish_sampled a t s)`, used at `t_syntax.v:69` as `\|> publish sampled BaselineClassicalOnly NoModelComparison`: assumption first, transfer second, which is the terminal's own argument order and the opposite of what the comment claims. Same as soundness Y6. | Swap the rule to `"s \|> 'publish' 'sampled' t a"` (see Q3 below) and write: "The transfer status and then the assumption status, in the order the manifest's path record carries them and the order the existing terminal rule writes them." |
| Z5 | MUST | `t_framework.v:104` on the lemma at 105-108 | "The Sampled twin of the completion equation." | No narrative or metaphor word for a mathematical relation, and a statement comment states the fact and its position, not a relation to a neighbouring lemma. "Twin" is both. The sentence also states nothing a reader could check against the statement. | "The path of a program published at Sampled records Sampled. Conversion decides it, so a reader of the value learns the level its program stopped at without consulting the manifest." |
| Z6 | MUST | `t_framework.v:215-219` on the `Variant` at 220 | "The two statuses TransferStatus also offers name a transfer theorem, which a program with no security evidence has not proved." | False against the pinned docstring of `TransferStatus` (`manifest/pgg_analysis_status.v:63-71`), which separates `IdealFinite` and `NegativeTransfer`, each naming a theorem, from `StaticExecutedOnly` and `NoModelComparison`, which "carry no such theorem". The two statuses this variant refuses are `IdealFinite` and `StaticExecutedOnly`, and only the first of those names a theorem. The probe itself compiles the docstring's own split in `t6_alt_split.v`; the comment here was not brought back to it. The type name `SampledTransfer` is a second problem: a transfer is not sampled. | Decided by the owner's T6 answer. If the restriction lands, take `t6_alt_split.v`'s split with the soundness audit's names: `TransferStatusWithoutTheorem`, constructors `SampledNoModelComparison` and `SampledStaticExecutedOnly`, map `transfer_of_sampled`; comment: "The two transfer statuses that assert no theorem about an idealized model. A program at Sampled has proved run correctness and the link lemma and nothing about an ideal, so these are the two its own proposition supports." If the restriction does not land, none of these names lands and the sentence goes with them. All names free. |
| Z7 | MUST | `t_framework.v:130-133` on the definition at 134 | "The Observed terminal has no payload and therefore no such spelling." | False about the framework as written. `publish_observed` has one payload, the assumption status; what it lacks is a *second* one. A reader who believes the sentence will look for an assumption status somewhere else. | The declaration goes away under Z8. If it is kept, write: "The Sampled terminal with its data and proof taken separately, so the transfer status is the line's payload and the terminal sequences with the bind." |
| Z8 | SHOULD | `t_framework.v:68,78,134,141` | `publish_observed`, `publish_sampled`, `publish_sampled_step`, `publish_sampled_stepE` | Two shapes for one terminal is one shape too many, and the probe already carries both plus an equation between them. The existing `publish` is bind-shaped, `publish a {c} q pf t`, which is why `\|> publish t a` expands to `s ;;; publish a of t`. Giving the two new terminals the same shape, `publish_observed (q) (pf) (a)` and `publish_sampled (a) (q) (pf) (t)`, makes all three terminals one shape, lets both new rules expand through `;;;` like every other line of the surface, and deletes `publish_sampled_step` and `publish_sampled_stepE`. A constant payload family is already precedent: `publish`'s own payload is a bare `TransferStatus`. | Land the bind shape; drop the two `_step` declarations. Cost: the instance writes `s5_dealt \|> publish Observed a` rather than `publish_observed a s5_dealt`, which is what the surface is for and what every other instance value already does. |
| Z9 | MUST | `t_s5.v:49-51` | "The mutation: the same program published under the baseline assumption status does not build the manifest's path" | No plan or ledger token in a statement comment. "Mutation" is the spec's word for a test, not a word about the term. | The recorded rejection moves to `instances/s5/tableau/s5_tableau_checks.v` (Z21), whose header word is a term the kernel refuses. There: "The same program published under the baseline assumption status: the path it builds is not the manifest's, which records the accepted group-order fact." The rejection says that of the one term written under it and of no other, per the TEMPLATE rule. |
| Z10 | MUST | `t_syntax.v:87-89` | "The last line is the new terminal, and the four above it are the surface as it stands." | No status or history words in a statement comment: "new" dates the declaration, "as it stands" reports a state of the tree. | The whole-program spelling stays in the probe (Z20). Where the value lands, its comment says what the value is and what a reader of it learns, not which line is recent. |
| Z11 | MUST | all four probe files | `(* ` openers with 3-space continuation | Measured: `instances/s5/tableau/s5_tableau_observed.v` has 13 `(**` docstrings and zero 3-space continuation lines; `manifest/pgg_tableau.v` and `manifest/pgg_tableau_syntax.v` have zero `(**` and use `(* ` with 3-space continuation. The probe uses the manifest style throughout, which is right for two homes and wrong for the third. | Convert every docstring landing in `instances/s5/tableau/` to `(** ` with 4-space continuation. The two manifest homes keep the probe's style unchanged. |
| Z12 | MUST | `manifest/pgg_tableau_syntax.v:40` | "The separator of the two terminal rules is \|>." | The sentence counts the rules. Today two rules use `\|>`, `\|> conclude c by p` and `\|> publish t a`. After this batch, four. A header fact that the same edit falsifies must move in the same edit. | "The separator of the terminal rules is \|>." and keep the measurement sentence that follows unchanged, since it is about the token and not the count. |
| Z13 | MUST | `manifest/pgg_tableau.v:80-146`; `manifest/pgg_tableau_syntax.v:64-88,90-111`; `instances/s5/tableau/s5_tableau_observed.v:29-51` | the three `Definitions:` / `Key results:` blocks and the keyword paragraph | Every home indexes every non-`Fail` declaration; the probe drafts no entry. The syntax header's keyword paragraph must also gain the two level tokens, and soundness Y7 measured what it must say about them. Overlaps Y12. | The entries and their columns are drafted in the placement table below. |
| Z14 | SHOULD | `t_framework.v:29` against `manifest/pgg_tableau.v:952` | `PublishedAtLevel l` beside `PublishedAt c` | The two "At" do collide, and not because of the word. `PublishedAt` is indexed by a `ConcludedBound`, a number a program publishes; `PublishedAtLevel` by a `CompletionLevel`, how far the program got. Neither name says which, so a reader meeting both learns that there are two published records and not what separates them. The sharper edge: `PublishedAtLevel AnalysisBridged` is inhabited and its field types are convertible with `Published`'s, since `StackProp AnalysisBridged q` *is* `BridgedProp no_concluded_bound q` (`manifest/pgg_tableau.v:584`), yet the two are distinct records. A name that reads as a generalisation of `Published` but is not one is the one thing the reader must not guess. | **The better pair is `PublishedAtBound c` and `PublishedAtLevel l`.** Each says what it is indexed by; neither can be read as the other's generalisation. Measured cost of the rename: `PublishedAt` is written bare 21 times, 11 in `manifest/pgg_tableau.v` and 10 across `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`, `five_card_tableau_checks.v`, `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` and `pgl27_tableau_checks.v`; every occurrence is a type ascription, no proof script changes; `MkPublished` occurs twice, both in `manifest/pgg_tableau.v`, and becomes `MkPublishedAtBound`; the notation `Published` and the three field names are untouched, so the seventeen values and all five readers keep their text. Both names free. It does change an existing declaration, which the spec's soundness invariant forbids in this batch, so it is the owner's call. **Fallback without the rename:** keep `PublishedAtLevel`, and make the record's statement comment and its index entry carry the two sentences a reader would otherwise have to guess: the index is a completion level and not a bound, and at `AnalysisBridged` a program is published with `publish` into `PublishedAt`, never into this family (soundness Y3). |
| Z15 | SHOULD | `t_framework.v:154` | `level_run_correct` | The level-indexed proposition families of this file are `StackProp`, `BridgedProp`, `EvidenceProp`, and the two certificate propositions `IndistinguishabilityPropAt`, `IdealProximityPropAt`. All are UpperCamel and end in `Prop`. This one is neither, so a reader scanning the file reads it as a boolean or a projection. | `RunCorrectProp (l : CompletionLevel) : StackAt l -> Prop`. Free. Keep the probe's comment, which already states the vacuity at the two bottom levels (soundness Y10). |
| Z16 | SHOULD | `t_syntax.v:39,46` | the surface tokens `observed`, `sampled` | The token after a literal verb in this surface is the framework's own constructor name, spelled as the framework spells it: `certify ExactIndependence`, `certify InputIndistinguishability`, `certify IdealProximity`. The level constructors are `Observed` and `Sampled` (`manifest/pgg_analysis_status.v:60-61`). The probe writes two lowercase tokens that are no identifier of the framework, so a reader cannot tell whether the token names the level or is a slot. | `s \|> publish Observed a` and `s \|> publish Sampled t a`. Both tokens still follow a literal, so the measured keyword rule of the syntax header is unchanged and nineteen stays nineteen; `t_keyword_check.v` must be re-run at the capitalized tokens before the landing, since a measurement of one spelling is not a measurement of the other. |
| Z17 | SHOULD | `t_framework.v:232`, `t_pgl27.v:74` | `publish_sampled_restricted`, `pgl27_word_published_restricted` | If T6 restricts the payload, the restricted terminal is the only `Sampled` terminal and should carry the plain name; landing both `publish_sampled` and `publish_sampled_restricted` leaves a later author to choose between a terminal that asserts a theorem it does not have and one that does not, by name alone. | If the restriction lands: the restricted terminal **is** `publish_sampled` and the unrestricted one does not land. If it does not land: neither `SampledTransfer` nor `publish_sampled_restricted` lands, and `publish_sampled`'s comment carries the disclosure sentence the soundness audit requires. |
| Z18 | NOTE | `t_framework.v:30-32` | `published_level_at`, `published_level_path`, `published_level_thm` | Free, and parallel to `published_at`, `published_path`, `published_thm`, which is the right neighbour to copy. The middle one is the one a reader can misparse, as "the path of the published level" rather than "the manifest path of a program published at a level". The sibling `RestatedTableau` uses a two-letter record prefix instead (`rq_at`, `rq_thm`), which would not be read at all. | Keep all three. `published_level_at` sets the pattern one line above, which is enough to fix the reading of the second. Do not adopt a short prefix. |
| Z19 | NOTE | `t_framework.v:167,182` | `run_correct_of_level`, `view_identification_of_sampled` | `_of` is MathComp's and the carrier qualifier is last and spelled out, which is the rule. `run_correct_of_level` reads as "of a `PublishedAtLevel`" and `view_identification_of_sampled` as "of one published at `Sampled`". Both survive the Z14 rename unchanged. | Keep. `view_identification_of_sampled` is 30 characters and exceeds the index name column of `manifest/pgg_tableau.v`, so its index entry takes the two-line form; see the placement table. |
| Z20 | SHOULD | `t_pgl27.v:34,65,74`; `t_syntax.v:90,100,106,117,118,122` | the PGL(2,7) `Sampled` value and the whole-program surface values | Placement, answered in full under Q4 below. In short: the manifest carries no path at `Sampled` over the word model, so a landed value there describes a path the manifest does not hold, beside `pgl27_word_published`, which proves strictly more about the same model. The surface values `s5_det_published_program`, its two equations and the three `probe_` identifier checks measure the notation and are evidence, not declarations an instance owes. | Keep all of them in the probe. Land the `Sampled` terminal itself, whose first instance value arrives with the refutations that need it. |
| Z21 | SHOULD | `t_s5.v:52,93,96,99` | the four S5 rejections | `instances/s5/tableau/s5_tableau_checks.v` is the instance's home for a refused term, by its own header. The four belong there, as a third recorded boundary. Overlaps soundness Y13, which names three; the assumption-status rejection of `t_s5.v:52` is the fourth. | Land all four there, in that file's style, with a header paragraph naming the boundary: no security reader applies to a program published below `AnalysisBridged`, and the path a terminal builds records the assumption status it was published under. Respect the TEMPLATE rule against reading a universal off one refused term. |
| Z22 | NOTE | `t_pgl27.v:31-33` | "The transfer status is the refusal to compare" | No metaphor for a mathematical relation; a status does not refuse. Soundness Y17 gives the same finding and the same replacement. | "The transfer status is `NoModelComparison`: the program names a model and claims no relation between it and an idealized one." |
| Z23 | NOTE | `t_framework.v:24-28` | "It sits beside PublishedAt and does not replace it" | Motivation about the edit rather than about the object; the rule keeps design rationale out of the rendered statement. The two sentences around it are exactly right and must survive: what the record holds, and that a value asserts `StackProp l` and nothing above it. Soundness Y1 requires a further sentence, that the terminals and not the record tie the path to the data. | "A program's data at one completion level, a manifest path, and the proposition that level carries about the data. The terminals below build the path from the program's own data; the record does not force the two to agree. A value asserts `StackProp l` and nothing above it, so no coalition, privacy or security statement follows from one below `AnalysisBridged`." Plus the Y3 sentence from Z14. |
| Z24 | NOTE | `t_framework.v:34-35,38-39` | "A program whose last statement is the three run facts" / "A program whose last statement names an analysis model family" | Type-honest phrasing. A statement is not a fact, and neither notation names a program: each names a program handed over with its path and its proposition. | "A program that stopped at `Observed`, handed over with its path: it carries run correctness of the observed execution and names no model." / "A program that stopped at `Sampled`, handed over with its path: it carries run correctness and the link lemma of the model family it named, and no security evidence." |
| Z25 | NOTE | `t_framework.v:99`; `t_pgl27.v:37` | "The model slot of such a path is empty." / "The level of the path this terminal builds." | A statement comment carries the fact and its position; these carry the fact alone, and the fact is already the statement. | "...is empty: the program named no model, so nothing in the path points at a distribution." / "...is `Sampled`, which is as far as the program's own proposition reaches." |
| Z26 | NOTE | `t_s5.v:60-64` | "It is the statement the manifest pins for this path's correctness theorem" | The manifest's correctness cell for this path names three aliases and only the capability table pins one. Soundness Y9, same replacement. | Name `S5Analysis.observed_recovers`, and say that the other two conjuncts of the same `And3` come off the same reader. |

## The four questions

### Q1. `PublishedAt c` beside `PublishedAtLevel l`

They collide, and the better pair is **`PublishedAtBound c` and
`PublishedAtLevel l`**. Full reasoning, measured rename cost and the
no-rename fallback are in Z14.

### Q2. One scheme for the instance values

**`<inst>_<discriminator>_<phase>_published`, the phase word written at
`Observed` and at `Sampled` and elided at `AnalysisBridged`.**

| phase | scheme | this batch | the existing seventeen |
|---|---|---|---|
| Observed | `<inst>_<disc>_observed_published` | `s5_dealt_observed_published` | none, and none is renamed |
| Sampled | `<inst>_<disc>_sampled_published` | `pgl27_word_sampled_published` | none, and none is renamed |
| AnalysisBridged | `<inst>_<disc>_published` | none | all seventeen, unchanged |

Why the phase word goes before `published` and not after. After it,
`<inst>_<disc>_published_sampled` is, with the tree's `E` suffix, the
existing lemma name `pgl27_word_published_sampledE` (Z1). Before it, the
name at `Sampled` is the program's own name plus the terminal, because
`<inst>_<model>_sampled` already names the program there, so
`pgl27_word_sampled_published` reads as what the term is. `_published_at_`
was considered and rejected: `_at` already names the data field, as
`five_card_repeated_published39_atE` shows.

Equations follow the tree's suffixes unchanged: `_pathE` for the path
equation, `_recovers` for the run-correctness statement read off the value.
`_propertyE` has no analogue below `AnalysisBridged` and none is owed.

### Q3. The argument order of the surface

**Transfer status first, assumption status last, in all three rules.**

- The existing rule writes it that way and 31 uses in the tree follow it.
- The order is the manifest's own. `AnalysisPath`
  (`manifest/pgg_analysis_manifest.v:941-960`) carries `ap_transfer` then
  `ap_assumptions`, and every path block of the manifest header prints
  `| completion level | ... | transfer status | ... | assumption status |`
  in that order (for instance `manifest/pgg_analysis_manifest.v:481-484`).
- It puts the assumption status last in all three rules, including the
  `Observed` rule, whose only payload is the assumption status. A reader who
  learns one rule can then read the other two.

So: `s |> publish Observed a`, `s |> publish Sampled t a`, beside the
existing `s |> publish t a`. The probe's rule writes `a t` while its comment
claims `t a`; the comment is what the landing should keep and the rule is
what must change (Z4). With Z8 the two new rules expand through `;;;` like
every other line, so all three terminals have one argument order and one
shape.

### Q4. What lands where, and what does not

**`instances/s5/tableau/s5_tableau_checks.v` receives the four S5
rejections.** Its header already declares it the home of a term the kernel
refuses at this instance, and the batch's rejections are exactly that: the
three security readers that do not apply to a value published at `Observed`,
and the path that is not the manifest's under the baseline assumption status.
The framework-level rejections have no such home, since `manifest/pgg_tableau.v`
carries no `Fail` today, and they stay in the probe. Details in Z21.

**The PGL(2,7) `Sampled` value does not land.** Three reasons.

1. The manifest holds no path at `Sampled` over the word model. Its only
   path over that model is `pgl27_word_path`, at `AnalysisBridged`, and the
   probe's own T7 evidence is that the published path is not that one. The
   batch exists so that a manifest path below the bridge can carry the
   proposition its program proved; a value whose path matches no manifest
   path inverts that.
2. It would sit in the same file as `pgl27_word_published`, which proves
   strictly more about the same model, and a reader would have to work out
   which of two published values over one model is the instance's claim.
3. Its purpose is to show that the terminal typechecks, which the probe
   records and the ledger cites. That purpose is served where it is.

The `Sampled` terminal itself lands: the record is indexed by the level, the
refutation work named in the spec needs `publish_sampled`, and the terminal
without an instance value asserts nothing.

**The whole-program surface values stay in the probe.** `s5_det_published_program`,
`s5_det_published_programE`, `s5_det_published_program_pathE` and the three
`probe_` identifier checks measure the notation. The instance value should be
written in the surface from the named program, as `s5_rand_published` is
written from `s5_supplied`:

```coq
Definition s5_dealt_observed_published : PublishedObserved :=
  s5_dealt |> publish Observed (AcceptsAxioms [:: AxS5GroupOrder]).
```

so no second spelling exists at the instance and no equation between
spellings is owed. The tree keeps the "which statement a rule expands to"
equations in `manifest/pgg_tableau_syntax.v` (`dealt_params_stepE`), and
there is none for `|> publish t a` either.

## The proposed final name list

Every name below was searched across the 225 tracked `.v` files outside
`notes/` and across mathcomp and infotheo. **All are free.**

### `manifest/pgg_tableau.v`

| probe name | landing name | note |
|---|---|---|
| `PublishedAtLevel` | `PublishedAtLevel` | with `PublishedAt` renamed to `PublishedAtBound` if the owner takes Z14; otherwise unchanged with the two extra comment sentences |
| `MkPublishedAtLevel` | `MkPublishedAtLevel` | |
| `published_level_at`, `published_level_path`, `published_level_thm` | unchanged | Z18 |
| `PublishedObserved`, `PublishedSampled` | unchanged | the names instance files write |
| `publish_observed` | `publish_observed` | bind shape, `(q) (pf) (a)`, Z8 |
| `publish_sampled` | `publish_sampled` | bind shape, `(a) (q) (pf) (t)`, Z8; the restricted payload if T6 restricts, Z17 |
| `publish_sampled_step`, `publish_sampled_stepE` | do not land | Z8 |
| `publish_observed_completionE`, `_transferE`, `_modelE` | unchanged | |
| `publish_sampled_completionE`, `_transferE`, `_modelE` | unchanged | |
| `level_run_correct` | `RunCorrectProp` | Z15 |
| `run_correct_of_level` | `run_correct_of_level` | Z19 |
| `view_identification_of_sampled` | `view_identification_of_sampled` | Z19 |
| `SampledTransfer` | `TransferStatusWithoutTheorem`, or does not land | Z6, Z17 |
| `SampledNoModelComparison`, `SampledNegativeTransfer` | `SampledNoModelComparison`, `SampledStaticExecutedOnly`, or do not land | Z6 |
| `transfer_of_sampled` | `transfer_of_sampled`, or does not land | Z6 |
| `publish_sampled_restricted`, `publish_sampled_restricted_transferE` | do not land under these names | Z17 |

### `manifest/pgg_tableau_syntax.v`

| probe rule | landing rule |
|---|---|
| `"s \|> 'publish' 'observed' a"` | `"s \|> 'publish' 'Observed' a"` := `(s ;;; publish_observed of a)` |
| `"s \|> 'publish' 'sampled' a t"` | `"s \|> 'publish' 'Sampled' t a"` := `(s ;;; publish_sampled a of t)` |

Z16 for the capitalized tokens, Q3 for the order, Z8 for the bind spelling.
Both tokens follow a literal, so no keyword is reserved and the header's
count of nineteen is unchanged; the measurement must be re-run at the
capitalized spelling.

### `instances/s5/tableau/s5_tableau_observed.v`

| probe name | landing name |
|---|---|
| `s5_det_published` | `s5_dealt_observed_published` |
| `s5_det_published_pathE` | `s5_dealt_observed_published_pathE` |
| `s5_det_published_recovers` | `s5_dealt_observed_published_recovers` |
| `s5_det_published_program`, `_programE`, `_program_pathE` | do not land, Z20 |

### `instances/pgl27/tableau/`

Nothing lands. If the owner overrules Z20, the name is
`pgl27_word_sampled_published` and its equations
`pgl27_word_sampled_published_completionE` and `_modelE`.

## Placement

Layout measured in each home: box banners are exactly 80 bytes in all three
files and in the probe; no probe line exceeds 80 bytes.

| home | what lands | where | header work |
|---|---|---|---|
| `manifest/pgg_tableau.v` | `RunCorrectProp`, `PublishedAtLevel` with its constructor and three fields, the two notations, `publish_observed`, `publish_sampled`, the six path-field equations, `run_correct_of_level`, `view_identification_of_sampled`, and the `Arguments` lines soundness Y11 requires | one new section after `security_property_of` (ends line 1016) and before the banner "Where a program's security property is decided" (line 1018). Keeping the whole batch in one section, rather than putting `RunCorrectProp` beside `StackProp` at line 586, keeps a reader's one question in one place | new banner, 80 bytes, space before the closing delimiter, for instance `(*     Handing a program over below AnalysisBridged                          *)`. One new header paragraph after the paragraph at lines 69-78, saying what a program that stops below the bridge hands over and what a reader of such a value does not learn. Index entries below |
| `manifest/pgg_tableau_syntax.v` | the two notation rules, each with its comment | at the end of the file, after the existing `\|> publish t a` rule (lines 418-422) | Z12 fixes the count at line 40. The keyword paragraph (lines 64-80) gains the two level tokens in the sentence listing tokens that follow a literal and stay identifiers, with the re-measured date, and the sentence soundness Y7 requires: inside the publish position the two tokens are captured by the new rules and are not available there as status names. No `Definitions:` entry is owed, since that block indexes builders and not notations |
| `instances/s5/tableau/s5_tableau_observed.v` | `s5_dealt_observed_published`, `s5_dealt_observed_published_pathE`, `s5_dealt_observed_published_recovers` | in the existing section "The dealer-dealt run", after `s5_dealt_executableE` (ends line 109) and before the banner "The supplied run" (line 111) | the header's second paragraph (lines 13-21) gains a sentence: the dealt program is handed over at this level with the path it answers, and what such a value carries and does not. Index entries below. Docstrings in this file's style, `(** ` with 4-space continuation (Z11). **Imports:** `_recovers` needs `OE`, `exec_decode`, `pgg_gT` and `mp_M`, so the file gains `From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.` and `From pgg_smc Require Import pgg_observed_execution.`, which `t_s5.v:14-15` already had to add |
| `instances/s5/tableau/s5_tableau_checks.v` | the four recorded rejections of Z21 | a new section after "The tolerated coalition size is read off the algebra" | a third paragraph in the header naming the boundary. This file has no index block and owes none |
| probe, not landed | the PGL(2,7) `Sampled` value and its three lemmas, the whole-program surface values, the three identifier checks, both T6 variants not chosen, `publish_sampled_step` and its equation | Z8, Z17, Z20 | |

### Index entries, at each file's own columns

`manifest/pgg_tableau.v`: name at column 6, `==` at column 29, description
at column 32, wrapped lines resuming at column 32; a name wider than 22
characters takes a line of its own with `==` at column 29 beneath it. Add to
`Definitions:`, in declaration order, after `security_property_of`:

```
PublishedAtLevel      == a program's data at one completion level, its
                         manifest path and that level's proposition
PublishedObserved     == a program handed over carrying run correctness
PublishedSampled      == a program handed over carrying its model's link
                         lemma
publish_observed      == the terminal of a program that stops at run
                         correctness
publish_sampled       == the terminal of a program that stops at its named
                         model
RunCorrectProp        == run correctness at each completion level
run_correct_of_level  == run correctness of a program published below
                         AnalysisBridged
view_identification_of_sampled
                      == the link lemma of a program published at Sampled
```

and to `Key results:` the six path-field equations, one entry each, in the
two-line form where the name exceeds the column:

```
publish_observed_completionE
                      == the path of a program published at Observed
                         records Observed
publish_observed_transferE
                      == it records no model comparison
publish_observed_modelE
                      == its model slot is empty
publish_sampled_completionE
                      == the path of a program published at Sampled records
                         Sampled
publish_sampled_transferE
                      == it records the transfer status the program's last
                         line wrote
publish_sampled_modelE
                      == its model slot is the family the program named
```

If Z14 is taken, the existing entry at line 109 becomes `PublishedAtBound`
and keeps its description.

`instances/s5/tableau/s5_tableau_observed.v`: name at column 6, `==` at
column 27, description at column 30. All three names exceed the column, so
all three take the two-line form, as `s5_dealt_path_observedE` already does
at lines 36-38. Add to `Definitions:`:

```
s5_dealt_observed_published
                     == the dealer-dealt program handed over with the
                        manifest path it answers
s5_dealt_observed_published_recovers
                     == the endpoints of that run decode to the dealt
                        position, read off the published value
```

and to `Key results:`:

```
s5_dealt_observed_published_pathE
                     == the path that program builds is the manifest's
                        deterministic path
```

`manifest/pgg_tableau_syntax.v`: `Definitions:` uses `==` at column 19 and
`Key results:` at column 25. Nothing is added to either, since only
notations land there.
