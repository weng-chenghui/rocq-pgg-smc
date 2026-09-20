# Naming and style audit of the landing: terminals below AnalysisBridged (2026-09-21)

Read-only. No repository file was edited except this one. Nothing was compiled,
no Rocq process was started, and no git command that writes was run.

Audited: the working tree on top of `b807b6b`, `git diff HEAD` over
`manifest/pgg_tableau.v` (202 added lines), `manifest/pgg_tableau_syntax.v`
(22), `instances/s5/tableau/s5_tableau_observed.v` (50) and
`instances/s5/tableau/s5_tableau_checks.v` (38), read against the seven
decisions of `notes/20260920-terminals-below-analysis-bridged-probe-design.md`,
the earlier audit `audit-naming.md` (Z1 to Z26) and `LANDING.md`. The earlier
audit was drafted for a record family that decision 1 replaced by two records,
so its entries for `PublishedAtLevel`, `RunCorrectProp` and
`run_correct_of_level` are not owed and their absence is not a finding.

## Verdict

**NO-GO under the landed text. GO after the eleven MUST rows are applied.**

Nothing found is a defect of the design, and no identifier collides: all 29
identifiers the landing introduces were searched across the 225 tracked `.v`
files outside `notes/` and the 1153 `.v` files of mathcomp and infotheo under
`/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib/`; every
occurrence of every one of them is inside the four landed files themselves.

What blocks the landing is four things.

1. **Four statement comments and one notation comment misattribute the path's
   coordinates.** Three of a path's five coordinates are constants the terminal
   writes, one is read off the program's data and one is the line's payload.
   The landing writes "all read off the program's own data" (B3), "the path is
   built from the program's own data:" followed by all four (B4), and "four of
   its five coordinates are fixed by the terminal" (B5). The third contradicts
   the docstring two declarations above it, which says the author writes the
   assumption status. This is the Z7 class: a reader who believes the sentence
   looks for the assumption status in the wrong place.
2. **One name reuses a suffix for a second carrier.** `_of_sampled` means "of a
   program published at Sampled" in `run_correct_of_sampled` and
   `view_identification_of_sampled`, both of which take a `PublishedSampled`.
   `transfer_of_sampled` takes a `TransferStatusWithoutTheorem` (B7).
3. **Two header facts over-claim.** The keyword paragraph puts the two level
   tokens in the wrong one of its two lists, in a sentence that then contradicts
   itself (B1), and ends on a count of instance uses that the next published
   program falsifies (B2).
4. **The new banner of the checks file asserts a general impossibility** that
   the file's own header forbids, and does not cover the fourth rejection under
   it (B9).

Layout is clean: no added line exceeds 80 bytes, both new banners are exactly
80 bytes with a space before the closing delimiter, the manifest files keep
`(* ` with 3-space continuation and the S_5 file `(** ` with 4-space
continuation, and no added comment block has an orphan short line
mid-paragraph. Index completeness passes in both indexed files.

## Findings

| id | class | file:line | the name or sentence | rule and problem | replacement |
|---|---|---|---|---|---|
| B1 | MUST | `manifest/pgg_tableau_syntax.v:80-84` | "Observed and Sampled belong to that first list too, measured on 2026-09-21: ... and each is still a binder name and still the CompletionLevel constructor it names" | The paragraph holds two groups: the nineteen identifiers reserved as global keywords, named first, and the tokens that follow a literal and stay identifiers, named second. Observed and Sampled are in the second group, and the sentence says so itself one clause later, so "that first list" makes the sentence contradict itself. "still", twice, also dates the measurement against an earlier state; the paragraph's own word for this outcome is "stay". | "Observed and Sampled follow a literal too, measured on 2026-09-21: each follows the literal publish in one of the two terminal rules below AnalysisBridged, and each stays a binder name and stays the CompletionLevel constructor it names, in a file whose Require lines are ssreflect and this one." |
| B2 | MUST | `manifest/pgg_tableau_syntax.v:85-87` | "so a transfer status spelled Observed or Sampled could not be written where the other thirty-one uses write theirs." | A header fact that a routine edit falsifies, which is what Z12 was about, and it carries no measurement date while every other count in the paragraph does. Measured: `\|> publish` occurs 33 times in the tracked tree now, 31 of them through the three-payload rule, so the next instance that publishes at AnalysisBridged makes the sentence wrong. The fact decision 4 asks for is the capture, not the census. | "Inside the publish position the two tokens are taken by those two rules, so the transfer-status slot of the three-payload rule cannot be filled by a token spelled Observed or Sampled." |
| B3 | MUST | `manifest/pgg_tableau_syntax.v:431-432` on the rule at 433 | "One payload, the assumption status: the level, the model slot and the transfer status of the path are all read off the program's own data." | False about the terminal the rule expands to. `publish_observed` writes `@MkAnalysisPath (ob_obs q) Observed None NoModelComparison a`: only the observed execution is read off the program's data; the level, the empty model slot and NoModelComparison are constants of the terminal, and the assumption status is the payload. Same class as Z7. | "One payload, the assumption status. The terminal takes the observed execution from the program's own data and writes the other three coordinates itself: the level, the empty model slot and NoModelComparison." |
| B4 | MUST | `manifest/pgg_tableau.v:1115-1119` on `publish_observed` at 1123 | "The path is built from the program's own data: the observed execution the program reached, the level Observed, the empty model slot, and NoModelComparison, which is not a payload because ..." | Same misattribution as B3, in the home file: the colon makes all four items data-derived, and three of them are constants the terminal writes. The clause explaining NoModelComparison is right and must survive. | "The path takes the observed execution from the program's own data and the terminal writes the other three coordinates: the level Observed, the empty model slot, and NoModelComparison, which is not a payload because a program naming no model compares its execution with nothing." |
| B5 | MUST | `instances/s5/tableau/s5_tableau_observed.v:139-140` on the lemma at 143 | "Four of its five coordinates are fixed by the terminal and the fifth is the observed execution s5_dealt_path_observedE already identifies" | False, and it contradicts the docstring at 127-134 of the same file, which says the assumption status is written here by the author. Three coordinates are fixed by `publish_observed`; the assumption status is this file's payload, `AcceptsAxioms [:: AxS5GroupOrder]`, and it matches the manifest's `s5_det_path` because this file writes the same status, not because the terminal supplies it. | "Three of its five coordinates are fixed by the terminal, the assumption status is the payload this file writes, and the fifth is the observed execution s5_dealt_path_observedE already identifies." |
| B6 | MUST | `instances/s5/tableau/s5_tableau_observed.v:141-142` | "so what the equation adds is that the theorem now travels beside the path rather than the path being a description a reader matches by eye." | Three rules at once: "now" dates the declaration; "travels beside" and "matches by eye" are metaphors for a mathematical relation; "what the equation adds" is meta about the edit rather than the position of the statement. | "A reader of the value therefore holds the manifest's row for this program and the proof of run correctness in one term." |
| B7 | MUST | `manifest/pgg_tableau.v:1108` (and its uses at 1142, 1183, index entry at 145) | `transfer_of_sampled` | One word per concept, file-wide. In this file `_of_sampled` means "of a program published at Sampled": `run_correct_of_sampled` and `view_identification_of_sampled` both take a `PublishedSampled`. This one takes a `TransferStatusWithoutTheorem`, so the suffix names two carriers and the name reads as "the transfer status of a sampled thing", which no argument of it is. The carrier qualifier must be last and spelled out, and here the carrier is the payload type. | `transfer_of_without_theorem`. Free in the 225 tracked `.v` outside `notes/` and in the 1153 `.v` of mathcomp and infotheo. Four sites, all in `manifest/pgg_tableau.v`: the definition, `publish_sampled`, `publish_sampled_transferE`, the index entry. Index entry becomes the two-line form, B12. |
| B8 | MUST | `instances/s5/tableau/s5_tableau_checks.v:94` | `s5_dealt_baseline_pathE` | The name does not name the value whose path equation is refused. `s5_dealt_baseline` is no program of this instance: the run is `s5_dealt` and `baseline` is an assumption status. The tree's precedent for a refused path equation is the published value's full name, then the coordinate that differs, then `_pathE`, as in `five_card_repeated_indistinguishability_published_uniform_pathE` (`instances/kim2025/tableau/five_card_tableau_checks.v:129`). The `E` suffix on a refused equation is precedented in three files and stays. | `s5_dealt_observed_published_baseline_pathE`. Free. |
| B9 | MUST | `instances/s5/tableau/s5_tableau_checks.v:73` | banner "No security reader applies to a program published at Observed" | The file's own header at lines 6-10 says a recorded rejection "says what it says about the one term written under it and about no other term ... and states no general impossibility". The banner is a universal over readers, and the section exercises two of the four security readers (`view_secrecy_of`, `security_property_of`; `view_indistinguishability_of` and `view_proximity_of` are untouched). It also does not cover the fourth rejection under it, which is about the assumption status and no reader. | Exactly 80 bytes, space before the closing delimiter:<br>`(*     Terms refused at the dealer-dealt program published at Observed        *)` |
| B10 | MUST | `manifest/pgg_tableau.v:1196-1198` on `run_correct_of_observed` at 1199 | "so the terminal hands back what the instance discharged and the reader adds nothing to it." | The terminal is `publish_observed` and hands nothing back; this reader is what returns the field. The sentence gives one act two subjects and then says the second adds nothing, which leaves a reader unable to tell which declaration is being described. The preceding clause, that the proof is the observed execution's own field, is faithful to `observed_correct` at 468-472 and must survive. | "so this reader hands back what the instance discharged and adds nothing to it." |
| B11 | MUST | `manifest/pgg_tableau.v:1102-1103` on the Variant at 1104 | "The restriction is on the terminal below and not on the record: a value written by hand still carries any path." | The sentence is about `PublishedSampled` and `publish_sampled`, not about the type it sits on, and a statement comment describes the statement it sits on (Z4). "still carries" also reads as a change over time where the fact is a permission. | Move it onto `publish_sampled` and write: "The restriction is carried by this terminal and not by the record, whose path field accepts any path." |
| B12 | SHOULD | `manifest/pgg_tableau.v:145` | index entry `transfer_of_sampled == the manifest status such a payload stands for` | An index entry is read alone, and "such a payload" has no antecedent in the block. With the B7 rename the name is 27 bytes, wider than the 22-byte name column, so it takes the two-line form. | Three lines, each exactly 80 bytes, at the file's columns:<br>`(*   transfer_of_without_theorem                                              *)`<br>`(*                          == the manifest transfer status a payload of the  *)`<br>`(*                             Sampled terminal stands for                    *)` |
| B13 | SHOULD | `manifest/pgg_tableau.v:146,148` | `publish_observed == the terminal of a program that stops at run correctness`, `publish_sampled == ... stops at its named model` | One word per concept inside one index block. Six lines above, "stopped at" takes a level: "a program stopped at Observed". Here the same verb takes a proposition and a model, so a reader meeting three phrasings cannot tell whether the level is the thing being named. | `(*   publish_observed       == the terminal of a program stopped at Observed  *)`<br>`(*   publish_sampled        == the terminal of a program stopped at Sampled   *)`<br>Both exactly 80 bytes; each drops its continuation line, so the block loses two lines. |
| B14 | SHOULD | `manifest/pgg_tableau.v:1107` | "The manifest's own status such a payload stands for." | The fact alone, and the fact is the statement restated; the comment carries no position (Z25). Its Observed and Sampled siblings all carry one. | "The manifest transfer status a restricted payload stands for. It is the coordinate a reader of such a path finds, so the two statuses naming a transfer theorem never appear on a path the Sampled terminal built." |
| B15 | SHOULD | `manifest/pgg_tableau.v:1204-1205` on `run_correct_of_sampled` at 1206 | "Run correctness of a program published at Sampled, the first of the two conjuncts that level carries." | Fact without position, where the Observed sibling has one. A reader cannot tell from this what a value of `PublishedSampled` does not give. | Add one sentence: "A reader of such a value learns that the run finished and that its endpoints decode, and nothing about a coalition." |
| B16 | SHOULD | `manifest/pgg_tableau.v:1213-1214` on `view_identification_of_sampled` at 1215 | "the fact a security statement about this model would be made along were one proved." | Not readable as English, and the file already has the phrasing for exactly this relation at 478: a hypothesis "along which exact_tail transports a witness's independence". One word per concept. | "It is the second and last conjunct of that level, and the hypothesis along which a security statement about this model would be transported, were one proved." |
| B17 | SHOULD | `manifest/pgg_tableau.v:1147-1149` on `publish_observed_completionE` at 1150 | "so the manifest's sentence about how far a path's theorems reach is a term at this level and not prose." | Type-honest phrasing: a sentence of the manifest is not a term, and an equality between a completion level and `Observed` is not a sentence turning into a term. Z5 gave the wording for this statement. | "Conversion decides it, so a reader of the value learns the level its program stopped at without consulting the manifest." |
| B18 | SHOULD | `manifest/pgg_tableau_syntax.v:437-438` | "the order the existing publish rule writes them" | "existing" dates the rule against this edit, and the file now holds three publish rules, so the phrase no longer picks one out. | "the order the three-payload publish rule writes them" |
| B19 | NOTE | `manifest/pgg_tableau.v:1144` | "Explicit for the reason publish_observed's directive gives." | A pointer to another declaration's comment in place of the fact; the file's precedent at 379-388 writes one comment over a block of directives instead. | "The data occurs in the type of the proof here too." |
| B20 | NOTE | `instances/s5/tableau/s5_tableau_observed.v:149-150` | "the two other conjuncts of the same And3 come off the same reader" | `And3` is the shape of the type where the sentence already has the word for the content, "conjunct". | "the two other conjuncts come off the same reader." |
| B21 | NOTE | `manifest/pgg_tableau.v:84-86` | "so a later reading of PublishedAt as one of them would turn each recorded rejection into an acceptance" | The fact is right and worth keeping, but "a later reading of PublishedAt as one of them" does not name what would have to change. | "so a coercion added later between PublishedAt and either record would turn each recorded rejection into an acceptance." |
| B22 | NOTE | `instances/s5/tableau/s5_tableau_checks.v:22-23` | "the path that value builds records the assumption status it was published under" | The manifest's new header says the terminal builds the path from the program's own data; here the value builds it. One word per concept across the two homes. | "the path built for that value records the assumption status it was published under" |
| B23 | NOTE | `instances/s5/tableau/s5_tableau_observed.v:24-26` | "the assumption status written into its path is a statement of the author" | `manifest/pgg_tableau.v:92` writes the same fact as "it is the author's statement". Two spellings of one concept across the two homes. | "the assumption status written into its path is the author's statement" |
| B24 | NOTE | `manifest/pgg_tableau_syntax.v:80-84` against `t_keyword_check_two_records.v` | "each stays ... the CompletionLevel constructor it names, in a file whose Require lines are ssreflect and this one" | The cited measurement file binds both tokens as binders and then shadows both constructors with `Definition Observed : nat := 0.`, so it measures the binder half only. The constructor half is evidenced in production instead, by `Tableau Observed` at `instances/s5/tableau/s5_tableau_observed.v:100` and `Tableau Sampled` at `s5_tableau_sampled.v:71`, both in files that require this one. | Either cite the production use in the sentence, or record a second probe line that checks the constructor before shadowing it. No wording change is owed if the probe is extended. |

## The four checks that pass

**Names.** Every identifier the landing introduces is free and reads as what it
is: `PublishedObserved` and `PublishedSampled` sit beside `PublishedAt` without
claiming to generalise it, the constructors follow the tree's `Mk` prefix, the
six fields copy `published_at`, `published_path`, `published_thm`,
`TransferStatusWithoutTheorem` and its two constructors are the split the
pinned `TransferStatus` docstring at `manifest/pgg_analysis_status.v:63-71`
makes, `publish_observed` and `publish_sampled` are the literal verb of the
surface, the six path equations carry `E` on an equation that holds,
`run_correct_of_observed`, `run_correct_of_sampled` and
`view_identification_of_sampled` put `_of` and the carrier last and spelled
out, and the three S_5 names follow `<inst>_<discriminator>_<phase>_published`
with `_pathE` and `_recovers` unchanged. `transfer_of_sampled` (B7) and
`s5_dealt_baseline_pathE` (B8) are the two exceptions.

**Index completeness.** `manifest/pgg_tableau.v` indexes all nine new
non-`Fail` definitions and all six new lemmas, in declaration order, appended
after `security_property_of`, which is where the new section sits; fields and
constructors are not indexed, as `MkPublished` and `published_at` are not.
`instances/s5/tableau/s5_tableau_observed.v` indexes all three, two under
`Definitions:` and the equation under `Key results:`, in file order.
`s5_tableau_checks.v` has no index block and owes none;
`manifest/pgg_tableau_syntax.v` indexes builders and not notations, so nothing
is owed there either.

**Columns and widths.** Every added line is at most 80 bytes; the widest are
exactly 80. `manifest/pgg_tableau.v` index entries: name at 5, `==` at 28,
description and continuation at 31, and every name wider than 22 bytes
(`TransferStatusWithoutTheorem`, `run_correct_of_observed`,
`view_identification_of_sampled`, and four of the six equation names) takes a
line of its own with `==` beneath it at 28.
`instances/s5/tableau/s5_tableau_observed.v`: name at 5, `==` at 26,
description and continuation at 29, all three names in the two-line form. Both
new banners are three lines with one content line, exactly 80 bytes, with a
space before the closing delimiter. Continuation is 3 spaces in the two
`manifest/` files and 4 in the S_5 file, as Z11 requires.

**The terminal-rules sentence.** `manifest/pgg_tableau_syntax.v:40` now reads
"The separator of the terminal rules is `|>`", and it is right: the file
declares four rules with `|>` (`conclude`, the three-payload `publish`, and the
two new ones) and no terminal rule without it, since `restate` has no notation.
The 2026-09-14 measurement sentence that follows is about the token and is
untouched, which is what Z12 asked for. The new measurement carries its date in
the file's own form, "measured on 2026-09-21", matching "Measured on
2026-09-14" and "measured on 2026-09-19" in the same paragraph. B1, B2 and B24
are about what that sentence claims, not about the date.

## Applying this

Eleven MUST rows. Nine are comment or banner text and touch no identifier. Two
are renames: B7 rewrites four sites in `manifest/pgg_tableau.v` and its index
entry, B8 rewrites one name inside a `Fail Definition` in
`instances/s5/tableau/s5_tableau_checks.v`. Both new spellings were searched
and are free, so the only files that need recompiling are the two edited ones
and, for B7, the importers of `manifest/pgg_tableau.v` that name the map, of
which there are none outside that file.
