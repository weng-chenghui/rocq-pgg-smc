# Naming and style audit of landing 1, adversarial

Audited: the frozen export of
`notes/probes/2026-09-20-tableau-extensions-landing1/` at commit `16066cd` —
the seven files under `staged/`, read as PERMANENT TEXT, against production at
the same commit. No file of the repository was read for writing and nothing was
compiled; findings that would need a compile say so.

## Verdict

**NO-GO as staged. GO once the seven MUST items are applied.**

Every MUST item is a comment-only edit: no code token moves, so the cost is one
recompile of each of the four files touched, `manifest/pgg_tableau.v`,
`instances/kim2025/five_card_rows.v`, `instances/pgl27/pgl27_rows.v` and
`instances/psl211/psl211_reading_constancy.v`. The reason for a NO-GO rather
than a conditional GO is that three of the seven are statements that are
**false about the file that ships them**:

* M1 — a docstring in `five_card_rows.v` describes a certificate the landing
  itself withdrew.
* M3 — `publish_armE` enumerates two of the three `certify_*_armE` lemmas in a
  file that now declares three.
* M4 — `psl211_reading_constancy.v` calls a premise the premise of "both"
  security arms in a framework that now has three.

STATUS.md section 3 reports that its scan of `staged/` found nothing to remove
and that no count is stale. The first claim survives my reading (see coverage,
item 1). The second does not: M3 and M4 are stale counts that a search for the
word "two" cannot see, because one is an enumeration of two names and the other
is the word "both".

## Findings

MUST = the text is false, or names a concept by a word that already names a
different declaration in the same file. SHOULD = true but drifting, duplicated
or narrating. NOTE = recorded, no action asked.

Line numbers are the staged file's. Replacements longer than a table cell are
in the **Replacements** section, keyed by id.

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| M1 | MUST | `staged/instances/kim2025/five_card_rows.v:679-683` | "An input-indistinguishability certificate publishes its marginal bound twice, once for each of the two committed pairs, so a row at the constant bound publishes a sum of two equal terms, and this identity is what bounds that sum by a single constant." | "a row at the constant bound" is `kim_centi_cert40`'s row, which E2 withdrew. After the withdrawal no certificate in this file carries `2^-40` in its marginal-bound field: `kim_centi_cert`'s number is `Num.sqrt 5%:R * (1/80)^+7` twice (`:697-699`) and `kim_biased_cert_exact`'s is `1/50` twice (`:788-796`). The only use left of `five_card_pow2_39_split` in the staged file is inside the proof of `kim_centi_cert_eps_lt` (`:709`), where it rewrites `2^-39` as `2^-40 + 2^-40` so that `ltrD` can bound each summand by `kim_bound_centi` (`:707-710`). The second clause also calls an equality a bound. | R-M1 |
| M2 | MUST | `staged/instances/kim2025/five_card_rows.v:157-158` | "five_card_pow2_39_split, five_card_inv50_split == the identity behind each concluded number" | True of `five_card_inv50_split`, which is the payload of `five_card_row_biased_inv25` under `ssr_ext.eqW` (`:822`). False of `five_card_pow2_39_split`: the repeated row is concluded by `Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx)` (`:757-758`), and the identity never reaches a terminal. One entry describing two declarations of which one changed role is the same fault E2 corrected at `:98`. | R-M2 |
| M3 | MUST | `staged/manifest/pgg_tableau.v:1031-1035` | "This is the step that carries certify_exact_armE and certify_indistinguishability_armE out to a published row, where a paper's table reads them." | The file declares three certify arm equations: `certify_exact_armE` (`:990`), `certify_indistinguishability_armE` (`:1000`) and `certify_idealproximity_armE` (`:1013`). The sentence enumerates two, so a reader of the proximity arm is told the publish step does not carry his. `publish_armE`'s statement (`:1040`) is generic in the port and carries all three. | R-M3 |
| M4 | MUST | `staged/instances/psl211/psl211_reading_constancy.v:235-236` | "those three seats meet the threshold premise of both security arms, the derived profile declaring six" | Two-arm count in a three-arm framework. All three propositions of the staged `pgg_tableau.v` state the premise `(#\|C\| < profile_k (instance_profile A))%N`: `ExactProp` (`:425`), `IndistinguishabilityPropAt` (`:454`), `IdealProximityPropAt` (`:487`). This file's code is unchanged and its comments were re-read for landing 1 (STATUS.md E5 lists `:31-38`, `:14-15`, `:202`, `:208`, `:560`, `:674`, `:706`, `:725`); `:236` is not on that list. | R-M4 |
| M5 | MUST | `staged/manifest/pgg_tableau.v:447`, `:462`, `:481`, `:922` | ":447 so a terminal can restate a finished row at the number a paper cites"; ":462 the number a row carries when nothing restates it"; ":481 so a terminal can restate a finished row at the number a paper cites"; ":922 what a row that never restates its number publishes" | The terminal meant is `conclude`. `restate` is a different terminal declared in the same file at `:906`, whose own comment at `:903-905` says "conclude is not an instance of it". One word naming two terminals is the drift the file's own text warns against. Under the `<=` obligation the phrase is also not type-honest: `ConcludePayload` (`:834-841`) asks for `cert_eps cert <= odflt (cert_eps cert) (c R)`, so the published number may be strictly above the one a row proved and nothing is restated. | R-M5 |
| M6 | MUST | `staged/instances/kim2025/five_card_rows.v:747-752`, the clause at `:748-749` | "The terminal is supplied kim_centi_cert_eps_lt weakened to a non-strict inequality, and it changes nothing else" | How the payload is built, in a `(**  *)` statement comment. True — the payload is `Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx)` (`:758`) — and it belongs in a plain `(*  *)` source comment beside the definition, which is where this same file already puts its proof notes (`:684-686`, `:777-782`). | R-M6 |
| M7 | MUST | `staged/instances/pgl27/pgl27_rows.v:485-493` and `:417-422` | ":487 The accumulated bound is 2^-40 twice, pow2_split adds the two copies, and eqW reads that identity as the inequality the terminal's obligation asks for" (and the same sentence at `:417-419`) | Proof strategy in a statement comment, and stated twice in one file for two definitions whose payload is the same term `(fun R _ => ssr_ext.eqW (pow2_split R))` (`:427`, `:497`). The novelty of `pgl27_row_word_branch39` is the branch point, not the arithmetic: it is `pgl27_row_word39` (`:423-428`) with the prefix replaced by the name `pgl27_word_sampled` (`:482-483`, used at `:495`), the same certificate, the same coordinate and the same two statuses. The comment spends five of its nine lines on the payload and two on the branch. | R-M7 |
| S1 | SHOULD | `staged/manifest/pgg_tableau.v:35-36`, `:47-48` | two empty comment lines before the new paragraph, none after it | The E4 paragraph is inserted with a double separator above and no separator below, so it runs into "Each arm has one composition law" as one block. Every other paragraph of this header is separated by exactly one empty comment line. | delete line 36; insert one empty comment line between `:47` and `:48` |
| S2 | SHOULD | `staged/manifest/pgg_tableau.v:44-46` | "The other two arms are chosen with the same freedom: ic_ideal is any law on the group, and a constant ew_secret satisfies ew_indep at every coalition." | `ic_ideal`'s **type** is any law (`:187`), but the record constrains which laws can be fielded: `ic_close` (`:188`) asks the ideal to be within `sw_bound_eps (ic_b cert)` of the shuffle law and `ic_const` (`:189-193`) asks a coalition's reading of it to be constant in the run argument. Stated flat, the clause says the arm's ideal is unconstrained, which is the opposite of what `psl211_alldecks_no_small_eps_cert` in this tree lives on. The parallel the paragraph draws survives if the clause says the instance names the law. | R-S2 |
| S3 | SHOULD | `staged/manifest/pgg_tableau.v:46-47` | "So the proximity arm adds no freedom the tree did not already carry." | "the tree" is the repository, not the mathematics; the sentence also repeats the preceding clause. | "So the proximity arm's latitude is the latitude the other two arms already have." |
| S4 | SHOULD | `staged/instances/pgl27/pgl27_rows.v:39-40` | "Two further things stay outside the programs: the reprice of the word row's bound from 2^-40 + 2^-40 to 2^-39, which moves a number and proves nothing new about a coalition" | The file's index entry for the same object was rewritten to "the word row concluded at that number" (`:55`) and its section banner to "The word row concluded at 2^-39" (`:410`), so the header prose is now the only place in the file naming the operation by the older word. Still true as a fact. | "the word row's conclusion at 2^-39, which moves a number and proves nothing new about a coalition" |
| S5 | SHOULD | `staged/manifest/pgg_tableau.v:504`, `:508`, `:905` | ":504 The reprice that names nothing. It is the coordinate of every row that publishes the bound it accumulated."; ":508 The proposition a port carries at a given reprice"; ":905 conclude's target is computed by the framework from the reprice, this one's is supplied" | The three comment sentences that use the older word as a noun for the coordinate. All three are **still true** under the `<=` obligation: `no_reprice = fun _ => None` (`:506`) and `PortProp` reads `odflt (cert_eps cert) (c R)` (`:520`), so a row at `None` does carry its accumulated bound, and `conclude`'s target is computed from `c` (`:876-882`). They are the sentences that must move if the owner renames the type (see N2). | ":504 The coordinate that names nothing."; ":508 The proposition a port carries at a given coordinate"; ":905 conclude's target is computed by the framework from that coordinate, this one's is supplied" |
| S6 | SHOULD | `staged/instances/kim2025/five_card_rows.v:59-61` | "instances/s5/s5_rows.v records for s5_row_word the gap this file no longer has: there the constancy an input-indistinguishability certificate asks for is false." | Narrates this file's history instead of stating what holds. Pre-existing: byte-identical in production `16066cd` at `:61-63`. The landing re-lands the whole file, so this is the moment it can be stated declaratively. | "instances/s5/s5_rows.v records the same question answered the other way for s5_row_word: there the constancy an input-indistinguishability certificate asks for is false." |
| S7 | SHOULD | `staged/instances/psl211/psl211_reading_constancy.v:689` | "A row publishes odflt (cert_eps cert) (c R) at its own conclude coordinate c" | E5's rename of the word introduces a third name for the coordinate, and this one is wrong for a row that never concludes: such a row's coordinate is `no_reprice` (`pgg_tableau.v:924`). The coordinate belongs to `PublishedRowAt`, not to the terminal. | "A row publishes odflt (cert_eps cert) (c R) at its own coordinate c" |
| S8 | SHOULD | `staged/instances/psl211/psl211_reading_constancy.v:697-701` | "The obligation of conclude at an input-indistinguishability port is cert_eps cert <= odflt (cert_eps cert) (c R) … not a further argument." | After E5's edit this plain comment restates the docstring three lines above it (`:692-694`, "The obligation of conclude bounds the published number below by cert_eps cert, so no row over this model publishes less"). Before the edit the two differed, because the plain one carried the epistemic marker the edit removed. | R-S8 |
| S9 | SHOULD | `staged/instances/kim2025/five_card_rows.v` (whole file) | one `_armE` lemma, `five_card_row_uniform_armE` (`:411`) | STATUS.md Q6. Judged as coverage, not naming: the name follows the tree's convention exactly. The defect is that the file's four input-indistinguishability programs (`:611`, `:621`, `:753`, `:816`) carry no arm equation, so the file that is *about* that arm states nothing about it, while `pgl27_rows.v` pins both arms it carries and the concluded row besides (`:352`, `:361`, `:448`). Adding `five_card_row_repeated_indistinguishability_armE` and `five_card_row_biased_indistinguishability_armE` is a code change: needs a compile, and it is landing-2 work, not a landing-1 blocker. | none in landing 1; record the two names for landing 2 |
| S10 | SHOULD | `staged/manifest/pgg_tableau_syntax.v:30-33` and `:391-394` | "four of that record's five fields are terms of the instance and the fifth is the number, so a builder would display the plumbing and not the mathematics" | The same sentence, nearly verbatim, in the file header and on the notation. Long exposition belongs at the header; the notation's comment should say what the rule takes. | R-S10 |
| S11 | SHOULD | `staged/manifest/pgg_tableau_syntax.v:262` | "…claims about one object rather than two.  A scheme guarantees nothing at or above its threshold…" | Production `:252-254` has a paragraph break here; the staged reflow replaced it with two spaces inside a line, joining an object statement to an unrelated statement about thresholds in one block. | restore the empty line inside the comment |
| S12 | SHOULD | `staged/instances/kim2025/five_card_rows.v:52` | "the exact arm asks for independence of the static coalition observation from a secret" | Third name in one file for `static_coalition_obs`, beside "the framework's direct computation of a coalition's view" (`:117-119`) and "a coalition's static endpoint reading" (`:34`). `pgg_tableau.v` settles on "the direct computation" (`:693`, `:739`). Pre-existing. | "independence of the direct computation of a coalition's view from a secret" |
| S13 | SHOULD | `staged/instances/kim2025/five_card_rows.v:798-801` | "It is the identity that bounds the sum of the one-cut row's two exact per-card-position numbers by the single constant that row publishes." | `five_card_inv50_split` is `(1/50 : R) + 1/50 = 1/25` (`:802`), an equality; `ssr_ext.eqW` is what turns it into the terminal's inequality (`:822`). An equality is not a bound. Production said "names … by the single constant", which was type-honest. | "It is the identity that equates the sum of the one-cut row's two exact per-card-position numbers with the single constant that row publishes." |
| N1 | NOTE | `five_card_rows.v:780-782`, `psl211_rows.v:74`, `psl211_reading_constancy.v:71` | three citations of a probe directory | Recorded, not findings, per the brief. The first is the 147 s against 0.07 s measurement behind `reflexivity`; the other two are byte-identical to production. They stand or fall together, as STATUS.md Q3 says. |  |
| N2 | NOTE | `pgg_tableau.v:502`; `pgl27_rows.v:415`, `:505`, `:512`; `five_card_rows.v:745`, `:806`, `:837` | the type name and the constants built on it | The owner's pending decision (design R13, STATUS.md Q4). Two further carriers the design's R13 text does not list: the lemma names `pgl27_word_reprice41_false` (`pgl27_rows.v:512`) and `five_card_reprice_inv25_lt2` (`five_card_rows.v:837`), whose own index entries now describe them in the new vocabulary ("the terminal's obligation at 2^-41 is false", "the concluded one-cut number under the ceiling"). If the type is renamed, S5's three sentences and these two lemma names go with it. |  |
| N3 | NOTE | tree-wide | collision scan | The 40 names landing 1 adds or moves were checked against every `.v` file under the `pgg_smc` logical path outside `notes/`, `docs/` and `.claude/` (203 files). No identifier the landing adds is declared anywhere else. |  |
| N4 | NOTE | `pgg_tableau_syntax.v:333`, `:371`, `:403` | three lines over 80 bytes | The three notation string literals the brief exempts (101, 90 and 128 bytes). No other line in the seven files exceeds 80 bytes, and no padded box-comment line closes off column 80. |  |
| N5 | NOTE | seven files | the project's banned vocabulary list, and abbreviation | No hit for any word on the project's banned vocabulary list, and no abbreviation of "indistinguishability": the word is spelled out at every site. Confirmed by my own scan, not by STATUS.md's. |  |
| N6 | NOTE | STATUS.md section E4 | the clause-by-clause table's line citations | The clauses check out against the records, but the line numbers in the table are not the staged file's: `ipc_ideal` is at `:211` not `:213`, `ipc_witness` at `:212` not `:214`, `ipc_secret` at `:213` not `:215`, `ipc_close` at `:215-225` not `:217-227`, `ic_ideal` at `:187` not `:175`, `ew_secret`/`ew_indep` at `:168-172` not `:156-160`, and the `InputIndistinguishability` branch of `ConcludePayload` at `:838-839` not `:826-827`. A later reader following those citations lands in the wrong declaration. |  |
| N7 | NOTE | `pgg_tableau.v:359` | `ab_arm` has no index entry | Consistent with the file's convention: no `ab_*` projection is indexed (`ab_Ht`, `ab_He`, `ab_Hr`, `ab_obs`, `ab_f`, `ab_port` are all absent too). Not a defect. |  |
| N9 | NOTE | `staged/manifest/pgg_tableau_syntax.v:40`, `:68`, `:79` | "Measured on 2026-09-14, \|> occurs as a standalone notation token nowhere in the kept tree"; "Measured on 2026-09-14, fuel is among them"; "measured on 2026-09-19 by binding it in a file that requires nothing but ssreflect" | The three dates in the seven files that are not a probe-path citation. Each dates a measurement of the notation namespace, which is a fact about a checked environment and goes stale in a way a reader must be able to see; production already carries the first two at `:36` and `:64`, and the design's section 5 says the third lands with the file. Recorded, not a finding. |  |
| N10 | NOTE | `landing_fidelity.v` | the fidelity instrument | Read for the same categories. It is a probe instrument and not permanent text, so its narration is in place. All 31 of its declarations carry the `landing_` prefix, and its four `Fail Check`s name exactly the four withdrawn identifiers. Nothing on the project's banned vocabulary list, and no abbreviation. |  |
| N8 | NOTE | all seven headers | index tables | Every name in a `Definitions:` or `Key results:` block is declared in that same file with that exact spelling (checked mechanically, 172 entry lines across the seven headers). No entry survives for `kim_centi_cert40`, `kim_centi_cert40_epsE`, `RepricePayload` or `port_reprice`, and those four names occur nowhere in `staged/`. Every declaration the landing adds or moves has an entry except the payload types, which the file has never indexed. |  |

## Replacements

**R-M1** — `five_card_rows.v:679-683`, the docstring of `five_card_pow2_39_split`:

```
(** Two copies of two to the minus fortieth make two to the minus
    thirty-ninth. It puts the constant PGL(2,7)'s word row publishes into the
    shape an input-indistinguishability certificate's own number has, a sum of
    two per-pair bounds, which is what lets the repeated row's number be
    compared with that constant one pair at a time. *)
```

Read off `kim_centi_cert_eps_lt` (`:704-711`): the proof rewrites `2^-39` into
`2^-40 + 2^-40` and then bounds each summand by `kim_bound_centi` under
`ltrD`. The plain comment at `:684-686` about `mulr_natl` and `mulr_natr`
stays where it is.

**R-M2** — `five_card_rows.v:157-158`, two entries in place of one (pad to
column 80 as the block does):

```
(*   five_card_inv50_split   == the identity the one-cut row's terminal       *)
(*                              discharges                                    *)
(*   five_card_pow2_39_split == 2^-39 as a sum of two per-pair bounds         *)
```

**R-M3** — `pgg_tableau.v:1031-1035`:

```
(* Publishing attaches the manifest row and leaves the arm alone, so the arm
   a finished row reports is the arm its data carried before the last line.
   This is the step that carries the three certify statements' arm equations
   out to a published row, where a paper's table reads them. *)
```

**R-M4** — `psl211_reading_constancy.v:235-239`:

```
(** psl211_perdeck_coalition_below_k — those three seats meet the threshold
    premise every security arm states, the derived profile declaring six. A
    refutation of a field quantified over coalitions below the threshold has
    to discharge this premise, and it is the only nontrivial premise the
    counterexample owes. *)
```

**R-M5** — four sites in `pgg_tableau.v`.

`:444-448`:

```
(* The input-indistinguishability arm's proposition: below the threshold, two
   run arguments give coalition readings of the cut within variation distance
   c. The bound is a parameter rather than the certificate's own sum, so the
   conclude terminal can publish a finished row at any upper bound of that
   sum, the constant a paper cites among them, without reproving the arm. *)
```

`:460-462`:

```
(* A certificate's own bound: the marginal bound's epsilon twice, one for each
   of the two run arguments the arm compares. It is the number a row carries
   when its coordinate names none. *)
```

`:480-482`, the last sentence of the `IdealProximityPropAt` comment:

```
   The bound is a parameter, as it is for the input-indistinguishability arm,
   so the conclude terminal can publish a finished row at an upper bound of
   it, the number a paper cites. *)
```

`:922-923`:

```
(* A published row at the program's own bound: what a row whose terminal names
   no number publishes. *)
```

**R-M6** — `five_card_rows.v:750-758`, docstring and a plain comment:

```
(** The repeated row concluded at that constant, continuing from the
    certificate at the bundle's own spectral number. The data, the model and
    the certificate are the same terms, so what a coalition of at most one
    seat is shown is what that certificate proved, stated at the number a
    reader cites. *)
(* The terminal's payload is kim_centi_cert_eps_lt weakened by ltW. *)
```

**R-M7** — `pgl27_rows.v`, two sites.

`:486-493`, the docstring of `pgl27_row_word_branch39`:

```
(** The word row built from the named value pgl27_word_sampled rather than
    from the dealt prefix: the same certificate, the same terminal at 2^-39
    and the same two statuses as pgl27_row_word39. Naming the Sampled value
    is what lets a second row over this model be written without repeating
    the prefix. *)
```

Each clause read off the two definitions: `pgl27_word_sampled :=
pgl27_dealt sample pgl27_word_family` (`:482-483`); `pgl27_row_word39`
(`:423-428`) and `pgl27_row_word_branch39` (`:494-498`) differ only in that
prefix, and both carry `pgl27_word_cert`, `conclude pgl27_reprice39 by (fun R
_ => ssr_ext.eqW (pow2_split R))` and `publish IdealFinite
BaselineClassicalOnly`. The equality of the two published rows is not claimed
here, because no lemma of this file states it; `landing_fidelity.v` owns it.

`:417-422`, the docstring of `pgl27_row_word39`, with the arithmetic moved out
of it:

```
(** The word row concluded at the single constant 2^-39. The data, the model
    and the certificate are untouched, so the published row asserts about a
    coalition no more than pgl27_row_word_tableau, at the number a reader
    expects to cite. *)
(* The accumulated bound is 2^-40 twice; pow2_split adds the two copies and
   eqW reads that identity as the terminal's inequality. *)
```

**R-S2** — `pgg_tableau.v:44-46`:

```
   freedom: ic_ideal is a law on the group the instance names, held only by
   ic_close and ic_const, and a constant ew_secret satisfies ew_indep at
   every coalition.
```

**R-S8** — `psl211_reading_constancy.v:697-701`, cut to the part the docstring
does not already say:

```
(* The obligation of conclude at an input-indistinguishability port is
   cert_eps cert <= odflt (cert_eps cert) (c R), and the proposition the row
   carries is IndistinguishabilityPropAt cert c. *)
```

**R-S10** — `pgg_tableau_syntax.v:391-394`, with the reason left at the header
(`:30-33`) where it already stands:

```
(* The proximity rule takes one certificate whole, as the
   input-indistinguishability rule does, and has no builder. *)
```

## Coverage

1. **Permanent-text read of all seven staged files, comments included.**
   Method, stated so the claim can be checked: every header block was read in
   full; every comment inside a region the landing changed was read against
   production `16066cd` by diff; the remaining comments were read in bulk as
   extracted comment text and passed through a keyword scan for the remit-1
   categories and for status, effort, progress and roadmap vocabulary (35
   patterns, including "key", "important", "deferred", "machine-checked",
   "still", "so far", "previously", "pending", "task", "risk", "hours"). The
   scan returned 31 lines, every one of them a false positive: the licence
   line's "or-later", the `Key results:` block markers, and "still", "so far",
   "earlier", "left to" used mathematically. No sentence anywhere in `staged/`
   speaks of a probe, a stage, an audit, a fix pass, a ledger row, "this batch"
   or the landing, and no date occurs except N1's citations and N9's three
   measurements. STATUS.md's claim that its scan found nothing to remove
   therefore holds for those categories. One sentence outside them narrates a
   history rather than stating what holds: `five_card_rows.v:59-61` on what
   this file "no longer has" (S6).
2. **Statement-comment discipline.** The five passages the brief names were
   audited individually: the new `pgl27_row_word_branch39` comment (M7), the
   `pgl27_word_sampled` comment (clean as text — every clause is about the
   declaration or about any continuation of it — though see the note below),
   the new header paragraph of `pgg_tableau.v` (S1, S2, S3; the mathematical
   clauses check out against the three records, see item 5), the reworded index
   entry of `kim_biased_cert_exact` (clean: the certificate's marginal-bound
   field is `kim_biased_marginal_bound_exact`, the exact constant one
   fiftieth, `:789-797`, so "with a constant in the
   marginal-bound field" is right and the entry no longer promises two
   certificates), and the two changed passages of
   `psl211_reading_constancy.v` (S7, S8; the new text at `:697-701` is a
   correct copy of the `InputIndistinguishability` branch of `ConcludePayload`,
   `pgg_tableau.v:838-839`). Beyond those five, the pass found M1, M3, M4, M5,
   M6, S12 and S13. Note on `pgl27_word_sampled`: its comment carries the
   object but not its position, while the branch-point reason sits in
   `pgl27_row_word_branch39`'s comment instead; R-M7 moves that reason to the
   row and leaves `pgl27_word_sampled` as it is, which is the smaller edit.
   Moving it the other way would also be defensible and is the owner's call.
3. **One word per concept.** "conclude"/"concluded at" is now uniform in the
   index entries, the section banners and the new comments; the three surviving
   uses of the older word as a noun are S5, and the one surviving use in file
   prose is S4. "restate" is used for `conclude`'s operation at four sites while
   naming a different terminal in the same file: M5. "input-indistinguishability
   arm" is the only phrase for that arm in all seven files — no hit for any
   other spelling, and no abbreviation. Reading vocabulary: `sa_coalition_view`
   is "the view" or "the executed reading" and `static_coalition_obs` is "the
   direct computation" throughout the framework; one site in
   `five_card_rows.v` calls it a third thing (S12). Number vocabulary:
   "marginal-bound epsilon", "the bundle's spectral number" and "the
   certificate's own number" all occur, and they name three different things
   (the `sw_bound_eps` field, the spectral expression that field holds at Kim,
   and `cert_eps`, which is the field twice); no drift that could be read as two
   things being one.
4. **Header tables.** N8. Counts in prose were checked against the files:
   "There are six statements" (`pgg_tableau.v:17`) matches the six statement
   definitions; "three arms" and "the three terminals" match; "Five fields"
   for `IndistinguishabilityCert` (`:178`) and "five fields" for
   `IdealProximityCert` (`pgg_tableau_syntax.v:31`) match the records at `:182`
   and `:208`; "nineteen identifiers" and "the other eighteen"
   (`pgg_tableau_syntax.v:65-86`) match the list given; "three rows, as seven
   programs" (`five_card_rows.v:4`) matches the seven programs left after the
   withdrawal, which removed a certificate and not a program. The two counts
   that do not match are M3 and M4.
5. **Name collisions and conventions.** N3. The new lemma names follow the
   tree's suffixes without exception: `_armE` for an arm equation, `_rowE` for a
   published-row equation, `_atE` for an equality of accumulated stacks,
   `_bindE` for the surface-against-bind equation, `_epsE` for a number in
   closed form, `_lt`/`_lt2` for a strict bound. `pgl27_row_word39_unindexed`
   and `five_card_row_repeated39_unindexed` rename the older `_bare` guards and
   describe what is rejected, which is an improvement. Q6 is S9: acceptable as
   naming, a coverage gap as text, and not a landing-1 blocker.
6. **Mechanical.** N4 for long lines and box comments; N5 for the project's
   banned vocabulary list and for abbreviation. Two formatting regressions
   against production: S1 and S11.

## What I could not settle without a compile

* That a constant `ew_secret` satisfies `ew_indep` at every coalition
  (`pgg_tableau.v:45-46`) is true as mathematics — a constant random variable
  is independent of anything — but it is not proved anywhere in the staged
  tree, so the header asserts it on the reader's credit. I did not raise it as
  a finding; a one-line lemma would settle it, and that needs a compile.
* That `var_dist d d = 0`, which the header's "ipc_close holds at zero" clause
  (`:43-44`) rests on, is likewise standard and not stated in the staged tree.
* S9's two proposed lemmas are code and need a compile.
