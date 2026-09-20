# Combined audit of the landing: comments, names, layout, placement (2026-09-21)

Working tree on top of `b953b82`: `git diff HEAD` plus the three staged new
files. Nothing in the repository was written by this audit but this file. No
Rocq process was started and nothing was compiled; every claim below is read
off the sources, off the definitions it cites by file and line, and off the
compiled evidence the two earlier audits recorded.

Vocabulary of this report: a Tableau value is a PROGRAM, the manifest's record
is a PATH, a program certifies a SECURITY PROPERTY with SECURITY EVIDENCE, the
evidence proves a PROPOSITION, and `static_coalition_obs` is a coalition's
static reading.

## Verdict

**NO-GO as it stands, GO after the six MUST rows.** Nothing landed is
mathematically wrong, no name is wrong, no line is over eighty bytes, no boxed
header is off, the two new manifest leaves are correctly separated, nothing
went under `instances/psl211/tableau/`, the new psl211 file is required by
nothing, and the addition is pure: no existing statement, proof or name
changed. What blocks the commit is four statement comments that claim more than
the tree proves and two word-discipline defects, all of them local edits to
comment text:

- **E1** and **E2** in `manifest/pgg_tableau_reading.v` and **E3** in
  `instances/psl211/psl211_colour_reading.v` say that the framework's
  propositions are stated at a coalition's static reading, and that exact
  independence at a reading is the conjunct the framework's entropy forms are
  derived from. Two of the three propositions are stated at the executed
  coalition view, and the reading form reaches that view only along the link
  lemma. This is the very distinction findings P6 and P7 were written to
  protect, and the file's own header states it correctly.
- **E4** in `instances/psl211/psl211_reading_constancy.v`: one of the two
  rewritten sentences says the adapter pins an ideal and, four words later,
  that no certificate is built over it. The other says "now exists".
- **E5**: `manifest/pgg_tableau_marginal_bounds.v` names the run index zero
  something the tree does not call it and the code does not support.
- **E6**: the same file calls the cut map "a reading" four times while
  asserting that a marginal bound is not a statement at a reading.

Twelve SHOULD rows and eight NOTE rows follow. The SHOULD rows are worth the
same fix pass; none of them blocks a commit on its own.

## Answers to the seven questions

**1. Pure addition.** Yes. Every removed line is comment text or an import
line; no `Definition`, `Lemma`, `Record`, statement, proof script or name was
removed or changed anywhere in the diff. The removals, classified:

| file | removed | class |
|---|---|---|
| `_CoqProject` | none | — |
| `instances/pgl27/pgl27_proximity.v:41` | one header prose line, extended to three | allowed (header prose of a file that receives a declaration) |
| `instances/pgl27/pgl27_proximity.v:83` | `From pgg_smc Require Import pgl27_exec pgl27_models.` | import line, one module added (departure 2) |
| `instances/psl211/psl211_reading_constancy.v:56-58` | three header lines | allowed (decision 4) |
| `instances/psl211/psl211_reading_constancy.v:967-968` | two docstring lines | allowed (decision 4) |
| `instances/kim2025/tableau/five_card_tableau_sampled.v:29-33` | five header lines | allowed (the count sentence and its enumeration) |
| `instances/s5/tableau/s5_tableau_sampled.v:36` | one header prose line, extended to four | allowed |
| `instances/s5/tableau/s5_tableau_sampled.v:47` | `From pgg_smc Require Import s5_exec s5_models.` | import line, one module added (departure 3) |

The two import departures are inert. `instances/pgl27/pgl27_trace.v` and
`instances/s5/s5_mixing.v` declare no `Notation`, `Canonical`, `HB.instance`,
`Hint` or `Coercion` at top level, and the only names either contributes to its
receiving file are the ones the new lemma needs: `pgl27_coalition_trace` and
`pgl27_coalition_trace_E` in `pgl27_proximity.v`, `s5_alpha_R` in
`s5_tableau_sampled.v`. No identifier already occurring in either file resolves
to a declaration of the newly imported module, so no existing statement changed
meaning. `pgg_interface`, `pgg_session_types` and `pgg_monodromy_profile`
declare no notation or coercion at all.

**The scope question.** `Local Open Scope fdist_scope` cannot change how
`s5_rand_sampled` parses. Its body is `s5_supplied sample s5_rand_family`,
whose only notation is `"s 'sample' f"` of `manifest/pgg_tableau_syntax.v:386`,
declared in no scope and so unaffected by any scope stack; `Tableau Sampled` is
an application of two constants. The notations `fdist_scope` carries are
`@^-1`, `.-fdist`, `{fdist _}`, `>>=`, `<| |>`, `` `1 ``, `` `2 ``, `` `X ``,
`` `x `` and `` `^ ``, none of which shares a token with either. `ring_scope`
is still opened last and so is still innermost.

**2. Decisions honoured.** Yes, on every count.

- The concept word is "reading" in all three new files and in every added line:
  no occurrence of the second word (`grep` over the new files and the added
  lines returns none). One residue is pre-existing: E15.
- Two manifest leaves; `manifest/pgg_tableau_marginal_bounds.v` does not
  require `manifest/pgg_tableau_reading.v` and does not require
  `manifest/pgg_tableau.v` either.
- Nothing under `instances/psl211/tableau/`: no file there is in the diff.
- `instances/psl211/psl211_colour_reading.v` is required by nothing: the only
  `Require` naming it anywhere in the tracked tree is in the fidelity file
  under `notes/`. `manifest/pgg_tableau_reading.v` is required by that one
  instance file and by nothing in `manifest/`;
  `manifest/pgg_tableau_marginal_bounds.v` by the two tableau instance files
  only.
- The PGL(2,7) trace instance of the propositions did not land:
  `pgl27_proximity.v` does not require the reading leaf, and the only landed
  PGL(2,7) declaration is the identification lemma.
- `psl211_dealt_sample` is named after the model, per N17.

**3. Comment claims.** (a) The record's comment claims only what the type
enforces: correct, S1's replacement landed verbatim, with one added sentence
audited at E17. (b) The header's restriction is right (P7) and
`reading_indistinguishability_static_coalitionE` is an `erefl` equality, so "at
every certificate and every number" is exact; but the docstring on
`static_coalition_reading` contradicts the header, E1. The exact case is right
in the header and wrong on two docstrings, E2 and E3. (c) Q2's sentence is
present in three places and true. (d) `psl211_dealt_reading_indep_false` is at
one coalition of three seats, under both-chirality priors, placed beside
`psl211_dealt_constancy_false` and naming it, and says nothing about the
all-decks model. (e) Q5's replacement landed verbatim and is true: card zero
and card one are both hearts, `psl211_is_heart c := (val c < 6)%N`
(`instances/psl211/psl211_orbit.v:84`). (f) Q6's replacement landed, improved
by naming the card-identity reading rather than "the canonical" one, and is
true. (g) The factor two, the one seat or one position, the absence of a
coalition, of a second run argument and of a secret, and the sentence that
neither proposition is one of the three the evidence proves are all present;
the S_5 comment names `s5_group_order_eq` and its module; the five-card comment
names the strictness and `ltW`. Two defects there, E5 and E7. (h)
`pgl27_coalition_trace_static_obsE`'s comment says the trace theorems and the
reading theorems are one statement each, and the two published 2^-39 numbers
are one number; both are supported (`instances/pgl27/pgl27_models.v:324` at the
reading, `:343` at the content trace). (i) The two rewritten sentences of
`psl211_reading_constancy.v` are true in substance, and defective in wording:
E4.

**4. Names.** All thirty-six landed identifiers, the constructor and the two
record fields included, are exactly the audit's final list, with the SHOULD
replacements N5, N9, N10, N11, N18, N23, N25, N27, N28 all taken. A regex sweep
of every tracked `.v` outside `notes/`, `legacy` included, finds no other
declaration of any of them: no collision.

**5. Statement-comment rules.** No `Kind:`/`Why:`/`Used by:` slots, no
`[identifier]` brackets, no plan or ledger tokens, no letter-and-digit finding
ids, no proof strategy in any docstring (the two strategy notes in
`psl211_colour_reading.v` and the one in `pgg_tableau_reading.v` sit inside
proof bodies, which is where they belong), no restatement of a type signature.
The `(** name — sentence *)` docstring shape of the two instance files is the
tree's own convention, 4474 occurrences. Defects: E8 and E9 (build-graph
status), E10 ("today"), E4 ("now"), E6 (one word, two concepts), E15, E16, E17.

**6. Layout.** Clean. No line in the three new files or in any added line
exceeds 80 bytes. Every rule line is exactly 80 with no space before the
delimiter, and every wrapped comment line is exactly 80 ending in ` *)`; the
only short full-comment lines are three genuine one-line docstrings. Banners
carry one content line each. Index columns are uniform per file: 32 in both
manifest leaves, matching
`manifest/pgg_tableau_security_property_relations.v`; 31 in
`psl211_colour_reading.v`, 29 in `pgl27_proximity.v` and
`five_card_tableau_sampled.v`, 26 in `s5_tableau_sampled.v`, each its own
file's column. Manifest comments use plain `(* *)` with 3-space continuation.
Every non-`Fail` declaration is indexed: 4+15 of 19 in the psl211 file, 4+6 of
10 in the reading leaf, 2+2 of 4 in the marginal leaf, one entry each in the
three edited instance files. Two index defects: order, E13; and E12, E14.
`_CoqProject`: the two manifest lines sit after
`manifest/pgg_tableau_security_property_relations.v` and before the first
instance line, the psl211 line after `psl211_reading_constancy.v`; all three
beside their neighbours.

**7. `landing_fidelity.v`.** It requires production only: every
`From pgg_smc Require Import` names a tracked production module and no probe
file. It ascribes all thirty-six landed declarations, counted against the diff:
ten plus the constructor and the two fields for the reading leaf, four for the
marginal leaf, nineteen for the psl211 file, and one each for PGL(2,7), S_5 and
five-card. Every `Check` is in the `@` form with a full type, so any change to
a statement fails there. It exercises four of the five `Arguments` lines Q11
names, in the block at lines 142 to 154. Two gaps, both NOTE: E20 and E21.

## Findings

Every replacement below was read against the statement it sits on before it was
written.

| id | class | file:line | the name, sentence or finding | rule, problem and evidence | replacement |
|---|---|---|---|---|---|
| E1 | **MUST** | `manifest/pgg_tableau_reading.v:109-111` | on `static_coalition_reading`: "It is the reading every proposition of the Tableau is stated at today, and the reading the link lemma of the Sampled level identifies with the executed coalition view." | False, and it contradicts this file's own header and its own last lemma. `EvidenceProp` (`manifest/pgg_tableau.v:596`) maps the three constructors of `SecurityEvidence` (`:307`) to `ExactProp` (`:501`), `IndistinguishabilityPropAt` (`:529`) and `IdealProximityPropAt` (`:565`). Only `IndistinguishabilityPropAt` is stated at `static_coalition_obs`; `ExactProp` and `IdealProximityPropAt` are both stated at `sa_coalition_view`, the second at both of its two laws. That is why `exact_independence_executed_of_reading` exists twenty lines below. "today" is also a time word banned from a statement comment | "A coalition's static endpoint reading as a reading. The input-indistinguishability proposition of the Tableau is stated at it; the exact-independence and the ideal-proximity propositions are stated at the executed coalition view, which the link lemma of the Sampled level identifies with it." |
| E2 | **MUST** | `manifest/pgg_tableau_reading.v:217-221` | on `ReadingExactIndependence`: "It is an independence and not a numeric bound, so it is the conjunct the framework's entropy forms are derived from, and those forms are not restated here." | Over-claims at two levels. The definition quantifies over an arbitrary reading `r`, and at an arbitrary `r` the proposition is no conjunct of anything in the framework. Even at `static_coalition_reading` it is the `ew_indep` field, which finding P6 established is NOT the independence conjunct of `ExactProp`: the two differ by the link lemma, the hypothesis `Hview` of this file's own last lemma. The entropy forms of `ExactProp` are derived from independence of `sa_coalition_view` | "It is an independence and not a numeric bound. The framework's entropy forms sit inside `ExactProp`, derived there from independence of the executed coalition view, which this proposition reaches at a coalition's static reading along the link lemma of the Sampled level; none of those forms is restated here." |
| E3 | **MUST** | `instances/psl211/psl211_colour_reading.v:330-332` | on `psl211_colour_reading_indep`: "The statement is an independence and not a numeric bound, so it is the conjunct the framework's entropy forms are derived from, and those forms are not restated here." | The same sentence at a place where it is further from the truth: this statement is at the colour reading over `psl211_dealt_sample`, where there is no `ExactWitness`, no executed level and so no `ExactProp` at all, as the next sentence of the same comment says. Nothing here is a conjunct of a framework proposition | "The statement is an independence and not a numeric bound, and no entropy form of the framework is restated at it." |
| E4 | **MUST** | `instances/psl211/psl211_reading_constancy.v:57-61` and `:970-974` | the two rewritten sentences: "A dealer-dealt sample adapter now exists, psl211_dealt_sample ..., so an ideal can be pinned to these parameters, and no certificate is built over it." and "The dealer-dealt sample adapter psl211_dealt_sample ... pins an ideal to these parameters, and no certificate is built over it." | Three faults. The docstring version is self-contradictory: an ideal is a certificate's field, and the same sentence says no certificate is built, so nothing pins an ideal; what the adapter supplies is the sample space over which an ideal could be pinned, which the header version has right. "now exists" is a status word. And one fact is carried in two wordings three hundred lines apart. Both replaced by one sentence | at both places: "An ideal can be pinned to these parameters through the dealer-dealt sample adapter `psl211_dealt_sample` of `instances/psl211/psl211_colour_reading.v`, and no certificate is built over it. The dealt parameters carry no endpoints statement, so there is no program and no path over them either." (rewrapped to each site's own comment style and width) |
| E5 | **MUST** | `manifest/pgg_tableau_marginal_bounds.v:72-74` | on `SeatMarginalPropAt`: "at the process-identifier base zero every statement of the framework uses" | The nat is `P_idx` of `security/pgg_sample_adapter.v:136`, threaded to `exec_run x w0 P_idx` and on to `dealer_with_input_encoding ... [:: w0] ... P_idx` (`protocol/pgg_execution_plug.v:156-159`), where `protocol/pgg_run.v:45-50` and `protocol/card_exchange_pismc.v:70-75` make it the selection index into the dealer's deck `W`. The process identifiers are fixed elsewhere and do not move with it: dealer 0, verifier 1, seat `i` at `2 + i` (`protocol/pgg_execution_plug.v:131-141`). The tree's own words for this nat are "selection index" and "process offset" (`protocol/pgg_observed_execution.v:98`, `manifest/pgg_analysis_manifest.v:514`, `instances/s5/s5_exec.v:47`); "process-identifier base" is a third word and is not what it is | "at the selection index zero every statement of the framework fixes, the single entry of the run's one-element deck and so the cut itself" |
| E6 | **MUST** | `manifest/pgg_tableau_marginal_bounds.v:9`, `:30`, `:86`, `:87`, and `instances/kim2025/tableau/five_card_tableau_sampled.v:250` | "the law of one finite reading of the model's cut", "one finite reading of the cut has a law within c", "The reading is a function of the shuffle alone", "The reading compared is a function of the shuffle alone" | One word, two concepts, in the file that turns on the distinction: line 23 of the same header says "a marginal bound is not a statement at a reading", and "reading" is the tree's word for a coalition's static reading, fixed by decision 1. The cut map is a function of the shuffle with no coalition and no run argument | write "function of the cut": ":9" to "the cut form compares the law of one finite function of the model's cut"; ":30" to "one finite function of the cut has a law"; ":86" to "the law of one finite function of the model's cut"; ":87" to "That function is of the shuffle alone"; the five-card line to "The function compared is of the shuffle alone" |
| E7 | SHOULD | `manifest/pgg_tableau_marginal_bounds.v:11-12` | "so neither is one of the three propositions the security evidence proves, and no constructor of SecurityEvidence carries either." | S5 asked for one type-honest sentence and the second clause puts back the shape it removed. `SecurityEvidence` (`manifest/pgg_tableau.v:307-311`) has three constructors and each carries a witness or a certificate, never a proposition, so the clause is true of every proposition in the tree and separates nothing, while inviting a reader to think other propositions are carried by constructors | end the sentence at "proves." and delete the rest |
| E8 | SHOULD | `manifest/pgg_tableau_marginal_bounds.v:21-22` | "This file is required by the instance files that state an instance of either proposition and by nothing in manifest/." | A Used-by line inverted: a fact about the build graph that the next reorganization falsifies, and the reader's question is answered by what follows it | delete the sentence; keep "It does not require manifest/pgg_tableau_reading.v: a marginal bound is not a statement at a reading, ..." as the paragraph's opening |
| E9 | SHOULD | `instances/psl211/psl211_colour_reading.v:30` | "This file is required by nothing." | Same class. The sentence before it already places the file, and this one goes stale the first time anything requires it | delete the sentence |
| E10 | SHOULD | `manifest/pgg_tableau_reading.v:172-173` | on `reading_indistinguishability_static_coalitionE`: "The framework's proposition therefore states nothing the reading form does not, and nothing the framework proves today changes." | The second clause is about the landing, not about the statement, and "today" dates it. The first clause is exact and worth keeping | "The framework's proposition therefore states nothing the reading form does not." |
| E11 | SHOULD | `manifest/pgg_tableau_marginal_bounds.v:88-90` | on `CutMarginalPropAt`: "so this states less than the seat form: it is about the model's randomness and not about what any seat sees." | The two propositions are incomparable, not ordered: they compare different laws on different carriers, `sa_seat_dist` being a pushforward of the sample law along the executed endpoint reader (`security/pgg_sample_adapter.v:179-181`) and this one a pushforward of the cut law. Neither implies the other, so "states less" asserts a relation that does not hold | "so it speaks of the model's randomness and not of what any seat sees."; composed with E6 the sentence reads "That function is of the shuffle alone and not of the run argument, so it speaks of the model's randomness and not of what any seat sees." |
| E12 | SHOULD | `instances/kim2025/tableau/five_card_tableau_sampled.v:90-92` | index entry "== the same, at 2^-40 and not below it, as a one-position marginal bound on the cut" | Reads as a claim about the distance, that it is not below 2^-40, which is false: the cited theorem is strict. The intended content, that the published number is stated at `<=` and not at `<`, is already in the docstring where it belongs | `(*   five_card_repeated_cut_marginal                                          *)` / `(*                           == the same comparison as a one-position         *)` / `(*                              marginal bound on the cut, at most 2^-40      *)` |
| E13 | SHOULD | `instances/psl211/psl211_colour_reading.v:57-62` | the index lists `psl211_colour_of_reading_collides` before `psl211_colour_indistinguishability_of_coalition_reading` | Index entries go in file order; in the file the post-processing lemma is at `:286` and the collision lemma at `:306`. `LANDING.md`'s own declaration list has them the other way round from the index, which is how the slip shows | swap the two entries: `(*   psl211_colour_indistinguishability_of_coalition_reading                  *)` / `(*                             == the post-processing law at that             *)` / `(*                                factorisation                               *)` then `(*   psl211_colour_of_reading_collides                                        *)` / `(*                             == that colour map is not injective at a       *)` / `(*                                nonempty coalition                          *)` |
| E14 | SHOULD | `instances/s5/tableau/s5_tableau_sampled.v:44` | the new index heading "Lemmas:" | The four sibling files of `instances/s5/tableau/` head their lemma index "Key results:" (`s5_tableau_observed.v:43`, `_executable.v`, `_analysis_bridged.v`, and the same in every other instance's tableau directory). "Lemmas:" is the `manifest/` heading, which the two new leaves correctly use | `(* Key results:                                                               *)` |
| E15 | SHOULD | `instances/pgl27/pgl27_proximity.v:54`, and the two docstrings at `:100-105` and `:116-119` | the pre-existing index entry "pgl27_static_obsE == the framework's seat reader is the instance's", three lines above the landed entry that says "its static reading"; and "pushing a reader forward along a distribution on cuts", "it needs the reader as one function" | Decision 1 fixes one word for this concept, and the landing put both words in one index block and in one file. The word survives in 255 production lines tree-wide, so the fix is scoped to the files this landing touches and is not a rename campaign. `pgl27_static_obsE` compares `static_coalition_obs C s g` with `pgl27_view R C (s, g)`, a coalition's reading, so "seat" can go and the line stays at 80 bytes with the column kept | index: `(*   pgl27_static_obsE       == the framework's reading is the instance's     *)`; docstrings: "pushing a reading forward along a distribution on cuts", "it needs the reading as one function" |
| E16 | SHOULD | `instances/psl211/psl211_colour_reading.v:188-190` | on `psl211_colour_reading`: "It is what a coalition holding cards of two indistinguishable colours sees, and it holds no card identity." | The two colours are what the reading distinguishes; what it hides is which card of a colour a position holds. As written it says the colours cannot be told apart, which is the opposite of the definition, whose body is `psl211_is_heart (...)`. "indistinguishable" is also the tree's word for a security property and is best kept for it | "It is what a coalition sees when it can tell the colour at each of its positions and not which card of that colour lies there." |
| E17 | SHOULD | `instances/psl211/psl211_colour_reading.v:162-164` | on `psl211_dealt_sample_cut_distE`: "Every proposition stated at a reading pushes the reading forward along this law" | Only one of the two does. `ReadingIndistinguishabilityPropAt` pushes forward along `sa_cut_dist` (`manifest/pgg_tableau_reading.v:166-167`); `ReadingExactIndependence` uses the reading as a random variable on `sa_sampleP` (`:226`), which is `psl211P`, not this law | "The input-indistinguishability proposition at a reading pushes the reading forward along this law, so it is the law the colour theorems' own uniformity hypothesis meets." |
| E18 | NOTE | `manifest/pgg_tableau_reading.v:101-103` | on the record: "The value type depends on the coalition because a coalition of a different size reads a different amount." | The reason given is not realised anywhere: both readings in the tree are constant in the coalition, `fun _ => {ffun seats -> cards}` at `:113` and `fun _ => {ffun seats -> bool}` at `instances/psl211/psl211_colour_reading.v:193`. S1's own sentence is about what the type does and does not constrain, and this addition states a motivation as a fact | "The value type may depend on the coalition; both readings of this tree return a seat-indexed map at every coalition and do not use that freedom." |
| E19 | NOTE | `instances/psl211/psl211_colour_reading.v:18` | "Two readings of one run are separated here." | The same header says at `:29-30` that no statement below is about an executed run. One word, two senses, twelve lines apart | "Two readings of one model are separated here." |
| E20 | NOTE | `notes/probes/2026-09-21-psl211-colour-reader/landing_fidelity.v:92-96`, `:115-119`, `:161-171` | the four propositions are ascribed at `... -> Prop` | A `Check` of a `Prop`-valued definition pins its arity and argument types and not its body, so a change from `<=` to `<`, or to the threshold, would pass there. The guard exists elsewhere: `exact_independence_of_witness` type-checks only against the current body of `ReadingExactIndependence`, the two `_prop_at2` lemmas against the two marginal bodies, and `reading_indistinguishability_static_coalitionE` against the indistinguishability body, all in production | no change needed; worth one line in the fidelity file's header saying the bodies are pinned by those four production declarations |
| E21 | NOTE | `notes/probes/2026-09-21-psl211-colour-reader/landing_fidelity.v:142-154` | the implicit and explicit split block exercises `StaticReading`, `sr_read`, `static_coalition_reading`, `ReadingExactIndependence` and `ReadingIndistinguishabilityPropAt`, and not `reading_indistinguishability_postprocessing` | Q11 names that call site too: five explicit arguments after `{R A E sa}`. It is exercised in production, by the proof of `psl211_colour_indistinguishability_of_coalition_reading` (`instances/psl211/psl211_colour_reading.v:295-297`), which applies it positionally and would fail as a unification error on any change | none required; the production call site is the guard |
| E22 | NOTE | `manifest/pgg_tableau_reading.v:44`, `:54-56` | `exact_independence_of_witness` is a `Definition` indexed under "Lemmas:" | Its type is a `Prop` and it is used as a lemma, so the placement is defensible; noted only so the fixer does not take it for a slip | keep |
| E23 | NOTE | `instances/pgl27/pgl27_proximity.v:125-131` | "at these eight cards the two are one finite map" | The lemma quantifies over `C : {set 'I_8}`, a set of seats, and the shared value type is a map from seats to card positions; "at these eight cards" names the wrong index set, harmlessly | "at this instance's eight seats the two are one finite map" |
| E24 | NOTE | `instances/kim2025/tableau/five_card_tableau_sampled.v:29` | "Three of the statements here are about neither a program nor the manifest's path for it" | The file holds four such statements: the three enumerated and `kim_centi_small` (`:271`), a side condition on a real number. The count is of the enumerated ones and was already so before the landing, which only moved it from two to three | none; pre-existing, out of this landing's scope |
| E25 | NOTE | `manifest/pgg_tableau_reading.v`, `manifest/pgg_tableau_marginal_bounds.v`, `instances/psl211/psl211_colour_reading.v` | assumptions | `LANDING.md`'s ten `Print Assumptions` rows match the ten declarations the fidelity file prints, and no landed declaration carries an assumption beyond the three classical ones and, at the S_5 instance, `rigidity_s5_instance.s5_group_order_eq`, which its comment names. Not re-run here | — |

## What was checked and found sound

Recorded so a fix pass does not redo it.

- `psl211_colour_of_reading_collides`: the two witnesses are the constant maps
  at card zero and card one, and `psl211_is_heart c := (val c < 6)%N`, so both
  are hearts and Q5's sentence is exact.
- `psl211_colour_reading_dep_k6`: the threshold statements bound each other,
  `psl211_leak_coalition_not_below_k` sitting between them, and the sentence
  about a prior supported on one chirality is true, an almost surely constant
  secret being independent of everything.
- `psl211_dealt_reading_indep_false`: three is below six, the coalition is the
  one `psl211_dealt_constancy_false` uses, Q7's and Q9's sentences are both
  present and both true, and nothing in the comment speaks of the all-decks
  model.
- Q2's placement claim: `grep instance_endpoints_stmt instances/psl211/*.v`
  returns one line, `psl211_models.v:342`, at `psl211_alldecks_params`. No
  certificate is built over `psl211_dealt_sample`: the name occurs in the new
  file and in the fidelity file only.
- The five-card and S_5 instance comments: the factor two, the strictness
  dropped through `ltW`, the axiom and its module, and the advantage at most
  half the number are all correct against their statements.
