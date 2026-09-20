# Adversarial soundness audit of the landing below AnalysisBridged (2026-09-21)

Audited: the working tree over commit `b807b6b`, `git diff HEAD` across
`manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v`,
`instances/s5/tableau/s5_tableau_observed.v` and
`instances/s5/tableau/s5_tableau_checks.v` (312 inserted lines, 11 deleted).
Read against `notes/20260920-terminals-below-analysis-bridged-probe-design.md`
(last section, seven decisions), `LANDING.md` (seven departures),
`landing_fidelity.v` / `.out`, the five `t2_msg_*` files and
`t2_msg_outputs.txt`, and the earlier `audit-soundness.md` and
`audit-naming.md`.

Two scratch files were compiled for this audit, under
`scratchpad/below_landing_audit/`: `a1_audit.v` (rc 0) and `a2_shadow.v`
(rc 0). `manifest/pgg_tableau_syntax.v` was recompiled once with the
notation warnings re-enabled (rc 0), output to the scratch directory. No
repository file was edited except this report.

## Verdict

**NO-GO for committing as it stands.** Two MUST findings, A1 and A2, are
sentences in landed comments that state the opposite of what the landing
measured and of what the same landing says three lines away. Both are
sentence rewrites: no term, statement, proof, notation or name has to
change, and the two files need only be recompiled.

Everything the audit could falsify about the terms themselves came back
clean. The landing is a pure addition, the seven decisions are honoured,
the pinned statement is the pinned statement, the recorded rejections are
real type mismatches, and the surface survived every adversarial parse the
audit could construct.

## What was verified clean

**Q1, pure addition.** Eleven lines are removed, all of them header prose in
the three places the plan names. `instances/s5/tableau/s5_tableau_checks.v`
lines 12-19 at HEAD: the "Two boundaries" paragraph, rewrapped; a word-level
diff of the retained text shows exactly one changed word, `Two` to `Three`,
and one appended sentence, which is departure 7.
`instances/s5/tableau/s5_tableau_observed.v` line 70 at HEAD, the last line
of the second header paragraph, which gained a sentence (decision 6).
`manifest/pgg_tableau_syntax.v` lines 40 and 84 at HEAD, the two header
facts of Z12 and Z13. A keyword-anchored diff of every declaration line
(`Definition`, `Lemma`, `Theorem`, `Record`, `Variant`, `Inductive`,
`Notation`, `Arguments`, `Fail`, `Check`, `Section`, `End`) between HEAD and
the working tree reports no removed line in any of the four files.

**Q2, the seven decisions.** Two `Record`s and no indexed family; no
`PublishedAtLevel`, no `RunCorrectProp`, no `run_correct_of_level`.
`publish_sampled` is the only Sampled terminal and its status argument is
`TransferStatusWithoutTheorem`; no `publish_sampled_step` landed. Both
surface rules expand through `;;;`, that is `tableau_bind`, which the
measured types confirm: `publish_observed : forall q : StackAt Observed,
StackProp Observed q -> AssumptionStatus -> PublishedObserved` is exactly
the `f : forall x, Q x -> P x -> T` that `tableau_bind` wants. The spellings
are `s |> publish Observed a` and `s |> publish Sampled t a`. The three S_5
names follow decision 5. The PGL(2,7) value did not land; the diff touches
four files. Four rejections are recorded in the S_5 checks file.

**Q5, the pinned statement.** Verified by mutual ascription in `a1_audit.v`,
all three compiled: `@S5Analysis.observed_recovers` inhabits the landed
statement; `@s5_observed_recovers` inhabits it too; and
`@s5_dealt_observed_published_recovers` inhabits the pinned statement with
the endpoint list written out as `@exec_endpoints S5Analysis.profile
S5Analysis.exec_plug s w0 0`, which is how `s5_exec.v:440` writes it. The
landed statement differs from the pinned one only by the facade aliases and
by leaving the endpoint list to be inferred from the size proof, `ep` being
implicit under `Set Implicit Arguments`. The `And3 _ _ H` projection takes
the third conjunct, and `oe_correct_prop`'s third conjunct
(`manifest/pgg_tableau.v:461-465`) is `exec_decode ... (oe_endpoints_size oe
x w0) = oe_expected oe x`, the recovery one. The ascription against the
pinned type is what proves the conjunct is the right one.

**Q4, the surface, adversarially.** In `a1_audit.v` the pre-existing rule
still parses with the status held in a variable (`tv`), with variables named
`Observed0` and `Sampledx`, with a parenthesised computed status, at all four
literals, and with a written-out assumption status. Both new rules parse.
`fun Observed : nat => Observed` and `fun Sampled : nat => Sampled` elaborate
to `id`, and `Observed : CompletionLevel` still resolves, so neither token is
reserved. Recompiling `manifest/pgg_tableau_syntax.v` with
`notation-overridden` and `notation-incompatible-prefix` enabled produced no
warning at any of lines 422-442: every warning comes from the `Require
Import` lines 120-127 and names infotheo's `_ <| _` and MathComp's arithmetic
notations, all present at HEAD. So the three `s |> publish ...` rules do not
override one another and the parser reports no incompatible prefix among
them. Two refinements are in the table as A10.

**Q6, the messages.** `t2_msg_outputs.txt` holds five compiles, each rc 1.
The first three are `The term "s5_dealt_observed_published" has type
"PublishedObserved" while it is expected to have type "PublishedAt ?c"` twice
and `... "Published"` once. The fourth is a `cannot unify` between the two
paths. The fifth, behind decision 2, is `The term "IdealFinite" has type
"TransferStatus" while it is expected to have type
"TransferStatusWithoutTheorem"`. All five are type mismatches; none is an
unknown reference and none a syntax error.

**Q7, the `Arguments` directives.** `clear implicits` is the file's idiom,
used 25 times in `manifest/pgg_tableau.v`. `About` in `a1_audit.v` shows the
directives did what departure 1 says: `Arguments published_observed_thm p x
w0 _`, `Arguments run_correct_of_observed r x w0 _`, `Arguments
run_correct_of_sampled r x w0 _`, `Arguments view_identification_of_sampled r
R idx C`, `Arguments publish_observed q pf a`, `Arguments publish_sampled a q
pf t`. `published_sampled_thm` has no directive and needs none: `Arguments
published_sampled_thm p` already, because `StackProp Sampled q` is a
conjunction and has no trailing quantifier for the record argument to be
inferred from. The asymmetry is forced by the two propositions and is not a
defect. Every call site in `landing_fidelity.v` elaborates as written, and
so does `run_correct_of_observed s5_dealt_observed_published s w0 Gw0` at
`s5_tableau_observed.v:156`.

**Q3, the honesty sentences.** (a) is present at
`manifest/pgg_tableau.v:1071-1077` and `:1088-1092`, and is true in
substance but imprecise as written, see A4. (b) is present three times, in
the file header at `:90-93`, in `publish_observed`'s docstring at
`:1117-1122`, and in the S_5 docstring at `s5_tableau_observed.v:128-131`,
and is true each time. (c) is present at `s5_tableau_observed.v:138-142` and
is **false as written**, see A1. (d) is present at
`s5_tableau_checks.v:86-87` and is true in substance, with one type-honesty
slip, see A6. The one over-claim of the kind the question names, "the
manifest's claim and its proof are one term" said where the assumption status
is hand-written, is A1: the same docstring claims the path stops being "a
description a reader matches by eye", at a level where one of its five
coordinates still is exactly that.

## Findings

| id | class | file:line | finding | what to change |
|---|---|---|---|---|
| A1 | MUST | `instances/s5/tableau/s5_tableau_observed.v:138-142` | The docstring of `s5_dealt_observed_published_pathE` reads "Four of its five coordinates are fixed by the terminal and the fifth is the observed execution s5_dealt_path_observedE already identifies, so what the equation adds is that the theorem now travels beside the path rather than the path being a description a reader matches by eye." `publish_observed` (`manifest/pgg_tableau.v:1123-1126`) writes `@MkAnalysisPath (ob_obs q) Observed None NoModelComparison a`: the terminal fixes **three** coordinates, the data gives the observed execution, and the assumption status `a` is the payload written at the call site. `s5_det_path` (`manifest/pgg_analysis_manifest.v:1040-1042`) carries `AcceptsAxioms [:: AxS5GroupOrder]` because the author wrote that literal in both places. The fourth recorded rejection in `s5_tableau_checks.v:94-96` exists precisely to show this, and honesty sentence (b) sits three lines above in the same file. The second clause compounds it: the assumption coordinate IS still a description a reader matches against the manifest's prose. | Replace with: "Three of its five coordinates are fixed by the terminal, the observed execution is the one s5_dealt_path_observedE already identifies, and the assumption status is the payload written at the call site. What the equation adds is that run correctness now travels beside the path; the fourth recorded rejection of s5_tableau_checks.v shows the equation holds only for the assumption status this program was published under." Checked against the statement `published_observed_path s5_dealt_observed_published = s5_det_path` and against the definition at line 135-136. |
| A2 | MUST | `manifest/pgg_tableau_syntax.v:80-84` | "Observed and Sampled belong to that first list too, measured on 2026-09-21: each follows the literal publish in one of the two terminal rules below AnalysisBridged, and each is still a binder name and still the CompletionLevel constructor it names." The paragraph's first list, at line 64-67, is the nineteen identifiers the surface **reserves as global keywords**. The justification given in the same sentence is the criterion of the other group, the tokens at line 71-73 that "follow a literal and stay identifiers", and it is what was measured: `LANDING.md` says "Neither token is reserved and the header's count of nineteen is unchanged", `t_keyword_check_two_records.v` prints `fun Observed : nat => Observed`, and `a1_audit.v` reproduces both bindings and `Observed : CompletionLevel`. The sentence as written puts the two tokens in the reserved list and so contradicts both the measurement and the count of nineteen two sentences earlier. | Replace the clause with: "Observed and Sampled follow a literal and stay identifiers too, measured on 2026-09-21: each follows the literal publish in one of the two terminal rules below AnalysisBridged, and each is still a binder name and still the CompletionLevel constructor it names, in a file whose Require lines are ssreflect and this one. The count of nineteen is unchanged." Checked against the two measurements named. |
| A3 | SHOULD | `manifest/pgg_tableau.v:83-87` | "The two records are inductive types distinct from PublishedAt, which is what makes every security reader inapplicable to a value of either, so a later reading of PublishedAt as one of them would turn each recorded rejection into an acceptance." The direction is inverted. What would turn the rejections into acceptances is a coercion out of either record into `PublishedAt`, since the readers take `PublishedAt c` and the failure is `PublishedObserved` against `PublishedAt ?c`. Reading a `PublishedAt` as a `PublishedObserved` would do nothing to those terms. | "so a later coercion out of either record into PublishedAt would turn each recorded rejection into an acceptance." Checked against the message in `t2_msg_outputs.txt` lines 5-6 and against the six `Fail Check`s in `a1_audit.v`. |
| A4 | SHOULD | `manifest/pgg_tableau.v:1071-1073` and `:1089-1090` | "The three fields are independent, as the three of PublishedAt are" and "The three fields are independent in the same sense." Not type-honest: `published_observed_thm : StackProp Observed published_observed_at` is typed at the first field, as `published_thm : BridgedProp c published_at` is. What is independent is the path. The clause that follows already says the right thing, so only the opening is wrong. | At 1071: "The path field is constrained by neither of the other two, as PublishedAt's is not: the terminal below builds it from the program's own data, and the record accepts any path written by hand beside any data. The proposition field is typed at the data field, as PublishedAt's third field is." At 1089: "The path field stands in the same relation to the other two." Checked against the two `Record` bodies at 1078-1081 and 1094-1097 and against `PublishedAt` at 1001-1004. |
| A5 | SHOULD | `manifest/pgg_tableau.v:80-82` | "A program that stops at Observed hands over run correctness with the manifest path its own data builds." The data does not build the assumption coordinate; the author does. The paragraph repairs this three sentences later ("The assumption status is a payload at all three levels"), but the opening sentence is the one a reader carries away, and it is the same compression A1 makes load-bearing. | "A program that stops at Observed hands over run correctness with a manifest path whose observed execution is the program's own, whose level, model slot and transfer status the terminal fixes, and whose assumption status is the payload the line writes." Checked against `publish_observed` at 1123-1126: `ob_obs q` off the data, `Observed`, `None` and `NoModelComparison` fixed, `a` the payload. |
| A6 | SHOULD | `instances/s5/tableau/s5_tableau_checks.v:86-87` | "Nor is that value a Published. The two are distinct inductive types with no coercion between them." `Published` is not an inductive type: `manifest/pgg_tableau.v:1009` declares `Notation Published := (PublishedAt no_concluded_bound)`, confirmed by `Print Published` in `a1_audit.v`. The two distinct inductive types are `PublishedObserved` and `PublishedAt`. | "Nor is that value a Published, which is PublishedAt at the empty bound. PublishedObserved and PublishedAt are distinct inductive types with no coercion between them, so the ascription written here is refused." Checked against the notation at 1009 and the message at `t2_msg_outputs.txt:19-20`. |
| A7 | SHOULD | `instances/s5/tableau/s5_tableau_checks.v:90-93` | The fourth rejection's comment says the path built under `BaselineClassicalOnly` "is not the manifest's, which records the accepted group-order fact. Conversion decides the two paths apart." True, but it never says that both sides of the disagreement are hand-written: the payload at the call site and the `ap_assumption` field of `s5_det_path` at `manifest/pgg_analysis_manifest.v:1042`. A reader can take the rejection for the framework having checked which axioms the program uses, which is exactly what honesty sentence (b) denies, and (b) appears nowhere in this file's body. | Append one sentence: "Both sides of that disagreement are written by hand, the payload here and the manifest's field there, so what the kernel decides is whether two authors' statements agree and not which axioms the program uses." Checked against `pgg_analysis_manifest.v:1040-1042` and the `cannot unify` message at `t2_msg_outputs.txt:23-35`. |
| A8 | NOTE | `instances/s5/tableau/s5_tableau_observed.v:42-44` | `s5_dealt_observed_published_recovers` is indexed under `Definitions:` while `s5_dealt_observed_published_pathE` goes under `Key results:`. The first is a proof of a proposition, declared with `Definition` only because it is written in term mode. Its neighbours in `Key results:` are `s5_realises_expected` and `s5_rand_realises_expected`, both `Lemma`. Indexing it by keyword rather than by what it is sends a reader looking for the instance's recovery statement to the wrong block. | Move the entry to `Key results:`, keeping the wording "the endpoints of that run decode to the dealt position, read off the published value". |
| A9 | NOTE | `manifest/pgg_tableau.v:1098` and `:142-144` | "The two transfer statuses that assert no theorem about an idealized model", and the index entry "the transfer statuses asserting no theorem about an idealized model". `manifest/pgg_analysis_status.v:69-71` writes the same fact as "StaticExecutedOnly and NoModelComparison carry no such theorem, and a path with such a status names the absent premise instead". One word per concept: a status carries a theorem in the manifest's vocabulary and asserts one in the new type's. | Write "carry no theorem about an idealized model" in both places. Checked against `pgg_analysis_status.v:63-71`. |
| A10 | NOTE | `manifest/pgg_tableau_syntax.v:85-87` | "Inside the publish position the two tokens are taken by those two rules, so a transfer status spelled Observed or Sampled could not be written where the other thirty-one uses write theirs." Measured in `a2_shadow.v` under a local `Let Observed : TransferStatus := IdealFinite`: the bare spelling is indeed refused, and the two are refused differently, `Observed` by the typechecker and `Sampled` by the parser, `Syntax error: [term level 0] expected after [term level 0]`, which `Fail` cannot catch. But `prog \|> publish (Observed) a` compiles and yields a `Published`, and Rocq prints it back as `prog \|> publish Observed a`, a string that re-parses through the new rule as a different term. Nothing in the tree shadows either constructor, so no use is affected; the sentence is nevertheless stronger than the measurement supports. | Optional. If kept, narrow it: "written bare, a transfer status spelled Observed or Sampled cannot reach the slot the other thirty-one uses write theirs in, Observed being refused by the typechecker and Sampled by the parser; parenthesised, it reaches the slot and prints back without its parentheses." |
| A11 | NOTE | `manifest/pgg_tableau.v:1194-1198` | `run_correct_of_observed`'s docstring: "It is the whole content of such a value, and the proof is the observed execution's own field." Two loose clauses. The value also carries a path, so "the whole content" means the whole proved content. And the reader returns the record's third field, which is `OE.oe_run_correct` only for a value the `execute` rule built; a record written by hand holds whatever proof its author supplied. The load-bearing clause, "the reader adds nothing to it", is exact. | "It is the whole of what such a value proves, and the reader is the third field itself, so a value the execute rule built hands back the instance's own run-correctness field and the reader adds nothing to it." Checked against the body `published_observed_thm r` at 1199-1201 and against `observed_correct` at 471-472. |
| A12 | NOTE | `instances/s5/tableau/s5_tableau_observed.v:22` and `:127` | "the path it answers", twice. A path is not answered; the relation is the equality `s5_dealt_observed_published_pathE` states. Elsewhere the landing says a terminal *builds* a path and a path *records* a coordinate, which is the vocabulary the rest of the tree uses. | "the manifest path it builds", in both places. |
| A13 | NOTE | `instances/s5/tableau/s5_tableau_checks.v:73` | The banner reads "No security reader applies to a program published at Observed", a general statement over the readers, while two are recorded below it and the file's own header at line 8-10 says a recorded rejection "states no general impossibility". The generalisation is in fact supported: `a1_audit.v` compiles `Fail Check` at `view_proximity_of`, `view_indistinguishability_of`, `run_correct_of`, `view_identification_of`, `published_at` and `run_correct_of_sampled` as well, all six refused, and every one of them takes `PublishedAt c`. The other two banners in the file are equally general, so this is style, not soundness. | No change required. If the tension is worth removing, name what is recorded: "Two security readers refused at a program published at Observed". |

## What the audit could not falsify

No landed term, statement, proof, notation or name is wrong. The two MUST
findings and the five SHOULD findings are all sentences. After A1 and A2 are
rewritten and `instances/s5/tableau/s5_tableau_observed.v` and
`manifest/pgg_tableau_syntax.v` recompile, this landing is committable.
