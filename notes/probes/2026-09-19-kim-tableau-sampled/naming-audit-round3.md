# Naming and style audit, round 3: Kim's two five-card rows as Tableau programs

Date: 2026-09-19. Independent read-only audit, third and closing round.

Nothing was compiled, no Rocq process was started, no file was edited. Only
this report was written. Every claim is backed by a file:line read of the tree
at commit 2e567e0 or by a Python scan re-run in this session.

Scope, as set by the coordinator: round-2 items R2-B1 and R2-S1 through R2-S4,
Fixes A through E, and N3, plus a check that no replacement introduced a new
defect. References of the form `landing:N` are lines of
`notes/probes/2026-09-19-kim-tableau-sampled/five_card_rows_landing.v`, now 582
lines.

VERDICT: GO.

## 1. Round-2 items

| item | state | current file:line | evidence |
|---|---|---|---|
| R2-B1, "The two levels are one constructor" | RESOLVED | landing:42-43 | Now "neither of those is proved at this instance. AnalysisBridged is one constructor with two admission criteria." The subject is the single constructor, which is what the passage needs. Whitespace-normalised search for the old sentence: 0. |
| R2-S1, "is not an error" | RESOLVED | landing:46-49 | The defence is gone, 0 occurrences, and the reason replaces it: "A program reaches it only through one of the two arms of certify, each of which produces a theorem of that same kind, so the Tableau's criterion is the stricter of the two and the gap at this row is the manifest's criterion met by a theorem no arm takes." That is checkable and it is what the soundness auditor's request actually needed. |
| R2-S2, "one seat's endpoint" in the repeated program's comment | RESOLVED | landing:385-386 | Now "What is proved of this model is the law of one starting position's endpoint under its cut". 0 occurrences of the old phrase. The contradiction with the endpoint lemma's comment at landing:485, which says the statement "names no seat, no set of seats and no secret", is gone: both now say position. |
| R2-S3, ragged 21-character line | RESOLVED | landing:34 | Now full width: "there although the manifest places it at AnalysisBridged, because the". No prose line of the header is short for want of re-flowing. |
| R2-S4, singular in a three-program file | RESOLVED | landing:21, landing:52, landing:53, landing:59 | "The uniform row is written in the statement surface of"; "No statement of a program is a theorem about this instance"; "In the uniform row the algebra, ..."; "The security mathematics reaches that row through the last payload alone". The five-statement enumeration is now explicitly the uniform row's, which is the half that mattered. |
| N3, longer gloss for `five_card_row_biased_levelE` | RESOLVED | landing:119-122 | "== the manifest's completion level for the biased row, which its program does not reach". Four lines for three, and the header table now shows the asymmetry as deliberate. |
| Fix E, the spec | RESOLVED | spec "Folded in", plus two new paragraphs | The fold-in bullet now reads "Each arm produces a theorem of that same kind, so the Tableau's criterion is the stricter of the two, and the gap at this row is the manifest's criterion met by a theorem no arm takes", matching the landed header. One paragraph records that "one seat's endpoint marginal" in the `kim_deal_centi_lt` row of Cited objects and "a pair of seats" in ledger row K6 describe the upstream lemma and a probe mutation, both outside the landed text, and are left as their sources write them. A further paragraph records what naming round 2 stopped on, which is the right place for it. |

Application fidelity. I diffed the current file against
`history/five_card_rows_landing.2026-09-19-before-fix2.v` myself rather than
taking the report. Exactly four hunks, all inside comments, all byte-identical
to the blocks in `naming-audit-round2.md`: Fix A at landing:21, thirty lines
for thirty; Fix B at landing:52, sixteen for sixteen; Fix C at landing:383,
seven for six; Fix D at landing:119, four for three. Line count moves from 580
to 582, which is what those two one-line growths predict.

## 2. The four replaced passages, read in place

The header's three paragraphs now read as one argument, in the order the
coordinator named.

Paragraph one, landing:6-19. What the scheme is, what a five-card row's
security argument is, the scope of the coalition statements, and the one
statement in the file that is not a coalition statement. It closes by naming
`five_card_row_biased_leak_bound` as a ceiling on input privacy at any list of
card positions, which sets up the second paragraph rather than duplicating it.

Paragraph two, landing:21-50. What the uniform row is, statement by statement,
then where the two Kim rows stop and why, then the two-criteria account of the
level. The internal order is right: the biased row's stopping point is stated
before the account of why the manifest's higher level is nevertheless licensed,
so a reader meets the apparent conflict and its resolution in that order. The
pronoun chain holds across the new sentences: "AnalysisBridged" at landing:42,
"admits a row to it" at landing:43, "A program reaches it" at landing:46, all
one referent. "The gap at this row" at landing:48 contrasts with the two
indefinite "a row" uses just above it and reads as the biased row, which is the
subject of landing:33 onward.

Paragraph three, landing:52-67. What a program's statements are and are not,
with the five-statement enumeration now scoped to the uniform row, and the two
named facts the uniform row's security rests on. The scoping at landing:53
removes the old silent mismatch, since the two Kim programs have two statements
each and no fifth.

Across the three paragraphs the vocabulary holds. "Program" for the Tableau
value, "row" for the manifest row and the analysis path, "starting position"
for the endpoint bound's index everywhere, "completion level" in prose and bare
`level` only inside identifiers, "bias one hundredth" in prose and `centi` only
inside identifiers.

Two names sit close together and are worth one sentence here because a reader
may pause on them. Paragraph one names `five_card_row_biased_leak_bound`, the
statement this file lands, and paragraph two names
`five_card_colour_view_leak_bound`, the theorem in
`instances/kim2025/five_card_models.v:360` that carries the manifest's level.
They are different declarations and both mentions are correct. The declaration
comment at landing:509-512 says the landed one "is
five_card_colour_view_leak_bound with every random variable typed at that law",
which resolves the relation where a reader who cares will look. Adding that to
the header would lengthen it for a reader who does not. No change wanted.

Fix C in place, landing:383-389. The repeated program's comment now says
position twice and seat once, and the one use of seat is the denial, "not about
what any set of seats reads", which is the sentence that must keep the word.

Fix D in place, landing:119-122, sitting between the `modelE` pair at
landing:115-118 and the endpoint gloss at landing:123-125, in the same column
layout as its neighbours.

## 3. Mechanical re-run

All in Python with `\b` word boundaries, this session, on the current file.

- 582 lines. Zero lines over 80 bytes.
- Every non-doc comment line exactly 80 bytes, across all 140 header lines and
  all section banners. Zero deviations.
- The banned-vocabulary scan, whole-word and case-insensitive: 0 hits.
- Phrases that had to disappear, whitespace-normalised: "The two levels are one
  constructor" 0, "is not an error" 0, "one seat's endpoint" 0, the round-1
  rejected mutation name 0, "The row is written" 0, "No statement of the
  program" 0.
- Forbidden vernacular: no `Time`, no `Timeout`, no `Show`, no `Admitted`, no
  `Abort`, no `Axiom`, no `Parameter`, no `Hypothesis`, no `Variable`, no
  `Check`, no `Print Assumptions` command. The one occurrence of that phrase is
  prose inside the comment at landing:578, carried unchanged from
  `instances/kim2025/five_card_rows.v:374`.
- Three `Fail` statements, at landing:409, landing:473 and the pre-existing
  landing:571, none with an expected-failure marker, matching the file's own
  habit.
- Collision scan over 521 `.v` files, every file under `lib`, `protocol`,
  `groups`, `security`, `smc`, `reconstruct`, `instances` and `manifest` plus
  installed infotheo and mathcomp under
  `/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib`: zero hits for
  all eleven landed names and both mutation names.

## 4. New-defect check on the replacements

One heuristic flag, cleared.

`landing:21` fills 54 of the 74-column comment field, because
`pgg_tableau_syntax.v` is twenty characters and does not fit after "The uniform
row is written in the statement surface of". I checked whether a short
mid-paragraph line of that kind is normal in this file family, and it is:
`instances/s5/s5_rows.v:58` is 50 characters, `:42` is 56, `:32` is 59;
`instances/pgl27/pgl27_rows.v:33` is 49, `:37` is 56;
`instances/psl211/psl211_rows.v:52` is 36;
`manifest/pgg_analysis_manifest.v:50` is 17 and `:45` is 52. Every one of them
is a line broken early by a long identifier or a long parenthetical. The
round-2 defect was different in kind: 21 characters at the tail of a spliced
block with the six-character word "places" waiting on the next line and nothing
forcing the break. That is gone and nothing like it was introduced.

No other new defect. I re-read each replaced passage against its neighbours
above and below, and each joins cleanly: landing:20 blank into landing:21,
landing:50 into the blank at landing:51, landing:67 into the blank at
landing:68, landing:118 into landing:119 into landing:123, and landing:382
blank into landing:383 into the Definition at landing:390.

## 5. Fitness to replace the production file

Verified independently, not taken from the fix-pass report.

Diffing `instances/kim2025/five_card_rows.v` against the current landing copy,
29 lines are removed and every one of them is a comment line: the old title
line, the seven lines of the old first-paragraph ending, the eleven lines of
the old second paragraph, and the ten lines of the old third paragraph that
Fix A and Fix B rewrote. Stripping comments from both files leaves 146 code
lines in the production original and 214 in the landing copy, and a line diff
of those two sequences removes nothing: the production file's code is a prefix-
preserving subset of the landing copy's, with 68 lines added and none lost.

`five_card_rows_landing.v` is fit to replace
`instances/kim2025/five_card_rows.v` as it stands, byte for byte, on naming and
style grounds. Every round-1, round-2 and round-3 finding is resolved, the
mechanical checks are clean, no code line of the original is lost, and the
eleven new names collide with nothing in the tree or in the installed
libraries.

One boundary on that sentence, stated so it is not read for more than it is. I
did not compile and am not entitled to a build verdict. The compile evidence is
main's, reported as exit 0 on the landing copy and on `kim_fidelity.v` with ten
three-axiom blocks and one closed context, unchanged across the fix pass, and
as a comments-stripped identity against the before-fix2 copy. My statement of
fitness is a naming-and-style statement resting on that evidence, and the last
edits were comment-only, so it does not need a fourth round to hold.

VERDICT: GO
