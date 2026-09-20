# Plan: a name for `PublishedRow` that a paper can show without explaining "row"

Status: PLAN, not started. Owner's request, 2026-09-20: "PublishedRow is weird
to show in the paper since what is a Row suddenly need explanation. Unlike
others like Sampled and Observed. Need a new name and renaming."

## The problem

A Tableau program is read by a paper's reader as a sequence of phases, and the
phase names explain themselves: `Tableau Algebraic`, `Executable`, `Observed`,
`Sampled`, `AnalysisBridged` are participles or adjectives of what has been
done to the instance so far. The program's last line is `|> publish t a`, and
its type is `PublishedRow`. "Row" is the one word in that signature that is not
about the program. It comes from the manifest, which is a table with one row
per analysis path, and a reader who has not seen the manifest has to be told
what a row is before the type of the simplest program can be read.

What the object is (`manifest/pgg_tableau.v`, record `PublishedRowAt c`): three
fields. `published_at`, the program's data at `AnalysisBridged` (algebra, run
parameters, run facts, model family, security port). `published_row`, the
descriptive record the manifest carries for this path (`AnalysisPathRow`:
observed execution, completion level, model family, transfer status, assumption
status; it holds no `Prop`). `published_thm`, the proof of the proposition the
program accumulated, stated at the bound `c` the program was concluded at.
`PublishedRow` is `PublishedRowAt no_concluded_bound`.

## Candidate names, recommendation first

| # | Type | At a bound | Reads in a paper as | Against it |
|---|---|---|---|---|
| 1 | `Published` | `PublishedAt c` | the terminal `publish` yields a `Published`: the same grammar as the phases (`Sampled`, `Observed`), and no new noun to explain | as a prose noun it needs a head ("a published program"); that head is the word the files already use ("the word row as a program") |
| 2 | `PublishedClaim` | `PublishedClaimAt c` | the owner's own design rule is "one security claim, with its whole chain, per row" | the audits ruled that the value is a program and the claim is its theorem (`published_thm`, the reading statements); the manifest record holds no `Prop`, so "claim" cannot be the word for it as well |
| 3 | `PublishedProgram` | `PublishedProgramAt c` | explicit | long; "program" already names every `Tableau l` value, finished or not |

Recommendation: candidate 1. It removes the noun instead of replacing it, which
is what makes the phase names readable, and it fits the naming scheme the
`tableau/` directories already use for named values, `<inst>_<model>_<phase>`
(`pgl27_word_sampled`): a finished program becomes `<inst>_<model>_published`.

## What else carries "row", and how far the rename goes

Counted in production on 2026-09-20 (identifiers about matrix rows, such as
`ad_row` and `row_mx`, are unrelated and excluded).

| Layer | Identifiers | Occurrences | Proposed |
|---|---|---|---|
| A. The type the paper shows | `PublishedRowAt`, `PublishedRow`, `MkPublishedRow` | 36 | `PublishedAt`, `Published`, `MkPublished` |
| B. Its projections | `published_at`, `published_row`, `published_thm` | 25 | `published_row` -> `published_path`; the other two stay |
| C. The manifest's record | `AnalysisPathRow`, `MkAnalysisPathRow`, `apr_*` | 67 | `AnalysisPath`, `MkAnalysisPath`, `ap_*`: a path from an observed execution through a model to a level, with its two statuses |
| D. The equations between a program's record and the manifest's | `*_rowE` (about 25 lemmas) | 53 | `*_pathE` |
| E. Instance values | programs `<inst>_row_<model>_tableau`, concluded ones `<inst>_row_<model>39`, manifest records `<inst>_row_<model>` (about 60 names) | 509 | programs `<inst>_<model>_published` and `<inst>_<model>_published39`; manifest records `<inst>_<model>_path` |
| F. Prose | the word "row" in comments of 26 files | 868 | "published program" for the value, "path" for the manifest record, "the manifest's table" where the table itself is meant |

Three depths, each a complete and consistent stopping point:

1. Depth 1, layers A and B: what a paper's code listing shows. About two hours
   with verification. Leaves instance names and prose saying "row" for a type
   that no longer does.
2. Depth 2, layers A to D: the framework and the manifest say "path"
   throughout. About half a day. Instance values still carry `_row_`.
3. Depth 3, all six layers. One word per concept everywhere. About two days:
   layers A to E are one mechanical pass of about 690 occurrences (token
   identity under the map, as the earlier renames); layer F is 868 prose
   sentences, which is where this campaign's audits found nearly all their
   defects, so it is done file by file with an audit, not by substitution.

Recommendation: depth 3, in two commits. First A to E, mechanically. Then F,
as a comment pass with its own audit. The owner's banned-vocabulary rule asks
that a term be changed at every carrier at once, and a paper that shows
`Published` beside a lemma named `pgl27_row_word_rowE` has not removed the
question it set out to remove.

## Constraints and procedure

- No file in the forward closure of `instances/psl211/psl211_endpoints.v` holds
  any of these names (to be confirmed by scan before starting); that file is
  never compiled and `make` is never run.
- The manifest sits below the framework and all twenty-four phase files, so the
  whole Tableau chain is recompiled once per commit (about forty-five files,
  five minutes).
- The paper sources cite none of these names today (scan of 2026-09-20), so no
  `.tex` line changes; a dated list of old and new names is written for the
  owner as before.
- Verification as the earlier renames: comment-stripped tokens identical under
  the map; a comment word-diff listing every difference; every recorded `Fail`
  whose subject is renamed re-checked without `Fail` in its own file's
  preamble; `Print Assumptions` unchanged; one Opus audit of the prose.
- Order: after the `Reprice` rename and the pass that replaces the economic
  words, because all three edit the same files.

## Decisions the owner has to make

1. The name: `Published` (recommended), `PublishedClaim`, `PublishedProgram`,
   or another word.
2. The manifest record: `AnalysisPath` (recommended) or keep `AnalysisPathRow`.
3. The depth: 3 (recommended), 2 or 1.
