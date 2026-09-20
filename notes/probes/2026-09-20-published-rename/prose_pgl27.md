# Layer F, group pgl27: the word "row" in comments

Base c07f6a8, comments only, 17 files, 286 occurrences read one by one.
216 replaced, 191 by "program" and 25 by "path", and 70 left as "row"
because they name a row of a matrix, of a table or of a trace.

## Per file

| file | program | path | unchanged |
|---|---|---|---|
| tableau/pgl27_tableau_analysis_bridged.v | 124 | 24 | 0 |
| tableau/pgl27_tableau_checks.v | 22 | 0 | 0 |
| tableau/pgl27_tableau_observed.v | 7 | 0 | 0 |
| tableau/pgl27_tableau_algebraic.v | 5 | 0 | 0 |
| tableau/pgl27_tableau_sampled.v | 4 | 0 | 0 |
| pgl27_table_bridge.v | 0 | 0 | 27 |
| pgl27_profile_privacy.v | 22 | 0 | 0 |
| pgl27_view_census.v | 0 | 0 | 20 |
| pgl27_models.v | 2 | 0 | 7 |
| pgl27_spectral.v | 1 | 0 | 6 |
| pgl27_encoding.v | 0 | 0 | 3 |
| pgl27_mixing.v | 0 | 0 | 3 |
| pgl27_proximity.v | 3 | 0 | 0 |
| pgl27_analysis.v | 0 | 0 | 2 |
| pgl27_encoding_r5.v | 0 | 1 | 1 |
| pgl27_exec.v | 0 | 0 | 1 |
| pgl27_word_privacy.v | 1 | 0 | 0 |

The analysis-bridged file's 148 occurrences are 124 program and 24 path; the
checker counts 123 program because "row-against-row" is one comment word
holding two occurrences.

## Every unchanged occurrence, with its reason class

Line numbers are the ones of c07f6a8, which for these files is also the
current text, since none of them changed.

- pgl27_table_bridge.v, census table row: 4, 6, 8, 9, 10 (twice), 13, 19,
  24, 25, 26, 27, 44, 45, 53, 57, 62, 81, 82, 89, 90, 106, 120, 121, 132,
  140, 155. Every one of them is a row of the 336-entry census table of
  shuffles, including "336-row table" and the capitalised "Row and shuffle"
  of line 121.
- pgl27_view_census.v, census table row: 138 (twice), 148, 155, 245, 247,
  255, 338, 359, 454, 460, 473, 477, 478, 497, 498, 517, 550, 611, 612.
- pgl27_encoding.v, code table row: 27, 28, 109.
- pgl27_mixing.v, alphabet table row: 349 (a row of the literal alphabet
  table), 781 and 808 (a row of pred_table).
- pgl27_models.v, interpreter trace row: 15, 38, 168, 179, 186, 193, 260.
- pgl27_analysis.v, interpreter trace row: 113, 132.
- pgl27_exec.v, interpreter trace row: 309.
- pgl27_spectral.v, matrix table row: 238 and 253 (a row of
  pgl27_letter_tbl), 393 (a real row vector), 503 and 504 twice (a row of
  the dominating matrix, and "Row dominance").
- pgl27_encoding_r5.v, census table row: 146 ("the census table quotes all
  six rows").

## Occurrences whose sense was hard

1. `pgl27_spectral.v:537`, in the docstring of `pgl27_rayleigh_Q2`: "This is
   the one spectral input of the PGL(2,7) row and the only place the
   certificate tables are used." Six of this file's seven occurrences are
   matrix rows; this one is the analysis it feeds, so it took "program".
2. `pgl27_models.v:430`, docstring of `pgl27_prior_exact_family`: "so a row
   over the word model and a row over this one are read at one index." Seven
   of this file's nine occurrences are interpreter rows; these two are
   Tableau programs, so both took "program".
3. `pgl27_profile_privacy.v`, all 22: "the exact row" and "the all-decks
   row" throughout. The group brief expects a table sense in this file, but
   every occurrence here is an analysis: the objects that have a law, a
   view, a secret and data in the dealer sample space. All took "program".
4. `pgl27_tableau_analysis_bridged.v:929` (now 934), in the proof of
   `pgl27_word_proximity_published_pathE`: "an equation between two rows'
   coordinates". Both sides of that equation are AnalysisPath values, so it
   took "path", where the twin comment at 963 ("Each row stated against the
   named value", "the row-against-row form") is about two published programs
   and took "program".
5. `pgl27_tableau_analysis_bridged.v:84` (now 85): "the payloads, the rows,
   the row and arm equations". The first is the published programs, the
   second is the `_pathE` lemmas, so the line reads "the programs, the path
   and arm equations".

## Sentences I did not repair

Each is listed with the declaration that shows the problem. Line numbers are
those of the current text.

1. `pgl27_tableau_analysis_bridged.v:56` and the banner at 351, over
   `pgl27_exact_published` and `pgl27_word_published`: the banner "The two
   row programs" means the two programs of the two things published. Sense 1
   or 2 gives "The two program programs". I wrote **"The two path programs"**,
   which is true of that section, since its two programs are the ones that
   discharge `pgl27_exact_path` and `pgl27_word_path`, but it is a change of
   referent, not of noun only.
2. Same file, index entries at 102, 103 and 131, for
   `pgl27_exact_published`, `pgl27_word_published` and
   `pgl27_word_proximity_published`: "the exact row as a program", "the word
   row as a program", "the word row as a program at the proximity arm". The
   old text used "row" for the claim and "program" for the Tableau term, so
   the two collapse. I wrote **"the exact path as a program"**, "the word
   path as a program", "the word path as a program at the proximity arm".
3. Same file, 804, docstring of `pgl27_prior_exact_published_pathE`: "so the
   manifest's path for this path is a claim this equation discharges rather
   than a table maintained beside the program." The old "the manifest's row
   for this path" already used the word path in the other sense, and the
   sentence now says path twice for two different things.
4. Same file, 925, docstring of `pgl27_word_proximity_published_pathE`: "The
   proximity program publishes the manifest's path for the word path, as
   pgl27_word_published_pathE says of the word program." Same doubling: "the
   word path" is the name `pgl27_word_path`, and "the manifest's path for"
   it now repeats the noun.
5. Same file, 51 to 53, in the header: "The manifest carries no fourth path
   over this instance and publishes none of the three by a route this
   development's programs do not take." The manifest is the subject of
   "publishes". The sentence is negative, so it asserts no publishing, but
   it is the one place in the group where a manifest and the verb publish
   meet.
6. `pgl27_proximity.v:11`, in the header: "This file holds the mathematics
   that separates the two, with no program and no published program in it."
   The old text said "no program and no published row"; the two nouns now
   coincide, and the sentence repeats itself.
7. `pgl27_proximity.v:42`, in the header: "The certificate itself, the
   program it publishes and the statements about them are in
   instances/pgl27/tableau/". A certificate publishes nothing; a program
   publishes and carries a certificate. The relation reads backwards, and it
   did so before this pass.

Beside the seven, one observation that is not about this word:
`pgl27_word_privacy.v:89` now reads "the number a word program's spectral
arm carries", and the arm it names was renamed to input indistinguishability.
The stale adjective is outside this pass.

## Layout

Paragraphs and index entries that grew past 80 bytes were re-flowed; each
entry keeps its own `==` column and its own continuation column, which is 30
in the tableau files and 5 in pgl27_profile_privacy.v. Hyphen-split words
across a line break, such as "input-" and "indistinguishability", were kept
split, so no comment word was merged. A number and its unit, such as "96.0
s", and "exact: erefl" were kept on one line. Docstrings in the older files
use two spaces after a sentence stop, and the re-flow preserves that.

## Final checker lines

```
SAME  instances/pgl27/pgl27_encoding_r5.v  program 0, path 1, left as row 1
SAME  instances/pgl27/pgl27_models.v  program 2, path 0, left as row 7
SAME  instances/pgl27/pgl27_profile_privacy.v  program 22, path 0, left as row 0
SAME  instances/pgl27/pgl27_proximity.v  program 3, path 0, left as row 0
SAME  instances/pgl27/pgl27_spectral.v  program 1, path 0, left as row 6
SAME  instances/pgl27/pgl27_word_privacy.v  program 1, path 0, left as row 0
SAME  instances/pgl27/tableau/pgl27_tableau_algebraic.v  program 5, path 0, left as row 0
SAME  instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v  program 123, path 24, left as row 0
SAME  instances/pgl27/tableau/pgl27_tableau_checks.v  program 22, path 0, left as row 0
SAME  instances/pgl27/tableau/pgl27_tableau_observed.v  program 7, path 0, left as row 0
SAME  instances/pgl27/tableau/pgl27_tableau_sampled.v  program 4, path 0, left as row 0
```

pgl27_table_bridge.v, pgl27_view_census.v, pgl27_encoding.v,
pgl27_mixing.v, pgl27_analysis.v and pgl27_exec.v print no line: they are
byte-identical to the base. No LONG, BOX, BARRED or OTHER CHANGE was
reported on any file of this group. The run's overall verdict is PROBLEMS,
from a file of another group that was mid-edit at the time.
