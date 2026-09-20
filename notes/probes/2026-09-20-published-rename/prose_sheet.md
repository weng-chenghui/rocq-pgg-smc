# Prose sheet for layer F: the word "row" in comments

Owner's decision (2026-09-20): a paper shows `Published`, and "what is a Row"
must not need an explanation. The identifiers no longer carry the word (layers
A to E). This sheet fixes what the comments say instead. One word per concept,
file-wide and tree-wide.

## The four senses, and the word each gets

| # | What the old "row" meant there | How to tell | New word |
|---|---|---|---|
| 1 | A Tableau program, at any level: a value of `Tableau l`, or the thing a statement (`commit`, `execute`, `observe`, `sample`, `certify`, `conclude`) extends | the sentence speaks of lines, statements, levels, arms, certificates, witnesses, what is accumulated, "raising a row to Executable", "the first line of every row", "a row commits to one arm" | **program** |
| 2 | A finished program: a value of `Published` or `PublishedAt c`, what `publish` returns | "published row", "the finished row", "the row publishes 2^-39", a named value `<inst>_<model>_published` | **program**; "published row" becomes "published program". No word is added where the old text had none: `check_prose.py` compares the comment words position by position |
| 3 | The manifest's record for one analysis path: a value of `AnalysisPath`, or its prose entry in the header of `manifest/pgg_analysis_manifest.v` | "manifest row", "typed row", "Row 7", "this row declares an observer", "the row stores no theorem", the five coordinates (observed execution, completion level, model family, transfer status, assumption status) | **path** ("the manifest's path", "analysis path", "typed path", "Path 7", "this path declares") |
| 4 | A row of a matrix, of a table of decks or codes, of a trace or of the interpreter's output ("the dealer's executed row", "row sums", "row stochastic", "the representative row of", `ad_row`) | the mathematics of the file | **unchanged** |

The manifest as a whole, where the old text said "the table" or "a column":
"the manifest" and "a coordinate of a path". No sentence may say what an outside
document's table prints.

## Composite phrases

| Old | New |
|---|---|
| the exact row, the word row, the proximity row, the repeated row, the uniform row (sense 1 or 2) | the exact program, the word program, the proximity program, the repeated program, the uniform program. Keep the referent and change only the noun: "the repeated row's cut law" becomes "the repeated program's cut law", never "the repeated-cut model's cut law" |
| the word row concluded at 2^-39 | the word program concluded at 2^-39 |
| the two rows over this model | the two programs over this model |
| the manifest's word row, the manifest row | the manifest's word path, the manifest's path |
| the descriptive row (the `published_path` field) | the descriptive path |
| row equation (the `_pathE` lemma) | path equation |
| Row 10, Row 11, eleven typed rows | Path 10, Path 11, eleven typed paths |
| `| typed row            | x_path |` (box table of the manifest header) | `| typed path           | x_path |`, column widths kept |
| a row over any cut law | a program over any cut law |
| the rows file, `*_rows.v` (a retired file's name) | leave: it is a file name in a record of where things were |

## Rules of the pass

1. Meaning is preserved exactly. Only the noun changes ("a row" -> "a
   program", "its row" -> "its path", "rows" -> "paths", "Row 7" -> "Path 7");
   the number of words of every comment stays the same, which
   `check_prose.py` verifies position by position.
   Nothing else in a sentence is improved, shortened or corrected. A sentence
   that is FALSE or ambiguous once the right noun is in place is not repaired
   silently: it is listed in the report with the declaration that shows it.
2. Decide the sense of EVERY occurrence by reading the declaration or header
   paragraph it sits in. Where one sentence uses the word in two senses ("the
   row publishes the manifest's row"), each gets its own word ("the program
   publishes the manifest's path").
3. A manifest path holds no `Prop` and publishes nothing; a program publishes.
   A model is not a program. If choosing the noun exposes such a confusion,
   report it (rule 1).
4. Frozen files (the forward closure of `instances/psl211/psl211_endpoints.v`)
   are not edited; their occurrences in senses 1 to 3 are listed for the owner.
5. Layout as always: at most 80 bytes; boxed lines stay 80 bytes with a space
   before the closing delimiter; re-flow the paragraph, no orphan short line;
   no name touches `==`; banners stay one content line.
6. Never in new text: the project's barred vocabulary, tokens made of a capital
   L and a digit, an abbreviation of "indistinguishability", history words,
   metaphor words.
