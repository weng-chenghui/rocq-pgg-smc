# Frozen files: the word "row" in comments, senses 1 to 3 (group psl_s5_rest)

Read-only survey of the six frozen files this group was asked to classify.
Nothing in these files was edited. Senses are those of `prose_sheet.md`:
1 program, 2 finished program, 3 manifest path, 4 unchanged.

## Totals by file

| File | occurrences | sense 4 | senses 1 to 3 |
|---|---|---|---|
| instances/psl211/psl211_blocks.v | 16 | 16 | 0 |
| instances/psl211/psl211_closure.v | 8 | 8 | 0 |
| instances/psl211/psl211_exec.v | 2 | 0 | 2 |
| instances/psl211/psl211_orbit.v | 29 | 29 | 0 |
| protocol/pgg_execution_plug.v | 9 | 9 | 0 |
| protocol/pgg_observed_execution.v | 8 | 8 | 0 |
| total | 72 | 70 | 2 |

## The occurrences in senses 1 to 3, for the owner

Two, both in `instances/psl211/psl211_exec.v`, both in the one docstring of
`profile_k_psl211_algebra` (lines 126 to 131):

instances/psl211/psl211_exec.v:127 — sense 1 (a Tableau program).
Sentence: "profile_k_psl211_algebra — the privacy threshold the derived
profile declares is six, so every arm of a row over this algebra quantifies
over coalitions of at most five of the twelve seats."
Declaration: `Lemma profile_k_psl211_algebra : profile_k (instance_profile
psl211_algebra) = 6.`
Why sense 1: what carries an arm and quantifies over a coalition is a value of
`Tableau l`, not a record of the manifest and not a row of a table. The same
sentence shape sits in the two analysis-bridged headers of this group, where it
was changed to "a program says something about a coalition".
Proposed word: program ("every arm of a program over this algebra").

instances/psl211/psl211_exec.v:129 — sense 1 or 2 (the two programs of the
instance).
Sentence: "It is profile_k_psl211 read at the derived profile. The rows'
witness converts the framework's threshold hypothesis to the numeric bound
directly, and this lemma records the number that conversion relies on."
Declaration: same lemma.
Why sense 1 or 2: the witness meant is the exact witness
`psl211_exact_witness`, which the published programs of
`instances/psl211/tableau/psl211_tableau_analysis_bridged.v` carry; a manifest
path holds no witness.
Proposed word: programs ("The programs' witness converts ...").

Layout note for whoever applies these: the docstring is a plain four-space
continuation block; "program" is four bytes longer than "row" and both lines
are at 78 and 79 bytes, so the paragraph (126 to 131) has to be re-flowed.

## The sense-4 occurrences, by reason class

instances/psl211/psl211_blocks.v (16): block-table rows. The two Steiner
tables of 132 ascending six-lists and the operations on one such list
(lines 9, 338, 339, 345, 407, 421, 425 twice, 449 four times, 459, 462, 502,
505).

instances/psl211/psl211_closure.v (8): alphabet-table rows and the 660-state
enumeration (lines 13, 46, 104, 109, 166, 339, 393, 402).

instances/psl211/psl211_orbit.v (29): block-table rows, chiefly "the
representative row" of a Steiner system (lines 28, 45, 64, 100, 132, 142, 151,
162, 172, 173, 190, 305 twice, 393, 404, 405 twice, 407, 412, 427, 856, 915,
994, 1139, 1161, 1165 twice, 1214, 1232).

protocol/pgg_execution_plug.v (9): interpreter-trace rows, the message log a
process identifier indexes (lines 183, 189, 196, 205, 213 twice, 221 twice,
231).

protocol/pgg_observed_execution.v (8): interpreter-trace rows, the same
extractors specialised to the package (lines 18, 20 twice, 234, 238 twice,
262, 279).
