# Layer F prose pass, group psl_s5_rest

Comments only, branch feat/tableau-extensions-probe, base c07f6a8. 31 files
held 236 comment occurrences of the word. 140 were changed (110 to "program",
30 to "path") in 18 files; 96 were left as they stood in 13 wholly unchanged
files and in four files where only part of the occurrences are in senses 1
to 3. Nothing was compiled and no git command that writes was run.

## Per file

Counts are (program, path, unchanged). Line numbers are those of the base
commit c07f6a8, because the re-flow moved lines in the edited files.

### Edited files

| File | program | path | unchanged |
|---|---|---|---|
| instances/psl211/tableau/psl211_tableau_analysis_bridged.v | 40 | 13 | 0 |
| instances/psl211/tableau/psl211_tableau_observed.v | 6 | 0 | 0 |
| instances/psl211/tableau/psl211_tableau_algebraic.v | 4 | 0 | 0 |
| instances/psl211/tableau/psl211_tableau_checks.v | 4 | 0 | 0 |
| instances/psl211/tableau/psl211_tableau_sampled.v | 4 | 0 | 0 |
| instances/psl211/tableau/psl211_tableau_executable.v | 1 | 2 | 0 |
| instances/psl211/psl211_reading_constancy.v | 16 | 0 | 2 |
| instances/psl211/psl211_analysis.v | 1 | 1 | 4 |
| instances/psl211/psl211_word_model.v | 3 | 0 | 0 |
| instances/psl211/psl211_word_proximity.v | 3 | 0 | 0 |
| instances/s5/tableau/s5_tableau_analysis_bridged.v | 18 | 8 | 0 |
| instances/s5/tableau/s5_tableau_observed.v | 2 | 5 | 0 |
| instances/s5/tableau/s5_tableau_algebraic.v | 3 | 0 | 0 |
| instances/s5/tableau/s5_tableau_sampled.v | 1 | 1 | 0 |
| instances/s5/tableau/s5_tableau_executable.v | 1 | 0 | 0 |
| instances/s5/s5_exec.v | 1 | 0 | 7 |
| instances/s5/s5_mixing.v | 0 | 1 | 7 |
| protocol/pgg_functionality.v | 1 | 0 | 0 |

### Files left untouched, every occurrence in sense 4

| File | unchanged | reason class | lines |
|---|---|---|---|
| instances/psl211/psl211_alldecks.v | 22 | block-table row | 35, 51, 102, 116, 204, 211, 214, 215, 224, 233, 234 (2), 265, 485, 494, 727, 800, 813, 840 (2), 943, 1346 |
| instances/psl211/psl211_models.v | 14 | interpreter-trace row (13), block-table row (574) | 36, 61, 62, 93, 369, 370, 376, 389, 396, 398, 418, 434, 435, 574 |
| instances/psl211/psl211_recovery.v | 3 | block-table row | 122, 123, 151 |
| instances/psl211/psl211_mixing.v | 2 | predecessor-table row | 268, 296 |
| instances/psl211/psl211_secrecy.v | 1 | block-table row | 210 |
| reconstruct/s5_nogo.v | 7 | matrix row vector | 52, 66, 72, 84, 85, 86, 304 |
| reconstruct/invariant_profiler.v | 2 | matrix row space | 14, 55 |
| security/pgg_mixing.v | 8 | matrix row sum | 222, 348, 592, 741, 760, 886, 888, 932 |
| security/pgg_schreier_weighted.v | 5 | matrix row sum | 15, 85 (2), 379, 440 |
| security/pgg_schreier.v | 4 | matrix row sum | 43, 46, 190 (2) |
| security/pgg_weighted_words.v | 3 | matrix row vector | 7, 56, 59 |
| security/pgg_canonical_sharing.v | 1 | matrix row vector | 4 |
| groups/pgg_raag_clique.v | 4 | result-table row | 1090, 1099, 1111, 1125 |

### Unchanged occurrences inside edited files

| File | lines | reason class |
|---|---|---|
| instances/psl211/psl211_reading_constancy.v | 375, 811 | block-table row |
| instances/psl211/psl211_analysis.v | 112, 124, 125, 215 | interpreter-trace row |
| instances/s5/s5_exec.v | 86 (2), 475, 476, 477, 486, 487 | interpreter-trace row |
| instances/s5/s5_mixing.v | 29, 81, 143, 296, 382, 383 (2) | matrix row sum |

## Occurrences whose sense was hard, and the choice made

1. "the all-decks row as a program", "the word row as a program, published at
   2^-40", "the randomized row as a program".
   psl211_tableau_analysis_bridged.v:56 and :60, s5_tableau_analysis_bridged.v:47.
   Declarations: `psl211_alldecks_published`, `psl211_word_proximity_published`,
   `s5_rand_published`.
   Choice: **path**, against the composite table, which maps "the word row" to
   "the word program" when that phrase is in sense 1 or 2. The idiom is defined
   at `manifest/pgg_tableau.v:6`, "A row of the analysis manifest is written
   here as a program", so the noun before "as a program" names the manifest's
   entry and the whole phrase says the entry is written as a program. Reading
   it as sense 2 gives "the all-decks program as a program". The same idiom
   sits in the three other groups (pgl27 and five-card analysis-bridged,
   s5_tableau_executable.v's "the run's parameters as a program"), so the
   choice has to be settled tree-wide, not per group.

2. Banner "The row program", psl211_tableau_analysis_bridged.v:164, heading
   `psl211_alldecks_published`.
   Choice: **path**, giving "The path program". Sense 2 gives "The program
   program". The sibling banner at :334 heading
   `psl211_word_proximity_published` is plainly sense 2 and became "The
   program".

3. "This is the one spectral input of the S_5 row", s5_mixing.v:419,
   docstring of `s5_rayleigh_Q2_R`.
   Choice: **path**. The S_5 word analysis carries no program:
   s5_tableau_sampled.v:21 states that the manifest's entry `s5_word_path` "is
   published from a mixing theorem rather than from a program". What this
   spectral bound feeds is therefore the manifest's record.

4. "puts functional_extensionality_dep and propositional_extensionality into
   the row's assumption list", pgg_functionality.v:142, comment above
   `realises_expected`.
   Choice: **program**. What `Print Assumptions` reports is a term's dependency
   list, and rule 3 gives a manifest path no `Prop`.

5. "The three obligations below carry the mode word and the plug, the family
   and the row keep the instance's own word", s5_exec.v:903, the naming comment
   above the supplied-mode obligations.
   Choice: **program**. The pair meant is `s5_rand_family` and
   `s5_rand_published`.

6. "Its last line publishes a row whose transfer status is
   StaticExecutedOnly", psl211_tableau_analysis_bridged.v:173, and "Its last
   statement publishes a row whose transfer status is StaticExecutedOnly",
   s5_tableau_analysis_bridged.v:165.
   Choice: **path**. The transfer status is one of the five coordinates of the
   manifest's record, and `published_path` names the object of "publishes".
   The same reading was applied to "the row this program publishes"
   (:182, :178) and to "the program publishes the manifest's row" (:64, :58).

7. "the all-decks row comparing no idealized model where this one replaces an
   idealized shuffle by a finite word", psl211_tableau_analysis_bridged.v:379,
   docstring of `psl211_word_proximity_published_pathE`.
   Choice: **path**. The sentence contrasts `psl211_word_path` with
   `psl211_alldecks_path` in the transfer-status coordinate, so the referent
   named two clauses earlier is the second record.

8. The group guidance says a sentence in psl211_models.v is about the
   manifest's record. There is none. That file mentions the manifest once, at
   line 43 ("imports nothing from the manifest layer"), and that sentence holds
   no occurrence of the word. All 14 occurrences there are interpreter-trace or
   block-table rows and the file is untouched.

## Sentences that were not repaired

The noun change made was the one-for-one change least wrong; the sentence was
left as it fell out.

1. psl211_tableau_analysis_bridged.v, docstring of
   `psl211_word_proximity_published_pathE`: "The manifest writes those
   coordinates in the facade's vocabulary and the program in this file's, and
   conversion decides the equation, so the manifest's path for this path is a
   claim this equation discharges rather than a table maintained beside the
   program." The word now carries two referents one clause apart: the
   manifest's record, and the analysis path that record is for. "this path" is
   pre-existing at c07f6a8 and is not one of the changed words.

2. s5_tableau_observed.v, docstring of `s5_dealt_path_observedE`: "The observed
   execution this program reaches is the one the manifest's deterministic path
   describes. Conversion decides it, so the path's description of the run and
   the proof of run correctness for it are one term, which is the whole of what
   this path publishes." The last clause says a manifest path publishes, which
   rule 3 refuses. "this path" is pre-existing at c07f6a8; the change puts two
   further occurrences of the word beside it.

3. s5_tableau_sampled.v:21, file header: "the manifest's path over it,
   s5_word_path, is published from a mixing theorem rather than from a
   program". Under rule 3 a program is what publishes, so a path published from
   a theorem and expressly not from a program states the opposite. The
   substance is true of this instance: no program of it continues from the word
   model.

4. psl211_tableau_analysis_bridged.v:56 and :60,
   s5_tableau_analysis_bridged.v:47, and the banner at :164: reported as hard
   cases 1 and 2. Under the composite table's letter they would read "the
   all-decks program as a program", "the word program as a program", "the
   randomized program as a program" and "The program program".

## Final checker lines

`python3 notes/probes/2026-09-20-published-rename/check_prose.py c07f6a8`

```
SAME  instances/psl211/psl211_analysis.v  program 1, path 1, left as row 4
SAME  instances/psl211/psl211_reading_constancy.v  program 16, path 0, left as row 2
SAME  instances/psl211/psl211_word_model.v  program 3, path 0, left as row 0
SAME  instances/psl211/psl211_word_proximity.v  program 3, path 0, left as row 0
SAME  instances/psl211/tableau/psl211_tableau_algebraic.v  program 4, path 0, left as row 0
SAME  instances/psl211/tableau/psl211_tableau_analysis_bridged.v  program 40, path 13, left as row 0
SAME  instances/psl211/tableau/psl211_tableau_checks.v  program 4, path 0, left as row 0
SAME  instances/psl211/tableau/psl211_tableau_executable.v  program 1, path 2, left as row 0
SAME  instances/psl211/tableau/psl211_tableau_observed.v  program 6, path 0, left as row 0
SAME  instances/psl211/tableau/psl211_tableau_sampled.v  program 4, path 0, left as row 0
SAME  instances/s5/s5_exec.v  program 1, path 0, left as row 7
SAME  instances/s5/s5_mixing.v  program 0, path 1, left as row 7
SAME  instances/s5/tableau/s5_tableau_algebraic.v  program 3, path 0, left as row 0
SAME  instances/s5/tableau/s5_tableau_analysis_bridged.v  program 18, path 8, left as row 0
SAME  instances/s5/tableau/s5_tableau_executable.v  program 1, path 0, left as row 0
SAME  instances/s5/tableau/s5_tableau_observed.v  program 2, path 5, left as row 0
SAME  instances/s5/tableau/s5_tableau_sampled.v  program 1, path 1, left as row 0
SAME  protocol/pgg_functionality.v  program 1, path 0, left as row 0
```

No LONG, BOX, BARRED or OTHER CHANGE line names a file of this group, and no
FROZEN FILE CHANGED line was printed. The thirteen files with no change at all
do not appear, the checker listing only files that differ from the base.

## Frozen files

The read-only survey is in
`notes/probes/2026-09-20-published-rename/frozen_prose_occurrences.md`. Of the
72 occurrences in the six frozen files, 70 are sense 4 and two are in sense 1,
both in the one docstring of `profile_k_psl211_algebra` at
instances/psl211/psl211_exec.v:127 and :129.
