# Layer F, group kim: the word "row" in comments of the five-card instance

Base commit c07f6a8. Comments only, 18 files, 329 comment occurrences read one
by one. 215 became "program", 50 became "path", 64 stay.

## Per file

| file | program | path | unchanged |
|---|---|---|---|
| instances/kim2025/tableau/five_card_tableau_analysis_bridged.v | 153 | 23 | 3 |
| instances/kim2025/tableau/five_card_tableau_sampled.v | 14 | 15 | 0 |
| instances/kim2025/tableau/five_card_tableau_checks.v | 16 | 8 | 0 |
| instances/kim2025/tableau/five_card_tableau_observed.v | 7 | 0 | 0 |
| instances/kim2025/tableau/five_card_tableau_algebraic.v | 5 | 0 | 0 |
| instances/kim2025/tableau/five_card_tableau_executable.v | 2 | 0 | 0 |
| instances/kim2025/five_card_exec.v | 0 | 0 | 29 |
| instances/kim2025/five_card_mixing.v | 14 | 4 | 2 |
| instances/kim2025/five_card_kim.v | 0 | 0 | 4 |
| instances/kim2025/five_card_analysis.v | 2 | 0 | 1 |
| instances/kim2025/five_card_proximity.v | 2 | 0 | 0 |
| instances/kim2025/kim_input_privacy.v | 0 | 0 | 2 |
| instances/kim2025/five_card_family.v | 0 | 0 | 1 |
| instances/kim2025/five_card_models.v | 0 | 0 | 1 |
| instances/denboer1989/five_card_leakage.v | 0 | 0 | 7 |
| instances/denboer1989/five_card_program.v | 0 | 0 | 5 |
| instances/denboer1989/five_card_scheme_I5.v | 0 | 0 | 5 |
| instances/denboer1989/den_boer_encoding.v | 0 | 0 | 4 |

Nine files are therefore untouched: five_card_exec.v, five_card_kim.v,
kim_input_privacy.v, five_card_family.v, five_card_models.v and the four
denboer1989 files.

## Every unchanged occurrence, with its reason class

Line numbers are the base-commit ones for untouched files, the current ones for
the three in five_card_tableau_analysis_bridged.v.

five_card_tableau_analysis_bridged.v (3), all "dealt colour row":
392 (the leakage space's cut row), 395 (the rotated colour row at i), 428 (one
revealed colour of the cut row).

five_card_exec.v (29), all "interpreter trace row": 48, 52, 53, 111, 114, 116
(the header's gloss list), 767 and 822 (banners), 770, 775, 776 twice, 777,
778, 791, 801, 802, 805, 806, 833, 834, 849 twice, 851, 854, 861, 871, 881,
893.

five_card_mixing.v (2), "dealt card row": 12, 236.

five_card_kim.v (4), "stochastic matrix row": 27, 259, 294, 299.

five_card_analysis.v (1), "interpreter trace row": 317.

kim_input_privacy.v (2), "dealt card row": 5, 712.

five_card_family.v (1), "decoded card row": 69.

five_card_models.v (1), "condition table row": 73.

denboer1989/five_card_leakage.v (7): 7, 12, 65, 882, 956, 957 "dealt card
row"; 1048 "row position index".

denboer1989/five_card_program.v (5), "dealt card row": 13, 63, 68, 79, 89.

denboer1989/five_card_scheme_I5.v (5): 56, 157 "share value row"; 209 "decoded
share row"; 225, 229 "dealt card row".

denboer1989/den_boer_encoding.v (4): 113, 115, 221 "dealt card row"; 354 "row
position index".

## Occurrences whose sense was hard

1. five_card_tableau_analysis_bridged.v, header, "Seven programs are
   published, and the three the manifest carries for this instance are among
   them ... Of the three, the repeated path is the one whose route the
   programs here share ... For the one-cut path the manifest names two
   theorems reaching that level ... For the uniform path the manifest names
   five_card_exec_trace_secrecy at that path's own content trace".
   The first sentence counts published programs; the following ones say what
   the manifest records, which the sheet puts at sense 3, so the four
   occurrences at "Of the three", "For the one-cut", "For the uniform" and
   "that row's own content trace" became "path". A reader could instead take
   all of them as the three published programs.

2. The recurring phrase "the repeated row's certified program" and "the
   one-cut row's certified program" (five_card_tableau_analysis_bridged.v at
   the four statements _pathE, _armE and the two _path_fieldsE, and
   five_card_tableau_checks.v at the refused path equation). The possessor is
   neither the certified value itself nor clearly the manifest's record. The
   sheet's composite table fixes "the repeated row" as "the repeated
   program", so I took the possessor as the program. The result reads "the
   repeated program's certified program", which is listed below.

3. five_card_tableau_checks.v, "the uniform row holds the uniform family at
   StaticExecutedOnly, so the two rows differ in two of their five fields".
   Chosen: "the uniform path" and "the two paths". The verb is "holds" and
   the five fields are the coordinates of an AnalysisPath, and the refused
   definition compares published_path of the repeated certified program with
   five_card_uniform_path. The header sentence at line 18 of the same file
   was resolved the same way.

4. five_card_analysis.v, "Section 7 carries the base premises Kim's one-cut
   and seven-cut rows rest on": chosen "programs", because the premises are
   the fields of the two certificates. The same pair of words in
   five_card_mixing.v at line 17, "the certificates the analysis manifest
   records for Kim's one-cut and seven-cut rows", became "paths", because
   there the subject is what the manifest records.

5. five_card_mixing.v, "the distance is where the two rows' published numbers
   come from" and "the exact one fiftieth its row publishes": chosen
   "programs" and "program", since a manifest path publishes no number.

6. five_card_tableau_sampled.v, "five_card_repeated_indistinguishability_-
   published is the certified program for the same row" and the two sentences
   "one level under the AnalysisBridged the manifest records for this row":
   chosen "path" throughout, matching the same file's later sentence "the
   biased path also carries a program that does reach AnalysisBridged".

7. five_card_tableau_sampled.v, "they carry the published-row suffix although
   both are Tableau Sampled values and neither is a published row": chosen
   "published-program suffix", although the suffix the two names actually
   carry is _published.

## Sentences I may not repair

Each was given the one-for-one noun that is least wrong; none was reworded.

1. five_card_tableau_analysis_bridged.v, header (now line 86): "A published
    program is a program, and an AnalysisPath holds descriptive metadata and
    no Prop, so two programs publishing one AnalysisPath say nothing about
    each other's claim." The first clause is now a tautology; it used to
    carry the definition the rest of the sentence rests on.

2. Same file, four gloss lines of the Definitions block, on
    five_card_uniform_published, five_card_repeated_indistinguishability_-
    published, five_card_biased_indistinguishability_published and
    five_card_biased_proximity_published: "== the uniform program as a
    program", "== the repeated program as a program at the input-
    indistinguishability arm", "== the one-cut program as a program at that
    same arm", "== the one-cut program as a program at the proximity arm,
    published at one fiftieth". Each says a program is a program.

3. Same file, statement five_card_repeated_indistinguishability_published_-
    pathE: "The repeated program's certified program publishes the
    manifest's path for that path." Two words for the same concept in one
    possessive, and "the manifest's path for that path" repeats itself.
    The sibling statements _armE and _path_fieldsE, and the one-cut twins,
    carry the first half of the same problem.

4. Same file, statement five_card_biased_proximity_published_pathE: "An
    AnalysisPath holds descriptive metadata and no Prop, so one manifest path
    carrying an input-indistinguishability program and a proximity program
    says nothing about either claim." A path carries no program; two programs
    publish one path.

5. five_card_tableau_sampled.v, header: "Each of the two paths also carries a
    certified program that does reach AnalysisBridged". Same shape as the
    previous item. The file's own statement five_card_biased_path_levelE
    already said "the biased path also carries a program", so the wording
    predates this pass.

6. five_card_tableau_checks.v, header: "The third is a path equation written
    for another path, the repeated certified program against the uniform
    path, which differ in two of their five fields." The two things said to
    differ are named at two different senses, and only the second one has
    five fields.

7. Same file, before the refused definition
    five_card_repeated_indistinguishability_published_uniform_pathE: "The
    repeated program's certified program publishes the seven-cut model at
    IdealFinite and the uniform path holds the uniform family at
    StaticExecutedOnly, so the two paths differ in two of their five fields."
    Same mixture, plus item 3's possessive.

8. five_card_proximity.v, header: "This file holds the mathematics that
    separates the two, with no program and no published program in it." The
    two conjuncts were a Tableau value and a Published value; they now read
    as one thing said twice.

9. Same file, header: "The certificate itself, the program it publishes and
    the statements about them are in instances/kim2025/tableau/." A
    certificate publishes nothing. The artefact meant is the published
    program, which is indeed in that directory, so "program" was chosen over
    "path".

10. five_card_mixing.v, header: "The manifest sits below the file that
    certifies those paths". A path is not certified; the program that
    publishes it is.

## Layout note

Three gloss lines of the Definitions and Key results blocks of
five_card_tableau_analysis_bridged.v held a word hyphen-split across two
lines, "input-" then "indistinguishability", and "thirty-" then "ninth". The
four extra bytes of "program" push the break, and no wrapping keeps the hyphen
at a line end without leaving a six-byte line on its own, so the split now sits
inside a line: lines 156, 228 and 251. The two halves are separate words in the
comment either way, so the word-by-word check passes; the owner may want the
sentences rewritten instead.

## Checker

`python3 notes/probes/2026-09-20-published-rename/check_prose.py c07f6a8`, the
lines of this group's files:

```
SAME  instances/kim2025/five_card_analysis.v  program 2, path 0, left as row 1
SAME  instances/kim2025/five_card_mixing.v  program 14, path 4, left as row 2
SAME  instances/kim2025/five_card_proximity.v  program 2, path 0, left as row 0
SAME  instances/kim2025/tableau/five_card_tableau_algebraic.v  program 5, path 0, left as row 0
SAME  instances/kim2025/tableau/five_card_tableau_analysis_bridged.v  program 153, path 23, left as row 3
SAME  instances/kim2025/tableau/five_card_tableau_checks.v  program 16, path 8, left as row 0
SAME  instances/kim2025/tableau/five_card_tableau_executable.v  program 2, path 0, left as row 0
SAME  instances/kim2025/tableau/five_card_tableau_observed.v  program 7, path 0, left as row 0
SAME  instances/kim2025/tableau/five_card_tableau_sampled.v  program 14, path 15, left as row 0
```

No LONG, BOX, BARRED or OTHER CHANGE line names a file of this group. The nine
files with no replacement do not appear, because they were not changed. The run
that produced these lines ended in ALL OK for the whole tree.
