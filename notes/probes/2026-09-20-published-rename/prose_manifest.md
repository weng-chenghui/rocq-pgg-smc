# Layer F prose pass, group "manifest"

Six files, 252 comment occurrences of the noun, all decided. Comments only; no
code token, no file outside the group, no compilation, no git write.

## Counts per file

| file | program | path | unchanged | total |
|---|---|---|---|---|
| manifest/pgg_analysis_manifest.v | 6 | 110 | 2 | 118 |
| manifest/pgg_tableau.v | 91 | 10 | 0 | 101 |
| manifest/pgg_tableau_syntax.v | 21 | 0 | 0 | 21 |
| manifest/pgg_analysis_status.v | 0 | 7 | 0 | 7 |
| manifest/pgg_analysis_client.v | 0 | 3 | 0 | 3 |
| manifest/pgg_tableau_arm_relations.v | 2 | 0 | 0 | 2 |

## The unchanged occurrences

Both sit in the level justification of Path 3 of the manifest header.

| file:line | text | reason class |
|---|---|---|
| pgg_analysis_manifest.v:282 | "the content of the executed seat row at exactly that argument and that cut" | executed trace row |
| pgg_analysis_manifest.v:288 | "the input rows of the executed trace are empty" | executed trace rows |

Not an occurrence, recorded for the owner: `pgg_analysis_manifest.v:2235`
binds the code variable `row` in
`Timeout 60 Check (fun (row : AnalysisPath) ...`, used again at 2236 and 2239.
A comments-only pass cannot touch it and `check_prose.py` requires the code
tokens to stay identical, so the identifier layers left this one behind.

## Occurrences whose sense was hard

### pgg_analysis_manifest.v

1. **Line 9, file header.** "records one row per analysis path" -> **path**.
   The record is the analysis path, so the sentence becomes circular. Listed
   again below.
2. **Line 728, the "bound or certificate" cell of Path 10.** "none: this row is
   published through the exact arm, whose witness carries independence and no
   number" -> **program**. A path publishes nothing (sheet rule 3), so the cell
   of a path's table now speaks of the program published over it. The
   alternative, "this path is published", is the confusion rule 3 forbids.
3. **Line 821, the "missing premise" cell of Path 11.** "none: the row's
   certificate carries its own distance field" -> **program**, the brief's own
   reading: a certificate is carried by the published program.
4. **Line 850, level justification of Path 11.** "so a distinguisher's advantage
   against this row is at most 2^-41" -> **program**, same reading.
5. **Line 852, same paragraph, two senses in one sentence.** "the model of Row 9
   is the ideal this row's certificate is measured against" -> **Path 9** for the
   numbered entry and **this program's certificate** for the carrier of the
   certificate.
6. **Lines 446 and 1027 (the second in the docstring of
   `five_card_repeated_path`).** "endpoint_bound and deal_centi_lt stay in the
   row" -> **path**. Two named theorems are said to stay in a record that stores
   no theorem. What stays is their line in the path's prose table, so "path" is
   the least wrong; listed below.
7. **Line 892, "Absent capabilities".** "No row is filled with a dummy theorem,
   an option-valued proof, an axiom or a placeholder" -> **path**, in the same
   tension with rule 3; the subject is the manifest's entries.
8. **Line 496, level justification of Path 6.** "Print Assumptions on the row
   reports s5_group_order_eq" -> **path**. The command runs on a term; the typed
   value is a term, and the assumptions meant are those of the path's public
   results, so the sentence survives the change.
9. **Lines 322 and 408, the "final bridge theorem" cells of Paths 4 and 5.** "the
   coalition bound the cut-carrier transfer concludes at this row" -> **path**.
   "concludes at" is the terminal's verb for a program; here it reads as the
   coordinate the transfer reaches inside the analysis path.
10. **Line 862, end of Path 11.** "Those refutations stay true beside this row"
    -> **path**: the referent is the whole entry, not the published program.
11. **Docstring of `pgl27_prior_exact_path`.** "that index is what lets a row
    over the word model and a row over this one be read at one law of the
    secret" -> **program** twice, by the sheet's composite entry "the two rows
    over this model -> the two programs over this model", although the docstring
    belongs to an `AnalysisPath` value.

### pgg_tableau.v

12. **Line 4, the file banner.** "Tableau: the row program of one protocol
    instance" -> **path**. "program program" is not a sentence; the reading kept
    is the program of one analysis path.
13. **Lines 247 to 248, comment on `SecurityArm`.** "A published row's manifest
    row records the path the row ran" -> "A published program's manifest path
    records the path the program ran". Two meanings of the new word stand in one
    sentence, the record and the route. Listed below.
14. **Line 933, comment on `Notation Published`.** "A published row at the
    program's own bound: what a row whose coordinate names no number publishes"
    -> three occurrences of "program" in two lines, one of them already there
    before this pass. Correct, and repetitive.

### pgg_tableau_syntax.v

15. **Line 292, section banner.** "The row statements" -> "The program
    statements". The banner names the notations that build a program.
16. **Line 414, comment on the conclude notation.** "so a row that publishes a
    constant a paper cites is one program in one language and not a program that
    falls back to the bind" -> the new "program" now sits beside two that were
    already there.

### pgg_analysis_status.v

17. **Lines 116 to 117, comment on `AnalysisModelSlot`.** "a row cannot reach
    Sampled or AnalysisBridged without producing a typed sample-adapter family,
    while a row still at Algebraic, Executable or Observed may leave the slot
    empty" -> **path** twice. The slot is a field of the manifest's record and
    this file knows no Tableau, although "reach a level" is also the program's
    verb.
18. **Line 65, comment on `TransferStatus`.** "the row's prose names the ideal
    and the carrier of the transfer" -> **path**: the prose meant is the entry in
    the manifest header.

## Sentences I was not allowed to repair

1. **pgg_analysis_manifest.v:9**, file header, describing what the manifest
   records: "... and records one path per analysis path." Circular: the record
   is the analysis path.
2. **pgg_analysis_manifest.v:854 to 856**, level justification of Path 11: "The
   two paths differ in the model family and in the transfer status, and they
   carry different statements, Path 9 exact independence and this path a bound
   on the distance to that independent model." A path carries no statement
   (sheet rule 3). The two preceding coordinates named, model family and
   transfer status, are a path's, which is why both got "path"; the clause about
   statements needs the program.
3. **pgg_analysis_manifest.v:446**, level justification of Path 5, and the same
   wording in the docstring of `five_card_repeated_path`: "endpoint_bound and
   deal_centi_lt stay in the path for what they are". A path stores no theorem.
4. **pgg_analysis_manifest.v:892**, "Absent capabilities": "No path is filled
   with a dummy theorem, an option-valued proof, an axiom or a placeholder."
   Same tension.
5. **pgg_analysis_status.v:70**, comment on `TransferStatus`: "... and the
   manifest path of such a path names the absent premise instead." Circular.
6. **pgg_analysis_client.v:134**, section banner: "The typed status vocabulary
   and the nine paths". False before this pass as well: line 7 of the same file
   says eleven typed paths, and the manifest defines eleven.
7. **pgg_tableau.v:247**, comment on `SecurityArm`: "A published program's
   manifest path records the path the program ran and no theorem." The word
   carries its two readings in one sentence.

## Layout

Re-flowed paragraphs keep every word in place and every box line at 80 bytes
with a space before the closing delimiter; table cells keep their column bars
(`| typed path           | x_path |`) and the two index headers keep their `==`
column. Three re-flows fixed lines that were already irregular before this pass
(the assumption-convention paragraph of the manifest header, and two
paragraphs of pgg_tableau_syntax.v).

## Final checker lines

`python3 notes/probes/2026-09-20-published-rename/check_prose.py c07f6a8`

```
SAME  manifest/pgg_analysis_client.v  program 0, path 3, left as row 0
SAME  manifest/pgg_analysis_manifest.v  program 6, path 110, left as row 2
SAME  manifest/pgg_analysis_status.v  program 0, path 7, left as row 0
SAME  manifest/pgg_tableau.v  program 91, path 10, left as row 0
SAME  manifest/pgg_tableau_arm_relations.v  program 2, path 0, left as row 0
SAME  manifest/pgg_tableau_syntax.v  program 21, path 0, left as row 0
```

No LONG, BOX, BARRED or OTHER CHANGE line for any of the six. The run's last
two lines were `29 files changed; program 390, path 185` and `ALL OK`, the
counts covering the other three groups' files as well.
