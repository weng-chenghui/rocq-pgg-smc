# Rulings on the audit of landing commit 2 (2026-09-21)

Audit: `../audit-landing2/REPORT.md` (R1 to R40, one Opus auditor, read-only,
verdict GO-WITH-CHANGES: the Rocq is sound, the prose is not). Rulings by the
main session; each replacement was read against its declaration. Where a row
says ACCEPT with no text, the auditor's replacement in the report is the text
to land. The fix pass changes comments, six names (R19), three proof
terminators (R26) and one surface rule (R29); nothing else.

| id | ruling |
|---|---|
| R1 | ACCEPT, AMENDED. The auditor's "at no other" reads as a fact about every other reading; the lemmas leave the coarser readings open. Land: "The reading is the coalition's own endpoints, the finest, so what a program written this way publishes refutes certificates at that reading and leaves certificates at every coarser reading open. An obstruction written at a coarser reading refutes certificates there and at every reading it factors through, the endpoint reading among them." If R29 removes this terminal, the sentence moves to the comment of the remaining terminal, reworded for a named reading: "When the reading named is the coalition's own endpoints, the finest, what the program publishes refutes certificates at that reading and leaves certificates at every coarser reading open; an obstruction at a coarser reading refutes certificates there and at every reading it factors through, the endpoint reading among them." |
| R2 | ACCEPT, AMENDED. "it implies none of them" is a false universal (a coarser reading that is a renaming is implied). Land: "The reading is the coalition's own endpoints, the finest, so this is the weakest of the distinguishability statements about the model: an obstruction at any coarser reading implies it, and the converse does not hold in general." |
| R3, R4, R5, R6, R8 | ACCEPT |
| R7 | ACCEPT, with a duty: keep from the displaced docstring only what is true of `psl211_colour_of_reading`; check "card zero is a heart" against the colour table of the file before keeping that clause, and drop it if the file does not show it. The displaced docstring's true content about `psl211_colour_reading` goes to the docstring of `psl211_colour_reading`, restated for the one record. |
| R9, R35 | ACCEPT, after checking that the proof of `psl211_colour_indistinguishability_of_coalition_reading` passes the factorisation by conversion, as the auditor read it |
| R10, R11, R12, R13, R14, R15, R16, R17, R18 | ACCEPT |
| R19 | ACCEPT: `ReadingExactPayload`, `ReadingIndistinguishabilityPayload`, `ReadingIdealProximityPayload`, `reading_exact_payload`, `reading_indistinguishability_payload`, `reading_idealproximity_payload`. Use `scripts/comment_pass/rename.py` (build, apply, check) over code and comments of the tracked tree outside `notes/` |
| R20, R21, R22, R23, R24, R25 | ACCEPT |
| R26 | ACCEPT: `Proof. exact: erefl. Qed.` on the three `certify_*_readingE` |
| R27 | ACCEPT (the main session's own scan found the same word) |
| R28 | ACCEPT, after checking the two coordinates against `psl211_alldecks_obstruction_path` |
| R29 | ACCEPT IN PART. No alias: `psl211_endpoint_reading` would be a second name for one reading, the defect the one-record ruling removed. Instead every obstruction program names its reading: the all-decks program is written `|> publish Obstruction InputDistinguishability of (coalition_endpoint_reading psl211_algebra) at ... by ... assuming ...`, and the terminal WITHOUT `of r` is removed from `manifest/pgg_tableau_syntax.v` (it then has no caller, and the owner's approved rule is the one with `of r`). The builder keeps its reading argument. The all-decks program's `_pathE`, its consequence lemmas and the recorded rejection of `psl211_tableau_checks.v` must still hold (`exact: erefl` where they did); the syntax header's sentences about the two obstruction terminals become sentences about one; the fidelity equations of landing 1 that use the short rule are NOT edited (they are records), the new fidelity file carries the equation in the landed surface. If removing the short rule makes any equation stop closing by conversion, keep both rules and report. |
| R30 | ACCEPT. One opening sentence per witness or certificate docstring names the reading the record is indexed by; "reading" is never used for the value read. The auditor's pattern is the model; every site listed in the report, plus any other the prover finds with `git grep -n "coalition's reading\|executed reading"` in the changed files |
| R31, R32, R33, R34 | ACCEPT |
| R36 | ACCEPT, in lower case: "at this reading" |
| R37 | NO CHANGE |
| R38 | ACCEPT, after checking that the dealer-dealt run argument is the chirality alone |
| R39, R40 | ACCEPT the suggested wordings |

Layout duties: boxed lines exactly 80 bytes with a space before the closer; no
line over 80 bytes except an unbreakable notation string; reflow only the
paragraph a sentence sits in; every header index in file order and complete.
No history words, no ids, no barred or economic word.
