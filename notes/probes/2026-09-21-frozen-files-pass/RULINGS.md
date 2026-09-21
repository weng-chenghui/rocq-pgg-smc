# Rulings on the audit of the frozen-files sheet (2026-09-21)

Sheet: `SHEET.md` (one Opus writer). Audit: `AUDIT.md` (one Opus auditor,
read-only, GO-WITH-CHANGES, F1 to F24; its report was saved by the main
session from the hand-back). Rulings by the main session. Owner's order of
2026-09-21: do everything that was left in the forward closure of
`instances/psl211/psl211_endpoints.v`, compile that file ONCE after all
modifications, and again only if it has bugs.

| finding | ruling |
|---|---|
| F1, F2, F3, F4, F5, F6 | ACCEPT, the auditor's exact lines. These sites are edited BY HAND, line by line; no layout tool touches them |
| F7 | ACCEPT. `reflow.py` is NOT used in this pass at all: it joins words with one space, so it would remove the two-space sentence spacing these files use, and `--all` is not idempotent on them. Every rewritten paragraph is laid out by hand, keeping the file's own width and its two-space sentence spacing. The two defects of the tool are recorded for a later fix |
| F8, F9, F10, F11, F12 | ACCEPT, the auditor's texts |
| F13 | ACCEPT: `s5_n_traces_natB1`, `s5_n_traces_natB2`, `s5_n_traces_natB3`; and, for one word per concept, `star3_ntB0/1/2` become `star3_n_traces_natB0/1/2` in `groups/pgg_raag_clique.v` (every mention tree-wide found with `git grep -w`; no `.tex` file is edited, the names go into a dated rename note) |
| F14, F15, F16, F20, F21, F23, F24 | noted; F23's corrected reason for the order stands |
| F17 | ACCEPT into this pass (the file is not frozen): `manifest/pgg_tableau_security_property_relations.v:470`, "the distance below is what that omission costs" becomes "the distance below is what that omission loses", after reading the declaration it sits on; if "loses" is not true of it, the prover writes what is and reports it |
| F18 | KEEP "as probe P1b2": measurement provenance, like the date and the timing beside it |
| F19 | ACCEPT the in-row corrections of A35 and A36; lines 115, 237, 263 and 881 of `security/pgg_collusion_bound.v` are recorded as residue (237 and 263 assert a number and need a truth check, not a word swap) |
| F22, B3 | `smc/smc_interpreter.v` is NOT renamed: it declares itself vendored verbatim from the infotheo fork, and `rstep_disjoint` has no use site. Recorded as the one exception |
| A38 | TAKE ("no extra term") |
| A0-W ("worth") | LEAVE |
| A2's measured-time "cost" | KEEP, by the owner's precedent of cca5e24, which the auditor verified |

Every other row of the sheet is accepted as written (the auditor's list of
rows accepted unchanged).

## Order of work (the point is ONE compile of the endpoint file)

1. Stage 1, files that are NOT frozen: B4, B5, B6, B7, B8 with F1, F5 and F13,
   the `star3` family, F17. Each file compiled single-file through the lock as
   it is finished. None of them is required by a frozen file, so the compiled
   endpoint file stays valid, and a slip in a rename shows here.
2. Stage 2, the frozen files: Part A, B1, B2. NO compile. Every file except
   `instances/psl211/psl211_orbit.v` (B1) and
   `reconstruct/transitivity_privacy.v` (B2) changes in comments only.
3. Main session: code tokens identical for the comment-only files, identical
   modulo the rename map for the others; then ONE ordered pass over the
   reverse closure. A failure of B1 or B2 stops the pass before the endpoint
   file is reached, so the endpoint file, whose own change is comments only,
   is compiled once.
