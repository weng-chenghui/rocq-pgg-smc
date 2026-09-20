# Boost plan: how the rest of the campaign is run (2026-09-20)

Owner, 2026-09-20: "You must make this plan, and do rest of works follow this
boost plan." This note is the plan. It changes HOW the work is done, not what
the standing constraints are: every `.v` edit is made by an Opus `rocq-prover`;
Sonnet output is never final; never `make`; never
`instances/psl211/psl211_endpoints.v` nor its forward closure; nothing under
`notes/probes/` is deleted; no `.tex` edit; replies in zh-TW, files in English.

## What was measured on 2026-09-20

| Where the time went | Measured |
|---|---|
| Serial phases (write, audit, fix, audit again, recompile, commit), each an Opus agent of 15 to 40 minutes | the pass over the manifest's noun took about 2.5 to 3 hours end to end |
| Layout done by hand inside agents (80-byte boxes, `==` index columns, line breaks) | an identifier rename took an agent 17 to 23 minutes; the substitution itself is seconds |
| Machine sleep | four audits relaunched, two compiles cut by the wall clock: about one hour |
| An agent at its 120-call limit | once, at 147 sites in one group |
| Recompiles | NOT the bottleneck: a clean 60-file closure is 8 minutes; eight runs were 87 minutes, most of them after comments-only passes; three files are 60 % of a closure (`psl211_mixing.v` 175 s, `pgl27_spectral.v` 157 s, `pgl27_mixing.v` 110 s) |
| Tooling rewritten by agents each pass (apply and re-flow scripts) | three times |

## The rules of the boosted procedure

1. **One toolkit, in the repository, never rewritten per pass:**
   `scripts/comment_pass/` with
   `inventory.py` (every site of a word list in comments, with its paragraph
   and the declaration it sits on, to a TSV),
   `apply_tsv.py` (applies an audited TSV: for each row the old text of one
   comment paragraph is replaced by the new text; refuses a row whose old text
   does not match),
   `reflow.py` (deterministic layout: boxed lines to exactly 80 bytes with a
   space before the closing delimiter, `name == description` entries with the
   file's own columns, docstrings with 4-space and plain comments with 3-space
   continuation, no orphan short line, bytes not characters),
   `check_pass.py` (code tokens identical to the base; every changed comment
   paragraph is a row of the TSV and equals its new text; nothing else changed;
   no line over 80 bytes; the word list is gone; the owner's barred vocabulary
   is absent from new text),
   `rename.py` (checked map: injective, collision-free in the tree; whole-token
   apply; the `Locate` probe file generated; path map for moved files),
   `closure.py` and `compile_closure.py` (reverse closure in topological order,
   refusing any frozen file; single-file compiles through the lock; resumable),
   `fail_recheck.py` (each recorded `Fail` holding a changed identifier,
   recompiled without `Fail` under its own file's prefix, messages kept).
2. **Audit before apply.** Writers (Opus) do not edit files: they fill the
   "new text" column of the TSV, paragraph by paragraph, with the case and the
   declaration fact that decides it. Auditors (Opus) audit the TSV. The main
   session rules. Only then ONE `rocq-prover` runs `apply_tsv.py`, `reflow.py`
   and `check_pass.py` and hands back (minutes). A second fix round exists only
   if the audit of the applied text finds something the TSV audit could not.
3. **Sonnet fans out for inventory and classification only**, never for
   sentences: several Sonnet agents each take a slice of the inventory and fill
   "case" and "declaration" columns. Their columns are audited with the TSV by
   the Opus auditors, and the reply to the owner says who audited.
4. **One recompile per batch of comments-only commits.** With code tokens
   identical the compile cannot change; it is run once at the end of the batch
   (and always before a landing that edits code).
5. **`caffeinate` first**, at the start of every working block.
6. **At most 100 sites per agent**, and every brief says to write the report
   file first.
7. **Pipelines for the proving work (tracker step 4).** Independent groups are
   probed at the same time: their specs are written back to back, their probes
   share the compile lock, their audits share briefs
   (`docs/` holds none; the briefs of 2026-09-20 under `notes/probes/` are the
   templates). Landings stay serial because they edit the same framework files.
8. **Recurring defect classes go into every writer brief as a checklist** (verb
   rule; a universal where the declaration is about one object; a `Fail` read
   as an impossibility; a bound called the distance; twins in sibling files; a
   half-done re-wrap), so that the first audit finds fewer things.

## Order of the remaining work under this plan

1. Finish 2.6f (the fix pass in flight is of the old procedure; it is checked,
   the batch is recompiled once, committed).
2. Build the toolkit (one hour), with its own small test on a copy of two
   production files; it lands in `scripts/comment_pass/` in one commit.
3. P8 landing (3.4), by the landing plan
   `notes/2026-09-20-221500-p8-landing-plan.md`; while it runs, the specs of 4.3
   (terminals below AnalysisBridged) and 4.4 (one-position marginal bounds) are
   written, then probed together; then 4.1 and 4.2 the same way.
4. The reminder to the owner (2.6d), last.

Any further naming decision of the owner is run by rules 1 to 6: expected
about one hour instead of three.
