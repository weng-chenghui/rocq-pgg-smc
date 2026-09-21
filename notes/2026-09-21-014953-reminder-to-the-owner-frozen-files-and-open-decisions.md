# Reminder to the owner: what the campaign could not touch, and the decisions it made alone (2026-09-21)

Tracker step 2.6d. The owner asked on 2026-09-20: "For four files about
psl211_endpoints, give me a hint once all other tasks are done." The count was
wrong: it is twelve files and more than four kinds of thing. Everything below
was LEFT AS IT IS, because it sits in the forward closure of
`instances/psl211/psl211_endpoints.v` (editing one of those files means
recompiling the endpoint file: 900 s, 17 GB) or because it is code that only
the owner should rename.

**STATUS 2026-09-21, late afternoon: sections 1 and 2 are DONE** on the
owner's order, main eaad140: every item below was applied, the tree was
recompiled once (130 files, `psl211_endpoints.v` once, 799 s), and the one
exception is `smc/smc_interpreter.v`, vendored verbatim from the infotheo fork,
whose two lens names stay. The correction of this note's own text: only ONE
sentence of `psl211_profile.v` was a twin of a rewritten sentence, not three.
New names: `notes/2026-09-21-164859-renamed-identifiers-n-traces-and-bound-variables.md`.
The sections are kept as the record of what was found.

## 1. Comments in frozen files that still carry a word the owner barred

| What | Where | How many | List with the text |
|---|---|---|---|
| The economic words for a relation (spends, price, pays, budget, buys, owing, owed) | twelve frozen files; most in `protocol/pgg_instance.v` (14), `instances/psl211/psl211_exec.v` (12), `instances/psl211/psl211_profile.v` (6), `instances/psl211/psl211_endpoints.v` (5) | 49 and 4 found later | `notes/probes/2026-09-20-economic-words-pass/frozen_occurrences.md` with its addendum |
| The manifest's word for a published program ("row") in the program sense | `instances/psl211/psl211_exec.v:127` and `:129`, one docstring | 2 | `notes/probes/2026-09-20-published-rename/frozen_prose_occurrences.md` |
| The noun barred on 2026-09-20 for a constructor of the security-evidence type | `instances/psl211/psl211_exec.v:127`, the same docstring | 1 | `notes/probes/2026-09-20-security-property-rename/prose_psl_s5.md`, last section, with a proposed six-line replacement of the whole docstring that fixes this and the item above together |
| The norm abbreviation for the sum of absolute differences | `reconstruct/algebraic_rigidity.v:125` and `:155` | 2 | `notes/probes/2026-09-20-barred-words-pass/frozen_and_code_residue.md` |

Three sentences of `instances/psl211/psl211_profile.v` (78, 102, 132) are word
for word the sentences already rewritten in `instances/pgl27/pgl27_profile.v`;
the two sibling files now say one thing in two vocabularies until the freeze is
lifted.

Suggested way to do it, when the owner decides to pay the recompile once: one
comments-only pass over the twelve files with `scripts/comment_pass/`
(`inventory.py --frozen` already lists the sites), then ONE compile of
`psl211_endpoints.v` and its importers. Code tokens do not change, so nothing
can break; the cost is the rebuild alone.

## 2. Code identifiers only the owner should rename

Word-length and list variables spelled with a capital letter and the digits one
and two, which the owner reads as the barred norm abbreviation:
`security/pgg_schreier.v` (9 uses, with four comment lines that mirror them),
`security/pgg_schreier_weighted.v` (6), `instances/pgl27/pgl27_orbit.v` (9),
`instances/psl211/psl211_alldecks.v` (6), a lemma-name suffix in
`instances/s5/pgg_raag_s5.v:59` and `instances/s5/rigidity_s5_instance.v:31`;
frozen: `instances/psl211/psl211_orbit.v` (8) and lower-case variants in
`reconstruct/transitivity_privacy.v` (3), `smc/smc_interpreter.v` (5). Renaming
them changes proof scripts.

## 3. Decisions the main session made while the owner was away (2026-09-20 evening to 2026-09-21)

Each is recorded with its reasons in the spec named, and each can be overturned
without losing work, since every one was landed as a pure addition.

| Decision | Where it is argued |
|---|---|
| Terminals below the top level are TWO records (`PublishedObserved`, `PublishedSampled`), not a family indexed by the level; the Sampled terminal admits only the two transfer statuses that name an absent premise | `notes/20260920-terminals-below-analysis-bridged-probe-design.md`, last section |
| A proposition is stated AT a reading; the concept word is "reading"; one-seat and one-position marginal bounds are propositions of their own and NOT security evidence; the PGL(2,7) content trace is the coalition's reading under a second name (one lemma says so); the PSL(2,11) colour reading is the genuinely different instance | `notes/20260920-readers-and-marginal-bounds-probe-design.md`, last two sections |
| A refutation is published as input DISTINGUISHABILITY, a fact about the model with no certificate in it; the terminal is `publish_obstruction`; `SecurityEvidence` keeps three constructors | `notes/20260921-refutations-probe-design.md`, last section |
| How the campaign is run (toolkit, audit before apply, one recompile per batch) | `notes/2026-09-20-220834-boost-plan-for-naming-and-comment-passes.md` |

## 4. Decisions that are the owner's and were NOT made

1. **The manifest's capability vocabulary had no label for a limitation.**
   DECIDED by the owner on 2026-09-21 and landed: the label "input
   distinguishability" joins the closed vocabulary, and the published
   obstruction at PSL(2,11) is the manifest's twelfth path,
   `psl211_alldecks_obstruction_path` (AnalysisBridged, NegativeTransfer). The
   raw inequality moved below the manifest, into
   `instances/psl211/psl211_alldecks_input_distinguishability.v`.
2. **The prose tables of `manifest/pgg_analysis_manifest.v` now head each entry
   "Path n" where they said "Row n"**, by the main session's ruling on
   2026-09-20. The numbers did not change. If a text cites an entry by its
   number and old noun, that citation changes with it.
3. **The rule in the owner's own `CLAUDE.md`** that says "Price every step of a
   hybrid or hopping argument, and label the currency" uses the economic words
   the owner replaced on 2026-09-20 ("loses at most", "hop"). The main session
   does not edit that file.
4. **Git history.** One checkpoint commit of 2026-09-20 (d3a1957) carries an
   early deletion; HEAD is unaffected. Thirty-two older commit subjects use the
   noun barred on 2026-09-20; the owner said to leave history as it is.
5. **Work recorded as separate later units:** the three PSL(2,11) dealer-model
   theorems and the three PGL(2,7) theorems under other dealer laws each need a
   model family and a link lemma of their own; a conditional mutual information
   and the monotonicity in the coalition need a proposition about a leakage
   measure, which the Tableau has at no phase; the S_5 countermodel showing
   that a marginal bound implies no security property is argued in a comment
   and not compiled; `restate` below the top level.

6. **Declarations with no use site yet.** The landing of the published
   obstruction added `input_distinguishability_prop_le`,
   `indistinguishability_prop_of_ideal_close`, `run_correct_of_obstruction`
   and `view_identification_of_obstruction`, which nothing applies today. The
   two readers mirror `run_correct_of_sampled` and
   `view_identification_of_sampled`, equally unapplied, so they were kept by
   the existing pattern. Under the rule "keep only what the paper claims or
   later work needs", the owner may prune both pairs together.
7. **The sign of the number a published obstruction carries.** DECIDED by the
   owner on 2026-09-21 and landed: the proposition an obstruction stands for
   is `0 < c /\ InputDistinguishabilityPropAt sa c`, so a published value
   carries the positivity and a sentence at a number at or below zero cannot
   be published. `InputDistinguishabilityPropAt` itself is unchanged.

8. **Decisions made WITH the owner on 2026-09-21 (chat), all landed, main
   0fe7377:** the reading indexes `certify` (not `observe`, not a new phase);
   prepositions `of` what is read, `at` a number, a size or a real field with
   its index, `by` a proof or a piece of evidence, `assuming` an assumption
   status; the obstruction published inline with its reading and its number
   (the owner first chose a spelling with a leading `obstruction` keyword and
   replaced it after the read-aloud audit); `conclude at c by p`. Decided by
   the main session under the same principle and open to the owner:
   `at R idx by b` in the five-clause rule; ONE reading record
   (`CoalitionReading`) with `StaticReading` retired; every obstruction
   program names its reading and the terminal without a reading was removed.
9. **Later units the reading work left:** the manifest paths for the two
   programs over the dealer-dealt model are DONE (the thirteenth and the
   fourteenth, main 22e3d22); post-processing of ideal proximity (attempted, the
   construction does not typecheck yet, nothing calls it); slot-name clauses
   (`sample f`, `dealt fuel n`, `ideal u`) still read as an application to a
   first reader, and only a change of the language's shape would cure it;
   the word "reading" still means the value read in comments of files the
   landing did not touch (`five_card_proximity.v`, `pgl27_exec.v`,
   `pgg_analysis_manifest.v`, `var_dist_joint_law.v` and others).

10. **Two vocabulary decisions that are the owner's (found on 2026-09-21,
   nothing applied):** (a) `notes/probes/2026-09-21-frozen-files-pass/SHEET-READING.md`
   proposes 273 comment sites in 40 files where "reading" names a value, a
   law or an instance's own function, to be replaced by "endpoints", "view",
   "law"; that would overturn the concept word chosen on 2026-09-20 outside
   the record's own files and bring "view" back as a concept word. (b) DONE on the owner's decision of the same day (tracker 4.7;
   identifiers kept; two frozen sites left: `reconstruct/algebraic_rigidity.v:104`
   and `protocol/card_exchange_pismc.v:81`), which was: a
   `var_dist` is called a total variation, which is off by the factor two the
   tree otherwise states everywhere: `security/pgg_mixing.v` (ten comments and
   the identifier `symm_ds_TV_bound`), `instances/kim2025/kim_input_privacy.v`
   (four), `instances/pgl27/pgl27_mixing.v:13`, `security/pgg_schreier.v:321`.
   Neither touches a frozen file.
11. **`legacy/`** was not recompiled after the pass of 2026-09-21 (nor after
   any landing of this campaign); its compiled files are older than what they
   require. Tool defect fixed on 2026-09-21 (b426481): the layout pass keeps two-space
   sentence spacing. `--all` was idempotent all along; what it does is lay out
   hand-laid files by its own rules, and its README now says where not to use
   it.

## 5. Paper

No `.tex` file was edited at any point. The renamed identifiers a text would
have to follow are listed in three dated notes:
`notes/2026-09-19-230614-renamed-identifiers-input-indistinguishability.md`
(the only one with names the paper cites today, lines listed there),
`notes/2026-09-20-142813-renamed-identifiers-published.md`,
`notes/2026-09-20-205851-renamed-identifiers-security-property-and-evidence.md`.
