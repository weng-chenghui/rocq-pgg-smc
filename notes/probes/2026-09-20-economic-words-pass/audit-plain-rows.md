# Audit: the literal (R5) and plain-relation (R6) rows of the economic-word pass

Read-only adversarial audit of the uncommitted comment pass on top of 6a20f7d.
Scope: the 85 passages the prover's table classifies **R5** (literal: reductions
or a measured time, 13) and **R6** (the plain relation, 72). The security rows
R1-R4, RA and RB belong to a second auditor. No repository file was edited
except this one; nothing was compiled.

## Verdict

**NO-GO** for these 85 passages as they stand. Two MUST items block the commit:
one sentence that does not parse (B1) and one comment box whose line loses the
space before `*)` (B2). Both are one-line repairs and neither is conceptual.
With B1 and B2 applied, the 85 passages are committable; B3 to B6 are
improvements the owner may take or leave, and B7 to B14 are observations.

Nothing in the 85 was found to lose a clause, a count or a scope, and the four
new claims that are checkable against a declaration (B15 below) all check out.

## Findings

| id | grade | file:line | old sentence | new sentence | problem | replacement |
|----|-------|-----------|--------------|--------------|---------|-------------|
| B1 | MUST | instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:848 | `the refine path ssreflect's erefl takes spent 147 s here against reflexivity's 0.07 s` | `the refine path ssreflect's erefl takes costs 147 s here against reflexivity's 0.07 s` | Two finite verbs in one clause; the sentence does not parse. HEAD was already broken (`takes spent`) and the pass swapped one broken verb for another instead of repairing the clause. | `the refine path ssreflect's erefl costs 147 s here against reflexivity's 0.07 s` (keeps the sanctioned literal verb for a measured time) |
| B2 | MUST | manifest/pgg_tableau_syntax.v:79 | `(* because ssreflect already spends it, measured on 2026-09-19 by binding it  *)` | `(* because ssreflect already reserves it, measured on 2026-09-19 by binding it*)` | `reserves` is two characters longer than `spends`, so the closing `*)` lost its separating space. Every other line of this box is 80 bytes ending ` *)`. | Rewrap lines 79-80 (both 80 bytes): `(* because ssreflect already reserves it, measured on 2026-09-19 by binding   *)` then `(* it in a file that requires nothing but ssreflect.                          *)` |
| B3 | SHOULD | instances/pgl27/pgl27_exec.v:351 | `and the interpreter budget is pgl27_fuel.` | `and the fuel is pgl27_fuel.` | Dropping `interpreter` makes the clause nearly vacuous (`the fuel is pgl27_fuel`) and leaves a short line mid-paragraph. The two sibling files keep the qualifier: `the interpreter fuel is 100` (five_card_exec.v:464), `the interpreter fuel is 150` (s5_exec.v:363). | `and the interpreter fuel is pgl27_fuel.` (66 bytes with the existing indent, no rewrap needed) |
| B4 | SHOULD | instances/s5/s5_exec.v:936 | `so instantiating it at the additive layout costs this run no reduction of its own` | `so instantiating it at the additive layout uses no reduction of this run's own` | `no reduction of this run's own` is not idiomatic; the possessive lost its head noun when the verb changed. | `so this run uses no reduction of its own to instantiate it at the additive layout` |
| B5 | SHOULD | instances/s5/s5_mixing.v:480 and instances/pgl27/pgl27_spectral.v:106 | `one letter of the word buys a factor 1 - gap` | `one letter of the word gives a factor 1 - gap` | Each file states the same relation twice, and the second occurrence (s5_mixing.v:510, pgl27_spectral.v:586) was rewritten as `each letter of the word contributes its factor 1 - gap`. Two words for one concept inside one file. | `one letter of the word contributes a factor 1 - gap` |
| B6 | SHOULD | security/pgg_mixing.v:902 | `the elementary inequality that lets an off-diagonal entry pay for itself out of the two diagonal entries it sits between` | `the elementary inequality that lets an off-diagonal entry be absorbed by the two diagonal entries it sits between` | One economic metaphor replaced by another figure where the field's own word is available. The statement is `2 * \|a * b\| <= a^+2 + b^+2` and the sentence calls itself the per-entry step of a diagonal-dominance argument. (`absorbed` is not new to the tree: lib/mutual_info_recoding.v:82 carries it at HEAD.) | `the elementary inequality that lets the two diagonal entries an off-diagonal entry sits between dominate it` |
| B7 | NOTE | instances/psl211/psl211_alldecks.v:566 | `its stuck ordinal content is carried through at no cost and the all-decks mode costs no more to terminate than the dealer-dealt one` | `its stuck ordinal content is carried through unchanged and the all-decks mode needs no more reduction to terminate than the dealer-dealt one` | The first clause changes proposition, from a claim about reduction work to a claim about the content being unaltered. Acceptable: the new claim follows from the stated premise (`vm_compute never destructs the layout`), and the second clause still carries the reduction claim. | none needed |
| B8 | NOTE | instances/psl211/psl211_models.v:620 | `the identification costs nothing probabilistic` | `the identification adds nothing probabilistic` | Possible reclassification to the perfect/statistical row. `psl211_dealerPE` is an equality of laws, `fdistmap psl211_dealer_assoc (psl211_alldecksP R) = psl211_dealerP`, so the field's word for it is exact. `adds nothing probabilistic` leaves the reader to infer what would have been added. | `so the identification is exact and fixes which of the dealer model's three draws each of the instance's coordinates is` |
| B9 | NOTE | instances/pgl27/tableau/pgl27_tableau_checks.v:114 | `Three costs are each why one line reads as it does.` | `Three timings are each why one line reads as it does.` | The rewrite is right. The table's `Declaration checked` column for this passage names `Fail Definition pgl27_inline_neq` (line 137), but the comment sits inside the proof of `Lemma pgl27_row_word_arm_neq` (line 110). The prover recorded the wrong declaration for its own check. | table row only; no source change |
| B10 | NOTE | nine passages | `buys` / `owes` / `earns` / `charges` | `gives` | `gives` is now the pass's general-purpose replacement and carries five distinct relations across the 85: supplies a witness or an arm (#1, #82, #83), contributes a factor (#53, #67), is what establishes (#73), assigns mass (#85, #86), provides privacy rather than correctness (#101). No collision inside any one file except the one B5 names. | see B5 |
| B11 | NOTE | instances/s5/s5_exec.v:23 | `The instance spends three reductions in all` | `The instance needs three reductions in all` | Count verified: `s5_dealt_terminates` (line 384), `s5_profile_endpoints` (392), `s5_supplied_terminates` (930) are the three `vm_compute` proofs among the run-fact obligations of the two modes. The file holds a fourth `vm_compute` proof, `s5_aprocs_cut_terminates` (670), which is an auxiliary lemma and not a run-fact obligation, so `in all` is scoped to the obligations. Scope unchanged from HEAD. | none |
| B12 | NOTE | reconstruct/invariant_profiler.v:22 | `the cheap subset-sum reasoning is valid` | `the simple subset-sum reasoning is valid` | 82 bytes. Leave it: this box is already ragged at HEAD, lines 20, 21 and 23 are 82 bytes and line 22 was 81, so the added line makes the block even rather than uneven. The companion change at line 81 keeps one word for the concept. | none |
| B13 | NOTE | fuel wording, tree-wide | `budget` | `fuel` | 15 passages, 16 word occurrences, not 11: five_card_exec.v:464 and 481 (twice), pgl27_exec.v:351 and 374, psl211_alldecks.v:70 and 569, psl211_tableau_observed.v:8, 31, 41, 73, 130 and 143, psl211_models.v:347 and 386, psl211_tableau_executable.v:71. Every one is the interpreter's step bound (`ex_fuel` / `ep_fuel`), and the two `budget` uses that are not the step bound were correctly given other words: `row-indexed dominance condition` (pgg_mixing.v:886) and `al is split half onto each of the two coordinates` (pgg_mixing.v:915). | none |
| B14 | NOTE | protocol/pgg_instance.v:303, :315; protocol/pgg_execution_plug.v:85 | `ex_fuel is the interpreter budget` / `ep_fuel selects the interpreter evaluation budget` | unchanged (frozen) | The split matters only mildly, and it is tolerable as it stands. The editable tree now uses the field's own name, and the frozen glosses sit at the definition sites, which is where a reader meets the field and where a gloss in a second word is useful rather than confusing. All three sites are already on the owner's frozen list, so the word is recoverable when the freeze lifts. | none now |

### B15: the checkable new claims, checked against the declaration

- `five_card_row_biased_branch_indistinguishability_atE` (kim bridged:1033). New
  text: "naming the Sampled value leaves the input-indistinguishability row's
  coordinate unchanged". The lemma is `published_at branch = published_at
  written-out`. Correct, and more informative than the old "costs the row
  nothing".
- `table_T4_star3` (groups/pgg_raag_clique.v:1112). New text: the choice between
  two graphs with the same clique polynomial "leaves the deck designer's trace
  counts equal". The comment above the lemma states P(z) is the same for the
  path on four vertices and the three-point star and that the two rows agree.
  Correct.
- `exact_leaks` (manifest/pgg_tableau_syntax.v:283). New text: "the annotation
  leaves the term a row builds unchanged". The body is `:= p`. Correct.
- `pgl27_spectral_convergence_gap` and `s5_spectral_convergence_gap`. New text:
  "each letter of the word contributes its factor 1 - gap". The bounds are
  `sqrt 8 * (1 - gap)^L` and `sqrt 5 * (1 - gap)^L`. Correct.
- `fc_kim_rho_supp_pow` (five_card_mixing.v:44, index line). New text: "every cut
  in the support of a Kim word shuffle is a rotation". The statement is
  `rho_from_words_weighted ... g != 0 -> exists k, g = (fc_sigma ^+ k)%g`.
  Correct.

### Reduction counts in R5, checked against the files

- `five_card_exec.v:17`, "the instance needs two reductions for them": the two
  are `five_card_terminates` (line 486) and `five_card_commit_endpoints` (496),
  both `by vm_compute`. The file's three other `vm_compute` proofs (773, 788,
  845) are trace lemmas and not run facts. Correct.
- `five_card_exec.v:510`, "uses one reduction, at the profile": correct, that is
  `five_card_commit_endpoints`.
- `pgl27_exec.v:19`, "decides two by reduction ... needs no proof at all for the
  third": `pgl27_dealt_terminates` (378) and `pgl27_profile_endpoints` (387) are
  the file's only two `vm_compute` proofs, and `pgl27_dealt_recon` is
  `dealt_static_recon`. Correct, and consistent with `pgl27_exec.v:392`, "the
  instance uses no reduction of its own for it", since `pgl27_dealt_endpoints`
  is `profile_endpointsE pgl27_profile_endpoints`.
- `s5_exec.v:23` and `:25`: see B11. The companion claim "the two reconstructions
  use no reduction at all" holds: `s5_dealt_recon` is `dealt_static_recon` and
  `s5_supplied_recon` (948) carries no reduction.
- `psl211_alldecks.v:566`, "needs no more reduction to terminate than the
  dealer-dealt one": see B7.

### The five kept time statements

All five sit in plain `(* *)` comments in or beside a proof, never in a
statement comment or a file header, so the owner's rule on timings is kept:

- `pgl27_tableau_checks.v:115, 118, 120` (`costs 78.7 s`, `costs 24.3 s`,
  `costs 24.1 s`): inside the body of `Lemma pgl27_row_word_arm_neq`, between
  `Proof.` and the first tactic.
- `five_card_tableau_analysis_bridged.v:848` (`costs 147 s`): in the plain
  comment above `Lemma five_card_row_repeated39_atE`, beside the `(** *)`
  statement comment and not inside it. Sentence broken, see B1.
- `s5_mixing.v:211` (`costs minutes to typecheck`): in a plain comment beside
  the literal table it describes. Untouched by the pass.

`pgl27_tableau_analysis_bridged.v:951`, `expensive` to `slow` for a 96.0 s
measurement, is likewise in the proof body of `pgl27_row_word_obs_sampledE`.

### The nineteen keywords (item 5)

`manifest/pgg_tableau_syntax.v:64` now reads "The surface reserves nineteen
identifiers as global keywords". The enumeration that follows lists exactly
nineteen: dealt, functionality, execute, endpoints, recon, sample, certify,
leaks, tied, ideal, mixing, invariant, encoded, supplied, layout, decoded_by,
committed_by, expecting, fuel. All nineteen occur as literal tokens in the
file's fourteen `Notation` declarations. The other lowercase tokens in those
declarations are the ones the header itself excludes (inputs, terminates,
publish, conclude, vm_compute, at, by) plus the metavariables (a, b, c, d, e, f,
k, n, p, r, s, t, u, w, idx, enc, procs). The count was not changed by the pass.

`protocol/pgg_algebra_syntax.v` is **not** in `git diff --name-only`: the frozen
file was not touched.

### Layout of the added lines

173 added lines were scanned. One line over 80 bytes (B12, leave it), one box
line missing the space before `*)` (B2), no trailing whitespace, no index line
whose name touches `==`, no banner introduced or broken.

### Word scans over the added lines

- New metaphor or narrative words: one hit, `absorbed` (B6). No `gives up`,
  `falls to`, `wins`, `beats`, `escapes` or similar.
- History words (`now`, `no longer`, `formerly`, `previously`): none.
- Abbreviations of "indistinguishability": none; the word is spelled out
  everywhere.
- The project's banned vocabulary list: no hit in any added line. (One
  pre-existing hit sits at reconstruct/invariant_profiler.v:16 and 19, at HEAD,
  outside this pass.)
- `loss` / `hop` / `slack` / `tight` inside R5 or R6 added lines: none. Every
  occurrence of those four words in the diff falls in an R1, R2 or R4 passage.

### One observation that belongs to the other share

`instances/pgl27/pgl27_spectral.v:517` and `instances/s5/s5_mixing.v:396` (rows
R4, the second auditor's) now read "the second of the two slack conditions
psd_of_dominant needs". These are the row-dominance and column-dominance
hypotheses, not a gap between a bound and an exact value, so this gives the
reserved word a second concept to carry. "the second of the two dominance conditions
psd_of_dominant needs" would keep one word per concept. Flagged for the other
auditor, not counted in this verdict.

## Item 8: family members remaining in the editable tree

Scan of 127 editable `.v` files under `manifest/ instances/ security/ protocol/
lib/ smc/ reconstruct/ groups/`, excluding the frozen forward closure of
`instances/psl211/psl211_endpoints.v`, over comment text only (nested comments
handled, string literals skipped), for the whole family plus the inflections
`paying, buying, costing, pricing, spending, earning, investing, charging,
owing` and a wider set of trade words.

**Literal, keep (5):**

| file:line | text |
|---|---|
| instances/pgl27/tableau/pgl27_tableau_checks.v:115 | `costs 78.7 s in the statement alone` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:118 | `costs 24.3 s` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:120 | `costs 24.1 s` |
| instances/s5/s5_mixing.v:211 | `six-digit int literals costs minutes to typecheck` |
| instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:848 | `costs 147 s` — literal and sanctioned, but the clause is broken: see B1 |

**Missed metaphors (7).** The prover's own final scan reported five literal
occurrences and nothing else, so these seven were not seen. The likely cause is
that the scanner's word list did not expand the `-ing` forms.

| file:line | text | suggested replacement |
|---|---|---|
| instances/pgl27/pgl27_exec.v:352 | `the dealer-dealt mode is what leaves the instance owing termination alone among the three run facts` | `... is what leaves termination as the instance's only obligation among the three run facts` |
| instances/s5/s5_exec.v:364 | same sentence | same replacement |
| instances/s5/s5_exec.v:911 | `which is what leaves this run owing a reconstruction obligation of its own` | `which is what leaves this run with a reconstruction obligation of its own` |
| instances/s5/tableau/s5_tableau_executable.v:87 | `which is what leaves this mode owing a reconstruction obligation of its own at the level above` | `which is what leaves this mode with a reconstruction obligation of its own at the level above` |
| instances/psl211/psl211_secrecy.v:13 | `at any prior charging both chiralities, the law already depends on it` | `at any prior giving mass to both chiralities, ...` (the pass's own word, from lib/mutual_info_recoding.v:43) |
| instances/psl211/psl211_secrecy.v:37 | `psl211_colour_view_dep_k6 == at a prior charging both chiralities, a six-position coalition's colour view depends on the chirality` | `== at a prior giving mass to both chiralities, ...` (box line, rewrap to 80) |
| instances/psl211/psl211_secrecy.v:323 | `under a prior charging both chiralities, the colour view of the six positions ...` | `under a prior giving mass to both chiralities, ...`; the statement is `secretP true != 0 -> secretP false != 0` |

Two files are involved that the pass never opened: `instances/psl211/psl211_secrecy.v`
and `instances/s5/tableau/s5_tableau_executable.v`. `instances/pgl27/pgl27_exec.v`
and `instances/s5/s5_exec.v` were edited by the pass and still carry the word.

False positives excluded: `Saloff-Coste` (security/pgg_schreier.v:93, :321,
security/pgg_schreier_weighted.v:34), `coincide`/`coincides` (seven sites),
`fair coins` (instances/denboer1989/five_card_leakage.v:11).

## Item 9: the frozen occurrence list

`frozen_occurrences.md` parses to 49 entries over 12 files: groups/pgg_raag.v,
instances/psl211/{psl211_endpoints, psl211_exec, psl211_profile}.v,
protocol/{pgg_algebra_syntax, pgg_execution_plug, pgg_instance,
pgg_session_types}.v, reconstruct/{algebraic_rigidity, covering_scheme}.v,
security/{pgg_collusion_bound, pgg_security_solver}.v. **Every one of the twelve
is in the frozen forward closure, and none appears in `git diff --name-only`.**

Ten entries spot-checked against the files (pgg_instance.v:19, :54, :315, :765;
psl211_exec.v:35, :103; psl211_profile.v:79; psl211_endpoints.v:10;
algebraic_rigidity.v:194; covering_scheme.v:189): the quoted text is present and
unchanged in every case, and the recorded line number is the line carrying the
word. Where the quotation starts two lines earlier, it is because the entry
reproduces the whole enclosing comment, which is the useful form.

One bookkeeping duplicate: `protocol/pgg_instance.v:303` appears twice with the
identical snippet, because the comment holds the word twice. The file's count in
the heading (14) counts it twice. Harmless.

## Coverage

**85 of 85** passages read in full, old sentence against new sentence, clause by
clause. The declaration or the enclosing proof was opened for every passage
whose new sentence states something checkable, and for all 13 of R5. All 29
files that carry an R5 or R6 passage were opened as a diff and, where a count or
a claim had to be checked, as source.
