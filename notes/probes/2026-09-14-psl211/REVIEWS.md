# PSL(2,11) instance: per-task review record (Plan A)

Plan: docs/superpowers/plans/2026-09-14-psl211-chirality-instance.md.
Every task ran as implementer (fresh agent) -> spec-compliance reviewer
(Opus, independent, compiles) -> code-quality reviewer (Opus, mathcomp-skills
reference) -> fixes -> re-review. Sonnet implementers (Tasks 2, 5, 10) were
audited by Opus reviewers before their output counted.

| task | file | landed commits | spec review | quality review | assumptions |
|---|---|---|---|---|---|
| 1 | _CoqProject | 93608c3, a997e63 (+ one line per landed file) | n/a | n/a (peer session found pre-registration broke coqdep; fixed) | n/a |
| 2 | instances/psl211/psl211_blocks.v | 4bc5173, f021d50, e96f55b, 0b7dd1e | compliant (tables byte-identical to the probe; python re-derivation of every certificate) | approved after fixes (comments, Local helpers, shape and inverse certificates, widths) | all closed under the global context |
| 3 | instances/psl211/psl211_group.v | bf793ff, 338cdff, deed6dd, 4e8d51f (closure layer) | compliant (20 lemmas closed; mutation checks fail for the right reason) | approved after fixes (prefixed word layer, wapply Local, m6_permVE, comments, imports); closure layer: approved with fixes deferred to Step 2c | all closed |
| 4 | instances/psl211/psl211_orbit.v | 89aa93f, f5916eb, 120b1b8 | compliant (uniq premise on pattern_countE verified as a correction by counterexample) | approved (deprecated enum identity removed; tbl_ok_asc6 bridge exported; Notation reverted after a scheme hang) | all closed |
| 5 | reconstruct/design_privacy.v | f8450b3, 7453c24, registered 1741d47 | compliant (token-identical to probe_bridge.v 25-130 with renames) | approved with three comment rewrites, applied | exactly the three boolp axioms (transitivity_privacy.v floor) |
| 6 | instances/psl211/psl211_scheme.v | a75d6a2, 7d2b18d (+ 0b7dd1e in blocks) | compliant (re-deal keeps codes; #C = 0 branch; no s1 != s2 assumption; perm_of_eq_card absent from mathcomp) | approved after fixes; tidy items R1-R6 on the plan | all closed |
| 7 | instances/psl211/psl211_secrecy.v | 534fab6, 224bf3d | compliant (the leak's non-degenerate-prior premises proved necessary and minimal; route consumes only psl211_count_okT, psl211_card, the 132 counts) | approved after fixes (%N on nat equations under ring_scope; header currency and scope) | boolp trio (section-variable floor); leak_coalition_card6 closed |
| 8 | instances/psl211/psl211_recovery.v | d2af766, 44466cf, c482ad1 | compliant (witness pair (0,2), mutation probes) | approved (set-form psl211_reveal_ambiguous added) | all closed |
| 9 | instances/psl211/psl211_mixing.v | 688e10c, 98612df | compliant (pgl27 walk convention proved; assumption set identical to pgl27_word_mixing) | approved with fixes (psl211_Wuni; header; dedupe via psl211_closure.v); the table-sealing recommendation was refuted by measurement | identical to pgl27_word_mixing (boolp trio) |
| 10 | instances/psl211/psl211_profile.v | 291712e, 6d8e6f5, 2c5bf01 | compliant | accepted after two comment edits (profile_k attribution; profile_eps_psl211) | psl211_profile closed; distributional lemmas boolp trio |

Mathematical corrections found by the process and folded into the plan:
`psl211_pattern_countE` needs `uniq tbl` (Task 4); `psl211_colour_view_dep_k6`
needs a non-degenerate prior (Task 7); the plan's inline milk6 proof body and
the "quarter" wording were wrong (Task 3); `Local Notation` for a BFS
certificate makes downstream `done` walk into the table (Task 4 fix, and the
same trap in Task 9, resolved by keeping certificates as constants and ending
steps with explicit `exact:`).

Step 2c refactor pass (4c08386, 98612df, d9406a2, 6fda271): psl211_closure.v
split, renames, enumeration-lemma consolidation, wording; nine-anchor
assumption table reproduced unchanged; a separate Opus review of the four
commits was run before the full build (verdict recorded in the plan's Task 11
as-built once returned). Full build at 6fda271: make -j8 nothing to be done,
exit 0. Axiom sweep: standard axioms only, all ten files.
