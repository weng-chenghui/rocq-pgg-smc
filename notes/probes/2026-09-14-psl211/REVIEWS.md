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
commits returned GO with comment-level findings, applied in c7f46f8 and
recompiled green in order. Full build at 6fda271: make -j8 nothing to be done,
exit 0. Axiom sweep: standard axioms only, all ten files.

Final Plan A code HEAD: c7f46f8 (chain green; make -n reports nothing to do).

## Plan B (branch feat/psl211-plan-b, 2026-09-15)

Review: notes/probes/2026-09-15-psl211-planb/REVIEW-planb-mechanical.md (Opus,
independent, read-only, Print Assumptions over the .vo chain). Probe evidence
for the executed cone: notes/probes/2026-09-15-psl211-planb/PROBE-REPORT.md.

| task | file | landed commits | spec review | quality review | assumptions |
|---|---|---|---|---|---|
| B1 | lib/perm_exchange.v | 8c68c7c, ccebf4f (cosmetic fixes) | compliant (landed statement is the pre-move Local one with the `n` binder and fuel premise deleted, conclusion character-identical; ubnP form with the base case written once; mathcomp-only imports, no HB/infotheo/pgg_smc; registered after lib/perm_uniform.v; no exported statement of psl211_scheme.v or psl211_secrecy.v changed, declaration multiset diff) | approved with fixes, all cosmetic (unused `seq` import, measured; redundant `by` before a closing `exact:`; implicit profile `[T] [U V] _` deliberate but undocumented; one `have`/`case/` pair foldable) | perm_onS, perm_of_eq_card and psl211_private all closed under the global context |
| B2 | instances/psl211/psl211_mixing.v | 5032d4a, ccebf4f (comment fix) | compliant (statements and proof scripts token-identical to pgl27_mixing.v 1055-1112 under 6 4 200 -> 10 2 584, 'I_8 -> 'I_12, Wuni -> psl211_Wuni; psl211_profile and pgg_collusion_bound imported, no cycle, every pairwise name intersection of the six imported modules empty; nothing existing changed) | approved with one blocking comment fix: psl211_endpoint_mixing's second sentence describes sigma^-1 s where the lemma is of sigma s, against transitivity_privacy.v:427/:495 (pgl27's original wording was the correct one and stays); var_dist_prodR duplicated Local in two files, hoist to pgg_collusion_bound.v, does not block; var_dist_fdistmap_prod_mix measured to subsume it in seven lines at the same axiom cost, but yields only the inequality | psl211_endpoint_mixing and psl211_joint_mixing exactly the boolp trio; psl211_word_mixing anchor unchanged |
| B3 | reconstruct/design_privacy.v | e7504cb, 943c021 (review fixes) | compliant (uniform_pair_indep_of_fibers and card_fiber_sum character-identical to the plan's C3 statements; 1631-token comment-stripped diff against probe_c3_bridge.v 20-197 empty, so the %N annotations and the four recorded spellings are preserved by construction; discharge confirmed by About: HX at finset.setTfor X not a proper subset, `U resolving to fdist_uniform_supp, one premise not two, Let P and Let c inlined, R HA HX explicit and X G T implicit; _CoqProject a pure reorder, identical 173-line multiset, no duplicate, nine psl211 lines above the manifest in their pre-move order with mixing before recovery, none of the six new paths pre-registered; psl211_secrecy.v the only Require and it still loads with psl211_colour_view_indep unchanged at the boolp trio; eighteen pre-existing declaration lines identical and shifted +3, nothing existing reworded) | approved with fixes, two blocking, both comment accuracy: card_fiber_sum's "every conclusion is a total, and this is the only step between them" is true of one of the four lemmas below it and is contradicted by uniform_pair_indep_of_class crossing at Htot and Hsplit by cardsID, and uniform_pair_indep_of_fibers' "which is false here" asserts a negative the file does not establish where the accurate claim is that the premise does not give it. Seven cosmetic: header Section 3 list omits pair_fibers_class_sizes, all-caps FUNCTION with no precedent in any tracked .v, the inde_prod_fst paragraph is rejected-alternatives narration naming another file, six lines over 80 columns inherited from the probe against zero before the commit, the _of_ connective against the file's colour_view_indep_fibers and uniform_fdistmap_fiberE (observed and declined, the name is plan-pinned), pr_countE's comment naming the discharged Let c, and design-note row C3 still calling the lemma uniform_prod_inde_fiber. Findings 3, 4 and 5 are defects in plan-supplied text at lines 393-395 and 455-475, fix the plan too. Probe framing, trap relocation and the plan's own 79-column header line were all handled correctly | card_fiber_sum and pair_fibers_class_sizes closed under the global context, pr_countE, uniform_pair_indep_of_class and uniform_pair_indep_of_fibers exactly the boolp trio |
