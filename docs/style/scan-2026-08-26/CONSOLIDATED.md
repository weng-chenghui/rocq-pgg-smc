# Consolidated scan report — 2026-08-26

Twelve read-only scanners (11 directory batches + 1 cross-cutting) over
the 157 tracked `.v` files, keyed to `docs/style/quality-catalog.md`.
Per-batch detail lives in the sibling files of this directory. Roughly
900 raw findings; this file ranks them by leverage. Nothing has been
fixed; this is the punch list.

## Adjudication: the comment-tag question

Scanners disagreed on whether `@intent:`/`@composes:`/`@main <label>:`
tags are compliant (security-A said yes; protocol, reconstruct, and
denboer-kim flagged them). Ruling per the user's global statement-comment
rule: ALL label scaffolding is banned — `Kind:`, `What:`, `Why:`,
`Used by:`/`Used-by:`, `Naming:`, `Why waived:`, and the `@`-prefixed
variants alike. What survives is the prose inside the slots, folded into
one to three declarative sentences (fact + position). Cross-reference
content moves to non-rendered `(* ... *)` comments.

## P0 — Correctness-adjacent (small count, fix first)

1. `reconstruct/pgg_threshold.v:247-254` — `Theorem secure_edge_bound
   : ... -> True`: a vacuous theorem presented as a security bound.
2. `groups/pgg_raag_path.v:10-14` — header asserts the RAAG
   presentation for what is provably S_(m+2), and an "iff" proved only
   one way. `groups/pgg_raag_clique.v:1231-1247` — "stated as an
   axiom" narration for a fact proved two lines later.
   `reconstruct/pgg_deck_pairing.v:58-74` — one comment describes the
   wrong lemma; another claims a hypothesis the proof discards.
3. ~35 provably false "Used by:"/header claims (free_group_ball 9,
   clique 6, weval_inj 5, perm_uniform 1, raag_path 2 incl. a
   nonexistent lemma name, posterior doc/name mismatch, ...).
4. Axiom/Conjecture citations: `protocol/pgg_uc_security.v:86`
   Conjecture without UC-literature citation;
   `security/pgg_entropy_security_demo.v:160` and
   `instances/s5/rigidity_s5_instance.v:268` axioms with no (or
   informal, far-away) citation; `s5_mixing.v:188` certificate pointer
   should be a one-line fixed-hash citation above the Axiom.

## P1 — Comment layer (R2), tree-wide, the cheapest big win

~800+ stacked-template instances across every directory (worst:
pgg_security_solver 25, s5_nogo ~26 four-slot, five_card_exec 45+23,
pgg_raag all 28 + 65 undocumented, pgl27_mixing 76/76 undocumented).
Both failure modes: template bloat AND total absence. Also: process
narration in file bodies ("Amended work package A (user-approved
2026-08-13)", "Request 5.3", audit ticket "G001"), a ~200-line "Temp
note:" chat transcript in vendored smc_session_types.v, "Phase 1
Test" section names. Fix vehicle: `formal-comment-review` passes, one
directory at a time; the good prose already trapped in slots survives.
Template-free models to imitate: cover_tradeoff.v §1-3,
dropout_witness.v record fields, invariant_profiler.v content,
kim_run.v, pgg_leakage_witness.v, rs_privacy.v (proof strategy in
non-rendered comments), pgl27_orbit.v.

## P2 — Duplication (R9), ranked by duplicated line count

1. `pgg_raag_cartier_foata.v:48-655` == `pgg_raag.v:1161-1856` (~600
   lines verbatim; the sibling's header admits it) -> delete + import.
2. s5x5 intra-file pile1/pile2 doubling: s5x5_mixing (~140-line
   mirrored derivation), s5x5_models (~20 pairs), s5x5_exec (~23
   pairs), s5x5_trace -> Section pile_generic over the embedding.
3. cover_genus1.v/cover_genus2.v: two ~250-line concrete rederivations
   of the generic higher_genus section cover_genus1.v itself defines ->
   instantiate at g:=1,2.
4. Whole-file deletes: `protocol/pgg_correctness.v` (built; re-derives
   6 pgg_interface theorems; referenced only by a comment) and
   `protocol/pgg_program.v` [orphan].
5. Rigidity cluster (abelian/cyclic/oc/star): RS-code hypothesis block
   4x + complexity/tradeoff tail 5x — while `cover_genus0.v` already
   provides the factoring (RSCodeWitness + genus0_covering_witness),
   unused by all of them.
6. `pgg_schreier.v` <-> `pgg_schreier_weighted.v` 5-lemma pair ->
   shared spectral-bound interface.
7. kim_secrecy == denboer_secrecy (alias it, as kim_trace already
   does); s5/s5x5 run+exec cross-pairs; collusion_bound_unconditional
   = collusion_bound_k at k=1; landscape genus1 lemma pasted with
   proof; `mk_aproc (exchange_player ...)` boilerplate 125x ->
   mk_player_aprocs helper; clique spos/sneg mirror pairs; pow2_split
   Let x2.

## P3 — Notation and action packaging (E3)

1. PRIMARY: package rho as a mathcomp action. All three `is_action`
   laws are already proved (endpointM, endpoint1, endpoint_inj);
   `Canonical rho_action` inherits orbit/'C/astab/[transitive ...]
   vocabulary — which pgg_security_demo.v hand-rolls and s5x5_pile.v/
   pgl27_group.v partially reinvent. Bonus: the thrice-repeated Hreg
   regularity hypothesis IS `'C[s | rho_action] = 1`.
2. Scoped notations: word_eval (232 uses), endpoints (167); generator
   access `'g_i` for `tnth (pgg_sigmas M) i` / `tnth <fam>_gen_tuple i`
   (14x in raag_path alone); seatT for `'I_(pi_T' (mp_PI p)).+1`
   (51x in the manifest); run-context bundles in
   pgg_execution_plug/pgg_observed_execution (20-30x each).
3. Named definitions instead of respelled shapes: nswap/swap_at/
   swap_chain (raag files), mathcomp `commute` for raw x*y=y*x,
   `ord0` for `Ordinal (isT : 0 < T)`, path_edge, `let cs :=` in
   ar_protocol_correct.
4. Inventory hygiene: unify the family-shorthand convention (pgl27_M
   non-Local vs everyone else's per-file Local); finish the
   RAAGDesc/GroupDesc rename (delete the only-parsing shim); delete
   the dead Reserved Notations in vendored smc_interpreter.v; make
   masksvec/othermasks/"[> ps ]" Local/scoped.

## P4 — Statement shape (E1/E2/E4): section-hoisting and named premises

Sharpest E1 cases (hoist into dedicated Sections):
transitivity_privacy profile_view_indep (10 params/14 lines);
pgl27_profile_privacy x2 (9 premises, shared verbatim);
pgl27_mixing mixing_bound_gen; trace_secrecy pair (+ shared cancel
premise); word_analysis comm_pair_count_full_comm;
ar_protocol_correct + genus0_secret_invariant (shared G_stable shape);
pgg_covering_correctness; sharing_framework recon_monodromy_correct;
kim files eps-triple (five_card_models.v shows the correct pattern);
perm_uniform two clusters; s5_mixing (R : realType) x8; raag_path
0<m x4 incl. proof-term-in-statement Ordinals; abelian_word_collapse
abelian G x6; smc_interpreter rstep_disjoint [vendored].
E4 named predicates: coalition bound (#|C| <= t / 0 < #|C| — 10+
sites), regular_action/semiregularity, DoublyStochastic Q,
coalition_below_threshold, weval_inj hypothesis, fresh_pair +
perm_target (perm_uniform), G_stable, sw_security_bound,
recoverable_bits fragment, indep_set.
E2: Implicit Types absent essentially everywhere it would pay
(perm_uniform, raag files, graded_resource...).

## P5 — Hygiene sweeps (mechanical or small)

- R5: numerical occurrence selectors (schreier_weighted:410,
  security.v:121,135), brace blocks (hyp_priv_surj x8, pgg_oc_param
  x4), 2-subgoal bullets (word_analysis:343, rs_privacy:155,
  s5_nogo:220), by+exact double closers (raag_path x5),
  have->-by[] roundtrips (abel_profile x2, cyclic x1), funext-on-ffun
  (sample_adapter x2).
- R7: non-Local Open Scope in 5 reconstruct files; bare auxiliary
  lemmas -> Local/Fact (raag_path 10, others).
- R3: exported API renames first (raag_Hcomm mixin field,
  Hcard_remaining lemma); then the H1/H2/H3-in-conclusion cases
  (kim_input_privacy); ~25 Hxxx batch-wide.
- R8: size->card (free_group_ball), cycle_ namespace squat, _is_->E
  suffix (posterior), lemma_3_4/3_5 paper numbers [vendored,
  candidate-only], rs1/rs2, cta_*/sp_*.
- R6: boolp.funext qualified 14x across 3 files;
  Order.POrderTheory.* sites need per-site verification.
- R10: smc_session_types Temp-note block (~200 lines) + scratch test
  sections + ~500-line unreferenced apparatus [vendored — decide
  policy first]; two orphaned *_cryptographically_secure sections
  (both rigidity files); unused Lets (pgg_raag_star x3, gT);
  hyperelliptic empty genus2 section; commented-out monologue in
  pgg_raag.v; orphan files debug_morph/pgg_schreier_test (delete
  candidates); prescribed0/collusion_uniform dead exports;
  dead cartier_foata Section.
- R1: ~700 over-80 lines tree-wide; the majority sit inside P1's
  template comments and vanish with that fix.

## Vendored-file policy question (user decision needed)

smc/ (4 files) and lib/proba_entropy_ext.v were vendored VERBATIM for
provenance. The scan found real issues inside them (Temp-note block,
draft-prose comment, dead apparatus, paper-number names). Options:
(a) keep verbatim, record findings only; (b) clean them and drop the
verbatim claim from their provenance headers (they are project-owned
now — the fork will not supply updates). Recommendation: (b) for the
egregious dead weight (Temp note, scratch sections), (a) for the rest
until the piSMC layer is next touched.

## Exemplary files (patterns to propagate)

kim_run.v, five_card_models.v, pgg_leakage_witness.v,
pgg_fdist_rV_indep.v, pgg_cyclic_cut_leakage.v, cover_tradeoff.v
§1-3, coord_perm_compatible.v, lagrange.v, rs_privacy.v,
pgl27_orbit.v, manifest/pgg_analysis_manifest.v (mechanical
discipline), pgg_schreier.v's Sections, s5x5_run.v's proof factoring.
