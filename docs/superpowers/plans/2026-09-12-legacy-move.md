# Legacy move: keep the four instances and the piSMC layer, park the rest

Date: 2026-09-12. Decision by the user: keep PGL(2,7), den Boer, Kim, S_5,
the vendored piSMC layer, and every record and lemma those four need; move
everything else to `legacy/`. Manifest trimmed to the four instances.
Additional keeps by user decision: `reconstruct/s5_nogo.v`,
`reconstruct/gap_dimension.v`, `reconstruct/invariant_profiler.v` (the S_5
no-go, zero axioms), `protocol/card_protocol_posterior.v` (Kim bridge).

## Kept set (91 files)

The dependency closure of instances/{pgl27,denboer1989,kim2025,s5}/*.v and
smc/*.v, computed from .Makefile.rocq.d (87 files), plus the four keeps above.
Listed in docs/style/scan-2026-08-26/P0-P1-CLOSEOUT.md's successor note once
executed; the closure computation is reproducible with the Python snippet in
the session log (roots -> transitive `.vo` deps).

## Legacy set (61 files), destination `legacy/<original path>`

- groups: free_group_ball.v pgg_cycle.v pgg_raag_cartier_foata.v
- instances/abelian (7), instances/cyclic (1), instances/monster (1),
  instances/oc (2), instances/s5x5 (11), instances/star (1: pgg_raag_star.v;
  the orphan rigidity_star_instance.v moves with it)
- protocol: card_protocol.v pgg_uc_security.v
- reconstruct (22): ag_code ag_massey_bridge ag_multiplicative
  combinatorial_rigidity coord_perm_compatible cover_genus0 cover_genus1
  cover_genus2 dropout_witness hyperelliptic_code lagrange massey
  multi_covering pgg_assignment pgg_covering_correctness pgg_dealer_bridge
  pgg_landscape_demo pgg_protocol_landscape pgg_threshold product_threshold
  rs_massey_bridge rs_privacy
- security (9): pgg_abelian_collapse pgg_entropy_security
  pgg_entropy_security_demo pgg_leakage_product pgg_security
  pgg_security_demo pgg_uniform_security pgg_weighted_entropy
  pgg_word_analysis
- manifest: none moved; pgg_analysis_manifest.v and pgg_analysis_client.v
  are trimmed in place (rows 10-17: s5x5 x6, abelian x3, and the s5x5 /
  abelian lemmas in the manifest's later sections).

Also moved: instances/s5x5/*.py and any per-directory certificate artefacts
that belong to a moved instance.

## Rules

1. Logical names do not change. `_CoqProject` gets one `-R legacy/<dir>
   <same root>` line per moved directory; no `From ... Require Import` line
   in any file changes. Legacy keeps compiling in this phase.
2. Statement surface: `scripts/statement_surface.py` before/after must be
   identical after normalising the file-path column (`legacy/` prefix
   stripped), except for the manifest rows deleted in step 4.
3. Comment cross-references in kept files that name a moved file (about 20
   sites in 9 files: algebraic_rigidity.v x6, pgg_security_solver.v x3,
   pgg_raag.v x2, pgg_raag_clique.v x3, card_exchange_pismc.v x2,
   pgg_schreier.v, pgg_collusion_bound.v, pgg_monodromy_profile.v,
   rigidity_s5_instance.v) are rewritten to `legacy/<path>`; comment-only,
   verified with scripts/strip_comments.py.
4. Manifest trim (rocq-prover, Opus): delete the s5x5 and abelian row
   definitions, their documentation rows, the s5x5/abelian lemmas in the
   later sections, the two imports, and the client's Check/Locate lines for
   them. Renumber rows in comments. Gate: statement-surface diff is exactly
   the deleted names.
5. scripts/profile_facade_check_test.py: drop the s5x5 and abelian entries.
6. blueprint/src/content.tex and audit-inventory: regenerate or annotate
   after the move (separate commit).
7. Full `make -j8` EXIT=0 from a captured log; fixpoint pass 0 files.
8. One commit per step; no `--amend`.

## Order

A. `git mv` + `_CoqProject` + build (step 1, 7).
B. Comment cross-refs (step 3).
C. Manifest trim (step 4).
D. Scripts, blueprint, audit-inventory (steps 5, 6).
E. Close-out note: kept/legacy inventory, axiom counts (kept: 4 axioms +
   2 Parameters before this plan; legacy: 15), dead-with-respect-to-the-four
   kept files as reported by the architecture map
   (notes/2026-09-12-post-legacy-architecture-chain.md).
