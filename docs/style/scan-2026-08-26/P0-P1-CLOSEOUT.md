# P0 + P1 close-out — 2026-08-26

P0: 11 per-file commits (fix(P0): ...). All ten correctness-adjacent
items fixed after independent claim verification: the vacuous
secure_edge_bound theorem deleted; the S_(m+2)-vs-RAAG header and the
iff overclaim corrected; misleading axiom narration removed; the
deck-pairing comment bugs fixed; four axiom-class declarations now
carry citations/evidence pointers. New finding stated honestly in the
code: pgg_uc_security's Conjecture is vacuous as stated (ideal_exec
discards its Simulator).

P1: 9 batch commits (style(P1): ...). ~2,477 declaration comments
rewritten or written across 145 files; zero template tokens remain
outside vendored files; ~85 provably false "Used by:" claims deleted;
all process narration/ticket IDs removed. Verification: every file
mechanically proven comment-only against HEAD (scripts/
strip_comments.py); full rebuild 153/153 EXIT=0, then incremental
rebuild after review fixes 88 files EXIT=0. An Opus sampling review
(42 mandatory + 13 extra samples, numeric claims checked against
statements) returned COMMIT WITH FIXES; all 21 mandated fix sites
applied. Along the way agents found and fixed 9 additional factually
wrong comments beyond the scan's list.

Deviation from formal-comment-review skill: commits are per directory
batch, not per file (11-agent fan-out; per-file commits would have
raced). Undo granularity is per batch.

## Deferred follow-ups (not part of P0/P1)
1. DONE (commit 41fa5ed): "sheet" -> "card position" unified in
   comment prose, 191 replacements / 38 files; covering-theory sense
   kept (multi_covering, cover_tradeoff Klein bound, rigidity_s5x5
   Bring's-curve section); identifier glosses per file.
2. Docstring carrier policy: batches disagreed on (** *) coqdoc vs
   (* *) plain (net 3399 -> 3154 docstrings). Pick a policy per
   generated-docs intent.
3. Banner-box alignment: ~60 new lines off modal box width in 16
   files; one orphan half-line (manifest:855). Mechanical sed pass.
4. Two axiom-citation gaps flagged in rigidity_s5x5_instance.v
   (s5x5_inverse_galois_realised, s5x5_multi_realised) — need real
   sources, not fabricated ones.
5. Vendored files (smc/, lib/proba_entropy_ext.v) untouched pending
   the provenance-policy decision.

## P2 close-out (2026-09-03)

Spec: docs/superpowers/specs/2026-09-02-p2-deduplication-design.md
(adversarially audited before execution; four spec-wrong punch-list
items corrected there). Plan: docs/superpowers/plans/
2026-09-03-p2-deduplication.md. Gate: scripts/statement_surface.py —
the cumulative exported-surface diff over the whole campaign is
exactly the authorized set (W4's 8 removals; W1's 26-entry relocation
with the not_sorted_descent' rename; kim_ccd removed; pow2_split and
mk_player_aprocs added). Full rebuild EXIT=0; Admitted 0 / Axiom 16
throughout. Net **-905 lines** (2,011 insertions / 2,916 deletions,
26 files).

Per item:
- W4 dead files: DONE (97f5836). pgg_correctness.v + orphan
  pgg_program.v deleted; false cross-reference comment removed.
- W1 raag foata hoist: DONE (8e36c18). 26 section-local Lets exported
  from pgg_raag.v's new Section foata_infrastructure; cartier_foata's
  statement-identical restatements deleted; dead foldl_maxn_shift
  deleted rather than exported. Reviewer fixes folded in (header
  inventory entry, three restored load-bearing comments).
- W2 s5x5 pile mirrors: PARTIAL (94764b7). 2 of 20 pairs factored
  (word_eval equivariance + two-valued TV gap in s5x5_mixing); the
  rest measured net-positive and left in place — the promising floor
  pairs were implemented, compiled, and measured at +14/+18 before
  reverting. Remaining candidate with real mass:
  s5x5_exec_pile1_bound/2 (~42-line proofs, unattempted).
- W3 genus coverings: DONE for genus 1 (c369e02): the covering trio
  instantiates higher_genus; RH inputs keep concrete proofs.
  cover_genus2.v is NOT an instance (its data fixes 5 branch points
  where higher_genus at g:=2 forces 4 — probed with a positive
  control); untouched by design.
- W5 rigidity via RSCodeWitness: ALL SKIPPED on measurement — the
  routing compiles but costs +2/+3 lines per file (the 11 hypotheses
  must stay; nothing intermediate exists to delete). RSCodeWitness /
  genus0_covering_witness remain dead code tree-wide: P5 candidate to
  delete or document.
- W6 schreier pair: DONE for pairs 1-4 (bc5a0e4) via a shared
  geometric_rate section (Local lemmas reached by qualified name from
  the weighted file). Pair 5 (security_monotone) skipped: residual
  shared content after 1-4 is one le_trans step; helper measures +5.
- W7 tail: ar_genus1_gap2 delegation (cb16bdd); single pow2_split
  Fact (95f5575); kim_mechanism := denboer_mechanism (cda9557;
  kim_indep kept — kim_trace.v consumes it); spos/sneg pascal_core
  factored via parity-generic lemma, unfold pair skipped (24840c4);
  mk_player_aprocs helper, -58 lines / 12 files, zero proof
  adaptations (43cd13b) — mapping over a LITERAL seat list is
  definitionally convertible (only enum 'I_n fails to reduce); the 40
  in-statement mk_aproc sites and singleton definitions left as-is.
- W7.2 collusion_bound: SKIPPED per corrected spec (the unconditional
  theorem is not the k:=1 case; ideal references and carriers differ).

Measured law of the campaign (three independent confirmations, W2/W5/
W6): parametric factoring pays only when the duplicated PROOF BODIES
are >= 10 lines per member; section/hypothesis restatement overhead is
15-29 lines and qualified-name call sites eat one-liner savings.

Open naming question from the W7.6 audit: `mk_player_aprocs` composes
with the vendored `mk_aproc`, but repo precedent for lifting a helper
over a seq pluralizes without the prefix (`erase_aproc` ->
`erase_aprocs`), suggesting `player_aprocs`. Rename is one line plus 12
call sites; candidate for the P3 naming wave.
