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
4. DONE (commit 21072d0, see the A3 section below): axiom citations in
   rigidity_s5x5_instance.v and rigidity_monster_instance.v; the
   s5x5 Galois-closure axiom turned out to have no true source.
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

Naming question from the W7.6 audit, RESOLVED 2026-09-03: the user
ruled that MathComp style is the criterion, and under it
`mk_player_aprocs` loses to `player_aprocs`. Upstream `mk*` names
(`mkseq`, `mktuple`, `mkset`, `mkfun`) are constructors that turn a
function into the canonical enumeration over its whole domain; a fixed
family mapped over a selected index list is an image, which MathComp
names as a noun (`codom`, `perm_on`). The underscore spelling is also
off-pattern upstream (only `mk_monic`, `mk_path`, `mk_sequence` in the
whole tree). Renamed across the definition and 12 files; the
statement-surface diff is exactly the one definition entry (all call
sites sit in Definition bodies), context hash unchanged.

P5 partial, executed early by user order 2026-09-03: deleted the two
orphan files security/debug_morph.v and security/pgg_schreier_test.v
(never in _CoqProject, both contained Admitted) and the dead
RSCodeWitness apparatus at the tail of reconstruct/cover_genus0.v
(Record RSCodeWitness, Arguments rsw_auto, genus0_covering_witness;
zero consumers tree-wide, and the record-witness pattern measured
net-negative in P2 W5). Statement-surface diff is exactly the two
cover_genus0.v removals; the orphans were never in the surface. The
vendored smc/ quartet and lib/proba_entropy_ext.v stay verbatim by
the same order.

## A3 axiom citations (2026-09-12)

Deferred item 4 executed, comment-only (strip_comments.py identical against
HEAD for both files; full rebuild EXIT=0, 12 files; fixpoint 0).
Sources verified through research-kb (slices atlas-v3-monster-group-page,
wilson2001-monster-hurwitz, gkkl2007-presentations-finite-simple-groups,
braden-disney-hogg-2022-brings-curve).

rigidity_monster_instance.v: monster_n cites the ATLAS (index of 2.B =
97,239,461,142,009,186,000); monster_sigmas cites Aschbacher-Guralnick 1984
(2-generation of all finite simple groups) and Wilson 2001 (explicit
(2B,3B,7B) pair for M); monster_covering cites Wilson 2001 (M is a Hurwitz
group, so a Galois cover of P^1 with deck group M exists);
monster_genus0_klein cites Klein 1884. The three L* axioms have no
literature source and now say so.

Two correctness findings surfaced by the audit, recorded in the comments
and NOT fixed in code (both change what the instances claim):

1. Monster: monster_weval_inj_Lstar and monster_perm_endpoint_inj_Lstar
   jointly force 2^L* <= N (machine-checked in a scratch file: search
   space = 2^L* by weval_inj_search_space, injects into N positions by
   card_in_imset + max_card). The header's L* = 67 with 2^67 > N and
   epsilon = 0 therefore contradicts the file's own axioms; the direct
   epsilon 2(N - 2^L*)/N is at least 2(N - 2^66)/N ~ 0.48 and is never 0
   since N is not a power of two (direct_eps truncates by nat subtraction
   otherwise). pgg_entropy_security_demo.v's Section monster_perfect
   assumes 2^L* = N (Lstar_sat), unsatisfiable at the ATLAS degree, so
   its "perfect security" lemmas are vacuous there.
2. s5x5: s5x5_covering_data (genus 173, 6 branch points, ramification
   29144) is realised by no S_5 x S_5 Galois cover of P^1: each branch
   point of a Galois cover contributes >= |G|/2 = 7200, so 6 need >= 43200;
   and genus 173 admits no signature at all over the element orders of
   S_5 x S_5 (checked by enumeration for r = 3, 4, 5 and genus 173..180).
   s5x5_inverse_galois_realised therefore asserts a false statement under
   its stated reading. The two-Bring's-curve axiom s5x5_multi_realised is
   sound (Edge 1978; Wiman 1895) and now cites them. Related looseness:
   the s5 record's 4 branch points should be 3 for the (2,4,5) Bring's
   cover; the framework's CoveringData only constrains n_branch <=
   total_ramif, so neither record is rejected by the kernel.
