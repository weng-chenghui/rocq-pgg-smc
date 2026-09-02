# P2 de-duplication design

Date: 2026-09-02. Approved scope: all seven P2 items from
`docs/style/scan-2026-08-26/CONSOLIDATED.md`, executed under the
statement-preserving policy defined below. Baseline commit: `43b7974`.
All line numbers in this spec are as of that commit and drift with
every edit; the implementation plan must re-locate targets by
declaration name, never by line number.

## Goal

Remove the duplicated proofs, mirrored derivations, and dead files
that the 2026-08-26 quality scan cataloged as P2, without changing any
exported statement. Expected net removal is roughly 1,500 to 2,000
lines.

## Policy (user decisions, 2026-09-02)

1. **All seven punch-list items are in scope**, split into work items
   W1 to W7 below.
2. **Statement-preserving.** Every exported `Definition`, `Lemma`,
   `Theorem`, `Corollary`, `Record`, and `Fixpoint` keeps its exact
   name and statement. Only proof bodies, file-local material
   (`Let`, `Local`), and dead files change. New shared machinery may
   ADD exports; nothing existing is reshaped. Statement reshaping
   belongs to the queued P4 wave.
   - One deliberate exception class: W7's `mk_player_aprocs` item
     edits `Definition` BODIES (not statements). See W7 for its
     containment rule.
3. **Hard deletes, no deprecation aliases.** The paper and notes in
   `infotheo-pgg` cite none of the affected names (verified by grep
   2026-09-02).
4. **Untouchables.** Vendored `smc/*` and `lib/proba_entropy_ext.v`
   are not edited. The orphan files `instances/star/
   rigidity_star_instance.v`, `security/debug_morph.v`, and
   `security/pgg_schreier_test.v` are not edited (exception: the
   orphan `protocol/pgg_program.v` is deleted by W4, per the punch
   list).

## Corrections to the punch list (found while grounding this spec)

The scan's line ranges predate the P1 comment campaign and no longer
land; more substantively:

- The raag duplication mechanism is not "delete + import". The copies
  in `groups/pgg_raag.v` are `Let`-bound inside `Section
  raag_gen_reflect` and therefore invisible outside it; that is why
  `groups/pgg_raag_cartier_foata.v` restated them (its header says
  so). The fix must hoist first (W1).
- `security/pgg_schreier.v` and `security/pgg_schreier_weighted.v`
  share ZERO exported declaration names. The pair is a semantic
  near-duplicate; the fix is shared proof machinery, not name merging
  (W6).
- `instances/s5x5/s5x5_analysis.v` carries 76 pile1/pile2 sites and
  belongs in the pile-doubling item; `instances/s5x5/s5x5_trace.v`
  carries zero and does not (W2).
- `protocol/pgg_program.v` is already absent from `_CoqProject`;
  deleting it changes no build output (W4).

## Work items

### W1 — raag foata infrastructure hoist (~600 lines)

`groups/pgg_raag.v` proves ~25 lemmas about `foata_pairs` /
`foata_nf` / `dv_leq` as `Let`s inside `Section raag_gen_reflect`
(`foata_pairs_split'`, `foata_pairs_vals`, `size_foata_pairs'`,
`foata_depth_at_bigop`, `foata_nf_swap_adj`, `dv_leq_trans`, ...).
`groups/pgg_raag_cartier_foata.v` restates them as exported `Lemma`s
in `Section foata_infrastructure` (142 exported declarations in the
file overall), mostly under the same names, sometimes differing by a
prime (`size_foata_pairs` vs `size_foata_pairs'`).

Fix:
1. In `pgg_raag.v`, move the shared lemmas out of
   `Section raag_gen_reflect` into a new top-level section placed
   after the `foata_pairs`/`foata_nf` definitions, as exported
   `Lemma`s. This is possible because each takes its commutation
   relation `crel : nat -> nat -> bool` as an explicit argument and
   uses no section variable.
2. Name and statement reconciliation rule: where the two files'
   variants differ, the `pgg_raag_cartier_foata.v` exported form wins
   (it is the general, letter-unbounded restatement), and
   `pgg_raag.v`'s internal proofs adapt to it. Exported names in
   `pgg_raag_cartier_foata.v` do not change.
3. Delete the restatements in `pgg_raag_cartier_foata.v`; its
   remaining proofs consume the identical names by import. A lemma
   used only inside `raag_gen_reflect` and genuinely weaker than the
   cartier_foata form may stay behind as a `Let`; each such survivor
   is recorded in the commit message.

Both edits land in ONE commit (the two files would otherwise export
clashing names mid-sequence).

### W2 — s5x5 pile1/pile2 doubling

Mirrored pile1/pile2 derivations in `instances/s5x5/`:
`s5x5_models.v` (109 sites), `s5x5_analysis.v` (76), `s5x5_mixing.v`
(58), `s5x5_exec.v` (40). The pile embeddings live in `s5x5_pile.v`.

Fix: a `Section pile_generic` parametric over the pile embedding
(one section per file, or a shared one in `s5x5_pile.v` where the
content is file-independent). The existing pile1/pile2 exported names
are re-established as instantiations with byte-identical statements.
Where a mirrored pair differs beyond the embedding, it is out of this
item's scope and left in place (recorded in the commit message).

### W3 — cover_genus1/2 concrete rederivations

`reconstruct/cover_genus1.v` defines both a concrete `Section genus1`
derivation and the generic `Section higher_genus`;
`reconstruct/cover_genus2.v` rederives concretely again. Fix: keep
every exported statement in both files; replace the concrete proof
bodies by instantiating `higher_genus` at g:=1 and g:=2. If a
concrete statement turns out NOT to be an instance of the generic
section (e.g. a strictly sharper constant), it keeps its concrete
proof and is recorded; the item does not weaken statements to fit.

### W4 — dead files

1. `protocol/pgg_correctness.v`: remove from `_CoqProject` and
   delete. Its theorems re-derive `pgg_interface` results; the only
   reference is a comment in `protocol/card_exchange_pismc.v`
   ("verified in pgg_correctness.v"), which is rewritten to point at
   the surviving `pgg_interface` theorems it actually means.
2. `protocol/pgg_program.v`: orphan (not in `_CoqProject`); delete
   the file and rewrite the comment in `card_exchange_pismc.v` that
   mentions it.

W4 runs first: it is cheap and shrinks the tree for every later gate
run.

### W5 — rigidity cluster via RSCodeWitness

The built rigidity instances `instances/abelian/
rigidity_abelian_instance.v`, `instances/cyclic/
rigidity_cyclic_instance.v`, `instances/oc/rigidity_oc_instance.v`
each hand-roll the RS-code hypothesis block that
`reconstruct/cover_genus0.v` already packages as `RSCodeWitness` +
`genus0_covering_witness`. Fix: each file builds its witness record
once and re-derives its existing exported statements from it;
statements unchanged. Other rigidity files (kim, monster, s5, s5x5)
are inspected by the implementer and included only where the same
block appears verbatim; the orphan star instance is untouched.

### W6 — schreier / schreier_weighted near-duplication

`security/pgg_schreier.v` and `security/pgg_schreier_weighted.v`
prove ~5 lemma pairs that are the same argument modulo weighting
(enumerated in `docs/style/scan-2026-08-26/security-B.md`; the plan
must pull the exact pair list from there). Fix: factor the shared
spectral-bound machinery into a section or small shared file both
import; both files' exported names and statements unchanged. If the
generalization forces a statement change, the pair is skipped and
recorded (that reshaping is P4/P2-follow-up material).

### W7 — tail

1. `instances/kim2025/kim_secrecy.v` re-proved by applying
   `instances/denboer1989/denboer_secrecy.v`'s lemma, the pattern
   `kim_trace.v` already uses. Exported name and statement kept.
2. `security/pgg_collusion_bound.v`: `collusion_bound_unconditional`
   re-proved as the k:=1 corollary of `collusion_bound_k`; both
   theorems stay exported. If the k-general section's hypotheses do
   not specialize cleanly to the unconditional statement, skip and
   record.
3. The genus1 lemma pasted with proof into
   `reconstruct/pgg_protocol_landscape.v` imports the original from
   `reconstruct/cover_genus1.v` instead.
4. `pow2_split` (identical `Let` + proof in
   `instances/pgl27/pgl27_models.v` and
   `instances/pgl27/pgl27_word_privacy.v`): defined once, as an
   exported `Fact` in whichever of the two files the other already
   imports (or their common import), both `Let`s deleted.
5. `groups/pgg_raag_clique.v` `spos`/`sneg` mirror lemma pairs:
   factored through a parametric helper where the mirror is exact;
   skipped and recorded where not.
6. `mk_player_aprocs` helper for the 125 `mk_aproc (exchange_player
   ...)` sites across 16 protocol/instance files. This edits
   `Definition` bodies. Containment rule: the helper must produce a
   term CONVERTIBLE to the old body; after rewriting a file, if any
   downstream proof that unfolds those definitions breaks and cannot
   be fixed by a local, obvious adaptation (e.g. one `rewrite
   /mk_player_aprocs`), the FILE is reverted and recorded as skipped.
   This is the highest-risk tail item and lands last.

## Verification gates (every wave)

1. **Statement-surface gate** (new): `scripts/statement_surface.py`
   extracts, for every `.v` file in `_CoqProject`, the (kind, name,
   normalized statement text) of every exported declaration
   (`Definition|Lemma|Theorem|Corollary|Record|Fixpoint|Instance|
   Axiom|Notation`, excluding `Let` and section-`Variable`/
   `Hypothesis` context). Gate: after-surface = before-surface, minus
   the two W4 files' entries, plus new shared-machinery additions;
   NO existing entry changes. The before-surface is regenerated on
   demand from the pre-wave git commit (`git show <commit>:<file>`),
   so it needs no stored snapshot and survives session breaks.
   The script is committed with the campaign.
   Known limitation, accepted: the extractor compares statement TEXT
   after whitespace normalization; a statement rewritten to a
   convertible but textually different form would be flagged (good,
   that is a policy violation under this spec) and a semantically
   different statement with identical text cannot occur.
2. **Full rebuild** EXIT=0, judged from captured build logs (the
   compile-count hook decorates tool output; logs are the truth).
3. **Admitted/Axiom parity**: 0 `Admitted`, and exactly the 16
   pre-existing `Axiom` declarations, before and after every wave.
4. **Net line count** must decrease for every work item (except the
   statement_surface.py addition itself).
5. Comment prose added by this campaign follows the statement-comment
   rule (fact + position); no status or process narration.

## Team and sequencing

Controller fans out one implementer per work item, sequentially by
item (waves): **W4 → W1 → W2 → W3 → W5 → W6 → W7**. Opus for the
proof-adaptation items (W1, W3, W5, W6), Sonnet for the mechanical
ones (W2, W4, W7.1-7.5), Opus for W7.6. After each item: the
controller runs the surface gate + rebuild centrally, then one Opus
reviewer audits the diff against this spec before the commit is
accepted. One commit per work item (W7 may split into its six
sub-items). Agents stage only named files, never `git add -A`.
Prover-agent audits every ~5 minutes per the standing workflow rule.

## Out of scope

P3 notation/action packaging, P4 statement reshaping and
section-hoisting, P5 hygiene sweeps, all vendored files, the orphan
star/debug/test files (except the W4 delete), and any change to
exported statement text.
