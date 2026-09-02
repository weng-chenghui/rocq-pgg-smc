# P2 de-duplication design

Date: 2026-09-02. Approved scope: all seven P2 items from
`docs/style/scan-2026-08-26/CONSOLIDATED.md`, executed under the
statement-preserving policy defined below. Baseline commit: `43b7974`.
Adversarially audited against the code 2026-09-02; all audit findings
are folded in below. All line numbers are as of the baseline and
drift with every edit; the implementation plan must re-locate targets
by declaration name, never by line number.

## Goal

Remove the duplicated proofs, mirrored derivations, and dead files
that the 2026-08-26 quality scan cataloged as P2, without changing any
exported statement. Expected net removal is roughly 1,200 to 1,800
lines.

## Policy (user decisions, 2026-09-02)

1. **All seven punch-list items are in scope**, split into work items
   W1 to W7 below. Two sub-items were found unsound during the audit
   and are recorded as skipped inside W7 rather than silently dropped.
2. **Statement-preserving.** Every exported `Definition`, `Lemma`,
   `Theorem`, `Corollary`, `Record`, and `Fixpoint` keeps its exact
   name and statement. Only proof bodies, file-local material
   (`Let`, `Local`), and dead files change. New shared machinery may
   ADD exports; nothing existing is reshaped. Statement reshaping
   belongs to the queued P4 wave.
   - Deliberate exception class, granted to exactly two sub-items:
     `Definition` BODIES (never statements) may change in W7.1
     (mechanism alias) and W7.6 (`mk_player_aprocs`), each under its
     own containment rule below.
3. **Hard deletes, no deprecation aliases.** The paper and notes in
   `infotheo-pgg` cite none of the affected names (verified by grep
   2026-09-02).
4. **Untouchables.** Vendored `smc/*` and `lib/proba_entropy_ext.v`
   are not edited (`mk_aproc` is DEFINED in vendored
   `smc/smc_session_types.v` and stays there; only its call sites in
   non-vendored files change). The orphan files
   `instances/star/rigidity_star_instance.v`,
   `security/debug_morph.v`, and `security/pgg_schreier_test.v` are
   not edited (exception: the orphan `protocol/pgg_program.v` is
   deleted by W4, per the punch list).

## Corrections to the punch list (grounding + audit, 2026-09-02)

The scan's line ranges predate the P1 comment campaign and no longer
land; more substantively:

- The raag duplication mechanism is not "delete + import". The copies
  in `groups/pgg_raag.v` are `Let`-bound inside `Section
  raag_gen_reflect` and invisible outside it; the fix must hoist
  first (W1).
- `security/pgg_schreier.v` and `security/pgg_schreier_weighted.v`
  share ZERO exported declaration names; the pair is a semantic
  near-duplicate (W6), and the shared content is elementary real
  arithmetic over a rate `lam`, not spectral machinery.
- The s5x5 pile embeddings live in `s5x5_mixing.v` (`widen5to10`,
  `rshift5to10`), NOT in `s5x5_pile.v`; `s5x5_analysis.v`'s pile
  declarations are a one-line re-export facade and are excluded;
  `s5x5_trace.v` carries zero pile sites and is excluded (W2).
- `cover_genus1.v`'s generic `Section higher_genus` CONSUMES the
  Riemann-Hurwitz facts as hypotheses; the concrete `genus1_hurwitz`
  and `genus1_ramif_ge_nbr` are its inputs, not its instances (W3).
- `collusion_bound_unconditional` is NOT `collusion_bound_k` at k:=1:
  the ideal references differ (uniform law on `'I_N` vs a pushforward
  on `k.-tuple 'I_N`), the bridge `ideal_marginal_uniform` exists
  only on the unconditional side, and both proofs are already
  two-line DPI steps. The sub-item is skipped (W7.2).
- The "landscape genus1 paste" is INTRA-file:
  `pgg_protocol_landscape.v`'s `ar_genus1_gap2` copy-pastes
  `genus1_universal_option` from the same file (W7.3); no new import.
- `protocol/pgg_program.v` is already absent from `_CoqProject`;
  deleting it changes no build output (W4).
- The `mk_aproc` boilerplate spans 14 files, and 40 of the 125 sites
  sit inside exported Lemma STATEMENTS, which the policy forbids
  touching (W7.6 scopes them out).

## Work items

### W1 — raag foata infrastructure hoist (~600 lines)

`groups/pgg_raag.v` proves 27 declarations about `foata_pairs` /
`foata_nf` / `dv_leq` as `Let`s inside `Section raag_gen_reflect`
(baseline lines 1211-1897; 26 lemmas plus the `Definition`
`foata_inv`). `groups/pgg_raag_cartier_foata.v` (which imports
`pgg_raag`) restates all 27, statement-identical, in its
`Section foata_infrastructure` — 26 as exported `Lemma`s/`Definition`
plus `foldl_maxn_shift`, which is a `Let` in BOTH files.

The property licensing the hoist: none of the 27 uses a section
variable (`dv_leq` itself is top-level in `pgg_raag.v`, well before
the section). Seven of them take no commutation-relation argument at
all; that is fine, they are still section-free.

Fix:
1. In `pgg_raag.v`, move all 27 out of `Section raag_gen_reflect`
   into a new top-level section placed after the
   `foata_pairs`/`foata_nf` definitions, as exported declarations
   (`foldl_maxn_shift` included, promoted to exported). The clean
   boundary is exactly the block before `comm_nat_sym`, the first
   `Let` that touches a section variable.
2. Renames: all 27 statements are textually identical between the
   files, so reconciliation reduces to three primed/unprimed name
   pairs, where the cartier_foata (unprimed) name is adopted:
   `size_foata_pairs'` -> `size_foata_pairs` and
   `foata_descent_comm'` -> `foata_descent_comm`.
   EXCEPTION: `not_sorted_descent'` KEEPS its prime, because
   `pgg_raag.v` already exports a different `not_sorted_descent`
   (over `seq nat`, at baseline line 641); cartier_foata's
   `not_sorted_descent` (over `seq (nat * nat)`) is deleted and its
   call sites retarget to the primed name.
   (`foata_pairs_split'` is primed in both files and keeps its prime.)
3. Delete `Section foata_infrastructure` in
   `pgg_raag_cartier_foata.v`; its remaining proofs consume the
   hoisted names by import, modulo the `not_sorted_descent'`
   retarget.

Both edits land in ONE commit (the two files would otherwise export
clashing names mid-sequence).

### W2 — s5x5 pile1/pile2 doubling

Mirrored pile1/pile2 derivations in `instances/s5x5/`:
`s5x5_models.v` (109 occurrences / 20 declarations),
`s5x5_mixing.v` (58 / 14), `s5x5_exec.v` (40 / 6).
Excluded: `s5x5_analysis.v` (re-export facade),
`s5x5_trace.v` (zero sites).

Fix: one `Section pile_generic` PER FILE, parametric over the four
things a mirrored pair actually varies in: the embedding
(`widen5to10` / `rshift5to10`), the pile-uniform fdist
(`fdist_uniform_pile1` / `fdist_uniform_pile2`), the TV-bound lemma,
and the uniform-distance lemma. The shared-section-in-`s5x5_pile.v`
option is withdrawn: `s5x5_mixing.v` imports `s5x5_pile`, so a
section there mentioning `widen5to10` would be an import cycle.
The existing pile1/pile2 exported names are re-established as
instantiations with byte-identical statements. Pairs that are not
embedding-parametric (e.g. `prod_encode_pile1_lt` /
`prod_encode_pile2_ge`, which differ in hypothesis polarity and bound
direction) are out of scope and left in place, recorded in the commit
message.

### W3 — cover_genus1/2 concrete rederivations

`reconstruct/cover_genus1.v`'s generic `Section higher_genus` takes
`hurwitz_g` and `higher_genus_ramif_ge_nbr` as HYPOTHESES; at g:=1
these are exactly the concrete `genus1_hurwitz` and
`genus1_ramif_ge_nbr`, whose proofs therefore SURVIVE as the
instantiation's arguments (likewise their genus2 twins).

Fix: instantiate only the downstream covering trio — `genus1_data`,
`genus1_covering`, `elliptic_gap`, `genus1_vs_genus0` against
`higher_genus_data`, `higher_genus_covering`,
`higher_genus_gap_bound` — with all exported statements byte-kept
(two convertibility steps are expected: `cd_n_branch := 3` vs
`g + 2`, and `+ 2` vs `+ 2 * g` at g:=1). Mechanical prerequisites:
reorder `Section higher_genus` BEFORE `Section genus1` inside
`cover_genus1.v`, and add `From pgg_smc Require Import cover_genus1`
to `cover_genus2.v` (it currently imports only `pgg_interface`; no
cycle results). A concrete statement that turns out not to be an
instance keeps its concrete proof and is recorded; the item does not
weaken statements to fit.

### W4 — dead files

1. `protocol/pgg_correctness.v`: remove from `_CoqProject` and
   delete. No `.v` file `Require`s it. Five of its eight exports
   re-derive `pgg_interface` results (`pgg_correctness` ->
   `endpointM`, `pgg_correctness1` -> `endpoint1`, `pgg_correctnessV`
   -> `endpointV`, `pgg_injective` -> `endpoint_inj`,
   `pgg_distinctness` -> `endpoint_starts_uniq`); the other three
   (`pgg_bijectivity`, `starts_tnth_inj`, `endpoints_card`) have no
   counterpart and are dead exports nothing consumes — their loss is
   recorded in the commit message.
2. `protocol/pgg_program.v`: orphan (not in `_CoqProject`, nothing
   `Require`s it; duplicates `dealt_hand`/`compute`/`endpoints`/
   `endpointsE` from `pgg_interface.v`); delete the file.
3. The single comment at `protocol/card_exchange_pismc.v` naming both
   files ("Cross-equality with pgg_program.v ... verified in
   pgg_correctness.v") is already false — `pgg_correctness.v`
   contains no such cross-equality — so it is DELETED, not
   redirected.

W4 runs first: it is cheap and shrinks the tree for every later gate
run.

### W5 — rigidity cluster via RSCodeWitness

The built rigidity instances `instances/abelian/
rigidity_abelian_instance.v`, `instances/cyclic/
rigidity_cyclic_instance.v`, `instances/oc/rigidity_oc_instance.v`
each hand-roll, verbatim as section variables/hypotheses, the eleven
fields that `reconstruct/cover_genus0.v` packages as `RSCodeWitness`
(consumed by `genus0_covering_witness`). All three files already
import `cover_genus0`; no import is added, no cycle arises. The two
witness declarations are currently referenced NOWHERE in the tree, so
this item wires up existing dead machinery.

Fix: each file builds its witness once and re-derives its existing
exported statements from `genus0_covering_witness`; statements
unchanged. ARITY TRAP: the witness must be bound as a section-local
`Let`, never a `Definition`/`Variable`, or the discharged statements
of the section's exports gain a parameter and the surface gate fails.
Other rigidity files (kim, monster, s5, s5x5) are inspected by the
implementer and included only where the same block appears verbatim;
the orphan star instance is untouched.

### W6 — schreier / schreier_weighted near-duplication

The five near-duplicate pairs (resolved by name from
`docs/style/scan-2026-08-26/security-B.md`'s stale ranges):

1. `convergence_rate_ge0` / `weighted_convergence_rate_ge0`
2. `convergence_rate_lt1` / `weighted_convergence_rate_lt1`
3. `schreier_epsilon_ge0` / `weighted_schreier_epsilon_ge0`
4. `schreier_epsilon_decreasing` /
   `weighted_schreier_epsilon_decreasing` (verified token-identical
   modulo `sc`/`wsc` prefixes)
5. `security_monotone` / `weighted_security_monotone`

Fix: pairs 1-4 depend only on a real `lam` with `0 < lam` and
`lam <= 1`; they factor through a shared section over such a `lam`
(in whichever of the two files the other imports, or a small shared
file). Pair 5 additionally touches the endpoint law, which genuinely
differs between the files (`fdistmap ... (rho_from_words ...)` vs
`endpoint_dist_weighted ...`); it factors through a further section
parametric in the endpoint law, or is skipped and recorded if that
parametrization forces a statement change. Both files' exported names
and statements unchanged throughout.

### W7 — tail

1. `instances/kim2025/kim_secrecy.v` is byte-identical to
   `instances/denboer1989/denboer_secrecy.v` modulo the name prefix,
   but `kim_indep`/`denboer_indep` are Qed-opaque, so den Boer's
   final lemma cannot be `exact:`-applied to Kim's statement. The
   real move: alias `kim_mechanism := denboer_mechanism R` (a
   `Definition`-body edit under the policy exception; adds the
   `denboer_secrecy` import, precedented by `kim_trace.v`), deleting
   the duplicated construction; `kim_view_secrecy` keeps its
   statement and its one-line proof. If the opacity blocks even this,
   skip and record.
2. `collusion_bound_unconditional` vs `collusion_bound_k`: SKIPPED
   (see Corrections; the two theorems differ in ideal reference and
   carrier, and no derivation saves anything). Recorded here so the
   punch-list item is answered, not lost.
3. `reconstruct/pgg_protocol_landscape.v`: `ar_genus1_gap2` re-proved
   as `Proof. exact: genus1_universal_option. Qed.` — same file, the
   form its sibling lemmas already use; no new import.
4. `pow2_split` (identical `Let` + proof in
   `instances/pgl27/pgl27_models.v` and
   `instances/pgl27/pgl27_word_privacy.v`; `pgl27_models.v` imports
   `pgl27_word_privacy`, so the direction is forced): exported as a
   `Fact` in `pgl27_word_privacy.v`, both `Let`s deleted.
5. `groups/pgg_raag_clique.v` `spos`/`sneg`: only two pairs are exact
   mirrors under a parity parameter (`spos_unfold`/`sneg_unfold`,
   `spos_pascal_core`/`sneg_pascal_core`, ~18 lines); the high-value
   pairs differ structurally (`spos` carries a k=0 term `sneg` does
   not). Factor the two exact pairs through a parametric helper ONLY
   if it does not increase net lines; otherwise skip and record.
6. `mk_player_aprocs` helper for the `mk_aproc (exchange_player ...)`
   boilerplate: scoped to the 85 sites inside `Definition` BODIES
   across the 14 affected files. The 40 sites inside exported Lemma
   statements (`s5x5_verifier_endpoints`, `pgl27_verifier_endpoints`,
   `s5_verifier_endpoints`, `den_boer_verifier_endpoints`,
   `abel_verifier_endpoints`, `abel_exec_endpoints`,
   `abel_shuffle_endpoints`) are OUT OF SCOPE — the policy forbids
   statement edits. Containment rule: the helper must produce a term
   CONVERTIBLE to the old body; after rewriting a file, if any
   downstream proof that unfolds those definitions breaks and cannot
   be fixed by a local, obvious adaptation (e.g. one `rewrite
   /mk_player_aprocs`), the FILE is reverted and recorded as skipped.
   Highest-risk tail item; lands last.

## Verification gates (every wave)

1. **Statement-surface gate** (new): `scripts/statement_surface.py`,
   committed with the campaign. Extractor contract:
   - For every `.v` file in `_CoqProject`, one entry per exported
     declaration in `Definition|Lemma|Theorem|Corollary|Record|
     Fixpoint|Instance|Axiom|Notation`.
   - The recorded statement is the text from the declaration name to
     the `.` terminating the TYPE — the `:= body` of a `Definition`/
     `Fixpoint` is EXCLUDED (W3, W5, W7.1, W7.6 legitimately change
     bodies). Multi-line statements are the norm; the extractor must
     parse to the sentence terminator, not by line.
   - Comments are stripped (reuse `scripts/strip_comments.py` logic)
     before whitespace normalization.
   - `Local Lemma`/`Local Definition`/`Local Notation` (258 in the
     tree) and `Let` are non-exported: excluded from the surface,
     listed in a separate advisory section of the output.
   - Each entry is keyed by (file, enclosing-section path, kind,
     name), and the enclosing sections' `Variable`/`Hypothesis`/
     `Context` text is hashed into the entry, because section
     discharge changes a statement with zero text change (the W1
     hoist and W3 reorder are exactly such moves).
   - `#[...]` attribute lines are skipped to reach the keyword;
     HB-generated names (`HB.instance` etc., 29 sites) are out of the
     extractor's reach — accepted risk, noted in the script header.
   - Gate rule: after-surface = before-surface, minus the W4 file
     entries, plus new shared-machinery additions, plus ONE
     authorized relocation set for W1 (entries may move between the
     two raag files, and out of a section, provided kind + name +
     normalized statement are preserved; the three W1 renames and the
     `not_sorted_descent'` retarget are listed by name in the commit
     message and pre-approved). No other existing entry changes.
   - The before-surface is regenerated on demand from the pre-wave
     git commit (`git show <commit>:<file>`); no stored snapshot.
2. **Full rebuild** EXIT=0, judged from captured build logs (the
   compile-count hook decorates tool output; logs are the truth).
3. **Admitted/Axiom parity, scoped to `_CoqProject` files**: 0
   `Admitted` and exactly 16 `Axiom` declarations before and after
   every wave. (Tree-wide counts differ: the orphan files
   `pgg_schreier_test.v` and `rigidity_star_instance.v` each carry an
   `Admitted` and are outside the build.)
4. **Line count**: net decrease required for W1, W2, W3, W4, W7.6;
   no net increase for W5, W6, W7.1, W7.3, W7.4, W7.5.
5. Comment prose added by this campaign follows the statement-comment
   rule (fact + position); no status or process narration.

## Team and sequencing

Controller fans out one implementer per work item, sequentially by
item (waves): **W4 → W1 → W2 → W3 → W5 → W6 → W7**. Opus for the
proof-adaptation items (W1, W3, W5, W6), Sonnet for the mechanical
ones (W2, W4, W7.1-7.5), Opus for W7.6. After each item: the
controller runs the surface gate + rebuild centrally, then one Opus
reviewer audits the diff against this spec before the commit is
accepted. One commit per work item (W7 may split into its sub-items).
File-overlap hazards for the reviewer: `instances/s5x5/s5x5_exec.v`
is touched by both W2 and W7.6, and `protocol/card_exchange_pismc.v`
by both W4 (comment delete) and W7.6. Agents stage only named files,
never `git add -A`. Prover-agent audits every ~5 minutes per the
standing workflow rule.

## Out of scope

P3 notation/action packaging, P4 statement reshaping and
section-hoisting, P5 hygiene sweeps, all vendored files, the orphan
star/debug/test files (except the W4 delete), the 40 in-statement
`mk_aproc` sites, and any change to exported statement text.
