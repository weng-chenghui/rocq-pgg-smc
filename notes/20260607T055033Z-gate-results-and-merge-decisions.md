# Pre-implementation gate results and merge scope decisions (v3 -> v4)

Note date: 20260607T055033Z

Records the two pre-implementation gates run on the v3 protocol-merge spec
(Option C, `ReconPlug`) and the two scope decisions taken afterward, which
together produced the v4 spec
(`docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md`). Companions:
- `20260607T040424Z-reconplug-design-and-denboer-flow.md` (ReconPlug design;
  carries a post-audit correction header for the `rp_content` formula)
- `20260607T042916Z-algebraicrigidity-genus-and-s5-nogo-qa.md`
- `20260607T015612Z-concrete-recovery-mechanisms-survey.md`

---

## GATE 1 — record-shape typecheck against the live source (rocq-prover)

Greened the reconstruct dependency chain (pgg_interface, pgg_sharing_framework,
covering_scheme, cover_tradeoff, algebraic_rigidity, pgg_covering_correctness),
then typechecked the proposed `ReconPlug` / restructured `CoveringScheme` /
`Notation cs_scheme` in a scratch session. Verdict: **implementable as written**
for the retained four-instance scope.

- `ReconPlug` elaborates. `rp_recon_invariant` resolves to
  `@ts_recon_perm_invariant (pgg_gT M) (pgg_G M) 'I_N 'I_N rp_scheme
  rp_monodromy`. `ts_recon_perm_invariant`'s group argument is `{group gT}`;
  `pgg_G M : {group pgg_gT M}` is exactly compatible. The full-group statement is
  correct (no subgroup needed).
- `Notation cs_scheme cs := (rp_scheme (cs_plug cs))` is safe: all 103 non-wreath
  uses are applied `cs_scheme <cs>`; zero first-class uses (`@cs_scheme`, partial
  application, `map`, `Canonical`, ...).
- `cs_T'` and `cs_scheme_T` (the share-count cache field + its `erefl` equation)
  have ZERO projection consumers; downstream uses `ts_T' (cs_scheme cs)`. They
  are dropped with no spec gap.
- recon-symmetry drop is safe for the retained four. Each pins
  `cs_recon_symmetry = pgg_G` via `subxx`: s5 (rigidity_s5_instance.v:339), s5x5
  (rigidity_s5x5_instance.v:391), Kim and den Boer via `genus0_covering_witness`
  -> `genus0_covering` (cover_genus0.v:173). dealer_bridge migration:
  `Let G := pgg_G M`; `cs_monodromy -> rp_monodromy (cs_plug ...)`;
  `cs_recon_symmetry_sub -> subxx _`; `cs_recon_invariant -> rp_recon_invariant
  (cs_plug ...)`. `pgg_hidden_invariant_perm` is unchanged (already takes an
  arbitrary subgroup `H \subset pgg_G M`; feed `pgg_G`/`subxx`).
- Out-of-scope kill-shot (flagged): wreath7 sets `cs_recon_symmetry := wcore` (a
  PROPER abelian core, wreath_recovery.v:117) and star also uses a proper
  subgroup. They can never return under the dropped-field record without a
  per-plug symmetry field. Out of scope (project scope = kim/denboer/s5/s5x5), so
  the drop is safe.

Also confirmed: `cover_genus0/1/2.v` build `CoveringScheme` records too, so the
restructure touches them as well as the instance rigidity files.

## GATE 2 — adversarial math/feasibility re-audit (read-only)

Verdict: NOT READY (for v3 as written). Three corrections, all in the den Boer
integration, plus a genus inaccuracy. None reopened the `'I_5`-vs-`bool` choice
(that axis was settled in v3 and the audit reaffirmed it; reverting to `bool`
means reverting to Option B, which is strictly more work via the wire/duality
re-proof).

1. **`rp_content` type-incoherence (content correction).** The note had
   `rp_content = encode_bool ∘ fc_arrange`, but `fc_arrange : bool -> bool ->
   seq bool` (five_card_program.v:65) is not `'I_5 -> 'I_5`, and more deeply a
   pointwise position map cannot carry a secret-dependent arrangement
   (`pgg_rho g = g`, starts are positions; pgg_interface.v:535-545). FIX:
   `content` is the deck's FIXED face map `face : 'I_5 -> 'I_5`; the secret
   arrangement lives in `ts_encode`/the starts (a uniq card-identity
   permutation). `content (rho w (start_i))` = face value at each cut position =
   the trick's revealed sequence. Faithful (faces, not identities, on the wire)
   and the `'I_5` wire is unchanged. This actually strengthens the design:
   `content` earns its place as a genuine non-`id` readout, and starts stay
   `uniq`.
2. **den Boer rebuild is MEDIUM, not LOW.** den Boer's scheme is
   `ThresholdScheme bool bool` over `seq bool` (five_card_pismc.v:241-244). To
   plug into the monomorphic framework it must be rebuilt as `'I_5`:
   validity/recon/encode/correctness/privacy transport mechanically through
   `encode_bool`/`decode_bool`, but the NET-NEW `ts_recon_perm_invariant`
   (three-consec rotation-invariance over the full Z_5) does not exist today and
   must be proved. Mathematically sound (`fc_three_consec` checks all five cyclic
   windows over `s ++ s`, five_card_program.v:93-96), but real work.
3. **input-commitment cannot reuse FCCommit/FCRecvCommit.** They are
   `@sproc fc_dtype fc_data ...` (fc_dtype = {DT_CardVal, DT_Commit}; fc_data =
   {FC_card bool, FC_commit (seq bool)}, five_card_session_types.v:125-148), a
   different inductive universe from `pgg_dtype`/`pgg_data`
   (pgg_interface.v:309-312). FIX: build NEW commit/recv-commit `sproc` wrappers
   over the EXISTING `pgg_dtype`/`pgg_data` (committed payload reuses a
   sheet/card constructor, so the player/verifier wire stays unchanged); only the
   dealer gains a commit prologue, with a dealer-side duality re-proof.
4. **s5x5 genus (major).** The operative `cd_genus` in `s5x5_covering_data` is
   173 (rigidity_s5x5_instance.v:337), and `s5x5_cs_gap` is proved against a
   smaller witness lifted by `leq_trans`; the genus-8 two-Bring's reading
   (:505-574) is a separate decoration. Do not present "Bring's genus 8" as
   load-bearing; reconcile the 173 / gap-witness / 8 figures to one coherent
   operative genus as a cleanup.

GATE 2 confirmed-sound (tried to break, could not): wire unchanged for
`content = id`; den Boer needs no genus/CoveringScheme for correctness (no
consumer forces it; fc_rigidity/fc_covering have no external importer); the
three-consec invariance over the full Z_5 is real (NOT the obstruction); the
recon-symmetry drop; the Notation.

## Scope decisions (user)

- **den Boer:** do the `'I_5` rebuild NOW (in this merge), with `content = face`
  and the arrangement in `ts_encode`. Delivers goal #4 (den Boer through the
  general protocol).
- **input-commitment:** do it NOW too, no defer. Sequenced AFTER the den Boer
  rebuild (new pgg-typed commit wrappers + dealer-prologue duality re-proof).

Both folded into v4 spec §5b, §6, §15 (phases 5 then 6), §16. The `'I_5`-vs-`bool`
representation question is closed; remaining work is scheduling/scope, now fixed.
