# Wreath7 failure analysis, and the S_5 x S_5 comparison

Note date: 20260606T143722Z

Context: design review for merging the piSMC protocol into a single source of
truth. This note records why the wreath7 instance (Z_7 wr S_2) cannot
simultaneously deliver non-abelian security, a T > k threshold gap, and
recovery, and why the S_5 x S_5 instance (s5x5) is the coherent construction
that does.

All claims below are checked against the current code. Evidence files:
`instances/wreath7/wreath_smc.v`, `instances/wreath7/wreath_recovery.v`,
`instances/wreath7/wreath_monodromy_profile.v`,
`reconstruct/product_threshold.v`, `reconstruct/covering_scheme.v`,
`reconstruct/cover_tradeoff.v`,
`instances/s5x5/pgg_s5x5.v`, `instances/s5x5/rigidity_s5x5_instance.v`.

---

## Part 1: Why wreath7 fails

### 1. The group and its two roles

- Group: `Z_7 wr S_2 = (Z_7 x Z_7) ⋊ S_2`, order 98 (axiomatized as
  `card_wreath`), acting on N = 14 card positions (two piles of 7).
- Generators: within-pile cyclic cuts (`cut1`, `cut2`, each a 7-cycle) plus the
  pile-swap `wswap`.
- `wcore = <<cut1, cut2>>` (`wreath_recovery.v:117`). Since `cut1`, `cut2` are
  disjoint 7-cycles, this is `Z_7 x Z_7`, abelian of order 49. That structure
  is a math fact read off the generator supports, not a separate formalized
  lemma in the cited file (which proves membership and pile-preservation).

### 2. Recovery only holds on the abelian core

- `wreath_smc_recovers` (`wreath_smc.v:134`) proves reconstruction succeeds for
  any false shuffle `g \in wcore` (a sufficient condition; the code does not
  prove recovery fails outside `wcore`).
- `wreath_smc_swap_excluded` (`wreath_smc.v:160`) proves `wswap \notin wcore`:
  the pile-swap does not preserve the pile partition, so it lies outside the
  recon-symmetry group.
- Root cause: the threshold scheme is a product of two pile-local sum-mod-7
  schemes (`product_threshold.v`), and
  `product_sum_mod_perm_compatible` (`product_threshold.v:435-453`) proves
  recon-invariance only under permutations satisfying `preserves_pile1`, i.e.
  pile-preserving permutations. A pile-swap is not pile-preserving, so it is
  structurally barred from the recovery guarantee.

### 3. Security is claimed on a different (larger) group

- `wreath_profile` (`wreath_monodromy_profile.v`) plugs `M_wreath_sym`, the
  symmetric generating set that includes `wswap`, and carries a
  `SecurityAsymptotic` with `sa_eps_inf = 0` (anonymity vanishes). The
  `sa_eps_inf = 0` field is read off by a standard-only lemma
  (`wreath_asymptotic_eps_inf_zero`), but the underlying spectral gap rests on
  the custom axiom `wreath_rayleigh_Qsq_R`.
- That vanishing requires the action to be transitive on all 14 positions, and
  the only generator that connects the two piles is `wswap`. So the security
  claim depends on `wswap`, while recovery requires excluding `wswap`.

### 4. The incoherence

- Recovery group: `wcore` (pile-preserving, abelian).
- Security group: the full `Z_7 wr S_2` (with `wswap`, transitive).
- These are different groups. The full-group walk that earns
  `sa_eps_inf = 0` does not preserve recovery; the wcore walk that preserves
  recovery is intransitive and cannot earn `sa_eps_inf = 0`. The instance
  asserts both by reading them off two different groups, which is not one
  coherent protocol.

### 5. The obstruction (synthesis over the two routes in this codebase)

A genus tradeoff is formalized; the transitivity consequence below is an
observation about the two realized routes, not a proven universal law.

- Formalized: `cs_gap : ts_T <= ts_k + 2 * genus` (`covering_scheme.v:129-130`),
  so `T > k` strictly requires genus > 0 (`genus0_exact`,
  `covering_scheme.v:146`). The headline `security_threshold_tradeoff`
  (`cover_tradeoff.v:140`) is exactly this disjunction: either genus 0 with
  `|G| <= pgl_bound` and `T <= k`, or genus > 0 with a gap. It says nothing
  about transitivity.
- Observed (not a formalized theorem): in both routes present here, `T > k`
  forces the recon-symmetry to fix a substructure. The product route fixes the
  pile partition (`preserves_pile1`, `product_threshold.v:435-437`); the AG
  route fixes the secret coordinate (`sigma_fix0_ec g ord0 = ord0`,
  `cover_genus1.v:239-240`). A group fixing such a substructure is intransitive
  on the N positions.
- Intransitive action then carries a permanent anonymity floor against
  uniform-on-N. This link is recorded as a design comment at
  `card_exchange_pismc.v:91` (transitive actions drive eps to 0; non-transitive
  ones floor), not as a theorem. So for these two constructions "vanishing
  anonymity over all N" and "T > k" are incompatible. This is a property of the
  routes realized here, not a proven statement about every conceivable `T > k`
  scheme.

### 6. Why wreath specifically cannot be rescued in place

- The only restriction that keeps recovery is shuffling inside `wcore`, but
  `wcore = Z_7 x Z_7` is abelian. Restricting there abelianizes the security
  group, which defeats wreath's entire purpose (it exists to be the non-abelian
  exemplar) and yields intransitivity on top.
- The only generator that makes the group non-abelian is `wswap`, and `wswap` is
  exactly the recovery-breaking element. So in this construction the
  non-abelian generator and the recovery-breaking generator coincide. You
  cannot keep one without losing the other. Hence wreath cannot hold
  {non-abelian, T > k, recovery} together.

Note on a benign confusion: `wcore = Z_7 x Z_7` is the cyclic kind of abelian
(each `Z_7` still mixes within its pile), not the involution kind
(`Z_2 x Z_2` disjoint transpositions) that floors within an orbit. So the
within-pile mixing is fine; the failures are (a) loss of the non-abelian
property and (b) cross-pile intransitivity.

---

## Part 2: S_5 x S_5 (s5x5) as the coherent construction

### 1. The group gets its non-abelianness from inside the piles

- Group: `S_5 x S_5`, order 14400 (axiomatized as `s5x5_group_order_eq`,
  `rigidity_s5x5_instance.v:67`; `120^2 = 14400`), acting on N = 10 (two piles
  of 5).
- Generators: adjacent transpositions within each pile of 5
  (`pgg_s5x5.v:76-78`). There is no cross-pile swap.
- Non-abelian because `S_5` is non-abelian, sourced entirely from within-pile
  shuffles.

### 2. Recovery holds on the full group (coherent)

- `cs_recon_symmetry := pgg_G R_s5x5` with `cs_recon_symmetry_sub := subxx _`
  (`rigidity_s5x5_instance.v:391-392`): recovery holds for all of `S_5 x S_5`,
  not a proper subgroup.
- Because the whole group is pile-preserving, `product_sum_mod_perm_compatible`
  applies to every group element (`s5x5_perm_compatible`,
  `rigidity_s5x5_instance.v:377-381`). The shuffle group and the recovery group
  coincide. This is the coherence wreath lacked.

### 3. The threshold gap and a non-vacuous monodromy

- Product of two sum-mod-5 schemes: `T = 10`, `k = 5`, gap 5
  (`rigidity_s5x5_instance.v:357-358`). A genuine T > k.
- `cs_monodromy := @pgg_rho R_s5x5` (`rigidity_s5x5_instance.v:390`): the
  monodromy coupling is the real representation, not a trivial-sigma
  placeholder. Contrast the AG route, which is consistent with a transitive
  monodromy only via trivial sigma (vacuous).

### 4. Security reuses the S_5 analysis, with an honest floor

- Within-pile mixing uses the `S_5` Rayleigh certificate from `s5_mixing`
  (`rigidity_s5x5_instance.v:244-246`); spectral witness at `L = 591` gives
  40-bit (`:497-500`).
- `s5x5_asymptotic` sets `sa_eps_inf = 1` (`:251-271`), the orbit-vs-global
  floor from the two piles. This is the unavoidable T > k tax (Part 1, item 5),
  recorded honestly rather than papered over. The threshold privacy (`k = 5`,
  fewer than 5 parties learn nothing) is separate and intact.

### 5. Genus accounting is refined, not cooked

- Single-component Galois-closure genus 173 from the Hurwitz automorphism bound
  `g >= 1 + |G|/84` (`rigidity_s5x5_instance.v:303-337`; `ceil(1 + 14400/84) =
  173`, tight). The realising curve is an axiom
  (`s5x5_inverse_galois_realised`) and the 173 depends on the order axiom.
- Operational multi-component genus 8: two genus-4 Bring's curves (genus 4,
  automorphism group `S_5`), one per pile (`rigidity_s5x5_instance.v:523-559`,
  `reconstruct/multi_covering.v`). The total `8 = 4 + 4` is axiom-free
  (`mcd_total_genus_s5x5_E`).

### 6. Side-by-side

| property | wreath7 (Z_7 wr S_2) | s5x5 (S_5 x S_5) |
|---|---|---|
| order | 98 | 14400 |
| non-abelian source | cross-pile swap `wswap` | within-pile `S_5` |
| recon-symmetry | `wcore` (abelian, proper subgroup) | full `S_5 x S_5` |
| shuffle group = recovery group | no (incoherent) | yes (coherent) |
| T > k | yes (14 > 7) but recovery only on wcore | yes (10 > 5), recovery on full group |
| non-abelian + recovery together | no (swap is the recovery-breaker) | yes |
| monodromy coupling | real but recovery-limited | real, full-group |
| anonymity | claims eps_inf=0 on full group, contradicts recovery | within-pile vanishing + honest floor eps_inf=1 |
| meaningful card op | cuts + a pile swap | shuffle each 5-card pile |

### 7. Conclusion

s5x5 is what wreath was trying to be. The decisive move is to source
non-abelianness from inside the piles (`S_n` per pile) rather than from a
cross-pile swap. Then the whole group is pile-preserving, so the recon-symmetry
equals the full group and the shuffle group equals the recovery group. wreath,
corrected, is exactly s5x5 with pile size 7 (`S_7 x S_7`, no swap). For the
merge, s5x5 is the canonical non-abelian T > k exemplar; wreath should be
re-based onto the same pattern or retired in its favor. The within-pile-only
anonymity (cross-pile floor) is the unavoidable cost of any T > k scheme, not a
defect of this particular instance.

---

## Appendix: axiom status (what is proved vs assumed)

A math-expert audit (20260606) confirmed the numerics and structure and flagged
the following honesty points, now reflected above.

Assumed (axioms or hypotheses), not kernel-proved:

- Group orders: `|Z_7 wr S_2| = 98` (`card_wreath`) and `|S_5 x S_5| = 14400`
  (`s5x5_group_order_eq`). The genus-173 Hurwitz arithmetic depends on the
  latter.
- Wreath floor-0 spectral gap: the custom axiom `wreath_rayleigh_Qsq_R`
  underlies `wreath_asymptotic`, hence the `sa_eps_inf = 0` claim.
- Curve realisations: `s5x5_inverse_galois_realised` (genus-173 single curve)
  and `s5x5_multi_realised` (two Bring's curves) are `realised_by_curve`
  axioms.

Genuinely proved (closed / standard-only, verified by the audit):

- `wreath_smc_swap_excluded` (`wswap notin wcore`), `s5x5_preserves_pile1`
  (pile preservation), `mcd_total_genus_s5x5_E` (genus `8 = 4 + 4`),
  `wreath_asymptotic_eps_inf_zero` (reads the floor field).

Scope caveat: the "T > k forces intransitivity hence an anonymity floor" chain
(Part 1, item 5) holds for the two routes realized here (product and AG). It is
a synthesis, not a formalized universal law; `security_threshold_tradeoff`
proves only the genus/PGL-bound disjunction.

Code-hygiene note (not a claim in this analysis): `s5x5_covering` carries
`cs_data` at genus 173 while `s5x5_cs_gap` is discharged via the genus-3 bound
`10 <= 5 + 2*3`; this typechecks by convertibility (both sides reduce to
`true`), and the live `cd_genus` is 173, but the stale "`2*3 = 5+6`" comments
near `rigidity_s5x5_instance.v:362-364` should be updated to avoid misleading a
future reader.
