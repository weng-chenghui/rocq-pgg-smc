# A non-Abelian, non-dihedral, AG-recoverable single-deck instance: design

Date: 2026-07-01
Status: REVISED after adversarial audit (2026-07-01). The mathematical object is verified
sound. The claim that it fits the existing `cover_genus1.v` scaffold is REFUTED: that scaffold
is single-pole near-MDS and structurally forces an abelian recon-symmetry at genus 1.
Formalizing the object needs a divisor-based `L(D)` genus-1 scaffold, which does not yet exist.
Threshold semantics corrected below.
Scope: recovery only. Security/mixing analysis is out of scope for this instance.

## 1. Question and verdict

Question: is there a group that carries algebraic-geometry-code `(k, T)` recoverability,
is non-Abelian, and is not the trivial dihedral case, or is this rejected by the
theorems behind the `S_5` no-go?

Verdict: not rejected. The `S_5` no-go is narrow. It is the statement that a group acting
`2`-transitively on few points at genus `0` has only the rigid submodule lattice
`{0, 1, n-1, n}`, so no intermediate-dimension invariant code exists. Dropping
`2`-transitivity and adding positive genus escapes it. This design fixes the smallest
concrete escape that is single-deck, genus `1`, and formalizable by reusing the existing
genus-1 scaffold.

Companion background: [[20260630-170155-s5nogo-james-submodule-report]] (the James
Submodule Theorem framing and the three-tier obstruction/possibility/existence trichotomy),
[[20260602_135732_nogo_escape_groups_security_ladder]] (which transitive groups escape and
the Riemann-Hurwitz tension), [[20260630-192036-bring-and-pgl-routes-rejected]] (the
rejected `S_5` genus-0 PGL and Bring-curve routes).

## 1a. Adversarial audit outcome (2026-07-01)

A domain-expert audit verified the mathematical object and refuted the scaffold fit.

Verified sound:
- The group is `Dic_3` (order 12, non-Abelian, non-dihedral, unique involution), realized as
  `Aut(E, O)` and as `Stab(P_0)` for `E : y^2 = x^3 - x` over `GF(9)`.
- The curve is supersingular in char 3, `#E(GF(9)) = 16`, orbits `{1, 3, 12}`, and the
  char-3 separable-cubic model is correct (char 2 would be inseparable).
- The code automorphism induced by a curve automorphism is a pure coordinate permutation
  (functional code `C_L`, no residue or monomial twist), so `coord_perm_compatible` is the
  right and satisfiable notion.
- The wreath-escape logic is coherent: the recovery interface needs no transitivity, so a
  secret-fixing intransitive group is structurally fine for recovery.

Refuted (BLOCKER):
- `cover_genus1.v` is not a divisor code. It hardcodes a single pole at infinity,
  `L(m_deg . P_infty)` with `m_deg = k + g - 1`, and its hypotheses `Hkgn_ec` (`k + g < n`)
  and `Hparam_ec` (`n <= k + g + 1`) force `n = k + g + 1`, a near-MDS regime. The `[13, 3]`
  instance (`n = 13`) cannot discharge `Hparam_ec` (`13 <= 5` is false). The design does not
  instantiate the existing scaffold.
- Deeper structural obstruction (verified, `notes/ec_pole_check.py`): to preserve
  `L(m . P_infty)` the recon-symmetry must fix the single pole `O`; to satisfy `sigma_fix0`
  it must fix the secret `P_0`; on a genus-1 curve a two-point stabilizer is abelian (here
  `C_4` or trivial, max non-Abelian order `0`). So the single-pole scaffold structurally
  cannot host a non-Abelian recon-symmetry at genus 1, for any secret. The near-MDS repair
  `[13, 11]` fails on this count too.
- Threshold semantics were misread. In the scaffold `ts_T = n - 1` (all shares are consumed
  by `massey_reconstruct`) and `ts_k = k - g` (privacy). Their difference is `2g` only in the
  `n = k + g + 1` regime. The clean "gap 2" belongs to the AG-LSSS reading of the divisor
  object, and the exact privacy and reconstruction thresholds of the `[13, 3]` object must be
  derived from its dual distance, not asserted.

Consequence: the object stands, the formalization target changes. The `[13, 3]` code is the
functional code `C_L(D, E-set)` for the degree-3 `G`-invariant divisor `D`, the size-3 orbit,
which spreads the pole over three points so no single point is fixed and `Stab(P_0)` stays
non-Abelian. Formalizing it requires a genus-1 scaffold that takes a general effective
`G`-invariant divisor `D`, not `m . P_infty`. That generalized scaffold does not yet exist.

## 2. The obstruction chain that shapes the design

1. Recovery needs an intermediate-dimension `G`-invariant submodule of the code module.
   James's Submodule Theorem forbids it for the natural `S_n` action, because
   `2`-transitivity on `n` points forces the permutation module `M^{(n-1,1)}` with submodule
   dimensions `{0, 1, n-1, n}` in every characteristic.

2. The escape is a group that is transitive but not `2`-transitive (so intermediate
   invariant submodules can exist) together with positive genus (so the AG threshold gap
   `T = k + 2g` is positive).

3. Wreath lesson [[20260606T143722Z-wreath7-failure-and-s5x5-comparison]]: a `T > k` AG
   scheme forces the recon-symmetry to fix the secret coordinate. In
   `reconstruct/cover_genus1.v` this is the hypothesis
   `sigma_fix0_ec : forall g, g \in G -> sigma_code_ec g ord0 = ord0`.
   The wreath instance failed because its only non-Abelian generator (the pile-swap
   `wswap`) was exactly the element that broke the fixed substructure. The non-Abelian
   source and the recovery-breaker coincided. The design must source non-Abelianness from
   inside the secret-fixing group, the way `s5x5` sourced it from within the piles.

4. Genus-1 corollary: the secret-fixing group is a point-stabilizer of the curve
   automorphism group, which on a genus-1 curve is isomorphic to `Aut(E, O)`. Over a field
   of characteristic at least `5` this is cyclic, hence Abelian. A non-Abelian secret-fixing
   group at genus `1` exists only in characteristic `2` or `3`, on a supersingular curve.

5. Scaffold constraint: `cover_genus1.v` models the curve as `y^2 = f(x)` with `f` a
   separable cubic (`curve_sep_ec : separable_poly curve_poly_ec`), and its proved distance
   and gap bounds run through that model. The model is valid in characteristic `3` and
   invalid in characteristic `2` (where `y^2 = f(x)` is inseparable). Characteristic `3`
   therefore reuses the existing proved genus-1 machinery; characteristic `2` would require
   new Artin-Schreier distance lemmas.

Conclusion: characteristic `3`, genus `1`, supersingular, secret fixed by a non-Abelian
point-stabilizer.

## 3. The verified concrete instance

Curve: `E : y^2 = x^3 - x` over `GF(9) = GF(3)[t]/(t^2 + 1)`.

Automorphisms fixing `O`: `phi_{u,r}(x, y) = (u^2 x + r, u^3 y)` for `u^4 = 1`
(`u in {1, -1, t, -t}`) and `r in GF(3)`. Composition law
`(u, r) . (u', r') = (u u', r + u^2 r')`. This is the dicyclic group `Dic_3` of order `12`:
non-Abelian, with a unique involution `(-1, 0)`, hence not dihedral.

Spot-check confirmed (script `notes/ec_spotcheck.py`, run 2026-07-01):

- `#E(GF(9)) = 16` (`15` affine points and `O`).
- The group fixing `O` has order `12`, is non-Abelian, and has exactly `1` involution
  (`D_6` would have `7`). This is `Dic_3`, non-dihedral.
- Orbits of `Aut(E, O)` on the `16` points have sizes `{1, 3, 12}`, with `O` the singleton
  fixed by all `12` automorphisms.
- Affine placement (script `notes/ec_spotcheck2.py`): `E(GF(9))` has order `16`, element
  orders `{1, 2, 4}`. For the affine secret `P_0 = (0, 0)`, the stabilizer `Stab(P_0)` in the
  full curve automorphism group has order `12`, orbits `{1, 3, 12}`, and `O` lies in the
  size-`3` orbit. So the `13` evaluation points are all affine.

Scheme (the divisor object; see 1a for why it needs a generalized `L(D)` scaffold):

- Secret coordinate: the affine point `P_0 = (0, 0)`, a singleton orbit fixed by the whole
  recon-symmetry group `Stab(P_0) ~= Dic_3`. This satisfies `sigma_fix0_ec` with `G = Dic_3`
  entire, not a proper subgroup. This is the wreath escape: the non-Abelian group is the
  secret-fixing group.
- Recon-symmetry: `Stab(P_0)`, the point-stabilizer of `P_0` in the full curve automorphism
  group `E(GF(9)) rtimes Aut(E, O)` (order `16 * 12 = 192`, transitive on the `16` points),
  isomorphic to `Dic_3`.
- Divisor: `D`, the size-`3` orbit of `Stab(P_0)`, multiplicity `1`. This orbit contains
  `O`, so `deg D = 3` and its support is disjoint from the evaluation set.
- Evaluation set: `P_0` together with the size-`12` orbit, `n = 13` points, all affine
  (because `O` sits in the divisor orbit, not the evaluation set), `G`-stable.
- Code: `C = C_L(D, E-set)`. By Riemann-Roch at genus `1`, `k = l(D) = deg D + 1 - g = 3`.
  A `[n = 13, k = 3]` AG code over `GF(9)`.
- Gap: `2g = 2` in the AG-LSSS sense (privacy for coalitions below `n - deg D`, reconstruction
  at `n - deg D + 2g`). The exact privacy and reconstruction endpoints for this `[13, 3]` code
  must be derived from its dual distance in the worked example, not asserted. The scaffold's
  `ts1_gap` does NOT apply here, because that lemma lives in the single-pole `n = k + g + 1`
  regime this object does not inhabit (see 1a).

Correction to the raw spot-check: the script's `deg D = 2, k = 2` line used a degree-2
divisor that is not `G`-invariant. The smallest `G`-invariant divisor supported on the
size-`3` orbit has degree `3`, giving `k = 3`. A richer variant takes multiplicity `2`
(`deg D = 6, k = 6`) for stronger privacy.

## 4. Deliverable A: the paper worked example (write first)

Produce every artifact explicitly and verify by hand or small computation before any Rocq.

1. `GF(9)` model and the list of all `16` points of `E`.
2. The `12` automorphisms as explicit permutations of the points, with the finite checks:
   order `12`, non-Abelian, exactly one involution (non-dihedral).
3. The size-`3` and size-`12` orbits and the singleton `O`.
4. The divisor `D`, the evaluation set, and the generator matrix of the `[13, 3]` code.
5. A chosen secret `s in GF(9)`: the codeword that encodes it, the `13` shares it deals,
   one qualified coalition reconstructing `s`, and one unqualified coalition whose joint
   view is independent of `s`.
6. The `Dic_3` action permuting the `13` shares while fixing the secret coordinate `P_0`,
   exhibiting equivariance of recovery under the shuffle.
7. Parameter table: `n = 13`, `deg D = 3`, `k = l(D) = 3`, `g = 1`, gap `2g = 2`, with the
   concrete privacy threshold and reconstruction threshold derived from the code's dual
   distance (not assumed).

## 5. Deliverable B: Rocq formalization (next round, only after A checks)

The existing `cover_genus1.v` cannot be instantiated (1a). Formalizing the object requires a
divisor-based genus-1 scaffold. Scope:

- A genus-1 AG-code module `C_L(D, E-set)` parameterized by a general effective divisor `D`
  (here the size-3 `G`-orbit), not `m_deg . P_infty`. Re-prove the distance and dual-distance
  bounds for `C_L(D)` (the current `hyp_goppa_wt` is stated for the single-pole model).
- The recon-symmetry `sigma_code_ec : Dic_3 -> {perm 'I_n}` with `sigma_fix0_ec` (fixes the
  secret column `P_0`) and `code_auto_ec` (each `g` preserves `C_L(D)`, valid because `g`
  permutes `supp(D)` and fixes `P_0`; the audit confirmed this is a pure permutation).
- The threshold reading corrected to the AG-LSSS `(privacy, reconstruction)` pair with gap
  `2g`, replacing the scaffold's `ts_T = n - 1`, `ts_k = k - g` encoding.
- A `CoveringScheme`-style package with a computable `ts_recon`, confirmed axiom-free.

This is a new formalization component, not a plug-in to the existing genus-1 scaffold. Its
size is the main open scoping question for the next step.

## 6. Risks and adversarial audit

- Resolved by the audit: the `Dic_3` action on the `13` coordinates is a pure permutation
  that preserves the functional code `C_L(D)` and fixes the secret column `P_0`. This is no
  longer the primary risk.
- New load-bearing item: the divisor-based `C_L(D)` distance and dual-distance bounds, and the
  corrected AG-LSSS threshold reading, must be established. This is the substance of the new
  formalization component (Section 5) and the size of that component is unquantified.
- The exact privacy and reconstruction thresholds of the `[13, 3]` object are not yet
  computed. Derive them from the dual distance in Deliverable A before any threshold claim.
- `GF(9)` is an extension field. Confirm the `finfield` construction and the generator
  matrix build are tractable in the repo's mathcomp setup before committing Rocq effort.
- Before trusting the design, run a skeptic pass against two claims: that `G` fixes the
  secret coordinate for the chosen `E-set`, and that the gap is genuinely `2` and not
  collapsed by a degenerate parameter.

## 7. Out of scope

- Characteristic-`2` `SL_2(F_3)` (order `24`): richer group but needs new Artin-Schreier AG
  distance machinery, rejected for this round.
- Genus at least `2` (for example the Klein quartic with `PSL(2,7)`): no genus-3 scaffold
  exists; larger gap and larger worked example.
- Pile / covering structure: single deck this round; piles are a later variant via isogeny
  fibers.
- Security, mixing, anonymity: this instance is recovery only.

## 8. Pointers

- Scaffold: `reconstruct/cover_genus1.v` (the `sigma_fix0_ec` / `code_auto_ec` hypotheses and
  the proved `ts1_gap`).
- Spot-check: `notes/ec_spotcheck.py`.
- Related: [[20260630-170155-s5nogo-james-submodule-report]],
  [[20260602_135732_nogo_escape_groups_security_ladder]],
  [[20260606T143722Z-wreath7-failure-and-s5x5-comparison]],
  [[20260630-192036-bring-and-pgl-routes-rejected]],
  [[20260607T015612Z-concrete-recovery-mechanisms-survey]].
