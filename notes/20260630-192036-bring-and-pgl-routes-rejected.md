# Bring's curve and the genus-0 PGL/RS route: both evaluated and rejected for S_5 recovery

Purpose: record, with commit and file pointers, that the two algebraic-geometry
routes for giving the natural-action `S_5` (and `S_5 x S_5`) a recoverable
`(k, T)` threshold plug were already investigated in this repo and rejected, so
they do not get re-proposed. A 2026-06-30 deep-research pass floated both as
"new methods"; they are not new, and they do not work for the natural action.

## The question

Can the natural-action `S_5` (the card shuffle, adjacent transpositions on five
positions) or `S_5 x S_5` be given a recoverable secret-sharing `(k, T)`
threshold plug via either a genus-0 Reed-Solomon construction (using the
exceptional isomorphism `PGL(2,5) = S_5`) or a positive-genus algebraic-geometry
code (Bring's curve, genus 4, with `S_5` acting by coordinate permutation)?

## Verdict: no, both rejected

### Genus-0 PGL/RS route: blocked by the Klein finite-subgroup bound

- The repo proves `PGL(2,5) = S_5` (order 120) in `reconstruct/pgl_bound.v`
  (`pgl2_5_eq_s5`, `pgl_card_5 = 120`).
- But the genus-0 covering framework is geometric (char 0): the maximum
  non-dihedral finite subgroup of `PGL(2, Fbar)` is `A_5` of order 60 (Klein).
  `reconstruct/curve_realisation.v` records the old genus-0 hypothesis as
  evaluating to `120 <= 60`, "literally false" under the tightened
  `klein_genus0_bound`. Commit `418bc81` "tighten pgl_bound to Klein
  finite-subgroup bound" is where the arithmetic PGL bound (120) was replaced by
  the geometric Klein ceiling (60).
- The `PGL(2,5) = S_5` coincidence is real but does not rescue the protocol: it
  realizes `S_5` as Mobius transformations on the six points of `P^1(GF(5))`, the
  exotic 3-transitive action, not the natural card shuffle on five positions.
  That action is transitive on the six points, so there is no group-fixed
  coordinate to hold the secret. The genus-0 extended-RS code is symmetric under
  the exotic action, not under the protocol's `S_5`.

### Bring's curve (genus 4) route: axiomatized, and excluded by the no-go

- Hurwitz's bound forces `g >= 3` for a faithful `S_5` action; Wiman (1895)
  rules out genus 3; the first realizable candidate is Bring's curve at genus 4
  [Edge 1978, J. London Math. Soc. s2-18(3): 539-545], the smooth projective
  curve in `P^4` cut out by `sum x_i = sum x_i^2 = sum x_i^3 = 0` with a faithful
  `S_5` action by coordinate permutation. Commit `0b7b4b4` "rebuild s5 on Bring's
  curve" introduced it; `instances/s5/rigidity_s5_instance.v` lines 218-239 carry
  the axiomatization.
- Bring's curve is only AXIOMATIZED (`s5_data_realises_brings`,
  `s5_group_order_eq`); the Coq-level curve construction is deferred. See
  `reconstruct/curve_realisation.v` (the `realised_by_curve` opaque predicate).
- Decisively, the algebraic-geometry recovery route is excluded BY DESIGN for
  `S_5`: the merge-design spec
  (`docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md`, lines
  371-381) states "AG route: excluded by design (`s5_nogo.v`)", and the
  concrete-recovery survey confirms the positive-genus AG path
  (`cover_genus1.v`/`cover_genus2.v`) is the only recovery mechanism with no
  concrete instantiation, so excluding it costs no working instance. Commit
  `6d2cc30` is titled "S5 is the no-go".

## Why the curve cannot help: the obstruction is representation-theoretic

The recoverability needs a secret-encoding `S_5`-invariant submodule of the gap
dimension, and `s5_nogo.v` proves none exists. That obstruction is a property of
the `S_5` representation, characteristic-independent (the difference-vector
argument uses no field hypothesis), so it is independent of which curve realizes
the geometry. A curve supplies genus and ramification data; it does not supply a
gap-window invariant code that the representation forbids. See the companion note
[[20260630-075156-s5-nogo-invariant-submodule-dimensions]] for the
characteristic-independence correction.

## What [9] (the MDS group-code dichotomy) actually says here

Garcia Claro and Tapia Recillas (arXiv:2002.06407): assuming the MDS conjecture
(a theorem for prime fields, Ball 2012), the only non-trivial MDS group code in a
non-semisimple `F_p[G]` is `G = C_p` with `p` odd, the extended Reed-Solomon
code. Over `GF(5)` that is the cyclic `C_5` corner, which is exactly **den Boer**
(genus-0 RS/Massey decode over `GF(5)`, transitive on `Z_5`, `T = 5 > k = 2`),
already wired and axiom-free. `S_5` and `S_5 x S_5` are non-semisimple over
`GF(5)` and not `C_p`, so the dichotomy gives **no** MDS group code for them. [9]
confirms the dividing line the repo already lives on; it is not a new method.

## What does work for recovery (for the record)

- den Boer: custom code on `Z_5` (`C_5`), transitive, `T = 5 > k = 2`, bare
  `ReconPlug`, no curve, genus-0 RS over `GF(5)`. Small, abelian, hand-crafted,
  does not generalize to large non-abelian groups.
- Kim: also genus-0 RS/Massey over `GF(5)`.
- `s5 x s5`: the product route, intransitive (pile-stabilizer, two pile-orbits),
  anonymity within-pile with a cross-pile floor. Carries a `CoveringScheme`.
- The spec states flatly there is no large non-abelian transitive `T > k`
  construction. The single-`S_5` instance carries security only (the
  Schreier-walk mixing, the 286-round bound), not recovery.

## Pointers

- Commits: `0b7b4b4` (rebuild s5 on Bring's curve), `418bc81` (tighten pgl_bound
  to Klein finite-subgroup bound), `6d2cc30` (S5 is the no-go).
- Files: `reconstruct/curve_realisation.v`, `reconstruct/pgl_bound.v`,
  `instances/s5/rigidity_s5_instance.v` (lines 218-239), `reconstruct/s5_nogo.v`,
  `docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md` (lines
  371-381).

## One-line takeaway

The genus-0 PGL/RS route fails the Klein `120 <= 60` bound and only yields the
exotic action, and the Bring-curve genus-4 route is axiomatized and excluded by
the no-go; neither gives the natural-action `S_5` a recoverable threshold plug.
The only working `(k, T)` recovery over `GF(5)` is the cyclic `C_5` Reed-Solomon
corner (den Boer), exactly as the MDS group-code dichotomy predicts.
