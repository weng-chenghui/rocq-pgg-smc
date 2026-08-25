# AlgebraicRigidity, the genus tradeoff, and the S_5 no-go (Q&A)

Note date: 20260607T042916Z

Captures four design-clarification exchanges from the merge brainstorming, about
how the reconstruction-plug design (`ReconPlug`, Option C) interacts with
`AlgebraicRigidity`, what the genus/tradeoff actually means, and what the S_5
no-go does and does not say. Companion to:
- `docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md` (merge spec)
- `20260607T040424Z-reconplug-design-and-denboer-flow.md` (ReconPlug design)
- `20260607T015612Z-concrete-recovery-mechanisms-survey.md` (recovery survey)
- `s5_nogo.v` (the formalized no-go)

---

## Q1. Do we need to change AlgebraicRigidity? Does it already present the group-vs-tradeoff characters?

Mostly yes. `AlgebraicRigidity`'s job is preserved and we keep it, but "nothing
to do" is slightly too strong because it transitively contains the
`CoveringScheme`, whose shape changes.

### What stays
- The record `AlgebraicRigidity = { ar_security : SecurityWitness ; ar_threshold
  : ThresholdWitness }` (`algebraic_rigidity.v:187`) is unchanged in shape.
- Its job is intact: it bundles the anonymity character (`SecurityWitness`,
  driven by `|G|`) with the threshold character (the genus/gap inside
  `ThresholdWitness`'s `CoveringScheme`), and `security_threshold_tradeoff`
  (`cover_tradeoff.v:140`) presents the tradeoff. That theorem reads
  `cs_data`/`cs_gap`, both still present, so it survives unchanged.
- The reconstruction-plug work is additive: it carves the bare recovery plug out
  for the program and den Boer; it does not touch the tradeoff narrative.

### What still ripples
`AlgebraicRigidity -> ThresholdWitness -> CoveringScheme`, and `CoveringScheme`
changes from 9 flat fields to `{ cs_plug : ReconPlug ; cs_data ; cs_gap }`, plus
`pgg_recon_endpoints` now carries `content`. So:
- Instances that build an `AlgebraicRigidity` (s5, s5x5, kim) restructure how
  they construct their `CoveringScheme`: nest the bare-plug fields into
  `cs_plug`, set `cs_content = id`. Mechanical, no re-proofs (the
  `*_perm_compatible`/`*_cs_gap`/`*_hurwitz` lemmas survive verbatim).
- `ar_protocol_correct` threads the `content` field (`= id` for these), a small
  edit in `algebraic_rigidity.v`. With transparent `Notation` accessors
  (`cs_scheme := rp_scheme (cs_plug ...)`), the consuming lemmas otherwise
  compile unchanged.
- `security_threshold_tradeoff` / `ar_tradeoff`: untouched.

### den Boer touches none of it
den Boer plugs a bare `ReconPlug` and proves correctness via
`pgg_hidden_invariant_perm` directly, so it builds no `CoveringScheme` and no
`AlgebraicRigidity`. Its old genus-0 RS5 `AlgebraicRigidity`
(`five_card_security.v:325`) is deleted, not migrated.

### Terminology correction
The tradeoff is anonymity-set size `|G|` vs threshold gap (genus), not literally
"group vs AG-code." Under the new design the genus is a `CoveringData`
decoration backed by a `realised_by_curve` axiom, sitting on top of a
combinatorial recovery scheme (sum-mod / product / three-consec). The actual
recovery is never an AG code; the AG curve is only the (shelved) geometric
justification for positive genus.

Net: keep `AlgebraicRigidity`, keep the tradeoff theorem, do not redesign that
layer. The only work is mechanical: restructuring the `CoveringScheme` literals
in the three tradeoff-carrying instances and threading `content` through
`ar_protocol_correct`. den Boer opts out of the whole layer.

---

## Q2. Since genus means an AG curve, is the tradeoff meaningful only if the reconstruction is curve-based?

Largely yes. The genus is only meaningful as the genus of an actual curve/cover;
a purely combinatorial scheme has no genus on its own.

### Genus is curve-contingent, by construction
`cd_genus` is the genus of the Galois cover `C -> P^1` whose deck group is the
monodromy group `G`, tied to `|G|` by Riemann-Hurwitz (`cd_hurwitz`). It is
meaningful only if such a cover exists. The framework makes it meaningful by
requiring a `realised_by_curve` axiom: the genus is asserted to be the genus of a
real curve realizing `G`'s action. So the `|G|`-vs-genus tradeoff has meaning
through a curve, not from the combinatorial scheme alone.

### The in-scope schemes are curve-realizable, by real curves
- genus 0: the cover is `P^1` itself (sum-mod, RS5). Trivially real.
- s5x5: the cover is two copies of Bring's curve (genus 4, automorphism group
  `S_5`), so genus 8 total. `S_5 x S_5` as deck group of two genus-4 Bring's
  components is a real geometric object.
So for the instances we keep, the tradeoff is genuinely meaningful; it is
axiom-backed but the underlying mathematics is true.

### Honest limits
1. The framework does not prove the combinatorial recovery equals the AG-code
   decode on the curve. It attaches the cover's genus via the axiom and checks
   `cs_gap : T <= k + 2*genus` (the Goppa-bound shape). The tradeoff reads as
   "the anonymity group `G`, realized by a genus-g cover, admits a `(T,k)`
   threshold consistent with what a genus-g AG code could achieve."
2. The tradeoff's meaning is exactly as strong as the `realised_by_curve` axiom.
   For an instance with no known realizing curve, attaching a genus would be a
   fiction and the tradeoff vacuous. For s5x5 (Bring's) and genus-0 (P^1) it is
   grounded; do not attach a genus to a scheme whose cover you cannot name.

### Why the split is right
This is exactly why the reconstruction-plug split is the correct architecture:
- `ReconPlug` (the recovery you run): combinatorial, computable, no genus, no
  axiom. Fully grounded. Used by the program and den Boer.
- `CoveringScheme` / `AlgebraicRigidity` (the `|G|`-vs-genus tradeoff): the
  curve-contingent decoration, meaningful only via `realised_by_curve`. Optional,
  carried only by instances with a real cover (s5x5, the genus-0 ones).
den Boer carries no genus at all. s5x5 carries the tradeoff, resting honestly on
Bring's curve. The design attaches the genus only where a real cover backs it and
keeps recovery curve-free everywhere. No design change follows; this is the
justification for the split already chosen.

---

## Q3. Why can S_5 (in the no-go file) not have a covering curve? (Remembered wrong.)

The memory is slightly off. The no-go is NOT "S_5 has no covering curve." It is a
representation-theory obstruction.

### What the no-go proves
The wired S_5 instance puts shares on the natural permutation action of S_5 on
six `GF(5)` coordinates: coordinate 0 is a fixed secret slot, coordinates 1..5
are permuted. An AG-code reconstruction with a threshold gap would need an
S_5-invariant submodule that carries the secret direction `e0` and has a
dimension in the gap window `[3,4]`. The file proves none exists:
- `s5_no_secret_dim3` / `s5_no_secret_dim4` (`s5_nogo.v:457,474`): no
  secret-carrying S_5-invariant submodule of dimension 3 or 4.
- `s5_gate_rejects` / `s5_wired_gap_impossible` (`:492,:513`): therefore the
  wired S_5 instance cannot realize a strict threshold gap via an invariant code.

### Kernel reason (char-5 specific)
`perm_module_no_dim23` (`:283`): the natural permutation module `GF(5)^5` of S_5
has no submodule of dimension 2 or 3; its submodule dimensions are exactly
`{0,1,4,5}`. Proof: a submodule either lies in the all-ones line (rank <= 1) or
contains a non-constant vector, which forces a difference vector `e_i - e_j` in,
and 2-transitivity of S_5 then forces the whole sum-zero subspace (rank >= 4).
The six-coordinate reduction sends a secret-dim-d submodule to a dim-(d-1)
submodule, so secret-dims 3 and 4 map to forbidden dims 2 and 3. This is char-5
specific: `5 | 5` puts the all-ones vector inside the sum-zero subspace and makes
the lattice uniserial; in coprime characteristic Maschke would split off a
dimension-3 "heart" and dims 2,3 would appear. The alphabet for a 5-card deck
must be `GF(5)`, so char 5 is forced.

### The distinction being conflated
S_5 DOES have a covering curve: Bring's curve (genus 4, automorphism group
exactly S_5) realizes the S_5 action; it is the per-pile component of s5x5's
genus-8 realization. Two different roles of "curve/AG":
- Cover (anonymity side, the `|G|`-vs-genus tradeoff): exists for S_5 (Bring's).
- AG-code reconstruction with a gap (recovery side): blocked by
  `perm_module_no_dim23`.
So the no-go kills the AG-code recovery route for S_5, not the cover.

### Design rationale
- S_5 uses sum-mod (`T = k`, no gap): it cannot get a gap from an AG code, so it
  does not try.
- s5x5 gets its `T > k` from the product construction (two sum-mod piles), a
  combinatorial mechanism, not an AG code. Its genus (Bring's, 8) is the cover's
  genus on the anonymity side, decorative.
- The positive-genus AG route stays shelved because, for the groups we use, it is
  either representation-theoretically blocked (S_5) or restricted to the
  `D_*`/Frobenius family (the fix-the-secret automorphism constraint).

---

## Q4. So AG-code cannot be used for S_5 no matter the curve, by AG-code's own requirements?

Essentially right, with one refinement: it is the AG code's requirements
colliding with the PGG coupling, and the collision is upstream of the curve.

### Why no curve helps
For an AG code to serve as S_5's reconstruction in the PGG framework, its
coordinate automorphisms must equal the S_5 monodromy, i.e. the natural
permutation action on the deck coordinates, with the secret pinned to a fixed
coordinate. So whatever curve you pick, its AG code must be an S_5-invariant
submodule of the same fixed module: the natural permutation module `GF(5)^6`
(secret coord + 5 permuted). The curve only chooses which invariant submodule; it
cannot change which module you choose inside, because that module is fixed by the
monodromy, not by the curve.

That module over `GF(5)` does not contain a submodule of the dimension a gap code
needs:
- Submodule dimensions of the 5-coordinate permutation module are exactly
  `{0,1,4,5}` (`perm_module_no_dim23`).
- So secret-carrying submodule dimensions of the 6-coordinate module are
  `{1,2,5,6}` (add 1 for the fixed secret coordinate).
- A strict threshold gap forces the code dimension into the window `{3,4}`
  (`gap_dimension`).
- `{1,2,5,6} ∩ {3,4} = ∅`. No curve's AG code can land in the window.

### The precise cause (the conjunction)
1. PGG coupling: the code's coordinate symmetry must be the S_5 monodromy
   (natural permutation action). This fixes the representation, making the curve
   irrelevant.
2. Secret in a fixed coordinate (the reduction that shifts dimensions by one).
3. Gap requires code dimension 3 or 4.
4. Char 5: `5 | 5` makes the permutation module uniserial, so dimensions 2 and 3
   are absent. In coprime characteristic the window dimensions would exist.

### Scope caveat
This is for S_5 acting naturally on the 5-card `GF(5)` deck. The no-go is
char-5-specific and action-specific: a different group, deck action, or
coprime-characteristic alphabet could reopen the window. But for the wired S_5
instance, the curve genuinely does not matter, the AG-gap route is dead at the
representation level, and that is why S_5 reconstructs with sum-mod (no gap) and
s5x5 gets its gap from the combinatorial product construction instead.
