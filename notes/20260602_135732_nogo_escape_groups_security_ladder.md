# Which transitive groups on 5 points escape the S_5 no-go, and what they cost in security

Date: 2026-06-02T13:57:32Z

One-line summary: among the five transitive groups of degree 5, exactly two clear
the dimension obstruction that defeats the wired S_5 gap, namely the cyclic group
Z_5 and the dihedral group D_5. They are exactly the non-2-transitive ones. Z_5 is
abelian and D_5 is non-abelian, and that split is the security axis. The obstruction
itself is 2-transitivity.

## The question

A proposed escape from the formalized S_5 wired-gap no-go (`reconstruct/s5_nogo.v`)
is to drop the wired group from S_5 to a smaller transitive subgroup so that a
positive threshold gap T > k becomes reachable. The candidates raised were the
dihedral group D_5 and the cyclic group Z_5. Two follow-up questions: are these
candidates all abelian, and does the choice carry a security cost.

## Correction first: the candidates are not all abelian

- Z_5, the cyclic group of order 5, is abelian. Every cyclic group is abelian. It
  is the simplest non-trivial choice.
- D_5, the dihedral group of order 10, is non-abelian. It is the semidirect product
  Z_5 rtimes Z_2 in which the reflection inverts the rotation, s r s = r^{-1}. Since
  r has order 5, r and r^{-1} differ, so rotations and reflections do not commute.
  In the codebase D_5 is built from two non-commuting generators, `cycle_r` (the
  5-cycle ncycle) and `cycle_s = (1 4)(2 3)` (a reflection), in
  `pgg-smc/groups/pgg_cycle.v`.

S_5 itself (order 120) is the non-abelian group, and it is the choice of the s5 and
s5x5 rigidity instances, which is exactly where the no-go bites.

## The escape has a real security cost, and it is already measured in the codebase

The framework's anonymity rests on the size and structure of the symmetry group
that the monodromy walk ranges over. Shrinking that group weakens anonymity through
two distinct mechanisms.

1. Anonymity-group size collapses from 120 to 5 or 10. `cyclic_search_space_le`
   in `instances/abelian/pgg_abelian.v` bounds the cyclic search space by the order
   of the generator, which is 5 for Z_5. S_5 offers 120.
2. Abelianness collapses the word search space. In an abelian group the order of
   shuffles does not matter, so the count of distinguishable shuffle words drops
   from the free count to the count of frequency vectors.
   `abelian_word_collapse.v` proves this collapse: `abelian_search_space_bound`
   gives a bound of C(L + r, r) by stars and bars, and `cyclic_G_abelian` in
   `pgg_abelian.v` is the lemma that triggers it. A non-abelian group of the same
   generator count does not collapse this way.

The second mechanism is the reason the abelian-versus-non-abelian split matters.
Z_5 suffers both penalties. D_5, being non-abelian, suffers only the size penalty
and keeps a richer word space, and its order is 10 rather than 5.

## The structural fact: the obstruction is 2-transitivity

The S_5 no-go proof reduces to a single kernel fact, `perm_module_no_dim23` in
`s5_nogo.v`: the natural permutation module GF(5)^5 has no submodule of dimension 2
or 3. The proof uses only 2-transitivity of the acting group. A submodule that
contains any non-constant vector contains a difference vector e_i - e_j, and
2-transitivity (realized in the proof by `pair_perm`) carries that one difference
vector to every difference vector, so the submodule contains the whole sum-zero
subspace of dimension 4. Hence every submodule is either inside the constant line,
of dimension at most 1, or contains the sum-zero space, of dimension at least 4.
Over GF(5) the constants sit inside the sum-zero space, so the lattice is uniserial
and the dimensions are exactly {0, 1, 4, 5}, never 2 or 3.

A positive gap at length 6 needs a secret-encoding invariant code of dimension 3 or
4, which translates to a dimension-2 or dimension-3 submodule of the permutation
module. So 2-transitivity is precisely what forbids the gap. To open the gap you
must drop to a group that is transitive but not 2-transitive.

## The classification at degree 5

There are exactly five transitive groups of degree 5, and they split cleanly by
2-transitivity.

| Group | Order | Abelian | 2-transitive | Clears the obstruction |
|-------|-------|---------|--------------|------------------------|
| Z_5 (cyclic) | 5 | yes | no | yes |
| D_5 (dihedral) | 10 | no | no | yes |
| F_20 = AGL(1,5) | 20 | no | yes (sharply) | no |
| A_5 | 60 | no | yes | no |
| S_5 | 120 | no | yes | no |

Correction to an earlier remark made in discussion: F_20 = AGL(1,5), the affine
group x -> a x + b on GF(5), is sharply 2-transitive on the five points, because
the point stabilizer x -> a x acts transitively on the four nonzero points. So F_20
is 2-transitive and fails by the same difference-vector argument as S_5 and A_5. It
is not an escape. The earlier suggestion to "verify F_20 as a possibly larger
escape" resolves to "F_20 fails".

Consequently, at degree 5 the groups that clear the obstruction are exactly the two
non-2-transitive transitive groups, Z_5 and D_5. D_5 is the unique maximal one.

Why each escape clears it:

- Z_5 over GF(5): the action on the five shares is a single 5-cycle, so the
  permutation module is the regular representation GF(5)[x]/(x^5 - 1), which equals
  GF(5)[x]/(x - 1)^5 because Frobenius collapses x^5 - 1 to (x - 1)^5. That is a
  uniserial local ring with submodules of every dimension 0 through 5. Equivalently
  M = perm_mx(sigma) - 1 is a single nilpotent Jordan block, so dim ker M^k = k.
  Dimensions 2 and 3 are present, so dimensions 3 and 4 of the secret-encoding code
  are reachable.
- D_5 over GF(5): every D_5-submodule is in particular a Z_5-submodule, so it lies
  in the uniserial chain above. The reflection acts as inversion x -> x^{-1} on the
  group algebra, which sends x - 1 to a unit multiple of x - 1, so each ideal
  (x - 1)^i is reflection-stable. The whole chain survives, and dimensions 2 and 3
  remain.

## The security ladder among escapes

```
Clears the obstruction, gap possible:    Z_5 (5, abelian)  <  D_5 (10, non-abelian)
Fails, no gap, the no-go bites:           F_20 (20)  <  A_5 (60)  <  S_5 (120)
                                          all three are 2-transitive
```

So among the groups that buy a gap, D_5 is strictly more secure than Z_5. It is
non-abelian, so it dodges the abelian word-space collapse, and its order is double.
D_5 is the most secure escape available at degree 5, not F_20.

## The tension to resolve

The two in-scope card protocols already use Z_5, the weakest of the escapes. den
Boer 1989 (`instances/denboer1989/five_card_group.v`, `fc_sigma` the 5-cycle, shuffle
`rot k` a uniformly random cyclic cut) and Kim 2025 (`instances/kim2025/five_card_kim.v`,
the same 5-cycle with all five powers for a biased cut) both ride on the cyclic cut.
Their security is designed around it and is proven for that model, so for the card
game the small abelian anonymity of Z_5 is the intended and adequate setting.

This leaves a genuine choice for any redesign that wants a gap:

- Card-faithful: Z_5. It is what the protocols use, abelian, weakest anonymity,
  proven secure for the five-card functionality.
- Anonymity-strongest among escapes: D_5. Non-abelian, order 10, no word collapse,
  still clears the obstruction. The cost is more proof work for reflection
  invariance and a less standard card operation, namely flipping the deck order.

## Verification status

- Z_5 clears the obstruction: a concrete formalization path is checked. The
  load-bearing lemmas exist in coq-mathcomp-character, namely
  `kermx_centg_module` (kernel of a centralizing matrix is a submodule) and
  `mxrank_ker` (dimension bookkeeping), and the nilpotency facts M^5 = 0 and
  M^4 <> 0 reduce to perm_mx being a monoid morphism plus characteristic 5. The
  planned positive theorem is `z5_gate_accepts : feasible rGV e0 [:: 3; 4]` in a
  new `reconstruct/z5_feasible.v`, the axiom-free counterpart to `s5_gate_rejects`.
- D_5 clears the obstruction: established by the reflection-stability argument
  above. Not yet formalized.
- F_20, A_5, S_5 fail: F_20 by sharp 2-transitivity, A_5 and S_5 by 2-transitivity,
  all via the `perm_module_no_dim23` difference-vector argument. S_5 is the
  formalized case.

Important scope caveat. Clearing the dimension obstruction is necessary for T > k
but not sufficient. A complete scheme also needs the code's minimum distance and
dual distance at the concrete instance, which fix positive genus and the recovery
threshold. Those are decidable over GF(5) at length 6 but are a separate check. The
result `z5_gate_accepts` should be reported as "the obstruction that killed S_5 is
gone for the cyclic card group", not as "Z_5 has a working T > k scheme".

## Cross-references

- `reconstruct/s5_nogo.v`: the formalized S_5 no-go, `perm_module_no_dim23`,
  `s5_gate_rejects`, `s5_wired_gap_impossible`.
- `reconstruct/invariant_profiler.v`: `feasible`, `secret_inv_dim`, `maschke_ss`.
- `reconstruct/gap_dimension.v`: the gap-to-dimension window forcing dim in {3, 4}.
- `instances/abelian/pgg_abelian.v`: `ncycle`, `ncycle_order`, `cyclic_G_abelian`,
  `cyclic_search_space_le`.
- `instances/abelian/abelian_word_collapse.v`: `abelian_search_space_bound`,
  the C(L + r, r) collapse.
- `groups/pgg_cycle.v`: `cycle_r`, `cycle_s`, the D_5 generators.
- `instances/denboer1989/five_card_group.v`, `instances/kim2025/five_card_kim.v`:
  the card protocols on the cyclic cut.
- Memory: `project_pgg_framework_coupling` (the |F| = N = sheet count coupling),
  `project_s5_nogo_formalized`.

## Addendum, 2026-06-02T14:09:52Z: does a large group (more security) strictly conflict with the T > k gap (the recovery scheme)?

Short answer. In the framework as it stands, yes, it is a strict tradeoff with a
sharp cutoff. As a general mathematical law it is a strong generic tension but not
absolute. The cleanest reading is that the real conflict is between symmetry-size
and the gap, and this framework turns that into a security-versus-gap conflict only
because it defines security as invariance under a large group.

### Level 1, proven and sharp at degree 5

The cutoff is not raw cardinality, it is 2-transitivity. The `perm_module_no_dim23`
argument kills every intermediate-dimension submodule for any 2-transitive group.
Among the five transitive groups on 5 points, the non-2-transitive ones (Z_5 of
order 5, D_5 of order 10) can carry the gap, and the 2-transitive ones (F_20 of
order 20, A_5 of order 60, S_5 of order 120) cannot. So at degree 5 there is a clean
threshold: order at most 10 can escape, order at least 20 cannot. Size and
2-transitivity happen to coincide there.

### Level 2, why this is not a degree-5 accident: Riemann-Hurwitz

The gap is positive genus, since `ts_T = ts_k + 2g` forces `g > 0` for a gap. Genus
0 is the projective line, whose automorphism group is PGL(2, q) of order about q^3,
sharply 3-transitive, and it gives exactly the MDS Reed-Solomon codes with no gap.
Push to positive genus and, generically, the Hurwitz bound caps the automorphism
group at 84(g - 1). So "huge symmetry acting on the code" and "positive genus" pull
against each other at the level of curves, not only at degree 5. This is the duality
the project already keeps separate and the memory warns not to conflate: a
Klein-type bound caps the group on the rigidity and security side, and
Riemann-Hurwitz caps the gap on the recovery side. The strict conflict is what you
get when one group is forced to satisfy both bounds at once, which is the current
coupling.

### Level 3, why it is not an absolute law, two escapes with a price

- Exotic characteristic-p curves. The Hurwitz bound 84(g - 1) fails in
  characteristic p. Hermitian and other Deligne-Lusztig curves have large genus and
  also large, highly transitive automorphism groups such as PGU(3, q). So "large
  symmetry plus positive genus" is not logically impossible, only rare. The catch is
  that these curves need the field to grow with the curve, which breaks the
  framework's |F| = N = sheet-count coupling. They buy out of the conflict by paying
  with the coupling.
- Re-grounding security off the symmetry group. The conflict is symmetry versus gap.
  It reads as security versus gap only because this framework derives anonymity from
  the size of the monodromy group. The other, standard notion of secret-sharing
  security, namely that any coalition below threshold learns nothing, is a property
  of the code's dual minimum distance, not of any symmetry group. A positive-genus
  AG code can be information-theoretically private against large coalitions while
  having a trivial automorphism group. Measure security by coalition-privacy rather
  than by group-anonymity and the two decouple, with no conflict. The price is giving
  up the group-anonymity story that motivated the permutation-group framing.

### Takeaway

Strict in the current design, where one group is both the security group and the
code-symmetry group. A strong generic tension even in general, via Hurwitz.
Dissolvable in two ways, either with special characteristic-p curves that break the
|F| = N coupling, or by changing what "secure" means from group-anonymity to
code-distance privacy. There is no setting that keeps all three of a large symmetry
group, the native GF(N) at N sheets, and a positive gap at once. That triple is the
impossible corner.

### A correction to the framing of the question

A gap T > k is not "easier to recover". It is a ramp, a positive-genus deficiency
from MDS. What it actually buys is code length beyond the field size, which is the
property the project was chasing, at the cost of needing more shares to reconstruct,
not fewer.

## Addendum, 2026-06-02T14:18:50Z: is there a non-abelian candidate near S_5's size (120)?

This sharpens, and partly corrects, the "impossible corner" stated above. The
binding constraint is not abelian-versus-non-abelian and not raw cardinality. It is
2-transitivity, and at prime degree 2-transitivity is forced precisely when the
group is large relative to the number of sheets.

### The decisive fact at degree 5

By the classical theorem on transitive groups of prime degree (Burnside): a
transitive group of prime degree p is either 2-transitive, or it is contained in the
affine group AGL(1, p) = Z_p rtimes Z_{p-1}, with the translations Z_p acting
regularly. The non-2-transitive transitive groups of degree p are therefore exactly
Z_p rtimes Z_d for d a proper divisor of p - 1, of order p * d, at most p(p-1)/2.

At p = 5: p - 1 = 4, proper divisors {1, 2}, giving Z_5 (abelian) and
Z_5 rtimes Z_2 = D_5 (order 10, the only non-abelian one). The step d = 4 is
F_20 = AGL(1, 5), which is sharply 2-transitive and fails. So on 5 sheets the
non-abelian escape ceiling is D_5 at order 10. No order-120 non-abelian group acts
on 5 points without being 2-transitive. The rich groups near 120, namely A_5 and
S_5, are exactly the 2-transitive ones the no-go kills.

### The ceiling grows with the degree

The non-abelian escape ceiling is p(p-1)/2, the order of Z_p rtimes Z_{(p-1)/2},
and it grows with the prime degree p.

| Degree p | Largest non-abelian escape | Order |
|----------|----------------------------|-------|
| 5 | Z_5 rtimes Z_2 = D_5 | 10 |
| 11 | Z_11 rtimes Z_5 | 55 |
| 13 | Z_13 rtimes Z_6 | 78 |
| 17 | Z_17 rtimes Z_8 | 136 |
| 19 | Z_19 rtimes Z_9 | 171 |

So the natural candidate near S_5's size is Z_17 rtimes Z_8, order 136, acting on 17
sheets over GF(17). It is non-abelian, transitive, not 2-transitive, so it clears the
dimension obstruction (Level 1).

### Two caveats

1. These are affine Frobenius groups, never rich groups. At prime degree, anything
   non-2-transitive is forced to be Z_p rtimes Z_d, solvable, with a regular normal
   p-cycle and a cyclic complement. You never get a near-S_5 group that is
   non-solvable or primitive-and-interesting. "Large and non-abelian" is achievable
   only in the affine way, not in the way S_5 is large. The full mixing symmetry that
   motivated S_5 is exactly what forces 2-transitivity and kills the gap.
2. Clearing the obstruction is still only Level 1. It guarantees intermediate-
   dimension invariant submodules exist. It does not by itself give a positive-genus
   gap. That needs an actual positive-genus curve over GF(p) with about p rational
   points carrying Z_p rtimes Z_d in its automorphism group. Riemann-Hurwitz permits
   it, since order 136 needs only genus at least 3, but whether such a curve exists
   over GF(17) is an algebraic-geometry existence question, not verified here, and
   not to be asserted without instantiation.

### Corrected takeaway

You can buy a large, non-abelian group with a gap, but only by spreading it across
many sheets as an affine group, never at N = 5, and never as a rich primitive group
like S_5. "Large relative to the degree" and "positive gap" remain mutually
exclusive at every prime degree. The "impossible corner" is therefore impossible at
fixed N = 5, and at larger prime degree it opens only to the affine ceiling
p(p-1)/2, subject to the unverified Level-2 curve-existence question. Composite
prime-power degrees give more room, since imprimitive groups are automatically
non-2-transitive, but they leave the prime-field setting and are not analyzed here.

## Addendum, 2026-06-02T14:26:05Z: can the near-S_5 escape group Z_17 rtimes Z_8 be a card game?

This grounds the previous addendum against the actual card-and-pile model and
exposes why the large non-abelian escape is not free as a card game.

### Decoding Z_17 rtimes Z_8 as card moves

Identify the 17 positions with F_17 = {0, ..., 16}. The group is the affine maps
x -> a*x + b in AGL(1, 17), with b in F_17 and a of multiplicative order 8.

- The translation part Z_17, x -> x + b, is a random cyclic cut of a 17-card cycle.
  A genuine physical card operation, den Boer's 5-card cut scaled to 17.
- The multiplier part Z_8, x -> a*x mod 17, with a = 2 (order 8 mod 17, since
  2^4 = 16 = -1), is the doubling map x -> 2x mod 17. As a permutation it is
  (0)(1 2 4 8 16 15 13 9)(3 6 12 7 14 11 5 10), two 8-cycles and a fixed point. This
  is a perfect-shuffle or faro-type move, realizable as a dealer skill but a precise
  number-theoretic operation, not a casual shuffle.

So as a single 17-card pile, Z_17 rtimes Z_8 is a mathematical-card-trick group:
free cut plus a faro doubling. And because 17 is prime, those cards cannot be split
into equal piles. The prime-degree affine groups are inherently single-pile,
single-cycle objects. That is the price of staying field-clean: prime degree gives
GF(17) but forbids piles.

### The card-natural route to large non-abelian groups is piles

Card-based cryptography has two primitive operations: the cut (Z_n within a pile)
and the pile-scramble shuffle (S_m permuting m piles). Combined they give a wreath
product Z_n wr S_m on N = m*n positions. Any group that respects a pile structure is
imprimitive, and imprimitive groups are never 2-transitive, so piles defeat the
obstruction by construction. The "constant on each pile" vectors form an
m-dimensional invariant subspace, so the pile structure itself supplies the
intermediate invariant submodule that S_5 lacked. The framework already has such an
instance: s5x5 is two piles of five (pgg_s5x5.v, s5x5_pile.v).

### Two catches, and the real lesson

1. Composite degree breaks the prime field. Two piles of five is N = 10, and GF(10)
   does not exist. This is the s5x5 N = 10 problem in project_s5_nogo_formalized. The
   representation-theory analysis lives over a prime field, so a pile structure
   forces work over a prime-power N or a per-pile decomposition.
2. A rigid within-pile group gives no gap. s5x5 uses full S_5 inside each pile, which
   is 2-transitive, so each pile is internally rigid and one is back to the per-pile
   S_5 no-go. The block structure alone is too coarse to encode a secret with a gap.
   To get a genuine secret-encoding gap from piles the within-pile group must itself
   be non-2-transitive, that is Z_5 wr S_2 (cut each of two 5-card piles, then swap
   the piles), not S_5 wr S_2.

### Synthesis: two escape families, neither complete

| Escape family | Card-game reading | Field | Gap source |
|---------------|-------------------|-------|-----------|
| Affine Z_p rtimes Z_d, prime degree | cut plus a faro/doubling move | clean, GF(p) | single cycle, no piles |
| Pile wreath Z_n wr S_m, composite degree | cut piles plus scramble piles | broken, N = m*n not a prime field | block structure, only if within-pile is non-2-transitive |

Z_17 rtimes Z_8 is field-clean but not a natural card game, since its non-cut
generator is a faro doubling on a 17-card cycle. The card-natural large groups are
the pile wreaths, but they sit at composite degree where the prime-field machinery
breaks, and they yield a gap only if one cuts inside each pile rather than fully
shuffling it. A single group that is at once a natural card game, over a prime field,
large and non-abelian, and gap-bearing is still not in hand.

## Addendum, 2026-06-02T14:34:45Z: a search strategy for a candidate satisfying card-game, field, and gap all at once

The goal is a group plus code that is simultaneously a natural card game, lives over
a genuine prime-power field, and carries a positive-genus (positive Singleton
defect) secret-encoding invariant code. The strategy is built to either find one or
prove the corner empty. Both outcomes are useful.

### The core move: search at prime-power degrees, not prime degrees

The tension is entirely Field versus Card-game. Card-natural groups want a block
structure (piles, hence imprimitive, hence non-2-transitive). Fields want a prime
power. The two extremes already examined are both bad. Prime N (like 5) is a field
but has no nontrivial blocks, only the bare cut Z_p or an affine group whose extra
generator is a faro. Composite non-prime-power N (like 10) has blocks but no field,
the s5x5 trap.

The unexplored middle is proper prime powers N = p^k with k >= 2. There GF(p^k) is a
genuine field, and the p^k points carry the affine geometry over GF(p), whose lines,
planes, and subfield cosets are exactly piles. The cleanest case is N = p^2, a p by
p grid of cards over GF(p) or GF(p^2), with card moves cut a row, cut a column,
scramble rows, scramble columns. That group is imprimitive, non-2-transitive,
card-natural, and lives over a real field.

### Reframe the gap source as known non-MDS code families with card symmetry

The gap is positive Singleton defect, equivalently positive genus, equivalently not
MDS. So search for a non-MDS code carrying card symmetry. Two concrete handles:

- Cut-invariant codes are exactly cyclic codes, the ideals of GF(q)[x]/(x^n - 1).
  Non-MDS cyclic codes such as BCH exist when the length is coprime to the
  characteristic, the separable regime, and they have positive defect. This is also
  the likely reason Z_5 over GF(5) clears Level 1 but may stall at Level 2: at length
  equal to the characteristic the cyclic codes are repeated-root and degenerate,
  probably MDS, hence no gap. That must be computed, not assumed.
- Grid-invariant codes include product codes C_1 tensor C_2, generically non-MDS.
  Lead candidate: the [3,2,2] parity code over GF(3), which is cyclic hence
  cut-invariant, formed into a product on a 3 by 3 grid, gives [9, 4, 4]. The MDS
  distance for [9,4] is 6, so the defect is 2, a genuine gap. It is invariant under
  row-cuts, column-cuts, and the transpose, so card-natural, and lives over GF(3),
  field-clean. This is the strongest single candidate. What remains unverified, and
  must not be asserted without instantiation, is whether it maps onto the framework's
  secret-encoding and T > k threshold and genus notions.

AG codes on superelliptic curves y^n = f(x) and Artin-Schreier curves y^p - y = f(x)
are a further family: a cyclic automorphism is the cut, and positive genus is built
in.

### Search-and-prune pipeline

1. Enumerate card-natural groups at prime-power degrees N in 4, 8, 9, 16, 25, 27,
   ..., as towers of cuts and pile-scrambles (wreath and affine subgroups). Discard
   any 2-transitive group at once, since s5_nogo kills it.
2. Level 1, cheap and decidable. For each survivor and field, compute the genuine
   invariant-submodule dimension profile with invariant_profiler.v, the real
   mxmodule lattice, never subset-sums of irreducibles. Keep only groups with a
   secret-encoding submodule of intermediate dimension.
3. Level 2, the hard gate. Build each survivor's code as an explicit evaluation
   matrix over GF(q) and compute its minimum and dual distance, certifying positive
   defect and the privacy threshold. Structural bounds like hyp_goppa_wt_mdeg where
   they apply, direct computation otherwise. No axiom that such a code exists.
4. Verify the survivor end-to-end in Rocq: feasibility, positive genus, and
   ts_T > ts_k non-vacuously, with Print Assumptions clean.

### Impossibility fallback, equally a result

If nothing survives, the deliverable flips to a meta-no-go: no card-natural group
over a prime field admits a secret-encoding positive-genus invariant code. That
generalizes s5_nogo from 2-transitive groups to all cut-and-pile groups and settles
that the corner is empty. Build it from the uniseriality and 2-transitivity
machinery plus a Singleton-defect argument for cyclic and product codes.

### Guardrails, the retrospective rules for this failure-prone regime

- Instantiate before abstracting. Every candidate ends in a concrete vm_compute or
  structural witness at the smallest instance, never an instance-shaped axiom.
- The headline theorem must assert ts_T > ts_k, not an upper bound that the
  degenerate case satisfies.
- One realizability audit per candidate at the exact (N, q, group, code).
- Keep recovery genus and rigidity genus as separate named quantities.
- Log every pruned candidate and the reason, so searched does not quietly mean
  searched some.

### Honest odds and the first spike

Level 1 should be easy to satisfy at the grid degrees, and Level 2 is where most
candidates die, because positive defect plus enough rational points plus a
card-symmetry group is a tight simultaneous demand. The [9,4,4] product code is the
one place to bet, since its defect is structural rather than accidental. The
cheapest first experiment is to instantiate the 3 by 3 grid product code over GF(3),
compute its distance and its invariance group in Rocq, and check whether it clears
Level 1 and Level 2 before investing in extending the framework to a grid instance.

## Addendum, 2026-06-02T23:31:16Z: fan-out results and verification of the working candidate

Four Sonnet research agents were fanned out over the candidate regions (grid/product,
cyclic/BCH, AG-curve, pile/affine). Results were collected and verified by direct
finite-field computation in Python (exact arithmetic), following the
instantiate-and-compute discipline rather than trusting asserted parameters.

### VERIFIED WORKABLE: elliptic genus-1 cut over GF(7), corrected to [6,4,2]

- E: y^2 = x^3 + 1 over GF(7) has exactly 12 rational points (verified by
  enumeration). The automorphism sigma(x,y) = (2x, -y) has order 6 (2 is a cube root
  of unity mod 7) and a genuine 6-point orbit {(1,3),(2,4),(4,3),(1,4),(2,3),(4,4)}.
- CORRECTION to the agent's claim: it proposed a [7,5,2] code, but L(5.O) cannot be
  evaluated at O, which is its pole. The correct code evaluates the Riemann-Roch
  basis L(4.O) = {1, x, x^2, y} at the 6-orbit, giving a [6,4,2] code over GF(7). The
  MDS distance for [6,4] is 3, the actual minimum distance is 2 (verified by
  enumerating all 7^4 = 2401 codewords), so the Singleton defect is 1 = genus 1 = a
  genuine gap.
- sigma permutes the 6 code coordinates as a clean 6-cycle [1,2,3,4,5,0] (verified),
  so the code is genuinely cut-invariant and the cut is a literal cyclic rotation of
  6 cards. The invariance is clean because gcd(6,7)=1 (Maschke applies).
- gap_dim_window for (n=6, k=4, g=1) passes all four conditions.

So a single object satisfies card-game (a Z_6 cut), genuine field (GF(7)), and gap
(genus 1, non-MDS), confirmed by computation. It is essentially the framework's own
cover_genus1.v construction with the automorphism chosen to be a cut.

### CONFIRMED DEAD: cut-only cyclic codes

Verified that every cyclic code over GF(3) at length 3 and over GF(5) at length 5 is
MDS (each dimension hits the Singleton bound exactly). The cut-only route over GF(N)
at length N cannot produce a gap. This is the Level-2 reason the Z_5-over-GF(5)
feasibility result clears the dimension obstruction but yields no genuine gap.

### KEY INSIGHT from the verification

The cut is never the obstacle. The dead route's cut is a coordinate rotation of a
cyclic code, which is MDS-locked. The working route's cut is the same kind of cyclic
permutation realized as an elliptic-curve automorphism, with the code a genus-1 AG
code, which is non-MDS. Same card move, different code construction.

### PARTIAL candidates

- Grid product [9,4,4] over GF(9): non-MDS confirmed (defect 2), but fails the
  framework's g < k (here g = 4 = k). A [9,5] reparametrization with g = 3 passes
  gap_dim_window, but whether a Z_3 x Z_3-invariant secret-encoding non-MDS code
  exists at dimension 5 is unverified.
- Pile Z_2 wr S_2, [5,3,2] over GF(4): parameters pass gap_dim_window, but the code
  invariance is unverified and likely false, since a 5-point elliptic code over GF(4)
  has translation group Z_5, not Z_2 wr S_2. The agent's fallback was to axiomatize
  the weight bound, which is the forbidden plausible-false-axiom move.

### Caveat for the working candidate

|F| = 7 but the cut acts on 6 sheets, so |F| does not equal the sheet count. The
candidate lives in the decoupled regime (field at least the code length, the natural
AG-code setting), not the framework's strict |F| = N coupling. Relaxing |F| = N is
the principled fix and also resolves the s5x5 N = 10 problem.

## Addendum, 2026-06-02T23:53:23Z: genus > 1 is reachable, genus 3 verified, and the one constraint that must move

A second fan-out (four Sonnet agents) targeted higher genus, with the goal of
genus > 2. Pre-analysis established that hyperelliptic curves y^2 = x^(2g+1) - c have
genus g and a Z_(2g+1) automorphism (x,y) -> (zeta*x, y) acting as a cyclic cut, so a
genus-g card-cut instance should exist for every g. The agents produced concrete
instances and an adversarial ceiling analysis; the key parameters were re-derived
from scratch in Python.

### Verified concrete instances (defect = genus, gap = 2g, real privacy)

| genus | curve | field | cut | code | ts_k | gap | status |
|-------|-------|-------|-----|------|------|-----|--------|
| 1 | y^2=x^3+1 | GF(7) | Z_6 (one 6-cycle) | [6,4,2] | 3 | 2 | verified earlier |
| 2 | y^2=x^5-1 | GF(11) | Z_5 (two 5-piles) | [10,7,2] | 5 | 4 | re-verified in Python |
| 3 | y^2=x^7-1 | GF(29) | Z_7 (two 7-piles) | [14,10,2] | 7 | 6 | re-verified in Python |
| 4 | y^2=x^9-13 | GF(19) | Z_9 (two 9-piles) | [19,14,~] | 10 | 8 | agent-computed, not re-checked here |

For genus 2 and 3 the independent Python check confirmed: the point count, the cut
orbit structure, the generator rank (k), an explicit weight-2 codeword, no zero
column, Singleton defect exactly equal to the genus, and all four gap_dim_window
conditions. So genus > 2 is not merely possible in principle, it is concretely
instantiated at genus 3.

### The genus ladder and a non-monotonic field cost

The most card-natural family is y^2 = x^(2g+1) - c, which always gives the same
shape: one fixed point at infinity (the secret slot) plus two equal piles of 2g+1
cards, cut simultaneously. Field size is NOT monotonic in genus, because the cut
needs (2g+1) | (q-1): genus 4 over GF(19) (since 9 | 18) uses a smaller field than
genus 3 over GF(29) (since 2*7+1 = 15 is not prime, q jumps to 29). Genus 6 first
needs an extension field GF(27) = GF(3^3). Hurwitz never binds, since the cut order
2g+1 is far below 84(g-1).

### The single binding constraint (confirmed by reading the source)

The framework is genus-parametric at the record level (cd_genus : nat, the gap bound
is proved for any g, higher_genus_covering takes arbitrary g). The blocker is one
Section-level coupling, not a record field:

- cover_genus1.v:129  Hypothesis HN_ec : N = #|F_ec|.
- cover_genus1.v:133  Hypothesis Hn_ec : n''_ec.+2 = N.

These force field size = sheet count = code length. With the Z_(2g+1) cut needing
(2g+1) | (q-1), and N = q = 2g+1 giving (2g+1) | 2g which is impossible, the cut
degenerates to the identity. The fix is to relax Hn_ec from "= N" to "n <= #|F|" and
allow |F| larger than the sheet count, a roughly two-line change per cover_genusN
file, leaving the CoveringScheme record untouched. ev_ec is already a free Variable,
so the cut-induced generator matrix can be supplied directly. This is the same
decouple-|F|-from-N move the genus-1 candidate needs, and it also resolves the s5x5
N = 10 problem.

### Honest caveats (retrospective discipline)

- The cut is a PILE operation. For these curves the evaluation set is two orbits (the
  y and -y twins of each x), so the cut acts as two disjoint (2g+1)-cycles, a
  parallel cut of two equal piles, not a single deck cut. Card-natural, but it is a
  pile-cut.
- Privacy is a parameter trade. At the minimal k = g+1, ts_k = k-g = 1, which is
  vacuous (a single party recovers). The verified instances chose comfortable k
  (ts_k = 5 at genus 2, ts_k = 7 at genus 3), buying real privacy at the cost of more
  cards (n = k+g+1 grows).
- dual_ev_encode is still axiomatized. The privacy side rests on a dual minimum-
  distance hypothesis (dual_ev_encode in cover_genus1.v / cover_genus2.v) that is a
  Section Hypothesis, unproved, the same at every genus (it does not worsen with g).
  Proving it means formalizing Riemann-Roch over finite fields, a large effort; it is
  dischargeable at the instance level by citing published mathematics, exactly as
  realised_by_curve is on the geometric side. Per the project's own rule, this axiom
  must be named and its concrete instance (the dual distance of the specific curve)
  computed before any genus-g scheme is credited as complete.

### Verdict

Genus > 2 is mathematically possible and concretely realized (genus 3 verified). The
framework already supports arbitrary genus structurally. Reaching it requires (a) the
two-line relaxation of the field = sheets Section hypothesis, and (b) honest handling
of the dual_ev_encode axiom by concrete computation rather than assertion. No genus
ceiling appears below the point where the field must become an extension field
(genus 6, GF(27)); the practical cost is more cards and a larger prime field as genus
rises.

## Addendum, 2026-06-03T00:48:51Z: every Z_* genus candidate is abelian, and why that is structurally forced

A recurring objection: the genus instances all use cyclic cut groups (Z_5 at genus 2,
Z_7 at genus 3, Z_9 at genus 4, in general Z_(2g+1)), which are abelian, hence
insecure by the anonymity measures established above (small group size, and the
abelian_word_collapse shrinkage to C(L+r, r)). The objection is correct, and the
abelianness is not an artifact of the search. It is forced.

### Why tame card-cut gap codes have abelian symmetry, always

1. A code invariant under a 2-transitive group is trivial (the perm-module argument
   of s5_nogo). So any non-trivial gap code must have a non-2-transitive symmetry
   group.
2. The gap code's symmetry group is the stabilizer of the secret point, namely the
   automorphisms that fix the secret slot and therefore preserve the divisor m.P.
3. In tame characteristic (char does not divide the stabilizer order), a point
   stabilizer on a curve is cyclic, because it acts faithfully on the one-dimensional
   cotangent line at the point. Cyclic means abelian.

Hence every tame card-cut gap code is forced to have abelian (cyclic) symmetry. That
is why all the genus candidates came out as Z_(2g+1).

### Two security issues that must be told apart

- Word-collapse (abelian-specific): removable while staying card-natural by adding the
  reflection, so the cut group becomes the dihedral D_(2g+1), non-abelian, no
  word-collapse. The card reading is cut-plus-flip (rotate the pile, then reverse its
  order). This is the D_5-over-Z_5 upgrade at higher genus. The catch: it needs a
  curve whose roots carry dihedral symmetry and a dihedral-invariant secret divisor,
  since the reflection moves the point at infinity so the secret can no longer sit
  there. The clean curves y^2 = x^(2g+1) - c lack the inverting involution, so this
  needs a different curve and is not yet verified. It is the natural next target.
- Small anonymity (the fundamental conflict): NOT removable while keeping a gap. Gap
  forces non-2-transitivity, and non-2-transitivity at prime degree forces an affine
  Z_p rtimes Z_d group of order at most p(p-1)/2. So the symmetry group of any gap
  code stays small at every genus. Genus grows the gap (T - k = 2g) and grows the
  cyclic cut, but does not grow the security group. Genus buys gap, not anonymity.

### The only escape to large non-abelian symmetry, and its price

To get a non-abelian and large point stabilizer one must leave the tame regime: wild
ramification in characteristic p, where stabilizers are a wild p-group extended by a
cyclic group (Hermitian, Deligne-Lusztig, Artin-Schreier towers). These give
genuinely non-abelian gap-code symmetry, but the non-abelian elements are wild
Artin-Schreier shifts rather than cuts or flips, the field is an extension GF(p^k),
and the card-table reading is murky. This is the same characteristic-p corner that was
the lone exception to the Hurwitz tension.

### Bottom line

Abelian symmetry is structurally forced for tame card-cuts and is removable only by
going dihedral (cut-plus-flip), which dodges the word-collapse but keeps the group
small. The anonymity-size insecurity does NOT go away at any genus, because gap and
large symmetry remain in the strict conflict proved earlier. The genus ladder answered
"how large a gap," not "how to get a gap with large security." Those two stay mutually
exclusive.

## Addendum, 2026-06-03T01:06:00Z: two separate knobs, the group decides IF a gap can exist, the genus decides HOW WIDE

A natural and important conflation to clear up: does the dihedral (or cyclic) group
"cause" the threshold gap T > k? No. There are two distinct knobs, and they are easy
to merge by mistake. Pinning them apart is worth recording in full.

### The correction: the group does not create the gap, the curve's genus does

The gap is T - k = 2g, where g is the GENUS of the curve the code is built on. The
genus is a property of the geometry, not of the symmetry group. The same curve
carrying a Z_n cut and a D_n cut-plus-flip yields the SAME gap, because it is the same
genus. So D_n and Z_n are equally good at T > k; their difference is security
(non-abelian versus abelian), not the gap size. The statement "D_n satisfies T > k" is
therefore imprecise. The accurate statement is "D_n is allowed to host a code that has
a gap, whereas S_n structurally forbids it."

### Knob 1, the group: can a gap exist at all (a yes/no)

This is the s5_nogo / 2-transitivity mechanism, restated as a permutation question.

- A non-2-transitive group (D_n, Z_n) preserves structure (adjacency on the n-gon).
  In linear-algebra terms its action commutes with a non-trivial matrix (the cycle
  adjacency), whose eigenspaces are intermediate-dimension invariant submodules. So an
  intermediate-dimension invariant code CAN exist. This is the necessary condition for
  any gap.
- A 2-transitive group (S_n) preserves nothing but the trivial structure. The only
  matrices commuting with the full symmetric action are combinations of the identity
  and the all-ones matrix, whose eigenspaces are just the all-ones line (dimension 1)
  and its complement (dimension n-1). No intermediate invariant submodule exists, so no
  gap can live there. This is exactly s5_nogo seen through "what can commute with the
  group."

So the group opens or closes the door. It is a binary gate, not a magnitude.

### Knob 2, the genus: how wide the gap is (a magnitude)

Once the door is open, the width of the gap equals 2g, and g is the curve's genus,
which is a deficiency in the precise sense of Riemann-Roch: a genus-g curve has g
"missing functions" (the Weierstrass gaps), so a genus-g code has g fewer usable
degrees of freedom than a maximally efficient (MDS) code of the same pole bound. This
deficiency is the gap, and it is two-sided:

- On the reconstruction side the minimum distance drops by g, so more shares are needed
  to recover. In the verified instances the minimum distance fell to 2, so
  reconstruction needs almost all n-1 shares (ts_T = n-1).
- On the privacy side the dual distance also drops by g, so fewer shares are guaranteed
  to leak nothing (privacy threshold ts_k = k - g instead of the MDS value k).

Those two deficiencies add to the 2g gap: ts_T - ts_k = (n-1) - (k-g) = 2g (using
n = k+g+1). So the "redundancy" intuition is correct in this precise sense: a
positive-genus code carries information less efficiently than MDS, and that slack,
counted on both the reconstruction and the privacy side, is exactly T - k.

### The deep tie that vindicates the "more constraint, more gap" instinct

There is a real theorem behind "more constraint produces a gap": Riemann-Hurwitz. The
genus is fixed by the RAMIFICATION of the cover. For the hyperelliptic family
y^2 = x^(2g+1) - c, the curve is a double cover of the projective line branched at
2g+2 points, and Riemann-Hurwitz gives 2g - 2 = -4 + (2g+2), so the genus equals the
branch-point count divided by two minus one. More branch points (a higher-degree, more
constrained defining equation) means higher genus means a wider gap. So the instinct
"more constraint carries more redundancy, hence a gap" is right, but the constraint
that sets the gap is the ramification of the curve, not the permutation rigidity of the
group.

### One-line summary

S_n versus D_n is "can there be a gap at all"; genus is "how wide." Two different
knobs. The group rigidity is the binary gate (non-2-transitive opens it, 2-transitive
shuts it); the curve genus is the magnitude (the Riemann-Roch deficiency, set by
ramification). Conflating them is the easy error; keeping them separate is the correct
picture.

## Addendum, 2026-06-03T01:16:38Z: large non-abelian candidates (PSL_2, Hermitian/Suzuki, generalized affine) verified against secure + T>k

Three classes of large non-abelian "intermediate" groups were proposed as candidates
that could give both long code length (large group, security) and a gap (T > k):
(1) PSL_2(F_q) and subgroups, (2) Suzuki groups Sz(q) and Hermitian automorphism
groups, (3) generalized affine semidirect products x -> a*x^p + b. Verified below
against the two requirements, with card-naturalness flagged as the third requirement
they strain.

### The correction that governs all three: transitivity is the obstruction, not the gap source

The sources credit the gap to high transitivity ("3-transitive, hence controlled
ramification, hence gap"). That conflates the two knobs (see the previous addendum).
The precise facts:

- A code invariant under a 2-transitive (or higher) group acting on its coordinates is
  trivial, dimension in {0, 1, n-1, n}. This is s5_nogo in general form. The natural
  high-transitivity actions of all three families give exactly this. PGL_2(q) is
  sharply 3-transitive on the q+1 points of the line, and the invariant codes there are
  the Reed-Solomon codes: MDS, genus 0, NO gap. So 3-transitivity on the line is what
  must be avoided, not exploited.
- The gap is 2g, set by the curve's genus, arising via Riemann-Hurwitz from the
  ramification of the group's cover. The group's only job is to be non-2-transitive on
  the actual evaluation points so a non-trivial code can exist.
- The large non-abelian symmetry of a gap code is the stabilizer of the secret point
  (one-point divisor m.P) or the divisor stabilizer. It is large-and-non-abelian only
  under WILD ramification (char p divides its order). In tame characteristic a point
  stabilizer on a curve is cyclic, hence abelian. This is the deciding fact.

### (1) PSL_2(q) / PGL_2(q), order approx q^3

- Math: on the line P^1(F_q), 2- or 3-transitive, so invariant codes are Reed-Solomon,
  genus 0, no gap. The gap appears only on a higher-genus PSL_2-curve, the canonical
  example being the Klein quartic (genus 3, Aut = PSL_2(7) of order 168 = the Hurwitz
  bound 84(3-1)); there 2g = 6, from the genus, via the quotient Klein/PSL_2(7) = P^1
  branched at three points of orders 2,3,7.
- Secure: yes in size (order approx q^3, non-abelian, no word-collapse), BUT with a
  one-point secret divisor the symmetry collapses to the point stabilizer, which in
  tame characteristic is cyclic (for Klein it is Z_7, abelian and small). Keeping the
  full PSL_2(q) requires a PSL_2-invariant divisor, so the secret is encoded globally,
  not at a fixed card.
- T > k: yes, on a non-2-transitive orbit of a high-genus PSL_2-curve (the 24-, 56-, or
  84-point orbits of the Klein quartic, not the 7- or 8-point 2-transitive ones).
- Card-natural: no. PSL_2(q) operations are not cuts or pile-scrambles.

### (2) Hermitian and Suzuki, the strongest candidate

- Math: the Hermitian curve y^q + y = x^(q+1) over F_(q^2) has genus q(q-1)/2 and q^3+1
  rational points, with Aut = PGU(3,q), 2-transitive on those q^3+1 points (so the full
  group gives a trivial code). The Hermitian CODE is invariant under the stabilizer of
  P_inf, a Borel-type group B of order q^3(q^2-1)/gcd(3,q+1). B is non-abelian (its
  order-q^3 unipotent radical is the wild inertia), is NOT 2-transitive on the remaining
  q^3 points (its point stabilizer C_(q^2-1) is far too small to be transitive on
  q^3-1), and fixes P_inf, which becomes the secret slot. Suzuki curves behave the same
  with larger genus (Sz(8): genus 14, group order 29120, 65 points).
- Secure: yes, genuinely. Anonymity group B has order approx q^3, non-abelian, no
  word-collapse. The cleanest non-abelian-and-large symmetry on the list.
- T > k: yes, and a huge gap 2g = q(q-1). The rich Weierstrass gap sequence at P_inf is
  exactly why Hermitian/Suzuki codes reach the Tsfasman-Vladut-Zink frontier.
- Card-natural: no. The non-abelian elements of B are wild unipotent automorphisms
  (Artin-Schreier-type shifts), not cuts or flips; the field is an extension F_(q^2);
  the deck has q^3 cards.

### (3) Generalized affine x -> a*x^p + b, the solvable middle

- Math: AGammaL-type semidirect products (affine maps composed with Frobenius x -> x^p),
  order approx q(q-1)*log_p q, larger than D_n but bound to polynomial-linear form, so
  unable to shuffle freely like S_n. Automorphism groups of Artin-Schreier curves
  y^p - y = f(x) and generalizations, positive genus by Riemann-Hurwitz (wild
  ramification at infinity, the order-p shift y -> y+1).
- Secure: moderately. Non-abelian, bigger than dihedral, no word-collapse, but smaller
  than the simple groups of (1) and (2). The non-abelian part again comes from wild
  ramification.
- T > k: yes, the curve's genus gives the gap. The AGL(1,q) form is sharply
  2-transitive (trivial code), so a non-2-transitive subgroup or higher-genus orbit is
  required.
- Card-natural: partial at best. The translation x -> x+b is cut-like, but Frobenius
  x -> x^p and the Artin-Schreier shift are not card operations.

### Summary table

| Candidate | Secure (large non-abelian) | T > k (gap) | Gap mechanism | Card-natural |
|-----------|----------------------------|-------------|---------------|--------------|
| (1) PSL_2(q) | yes, only with an invariant divisor (tame point-stab is cyclic) | yes, on a high-genus orbit | curve genus + Riemann-Hurwitz | no |
| (2) Hermitian / Suzuki | yes, cleanly (the Borel stabilizer of P_inf) | yes, very large | wild ramification at P_inf | no |
| (3) affine x->a*x^p+b | yes, moderate | yes | wild Artin-Schreier ramification | no |

### Conclusion

All three genuinely answer "secure + reconstructable by T > k". They escape the abelian
problem (their symmetry is non-abelian and large) and they carry a gap (they sit on
high-genus curves). And they all do it the way the abelian addendum predicted the
escape would have to work: through wild ramification in characteristic p, which is
exactly what makes a point stabilizer non-abelian. The uniform cost is the third
requirement: NONE is card-natural, and all live over extension fields rather than prime
fields, with large card counts. The wild automorphisms (Frobenius twists,
Artin-Schreier shifts, unipotent radicals) are not cuts or pile-scrambles. So these
resolve "secure + T > k" decisively and confirm that the only door to large non-abelian
security with a gap is the wild-ramification door, but they do NOT resolve
"card-natural + secure + T > k". That triple stays the open corner, with the dihedral
cut-plus-flip the only card-natural attempt at non-abelian security, and it stays small.

Correction to carry forward: the sources credit the gap to transitivity, but it is the
opposite. Hermitian and PSL_2 codes are non-trivial precisely on the parts where the
action is NOT 2-transitive, and the gap is the curve's genus. The 2-transitive actions
of these same groups give Reed-Solomon, genus 0, no gap.

## Addendum, 2026-06-03T01:23:57Z: what "card-natural" means in math

This note has leaned on the word "card-natural" throughout without defining it. It has
a precise mathematical meaning, and that meaning is exactly why the large non-abelian
AG candidates fall outside it.

### The core distinction: blind position-permutation versus label computation

A card is a physical token. During a shuffle the dealer may move it but must not read
its face, or the shuffle leaks. So a card operation is a permutation of POSITIONS,
applied BLINDLY, independently of what is printed on the cards. That single constraint,
"the permutation does not depend on the card's value," is the whole distinction.

- A cut sends position i to position i+1 mod n. Defined on positions, no reference to
  any label. Blind. Card-natural.
- The doubling map x -> 2x, the Frobenius x -> x^p, a Mobius map x -> (ax+b)/(cx+d):
  these send the card LABELLED x to a position computed from x by field arithmetic. To
  apply them the dealer must read x. Not blind. Not card-natural.

So card-natural means: the operation is a combinatorial permutation of positions, not
an algebraic function of the labels.

### The structure: cuts and pile-scrambles, hence wreath towers

Physically a deck is a set of positions with two pieces of structure: a partition into
piles, and within each pile a cyclic order. The blind operations a human can perform
are exactly the symmetries of that structure:

- rotate a pile (a cut): the cyclic group Z_n within a pile;
- permute equal-size piles (a pile-scramble): the symmetric group S_m on the piles;
- optionally reverse a pile (a flip): an involution, turning Z_n into D_n.

Composing these, the card-natural groups are exactly the subgroups of iterated wreath
products of cyclic and symmetric groups, Z_n wr S_m and its iterates. Invariantly, a
card-natural group is a subgroup of Aut of the deck AS A PHYSICAL ARRANGEMENT (a set,
partitioned into piles, each cyclically ordered). It is the combinatorial automorphism
group of the deck.

This matches the card-based cryptography formalization: the realizable shuffles
(Mizuki-Shizuya's abstract-machine model, Koch-Walzer's realizable-shuffle theory) are
the "uniform closed" shuffles, uniform random draws from subgroups generated by cuts
and pile-scrambles, applied so the chosen element stays hidden. The hiding (security)
and the blindness (label-independence) are the same condition: you can only apply a
permutation you are not allowed to compute from the faces.

### Why this is exactly the requirement the non-abelian AG groups fail

There are two automorphism worlds:

- the combinatorial automorphisms of the deck arrangement (cuts, pile-scrambles,
  flips), which is what card-natural means; and
- the algebraic automorphisms of the labels (the curve or the field): Frobenius, Mobius
  PSL_2, the unipotent radical of a Hermitian Borel.

PSL_2, Hermitian/Suzuki, and the affine x -> a*x^p + b groups are large and non-abelian
precisely because they are rich ALGEBRAIC automorphisms. Their non-abelianness lives in
field multiplication and Frobenius, which are label computations. So they sit
structurally on the wrong side of the line; a card cannot carry out a Mobius
transformation of itself.

The only operations that are simultaneously a curve automorphism (so they preserve an
AG code and give a gap) and a deck symmetry (so they are card-natural) are the cyclic
and dihedral cuts Z_n, D_n, the rotation x -> zeta*x read as "rotate the pile." Those
are abelian or small. That is the conflict at its root: card-natural means
combinatorial, security-with-a-gap via curves means algebraic, and the two worlds meet
only in the small cyclic/dihedral cuts.

### The one card-natural non-abelian direction still open

There is a loophole. A pile-scramble S_m is card-natural AND non-abelian. The wreath
Z_n wr S_m (cut each of m piles, then scramble the piles) is card-natural, non-abelian
via the S_m part, and imprimitive hence non-2-transitive on the mn cards, so it clears
knob 1 (an intermediate invariant submodule exists). It can be made large by using many
piles.

What it lacks is a curve. Its gap would have to come not from a curve's genus but from a
product or concatenated code (the Singleton defect of a tensor code), where the defect
is combinatorial rather than geometric. This is exactly the grid/product-code direction
from the first fan-out (the [9,4,4] over GF(9)), which was non-MDS and card-natural but
failed the framework's g < k parametrization. So the precise open question, now sharply
stated: is there a product or concatenated code, card-natural under a pile-wreath
Z_n wr S_m, that is framework-compatibly non-MDS and secret-encoding? That is the only
remaining route to "card-natural and non-abelian and gap," and it lives in combinatorial
coding theory, not algebraic geometry.

### Definition, in one sentence

A card-natural group is a subgroup of the combinatorial automorphism group of the deck
arrangement, the wreath towers of cyclic and symmetric groups generated by cuts and
pile-scrambles, applied blind, never an algebraic function of the card labels. And that
definition is exactly why the secure AG candidates (PSL_2, Hermitian, Suzuki, affine
Frobenius) fall outside it, while the cyclic and dihedral cuts fall inside it but stay
abelian or small.

## Addendum, 2026-06-03T01:34:57Z: CORRECTION from the literature: the "card-natural restricts to abelian/small" claim is too strong

A literature check (prompted by the question whether "only D_n is card-natural" could
be formalized) overturns the over-restriction built up in the previous three addenda
(the abelian conclusion, the two-knobs note, and the card-natural definition). Recording
the correction so the note is not left asserting a false limit.

### What the literature establishes

- Koch and Walzer, "Foundations for Actively Secure Card-Based Cryptography" (FUN 2021;
  IACR ePrint 2017/423), prove that ANY uniform closed shuffle, meaning a uniform random
  draw from ANY subgroup of the symmetric group, is physically realizable with only a
  linear number of helping cards. The Dagstuhl abstract states this covers any
  permutation group, not just special cases. So large non-abelian shuffle groups
  (PSL_2, the Hermitian Borel, the affine Frobenius groups) ARE realizable as card
  shuffles. There is no group-theoretic restriction to D_n.
- Even with no helping cards, the non-abelian door is already open: a pile-scramble is
  S_m on m piles, non-abelian for m >= 3. The dihedral case is published as the
  cycle-graph automorphism shuffle (the "dihedral shuffle" of Niemi-Renvall), and
  "Graph Automorphism Shuffles from Pile-Scramble Shuffles" (New Generation Computing,
  2022; arXiv 2109.00397) shows graph automorphism shuffles are implementable from
  pile-scrambles.
- What is real is a COMPLEXITY HIERARCHY, not a wall: "A Complexity Hierarchy of
  Shuffles in Card-Based Protocols" (arXiv 2603.18608) orders shuffles by implementation
  cost. Cuts and pile-scrambles are cheapest (no helping cards); arbitrary subgroups are
  reachable at higher cost.
- The genus gap is also standard: Chen and Cramer, "Algebraic Geometric Secret Sharing
  Schemes and Secure Multi-Party Computations over Small Fields" (CRYPTO 2006), give
  quasi-threshold ramp schemes that are t-rejecting and (t+1+2g)-accepting, gap 2g from
  the genus. Our genus-3 instance is an instance of a known family.

### The retraction

The earlier claim, that card-natural symmetry forces abelian-or-small groups and that
"card-natural + secure + gap" is an empty or near-empty corner, was too strong. Two
errors:

1. The "algebraic versus combinatorial" line was a red herring. As a subgroup of S_n a
   group is just a set of position-permutations; Koch-Walzer apply a uniform random one
   blindly with helping cards, never reading a label. A "Mobius" or "Frobenius"
   description is a label for the group, not a requirement to compute on labels.
2. "Only D_n" was never even the cheap-tier truth: pile-scrambles give the non-abelian
   S_m with no helping cards, and the pile-wreath Z_n wr S_m is non-abelian and
   card-natural already.

Corrected picture: "card-natural" is a cost gradient, not a binary. Any shuffle group is
realizable; cuts, pile-scrambles, and the dihedral cut-plus-flip are merely the cheapest.
Consequently "secure + T > k + card-realizable" is ACHIEVABLE, for example a Hermitian AG
code with a Koch-Walzer-realized shuffle of its Borel automorphism group, at the cost of
helping cards, an extension field, and many cards. The corner is expensive, not empty.

The strict-conflict addendum (large symmetry versus gap) still stands at the level of the
MATHEMATICS: gap forces non-2-transitivity, and at prime degree non-2-transitivity caps a
group at the affine ceiling. But the bridge to "therefore card protocols are stuck with
abelian/small" does NOT follow, because the realizability of large shuffle groups removes
the card-side restriction. The remaining honest cost is implementation complexity, the
subject of the 2026 complexity-hierarchy paper, not impossibility.

### Consequence for formalization

The restriction "card-natural implies D_n" must NOT be formalized, because it is false.
The genuinely true and formalizable content is unchanged: (1) the 2-transitivity
obstruction (s5_nogo, already machine-checked and axiom-free), and (2) the genus gap 2g
(Chen-Cramer, already encoded in cover_genus*.v and verified concretely up to genus 3).
A card-side theorem worth wanting would be the Koch-Walzer realizability statement, but
that is a published combinatorial result in the card-based-crypto model and a separate
large effort, not a restriction we found.

### Sources

[1] Koch, Walzer, "Foundations for Actively Secure Card-Based Cryptography," FUN 2021.
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FUN.2021.17 ; ePrint
    2017/423 https://eprint.iacr.org/2017/423
[2] "Graph Automorphism Shuffles from Pile-Scramble Shuffles," New Generation Computing,
    2022. https://link.springer.com/article/10.1007/s00354-022-00164-4 ; preprint
    https://arxiv.org/pdf/2109.00397
[3] "A Complexity Hierarchy of Shuffles in Card-Based Protocols," arXiv 2603.18608.
    https://arxiv.org/pdf/2603.18608
[4] Chen, Cramer, "Algebraic Geometric Secret Sharing Schemes and Secure Multi-Party
    Computations over Small Fields," CRYPTO 2006.
    https://link.springer.com/chapter/10.1007/11818175_31 ; related "Linear Secret
    Sharing from Algebraic-Geometric Codes," https://arxiv.org/pdf/cs/0603008

## Addendum, 2026-06-03T01:41:20Z: the candidate-group menu (closing synthesis)

With the card-natural restriction corrected away, the usable candidate groups form a
ladder, not a single answer. The structure is one hard gate and three dials.

### One gate, three dials

- Gate (mandatory): the group's ACTION on the code coordinates must be non-2-transitive.
  This is the only hard constraint, the s5_nogo obstruction; a 2-transitive action gives
  a trivial code and no gap. It is about the action, not the abstract group: PSL_2(7) is
  2-transitive on 8 points (excluded) but non-2-transitive on its 24-point orbit
  (usable). A candidate is a pair (group, non-2-transitive orbit).
- Dial 1, security: |G| and non-abelianness (anonymity, no word-collapse).
- Dial 2, gap: the curve genus (gap = 2g), or a combinatorial code defect; set by the
  code, not the group.
- Dial 3, cost: distance from cuts and pile-scrambles. Cheap shuffles need no helping
  cards; any group is realizable with helping cards (Koch-Walzer).

### The candidate ladder

| Tier | Group (and action) | Security | Gap source | Cost | Status |
|------|--------------------|----------|------------|------|--------|
| 0 (excluded) | 2-transitive: S_n, A_n, PGL_2 on the line, AGL(1,q), PGU(3,q) on q^3+1 | n/a | none, code trivial (Reed-Solomon is the genus-0 PGL_2 code) | - | ruled out by the gate |
| 1 | Z_n cut; D_n cut-plus-flip | small (n, 2n) | elliptic / hyperelliptic genus | cheapest, no helping cards | Z_n verified to genus 3; D_n needs a dihedral-symmetric curve |
| 2 | pile-wreath Z_n wr S_m (cut piles, scramble piles) | moderate, non-abelian via S_m | product / concatenated code defect, or a wreath-symmetric curve | cheap, pile-scrambles | product [9,4,4] non-MDS verified, but framework g<k unmet; open |
| 3 | affine / Frobenius Z_p rtimes Z_d, x -> a*x^p + b | larger, solvable non-abelian | Artin-Schreier / generalized hyperelliptic genus | moderate, helping cards | standard AG theory, not instantiated by us |
| 4 | PSL_2(q) on a high-genus orbit; Hermitian PGU(3,q) Borel; Suzuki Sz(q) | large (~q^3 and up) | high curve genus (Klein g=3; Hermitian g=q(q-1)/2) | high, helping cards, extension fields, many cards | standard AG codes (Chen-Cramer, Hermitian), not in our framework |

### Secret-encoding refinement (couples to the choice)

- Secret at a fixed point (one-point divisor m.P): symmetry = the stabilizer of that
  point. Tame characteristic makes it cyclic (abelian, small), so a fixed-card secret
  with a large non-abelian symmetry needs WILD ramification (the Hermitian/Suzuki Borel,
  Tier 4).
- Secret encoded globally (an invariant divisor, no fixed point): symmetry can be the
  full group, which is how the large TAME groups like PSL_2(q) on the Klein quartic
  become available, at the price that the secret is not a single distinguished card.

So Tier 4 splits: wild ramification gives large non-abelian WITH a fixed secret card
(Hermitian); tame high-genus curves give large non-abelian WITH a global secret (PSL_2).

### Bottom line

The usable candidates are every (group, action) pair that is non-2-transitive on the
code coordinates and is the automorphism group of a positive-genus code. That is a large
space, a ladder from the cheap small cyclic/dihedral cuts up to the expensive large
simple groups. One is not stuck with abelian or small; one trades security against
implementation cost, with the gap set independently by the genus. The only thing
genuinely off the menu is the 2-transitive top (S_n, the full line action), which is
exactly Reed-Solomon with no gap.

Concrete status for us: verified at Tier 1 (cyclic cuts, genus 1 through 3); the most
promising untested directions are Tier 2 (the pile-wreath product code, the cheapest
non-abelian, if the g<k parametrization can be met) and Tier 4 Hermitian (the strongest
security and gap, if helping cards and an extension field are accepted).
