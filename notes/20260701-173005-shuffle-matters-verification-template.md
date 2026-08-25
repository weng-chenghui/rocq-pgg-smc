# Template: verifying a nonlinear, non-trivial, non-cyclic, shuffle-matters (k,T) scheme

Date: 2026-07-01

A fixed verification standard so any candidate group can be checked the same way, group by group,
with the same three artifacts and comparable results. Companion to
[[20260701-144750-pivot-shuffling]] and [[20260701-134413-what-does-the-shuffle-buy]].

## The candidate tuple (what must be specified)

- `G`, a finite group.
- `Omega`, `N` positions with a `G`-action.
- a fixed public deck `M`, a multiset of `N` colors placed on the positions.
- a secret space `S`.
- an encoding `E : S -> arrangement`, using exactly the deck `M`.
- the shuffle, a uniform random `g` in `G` applied to the arrangement.
- a read-off `R`, from the colors on a revealed subset `A` to `S` or `bottom`.

Every rule below is a finite decidable check on this tuple.

## Rules, in gating order (fail-fast R0 -> R5)

### R0. Well-formed and composition-blind
Definition: the action is valid, and the color deck `M` is identical for every secret.
Test: check the action axioms; check the multiset of colors is the same across all `s`.
Pass: both hold. Blocks the trivial leak where counting colors reveals `s`.

### R1. Correct, shuffle-invariant recovery
Definition: the recovered value is a `G`-invariant of the arrangement and equals the true secret
from any qualified reveal.
Test: for all `s`, all `g` in `G`, all qualified `A`, confirm `R = s`.
Pass: recovery returns `s` regardless of `g`.

### R2. Shuffle-sourced privacy (the discriminator)
Definition: the shuffle is necessary and sufficient for privacy.
Test (a), sufficient: with the uniform-`G` shuffle, every coalition `A` of size `<= k` has a color
distribution identical across all secrets.
Test (b), necessary: with the shuffle removed but every other source of randomness kept, some
coalition of size `<= k` has colors that differ across secrets.
Pass: (a) and (b). This is the line separating den Boer (passes) from AG (fails (b): private with
no shuffle because of dealer randomness). Passing R2 also certifies effective nonlinearity, since a
linear scheme cannot pass (b).

### R3. Genuine (k,T) ramp
Definition: a real privacy region and a real reconstruction threshold.
Test: compute the coalition profile under the shuffle. Set `k` = largest size with all coalitions
secret-independent, `T` = smallest size with all coalitions determining `s`.
Pass: `k >= 1`, `T <= N`, and `k < T`. Record the gray zone `k < |A| < T`.

### R4. Non-trivial
Definition: the secret carries information and the read-off is not constant.
Test: `|S| >= 2`, and different secrets yield different recovered values.
Pass: both hold.

### R5. Genuinely non-cyclic (the hard gate) — CORRECTED after the Dic_3 run
Definition: the non-cyclic structure of `G` must buy PRIVACY that no cyclic group of comparable
order provides, measured on the privacy threshold `k`, not on a choice-dependent reconstruction
number.
Decisive test: `k_G > k_cyclic`, where `k_cyclic` is the privacy threshold of the analogous
scheme under a single-`N`-cycle group `C_N` on `Omega` with the same deck. Equivalently, since any
transitive group gives `k >= 1` for free, the headline indicator is `k_G >= 2`: the scheme must
hide PAIRS, which a regular cyclic (1-transitive) group cannot do for a non-trivial invariant.
Diagnostic (not sufficient): subgroup-irreducibility, no cyclic subgroup `C <= G` reaches `k_G`.
This is necessary but too weak alone: it passes automatically whenever `G`'s cyclic subgroups are
small, as the Dic_3 run showed.
Pass: `k_G > k_cyclic` (and in practice `k_G >= 2`). If an equal-order cyclic group matches `k_G`,
the scheme is cyclic in disguise and is rejected regardless of a tighter reconstruction number.

Why corrected: the first Dic_3 run passed the old R5(i) trivially (all its cyclic subgroups have
`k = 0`) yet the equal-order cyclic `C_12` achieved the same privacy `k = 1`. Dic_3's only edge was
a reconstruction number `T` that depends on which generic triples are chosen. So the old test
mistook a solvable, cyclic-grade scheme for a non-cyclic one. The privacy threshold `k` is the
choice-independent security quantity, so the gate is stated on `k`.

## Reading a run

Gate R0 to R5 in order, fail-fast. Clearing all six certifies a nonlinear, non-trivial,
non-cyclic, shuffle-matters `(k,T)` scheme. The "any group fails" squeeze lives in R2 and R3
together: too little mixing fails R2(a), too much mixing collapses the invariant and fails R3 or
R4. That is the Goldilocks condition made checkable. R5 is where solvable groups (e.g. Dic_3) are
most at risk, since a cyclic subgroup may already pass R2 and sink test (i).

## The certificate a passing candidate must exhibit

1. the tuple,
2. the computed `(k,T)` with the full coalition profile (R3),
3. the with-shuffle vs without-shuffle privacy witness (R2),
4. the cyclic-subgroup table plus the `C_N` benchmark comparison (R5).

Same four artifacts for every group, so results are comparable across candidates.
