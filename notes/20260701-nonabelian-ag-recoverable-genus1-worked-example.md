# Worked example: a non-Abelian, non-dihedral, genus-1 AG secret-sharing instance

Date: 2026-07-01
Companion to the design [[20260701-nonabelian-ag-recoverable-genus1-design]].
Every number below is computed and checked by `notes/ec_worked_example.py`.

This is the smallest concrete secret-sharing scheme whose recovery symmetry is non-Abelian
and non-dihedral, built from a genus-1 algebraic-geometry code. It answers the question
"is there a non-Abelian, non-dihedral group with AG-code `(k, T)` recoverability" with an
explicit witness.

## 1. Field and curve

`GF(9) = GF(3)[w]/(w^2 + 1)`, `w^2 = -1 = 2`. Elements: `{0, 1, 2, w, 2w, 1+w, 1+2w, 2+w, 2+2w}`.

`E : y^2 = x^3 - x` over `GF(9)`. Supersingular in characteristic 3, `j = 0`.
`#E(GF(9)) = 16`: fifteen affine points and the point at infinity `O`.

The three `2`-torsion points (`y = 0`) are `T0 = (0,0)`, `T1 = (1,0)`, `T2 = (2,0)`.

## 2. The recovery group

Secret point: `T0 = (0,0)`. The recon-symmetry is the point-stabilizer
`Stab(T0)` in the full curve automorphism group `E(GF(9)) rtimes Aut(E,O)`, of order `12`,
isomorphic to the dicyclic group `Dic_3` (`C_3 rtimes C_4`, non-Abelian, non-dihedral, unique
involution).

Orbits of `Stab(T0)` on the `16` points: sizes `{1, 3, 12}`:
- the singleton `{T0}` (the secret, fixed),
- the size-`3` orbit `{O, T1, T2}` (used as the divisor support),
- the size-`12` orbit (used, with `T0`, as the evaluation points).

## 3. The divisor and the Riemann-Roch basis

Divisor `D = O + T1 + T2`, degree `3`, equal to the size-`3` orbit, hence `Stab(T0)`-invariant.
Its support is disjoint from the evaluation set.

A basis of `L(D)` (dimension `l(D) = deg D + 1 - g = 3` by Riemann-Roch), with divisors on
`E : y^2 = x^3 - x` (`x` has divisor `2 T0 - 2 O`, `y` has divisor `T0 + T1 + T2 - 3 O`):

- `h0 = 1`, the constant.
- `h1 = y / (x - 1)`, divisor `T0 - T1 + T2 - O`, poles `{T1, O}`, both bounded by `D`.
- `h2 = y / (x^2 - 1)`, divisor `T0 - T1 - T2 + O`, poles `{T1, T2}`, both bounded by `D`.

Both non-constant basis functions vanish at the secret `T0`, so the secret coordinate of any
codeword reads off the constant coefficient `m0`.

## 4. The code

Evaluate the basis at the `13` evaluation points, ordered with the secret `T0` first
(position `0`) and the size-`12` orbit after. The generator matrix `G` (`3 x 13` over `GF(9)`):

```
h0: 1     1    1    1    1    1    1    1    1    1     1     1    1
h1: 0    1+w   2w   2    1   2+w   2w   2    w   2+2w  1+2w   1    w
h2: 0    2w    1   1+2w 2+w  2w    2   1+w   1    w     w    2+2w  2
```

Column `0` (the secret point `T0`) is `(1, 0, 0)`.

Parameters, all computed: `[n, k, d] = [13, 3, 10]`, almost-MDS with defect `1 = g`.
Dual distance `d_perp = 3`.

## 5. The secret-sharing scheme (Massey)

Message `m = (m0, m1, m2) in GF(9)^3`. Codeword `c = m G`, with `c_j` the `j`-th coordinate.
The secret is `s = c_0 = m G_0 = m0` (position `0`, the point `T0`). The `12` remaining
coordinates `c_1, ..., c_12` are the shares.

Thresholds, computed by exhausting all coalitions of the `12` shares:
- privacy `t = 1`: any single share is independent of the secret,
- reconstruction `r = 4`: any `4` shares determine the secret,
- gap `r - t - 1 = 2 = 2g`, the genus-1 ramp.

A coalition `A` reconstructs exactly when the secret column `G_0 = (1,0,0)` lies in the span of
its share columns. Sizes `2` and `3` are the ramp: some qualify, some do not.

This is a genuine ramp scheme, not a threshold scheme, which is the expected signature of a
positive-genus AG code. Privacy is deliberately minimal here (`1`-private) because the example
is the smallest hand-checkable one; a higher-degree invariant divisor raises `t` at the cost of
a larger matrix.

### Coalition profile

The scheme is linear, so every coalition either reconstructs the secret exactly or learns
nothing about it. There is no partial leakage. A coalition reconstructs exactly when the secret
column `(1,0,0)` lies in the span of its share columns. Counts over the `12` shares
(`notes/ec_coalition_profile.py`):

```
 size | #coalitions | reconstruct | learn nothing
   1  |     12      |      0      |     12
   2  |     66      |      6      |     60
   3  |    220      |    204      |     16
   4  |    495      |    495      |      0
  >=4 |    ...      |    all      |      0
```

Reading:
- Size `1`: always safe (all `12` learn nothing). This is the privacy threshold `t = 1`.
- Size `2`: mostly safe (`60/66`), but `6` specific pairs already reconstruct the whole secret.
  So two colluders are not guaranteed safe.
- Size `3`: mostly reconstruct (`204/220`), with `16` triples still learning nothing.
- Size `4` and above: every coalition reconstructs. This is the reconstruction threshold
  `r = 4`.

The mixed zone is exactly sizes `2` and `3`, width `2 = 2g`, where recovery depends on which
shares are held, not how many. A perfect Shamir threshold has no mixed zone; the genus-1 gap is
what smears the cutoff across two sizes. The scheme is therefore `1`-private, not `2`-private.

### Tuning the privacy threshold

Privacy is set by the divisor degree, an independent knob from the curve and the group. On the
identical curve, the identical `Dic_3`, and the identical `13` evaluation points, raising the
divisor `D_m = m (O + T1 + T2)` (degree `3m`, still `Dic_3`-invariant) slides the whole ramp
(`notes/ec_tune_privacy.py`):

```
 divisor      code       privacy t   reconstruct r   gap
 D  (deg 3)   [13, 3]        1            4            2
 2D (deg 6)   [13, 6]        4            7            2
 3D (deg 9)   [13, 9]        7           10            2
```

The gap stays `2 = 2g`, fixed by the genus. So `t` is not hardwired to the curve or the group;
it is dialed by `D`. What each ingredient fixes: the curve's genus fixes the gap; the number of
shares `n = 13` (curve point count and group orbit sizes) caps `t`; the group `Dic_3` fixes the
orbit menu `{1, 3, 12}` and hence which divisors are allowed. Pushing `t` past the cap needs a
larger curve over a larger field, which can still carry `Dic_3`.

## 6. Concrete deal and recover

Secret `s = w`. Dealer randomness `m1 = 2`, `m2 = 1`, so `m = (w, 2, 1)`.

Codeword `c = m G`:
```
c = [ w, 2+2w, 1+2w, 2, 1+2w, 1+2w, 2+2w, 2+2w, 1, 1, 2, 1, 2 ]
```
`c_0 = w = s`, as designed. The `12` shares are `c_1, ..., c_12`.

Reconstruction by the coalition `{share 1, share 9}` (a qualified pair):
`G_1 = (1, 1+w, 2w)`, `G_9 = (1, 2+2w, w)`. Solving `lam_1 G_1 + lam_9 G_9 = (1,0,0)` gives
`lam_1 = lam_9 = 2`. Then
```
s = 2 * c_1 + 2 * c_9 = 2*(2+2w) + 2*(1) = (1+w) + 2 = w.
```
Recovered `s = w`, correct.

An unqualified coalition: `{share 1}` alone. `G_1 = (1, 1+w, 2w)` does not span `(1,0,0)`, so
the single share carries no information about `s`.

## 7. The group action on shares

Each `g in Dic_3 = Stab(T0)` permutes the `13` coordinates. Verified computationally:
- it permutes the `13` columns (`g` maps evaluation points to evaluation points),
- it fixes column `0` (the secret `T0`),
- it preserves the code as a pure coordinate permutation (no diagonal twist), because `g`
  permutes `supp(D) = {O, T1, T2}` and the code is the functional code `C_L(D)`,
- the group is non-Abelian.

So recovery is equivariant under a non-Abelian, non-dihedral shuffle that holds the secret
card fixed and permutes the twelve share cards. This is the property the natural-action `S_5`
protocol cannot have (its `2`-transitive action on five points forbids any intermediate
invariant code), and it is achieved here by dropping to genus `1` and spreading the code's
pole divisor over a group orbit.

## 8. Status and honest limits

- Everything above is machine-checked by `notes/ec_worked_example.py` (points, orbits,
  generator matrix, distances, thresholds, the deal/recover cycle, and the four properties of
  the group action).
- Privacy is `1` at this minimal size. This is a ramp, not a `(t, n)`-threshold scheme.
- This is a paper artifact. Formalizing it in Rocq needs a divisor-based `L(D)` genus-1
  scaffold, since the existing `reconstruct/cover_genus1.v` is single-pole near-MDS and
  structurally forces an abelian recon-symmetry (see the design note, Section 1a, and
  [[project_ag_singlepole_abelian_obstruction]] in memory).
