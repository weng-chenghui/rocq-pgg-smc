# S_5 × S_5: basic group info and presentation

Date: 2026-05-09
Scope: pgg-smc/instances/s5x5

This note records basic structural facts about the S_5 × S_5 instance:
how the group is built, what its generators are, and its Coxeter
presentation.

## Generators in the framework

The framework uses 8 generators (`Tg = 8` in `Gen_PGGTypes 7 8`), four
per factor, the Coxeter generators of each `S_5`:

```
a_i = (i  i+1) acting on pile 1 = {0..4},   i = 1..4
b_i = (i  i+1) acting on pile 2 = {5..9},   i = 1..4
```

These are the adjacent transpositions; every permutation is a product of
adjacent transpositions (bubble sort), so they generate each `S_5`.

## Full presentation

```
S_5 × S_5  =  ⟨ a_1, a_2, a_3, a_4, b_1, b_2, b_3, b_4  |

    (involution)        a_i² = 1          for i = 1..4
                        b_i² = 1          for i = 1..4

    (braid)             (a_1 a_2)³ = 1
                        (a_2 a_3)³ = 1
                        (a_3 a_4)³ = 1
                        (b_1 b_2)³ = 1
                        (b_2 b_3)³ = 1
                        (b_3 b_4)³ = 1

    (far commutation)   (a_1 a_3)² = 1
                        (a_1 a_4)² = 1
                        (a_2 a_4)² = 1
                        (b_1 b_3)² = 1
                        (b_1 b_4)² = 1
                        (b_2 b_4)² = 1

    (cross commutation) (a_i b_j)² = 1    for all i, j ∈ {1,2,3,4}
⟩
```

## What each block does

- **Involution.** Each adjacent transposition is its own inverse.
- **Braid.** Two adjacent transpositions satisfy a length-3 relation
  `(i,i+1)(i+1,i+2)(i,i+1) = (i+1,i+2)(i,i+1)(i+1,i+2)`. Three per factor.
- **Far commutation.** Two transpositions on disjoint pairs commute,
  `(1 2)(3 4) = (3 4)(1 2)`. Three per factor.
- **Cross commutation.** Every move in pile-1 commutes with every move in
  pile-2, since they act on disjoint sets of cards. All 16 of these
  turn the two factors into a direct product.

## Coxeter diagram

Two disjoint copies of the type-`A_4` path:

```
   a_1 ── a_2 ── a_3 ── a_4               b_1 ── b_2 ── b_3 ── b_4
```

Standard convention: edge means braid `(s_i s_j)³ = 1`, no edge means
commutation `(s_i s_j)² = 1`, every vertex is an involution. The two
paths are disconnected, encoding the cross-commutation. So the full
Coxeter diagram is `A_4 ⊔ A_4`.

## Why this presentation has order 14400

Standard fact about Coxeter groups of type `A_{n−1}`: the group is `S_n`,
of order `n!`. So:

- `⟨ a_1..a_4 | A_4 relations ⟩` has order `5! = 120`.
- `⟨ b_1..b_4 | A_4 relations ⟩` has order `5! = 120`.
- The cross-commutation block makes the two halves into a direct product,
  giving `120 × 120 = 14400`.

The count `14400` falls out of the presentation, not from an external
axiom. In the file `s5x5_group_order_eq` is axiomatised only because
enumerating cardinality of a permutation group on 10 letters in Coq is
too expensive, not because the math is uncertain.

## Relation count

| Block | Per factor | Total |
|---|---|---|
| Involution `a_i² = 1` | 4 | 8 |
| Braid `(a_i a_{i+1})³ = 1` | 3 | 6 |
| Far commutation `(a_i a_j)² = 1`, `|i−j| ≥ 2` | 3 | 6 |
| Cross commutation `(a_i b_j)² = 1` | — | 16 |
| **Total** | — | **36** |

So `S_5 × S_5` is a Coxeter group of rank 8 with 36 defining relations:
`Cox(A_4 ⊔ A_4)`.

## Generation rank: 8 vs the abstract minimum

`S_5 × S_5` is in fact 2-generator as an abstract group. The framework
picks 8 not for minimality but for operational meaning:

- The protocol's monodromy walk is a random walk on `S_10` whose
  generator set is exactly these 8 adjacent transpositions.
- Each adjacent transposition is one physical operation: swap two
  adjacent cards in one pile.
- The mixing-time analysis (`s5x5_mixing.v`, Wilson 2004) and the
  Schreier spectral gap `(1 − cos(π/5))/4` are computed for this
  specific generator set.

## Numbers attached to the group

| Number | Meaning |
|---|---|
| 8 | physical moves the protocol can perform per step |
| 4 + 4 | Coxeter generators per factor |
| 14400 | total distinct permutations reachable by composing those moves |
| 10 | sheets the group acts on (the cards) |

The leap from 8 (moves) to 14400 (group size) is the combinatorial
richness of `S_5 × S_5`.

## Ramification points: bridge between topology and group theory

The conceptual key is one sentence:

> A true covering map has a free action of the deck group. A
> ramification point is where the action stops being free.

That single statement does all the work.

### Step 1: the unramified picture

For an honest covering `π : C → B` with no ramification, every point
`b ∈ B` has a fiber `π^{−1}(b)` of size exactly `|G|`. The deck group
`G` permutes the points of each fiber. Crucially, `G` acts freely on
`C`: no element of `G` other than the identity has a fixed point.

The reason: if some `σ ≠ e` fixed a point `p ∈ C`, then in any small
neighbourhood of `p` the action of `σ` would have to be trivial near
`p` by continuity and discreteness of `G`, contradicting `σ ≠ e`. The
one-to-many topology of a covering rules out fixed points.

So topology and group theory are already joined in the unramified case.

- Topology side: locally trivial fiber bundle.
- Group side: free `G`-action on `C`.

### Step 2: what goes wrong at a ramification point

A ramification point is a point `p ∈ C` where the cover is not locally
trivial. The fiber there is smaller than `|G|` because some sheets have
collided.

In group-theoretic language, at `p` some nontrivial `σ ∈ G` fixes `p`.
The set of `σ` fixing `p` is a subgroup `Stab(p) ⊂ G`, called the
inertia group at `p`. For curves and tame ramification, `Stab(p)` is
always cyclic, generated by a single element.

> A ramification point on `C` is a point with nontrivial
> `G`-stabiliser. The stabiliser is the cyclic subgroup `⟨σ⟩` for some
> `σ ∈ G`.

That `σ` is exactly the group element attached to the ramification
point.

### Step 3: the local model `z ↦ z^2`

Make this concrete with the simplest possible branched cover:

```
π : C → P^1,    π(w) = w^2.
```

Total space `C = P^1`, base `P^1`, deck group `G = Z/2 = {1, σ}` with
`σ(w) = −w`.

For `z ≠ 0`:

- Fiber `π^{−1}(z) = {+√z, −√z}`, two points.
- `σ` swaps them.
- Action is free.

For `z = 0`:

- Fiber `π^{−1}(0) = {0}`, one point.
- `σ(0) = −0 = 0`, fixes it.
- Action is not free at this point.

So `w = 0 ∈ C` is a ramification point. Its stabiliser is all of `Z/2`.
Two sheets fold together at `w = 0`. The group element associated to
this ramification point is the unique nontrivial element `σ ∈ Z/2`.

Picture, with sheets drawn:

```
        Total space C                  Base P^1
        --------------                 ----------
   away from 0:
   •  •     ←  fiber of 2 points  ←    •     two sheets above

   at 0:
       •    ←  fiber of 1 point   ←    •     sheets pinch together
   ramification point                  branch point
```

The single point at the top is a ramification point on `C`. The single
point at the bottom is the corresponding branch point on `P^1`. They
are different things on different spaces, though both are sometimes
called "branch points" in informal speech.

### Step 4: generalise to `z ↦ z^n`

Same picture, deck group `Z/n` acting by `w ↦ ζ_n · w`, multiplication
by an `n`-th root of unity.

For `z ≠ 0`: fiber is `n` distinct points, the `n`-th roots of `z`.
`Z/n` permutes them transitively. Free action.

For `z = 0`: fiber is `{0}`. Every element of `Z/n` fixes `0`.
Stabiliser is all of `Z/n`.

So `w = 0` is a ramification point with stabiliser `⟨ζ_n⟩ ≅ Z/n` and
ramification index `n`, meaning `n` sheets fold.

This is the local model for every tame ramification point. Near any
ramification point of index `e`, the cover looks analytically like
`z ↦ z^e`, and locally the stabiliser `⟨σ⟩` acts as `w ↦ ζ_e · w` in
suitable local coordinates.

### Step 5: from group element back to ramification point

Reverse the direction. Start with a finite group `G` acting on a curve
`C`. For each `σ ∈ G` with `σ ≠ e`:

- Let `Fix(σ) ⊂ C` be the set of fixed points of `σ`.
- For curves, `Fix(σ)` is a finite set. An automorphism of a curve has
  finitely many fixed points unless it is the identity. This is a
  theorem.
- Every point of `Fix(σ)` is a ramification point of `π : C → C/G`.

So the ramification points of the cover are

```
{ p ∈ C : Stab(p) ≠ {e} } = ⋃_{σ ≠ e} Fix(σ).
```

This is purely a statement about which points the group action fixes,
with topology playing only the passive role of telling us `C` is a
curve and the action is by automorphisms.

### Step 6: what each ramification point "means"

A ramification point `p ∈ C` corresponds to:

- A specific point of `C`, a geometric point on the curve.
- A specific subgroup `Stab(p) = ⟨σ⟩ ⊂ G`, the cyclic group of
  automorphisms fixing `p`.
- A specific generator `σ ∈ G`, up to choice within `⟨σ⟩`.

Conversely, each `σ ∈ G` with `σ ≠ e` produces a finite set of
ramification points, namely its fixed-point set.

The group element attached to the ramification point is just the
element generating its stabiliser. It tells you: at this point, `σ`
fixes the point. More precisely, `σ` acts as a rotation by
`2π/order(σ)` in local coordinates, and `σ` is the obstruction to the
covering being free here.

### Where topology re-enters

Topology comes back in when you ask: how many ramification points does
`σ` have? That count is the number of fixed points of `σ` on `C`, which
can be computed by the Lefschetz fixed-point theorem or by
orbit-stabiliser machinery applied to fibers above branch points. For
`S_5 × S_5` the count of ramification points on `C` per branch point is
`|G|/n_b = 14400/n_b`, which is the number of cosets `G/⟨σ_b⟩`. This is
the orbit size of `σ_b`'s fixed-point set under the rest of `G`.

The recipe in three lines:

1. Topology tells you the cover exists and the deck group acts.
2. Group theory tells you which points have nontrivial stabiliser, and
   the stabiliser at each such point is cyclic, generated by a specific
   element.
3. The two are stitched together by the local model `z ↦ z^e`, in which
   the cyclic stabiliser literally rotates the local disk.

Once you internalise step 3, "ramification point" stops being two
separate things, a topological notion and a group-theoretic notion, and
becomes one thing seen from two sides.
