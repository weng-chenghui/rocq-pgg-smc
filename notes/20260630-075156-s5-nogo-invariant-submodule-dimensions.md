# Why S_5 has no recoverable AG-style secret code: where the invariance lives

Source: `reconstruct/s5_nogo.v`. This note records the conceptual point that is
easy to misread when first looking at the no-go. The natural first reading is
"we encode the secret at a specific coordinate of the vector, and that
coordinate stays put under the permutations." That reading is correct but it
describes the trivial half of the picture. The obstruction is not about a single
secret coordinate staying fixed. It is about the dimension of the *invariant
code subspace* that recovers the secret. This note spells out that distinction
in full.

## The setup

The wired S_5 instance acts on `GF(5)^6` in the `1 + 5` block layout
(`secret_action`, `rG_secret`):

```
secret_action s = block_mx 1 0 0 (perm_mx s)
```

Coordinate 0 is the secret slot. Its standard basis vector is `e0`. Coordinates
1..5 are the shares, permuted by the natural action of S_5. The block-diagonal
shape means the action does two independent things at once. It applies the
identity matrix `1` to the secret coordinate, so coordinate 0 is held completely
fixed by every group element. It applies `perm_mx s` to the five share
coordinates, so those get shuffled. As a representation the module therefore
splits as a direct sum

```
GF(5)^6  =  trivial(secret, 1-dim)  (+)  natural-perm-module P(shares, 5-dim)
```

## The trivial half: a fixed coordinate is a 1-dimensional invariant piece

Because coordinate 0 is fixed by every permutation, the line `<e0>` is already a
G-invariant subspace all by itself, and it carries the secret. So at the level
of "the secret sits at a coordinate that the shuffles never move", everything
the first reading says is true. This costs nothing and is available for free.

The point is that this 1-dimensional invariant line is not a usable
secret-sharing code. It is the secret stored in the clear. There is no sharing,
no threshold behaviour, nothing distributed across the players. Recovering the
secret from `<e0>` is just reading coordinate 0. A real covering scheme has to
do more, and that "more" is where the dimension enters.

## What recoverability actually requires: a whole invariant subspace W

A covering scheme that recovers the secret needs a G-invariant *subspace* W,
which is the code, with two properties:

- (a) W contains the secret direction `e0`, so the secret is expressible inside
  the code, and
- (b) `dim W` lands in the threshold gap window, which `gap_dimension.v`
  (`gap_dim_window`) forces to `{3, 4}`.

The crucial word is *invariant*, and it is a property of the whole subspace W,
not of any one coordinate. W being G-invariant means: for every group element
`s` and every vector `v` in W, the shuffled vector `v *m secret_action s` is
again in W. In words, the entire subspace is mapped into itself by every
shuffle matrix at once. It is closed under the full group action. This is a far
stronger demand than "one coordinate sits still". It constrains how the secret
direction and the share directions are allowed to mix, because once a vector
that mixes the secret with some shares is in W, every shuffled copy of that
vector must also be in W.

This is why dimension matters. Look at what invariant subspaces containing `e0`
can be, by their size:

- dimension 1: W = `<e0>`, the secret in the clear, no sharing, as above.
- dimension 2: W = `<e0>` plus one invariant share direction. The only
  1-dimensional invariant subspace of the shares is the all-ones line (the
  constant vector), so this is essentially the secret plus a single global
  parity of the shares. Still far too rigid to be a gap-window code.
- dimensions 3 and 4: these are the codes the gap regime needs. They would have
  to bind the secret direction to a 2-dimensional or 3-dimensional invariant
  chunk of the share coordinates. That invariant chunk is exactly what does not
  exist.

So the question "is there a recoverable code" becomes the concrete
representation-theoretic question "does the share module have an invariant
subspace of dimension 2 or 3 to glue the secret onto".

## The kernel fact: the share module has no dimension-2 or dimension-3 submodule

Over `GF(5)` the natural permutation module `P = GF(5)^5` of S_5 is uniserial,
and its only submodule dimensions are

```
{0, 1, 4, 5}        (perm_module_no_dim23: no submodule of dim 2 or 3)
```

The proof is elementary and runs by a dichotomy on a submodule W of P:

- If every vector of W is constant (all coordinates equal), then W lies in the
  all-ones line, so `rank W <= 1`.
- Otherwise W contains a vector `v` with two differing coordinates `v_i <> v_j`.
  Applying the transposition `tperm i j` and subtracting leaves a scalar
  multiple of the difference vector `e_i - e_j`, which after rescaling puts
  `e_i - e_j` itself into W (`tperm_diff`, `nonconst_diff_in`). Now S_5 is
  2-transitive, so conjugating this one difference vector by the group produces
  every difference vector `e_a - e_b` (`diff_actE`, `pair_perm`, `all_diff_in`).
  The difference vectors span the 4-dimensional sum-zero subspace `P_0`, so
  `rank W >= 4` (`rank4_of_diff`, witnessed by the rank-4 matrix
  `diff_basis_mx`).

Hence `rank W` is in `{0, 1, 4, 5}` and never 2 or 3.

Correction on the role of characteristic 5. The difference-vector argument above
uses no characteristic assumption, so `rank W` is in `{0, 1, 4, 5}` over **every**
field. Characteristic 5 controls only whether the all-ones line sits inside the
sum-zero space. When `char F = 5`, the coordinate sum `5 = 0` places `<1>` inside
`P_0`, giving the uniserial nesting `<1> subset P_0 subset P` with no complement.
In a characteristic coprime to 5 the sum is nonzero, so `<1>` is a complement and
the module splits as `<1> (+) P_0`, with `P_0` the **irreducible** standard module
of dimension 4. Either way the submodule dimensions are `{0, 1, 4, 5}` and the
secret-carrying dimensions are `{1, 2, 5, 6}`, never the gap window `{3, 4}`.

So the `{3,4}` infeasibility is **characteristic-independent** for the natural
`S_5` action. The reason is that `S_5` has no 3-dimensional ordinary irreducible
at all (its irreducible dimensions are `{1,1,4,4,5,5,6}`), and its standard module
is the irreducible of dimension 4. The dimension-3 object `D^(4,1)`, the heart,
exists only in characteristic 5, and even there only as the subquotient `P_0/<1>`,
never as a submodule. The lemma `invariant_profiler.maschke_ss` gives
semisimplicity in coprime characteristic, which splits the module but does not
create a dim-3 submodule. An earlier draft of this note, following a comment in
`s5_nogo.v`, claimed that coprime characteristic makes dimensions 2 and 3 reappear
and that the no-go is a char-5 phenomenon. That is wrong for `S_5` and is
corrected here. Contrast the `S_4` case below: `S_4` does have a 3-dimensional
standard module, which is exactly why four shares would not exhibit the no-go.

## The reduction: stripping the secret coordinate drops the dimension by one

The six-coordinate problem reduces to the five-coordinate kernel fact by
projecting away coordinate 0. The projection is `proj_share = col_mx 0 1`, which
keeps the five share coordinates and discards the secret coordinate. Two lemmas
do the work:

- `proj_mxmodule`: the projection intertwines the two actions
  (`secret_proj_comm`), so the image `U *m proj_share` of an `rG_secret`-invariant
  submodule U is an `rG`-invariant submodule of the share module. Invariance is
  preserved by the projection.
- `mxrank_proj_pred`: when `e0 <= U`, the projection drops the rank by exactly
  one, so `rank (U *m proj_share) = (rank U).-1`. The reason the drop is exactly
  one is that `e0` lies in the 1-dimensional kernel of `proj_share`
  (`e0_proj_share`, `proj_share_rank`), and it is the unique direction U has
  inside that kernel, so projection kills exactly the secret line and nothing
  else.

Putting the kernel fact and the reduction together, a secret-carrying invariant
code of dimension d projects to an invariant subspace of the shares of dimension
`d - 1`, which must lie in `{0, 1, 4, 5}`. So the achievable secret-carrying
code dimensions are exactly those `d` with `d - 1 in {0, 1, 4, 5}`:

```
achievable secret-carrying code dims:  d in {1, 2, 5, 6}
gap window demands:                     d in {3, 4}
```

The gap window is precisely the missing middle of the share-module lattice
shifted up by one. There is no invariant chunk of the shares of dimension 2 or
3 to bind the secret to, so there is no code of dimension 3 or 4 that recovers
the secret.

## The theorems

- `s5_no_secret_dim3`: a dimension-3 secret code projects to share-dimension 2,
  forbidden by `perm_module_no_dim23`.
- `s5_no_secret_dim4`: a dimension-4 secret code projects to share-dimension 3,
  forbidden.
- `s5_gap_window_infeasible`: no recoverable secret submodule has a dimension in
  `{3, 4}`.
- `s5_gap_infeasible`: the end-to-end statement. Any strict-threshold-gap
  parameters at length 6 force the required code dimension into `{3, 4}` via
  `gap_dim_window`, and both no-go theorems refute those dimensions, so the
  wired S_5 gap instance is mathematically impossible.

## One-sentence summary

S_5 cannot carry a recoverable algebraic-geometry-style secret code because the
secret coordinate being fixed is only a 1-dimensional invariant line, while a
real code is a whole invariant subspace W that has to bind the secret to an
invariant chunk of the shares, and in characteristic 5 the share module
`GF(5)^5` admits invariant subspaces only of dimensions `{0, 1, 4, 5}`, so
secret-carrying codes can only have dimensions `{1, 2, 5, 6}` and the threshold
gap demands dimension 3 or 4, which does not exist.

## Relation to Shamir secret sharing (Q&A)

These two exchanges record the cleanest on-ramp for the result. Shamir's scheme
is the canonical thing to anchor on, because the no-go lives in exactly the same
world as Shamir, with one extra constraint.

### Q1: Can I understand this through Shamir's secret sharing?

Yes. The whole framework here is code-based secret sharing, and Shamir is its
canonical special case. Massey's observation is that every linear `[n, k]` code
gives a secret-sharing scheme in which one coordinate is the secret and the rest
are the shares, and the access structure is read off from the code. Shamir is
that construction applied to a Reed-Solomon code (random low-degree polynomial
`f`, secret `f(0)`, shares `f(1), ..., f(n)`, recover by interpolation).
"Algebraic-geometry-style" just means the higher-genus generalisation of
Reed-Solomon, codes from curves with more rational points, so Shamir is literally
the genus-0 case of what the S_5 instance is attempting.

The dictionary between the two:

```
Shamir / Reed-Solomon                 |  S_5 no-go
--------------------------------------+-------------------------------------------
secret s = f(0), a chosen coordinate  |  secret at coordinate 0, direction e0
shares f(1), ..., f(n)                |  the 5 permuted share coordinates
the scheme IS a linear code (RS)      |  the scheme IS a G-invariant submodule W
threshold set by the code dimension   |  code dimension forced into gap window {3,4}
recover s from enough shares          |  recover the secret because e0 is in W
```

The one ingredient Shamir does NOT have is symmetry. Plain Shamir imposes no
group action on the shares, so you are free to choose any Reed-Solomon code of
any dimension, and the dimension never blocks you. The S_5 instance wires the
share coordinates to be permuted by S_5 and requires the secret-sharing code to
be invariant under that shuffle, that is `v *m secret_action s` is in W for every
group element `s` and every `v` in W. Reed-Solomon never has to commute with a
prescribed permutation group. This code does.

Once invariance is imposed, the choice of code collapses to the short fixed list
of S_5-invariant subspaces of `GF(5)^5`: the zero space (dim 0), the all-ones /
repetition line (dim 1), the sum-zero / parity hyperplane (dim 4), and the whole
space (dim 5). Add the fixed secret coordinate back and the secret-carrying
invariant codes can only have dimensions `{1, 2, 5, 6}`. The gap regime needs
dimension 3 or 4, which are not on the menu.

### Q2: So is the picture "Shamir secret sharing PLUS a symmetry requirement", where the split won't survive the permutation-invariance test?

Yes, that slogan is right for the setup, with two sharpenings that turn it from
suggestive into precise.

Sharpening 1: the symmetry is not bolted on as an afterthought, it is forced by
the protocol. In Shamir you own the encoding and can pick any code. In the card
protocol you do not own it. The shares are literal card positions and the only
operation available is the physical shuffle, which is the S_5 action generated by
the adjacent transpositions. Any secret-recovery structure has to ride on top of
those shuffles, so the code is compelled to commute with S_5. The symmetry was
present from the first card. The pedagogical move "start from Shamir, then impose
symmetry" is a fine way to build intuition, but in the real protocol the symmetry
is intrinsic to the mechanism, not added laterally.

Sharpening 2: the conclusion is an impossibility over all codes, not a property
of one Shamir instance. If you take a particular Shamir code and test it for
S_5-invariance, it generically fails, but that is unremarkable, since almost any
code fails a random symmetry test. The no-go is stronger: at the dimension the
threshold gap needs, namely 3 or 4, NO code over `GF(5)` is S_5-invariant,
however it is designed, Shamir or AG or hand-rolled. So "Shamir plus symmetry
will not survive" should be read as "the symmetry-and-dimension demand is
unsatisfiable", not "this one scheme happens to break". The codes that do survive
the symmetry test exist only at dimensions `{1, 2, 5, 6}`, and those are the
wrong dimensions for a useful threshold: dimension 1 is the secret in the clear,
dimension 2 adds only a single global parity of the shares. The dimensions where
sharing becomes interesting are exactly the ones the symmetry forbids.

One escape hatch confirms that the symmetry is the whole story: drop the symmetry
requirement and you are back to ordinary Shamir, which works fine. Changing the
field does NOT escape it. The difference-vector argument is characteristic-free,
so the `{0,1,4,5}` share profile holds over every field, and `S_5` has no
3-dimensional irreducible to supply a gap-window code in any characteristic (see
the correction above). Moving off characteristic 5 only changes the module from
uniserial to split, not the available dimensions. The no-go is the
`S_5`-natural-action obstruction, characteristic-independent, not a
characteristic-5 artifact.

One-liner: PGG-by-S_5 is Shamir-style secret sharing whose code must be invariant
under the card shuffle, and over `GF(5)` that requirement has no solution at the
threshold dimensions, so the symmetric scheme cannot be built at all.

### Q3: How does the code dimension actually affect the secret encoding? Reason through an example.

"Dimension" sounds abstract, but in linear secret sharing it has a concrete
meaning: the dimension of the code is the threshold. It is how many shares must
cooperate to recover the secret, which is the same as how many independent random
masks are hiding it. The principle:

```
code dimension k  =  (number of random masks) + 1  =  shares needed to recover
```

The secret is mixed with `k - 1` independent random coefficients, and each share
is the secret plus a linear combination of those masks. To peel the masks off, a
coalition needs enough shares to solve for all `k - 1` unknowns. More dimension
means more masking means a higher threshold.

#### Worked example over GF(5)

Field GF(5), arithmetic mod 5, to match the no-go's field. Secret `s = 3`. Run
dimension 2, then dimension 3, and watch the threshold move.

Dimension 2, one random mask `a`, encode `f(x) = s + a*x`. Dealer draws `a = 4`.
Shares are the evaluations `f(1..4)`:

```
f(1) = 3 + 4    = 7  ≡ 2
f(2) = 3 + 8    = 11 ≡ 1
f(3) = 3 + 12   = 15 ≡ 0
f(4) = 3 + 16   = 19 ≡ 4
```

- One share, say `f(1) = 2`. A lone player solves `s + a = 2`, that is
  `a = 2 - s`. Every candidate secret `s in {0,1,2,3,4}` has a matching `a`, and
  `a` was uniform, so all five secrets remain equally likely. No information.
- Two shares, `f(1) = 2` and `f(2) = 1`. Now `s + a = 2` and `s + 2a = 1`.
  Subtract: `a = -1 ≡ 4`, then `s = 2 - 4 ≡ 3`. Recovered.

Dimension 2 gives privacy against 1 player and recovery by 2, a clean 2-out-of-n.

Dimension 3, two random masks `a, b`, encode `f(x) = s + a*x + b*x^2`. Dealer
draws `a = 4, b = 1`:

```
f(1) = 3 + 4 + 1     = 8  ≡ 3
f(2) = 3 + 8 + 4     = 15 ≡ 0
f(3) = 3 + 12 + 9    = 24 ≡ 4
f(4) = 3 + 16 + 16   = 35 ≡ 0
```

- Two shares, `f(1) = 3` and `f(2) = 0`. That is two equations in three unknowns
  `s, a, b`. Eliminating leaves one relation among `a, b`, and for every
  candidate `s` there is still a consistent `(a, b)`, so two players learn
  nothing.
- Three shares. Three equations in three unknowns, the Vandermonde system is
  invertible, so `s, a, b` are pinned down and the secret falls out. Recovered.

Dimension 3 gives privacy against 2 and recovery by 3. The single extra dimension
(the mask `b`) pushed both thresholds up by one.

That is the entire role of dimension: each added dimension is one more random
coefficient stirred into the secret, which raises by one the number of shares
needed to cancel it.

#### Why this is exactly the no-go's knob

In the S_5 instance, "code dimension" is this same number. The threshold-gap
regime needs an intermediate code, dimension 3 or 4, because that is where you
get a meaningful "you need several but not all players" structure, a real
3-out-of-something or 4-out-of-something. The two extremes are useless:

- dimension 1, no masks: every share equals the secret, threshold 1, no privacy,
  the secret in the clear.
- dimensions 5 and 6, almost everything is a mask: you would need nearly every
  share, the scheme degenerates the other way.

A generic, symmetry-free dimension-3 code is precisely the healthy scheme in the
worked example, which is what the protocol wants. But the S_5-plus-GF(5) symmetry
permits codes only of dimension `{1, 2, 5, 6}`. The useful middle, where the
masking gives a genuine threshold, is the forbidden band. The symmetry does not
merely make encoding awkward, it deletes the only dimensions at which the sharing
would be interesting.

Honest caveat: the surviving invariant codes at dimensions 1, 2, 5, 6 are special
rigid codes, not generic Shamir codes, so their exact access structures take a
separate short computation. The robust statement is the dimension count, which is
what the no-go pins down.

### Q4: Show concretely, with a real secret-bearing sharing, WHY the symmetry forbids the middle dimension.

A genuine dimension-3 sharing of a secret works fine on its own. The moment you
require it to commute with the card shuffle, the shuffle breeds difference vectors
that inflate the code past dimension 3. Here it is with explicit GF(5) numbers,
reusing the secret `s = 3`.

#### A note on counting shares over GF(5)

GF(5) has only five field elements, so a Shamir-style scheme cannot both put the
secret at a separate point and still have five distinct evaluation points for five
shares. The clean fix: use all five field points `0,1,2,3,4` as the five shuffled
share positions, and let the secret be the one remaining degree of freedom, the
leading coefficient (equivalently the value the polynomial would take at infinity).
The masks are the lower coefficients. It is the same Shamir idea, the secret is the
slot not handed out as a share.

This five-share count is not cosmetic. The obstruction needs `char = 5` to divide
the number of shuffled shares `= 5`, because that is what drops the all-ones vector
`(1,1,1,1,1)` into the sum-zero space (its coordinate sum is `5 ≡ 0`) and makes the
submodule lattice uniserial with dims `{0,1,4,5}`. With four shares `5` does not
divide `4`, the all-ones vector lies outside sum-zero, Maschke splits off a
3-dimensional piece, an invariant dimension-3 code exists, and there is no
obstruction at all. So the demonstration must run on five shares, not four.

#### The sharing function (it uses the secret and the masks)

Secret `s = 3`, placed in the leading coefficient. Masks `c_0 = 1, c_1 = 2`. The
sharing polynomial is

```
f(x) = 1 + 2x + 3x^2        (masks c_0, c_1 ; secret = leading coeff c_2 = 3)
```

Evaluate at the five share positions `0,1,2,3,4`:

```
f(0) = 1
f(1) = 1+2+3   = 6  ≡ 1
f(2) = 1+4+12  = 17 ≡ 2
f(3) = 1+6+27  = 34 ≡ 4
f(4) = 1+8+48  = 57 ≡ 2

share vector   v = (1, 1, 2, 4, 2)        secret = c_2 = 3
```

In the protocol's `1 + 5` layout the full codeword tags the secret onto the front,
in its own slot that the shuffle never touches:

```
c = ( 3 | 1, 1, 2, 4, 2 )      slot 0 = secret 3 ; the five shares follow
```

The shuffle permutes only the five share slots after the bar, so the secret stays
fixed while the shares move. The steps below track this full codeword `c`, so the
secret is visible throughout.

#### It works as a sharing BEFORE any permutation

Take any three shares, say positions 2,3,4 `= (2, 4, 2)`. Interpolating the
degree-2 polynomial through `(2,2), (3,4), (4,2)` returns
`(c_0, c_1, c_2) = (1, 2, 3)`, so the leading coefficient `c_2 = 3` is the secret.
Two shares leave `c_2` completely free, so they reveal nothing. So `v` is a
working dimension-3, threshold-3 sharing of the secret 3, built from the secret
and both masks. This is the "before permuting" object.

#### Step 1: the shuffle ejects the sharing

The card shuffle permutes the five share slots and leaves the secret slot fixed.
Swap the two shares at points 1 and 2 (the values `1` and `2`):

```
c   = ( 3 | 1, 1, 2, 4, 2 )
τ·c = ( 3 | 1, 2, 1, 4, 2 )      secret slot fixed, two shares swapped
```

Are the five shares of `τ·c` still evaluations of some degree-2 polynomial?
Interpolate them from points 0,1,2 `= (1, 2, 1)`:

```
c_0 = 1                      (position 0)
c_0 + c_1 + c_2 = 2          (position 1)  ->  c_1 + c_2 = 1
c_0 + 2 c_1 + 4 c_2 = 1      (position 2)  ->  2 c_1 + 4 c_2 = 0  ->  c_1 + 2 c_2 = 0
```

Solving gives `c_2 = 4, c_1 = 2`, so the only candidate is `g(x) = 1 + 2x + 4x^2`.
But at point 3 that predicts `g(3) = 1 + 6 + 36 = 43 ≡ 3`, while the share there is
`4`. Inconsistent. So `τ·c` is not a codeword: after the swap the five shares
agree with no degree-2 polynomial, so the shuffled configuration encodes no
consistent secret. The shuffle has thrown the sharing out of the code.

#### Step 2: why you cannot patch it, the blow-up to dimension 4

Suppose you enlarge the code to admit `τ·c` too. If an invariant space `W`
contains `c` and `τ·c`, it contains their difference. Subtract coordinate by
coordinate, the secret slot first:

```
c − τ·c = ( 3−3 | 1−1, 1−2, 2−1, 4−4, 2−2 )
        = (  0  |  0,  −1,   1,   0,   0 )
        = 4 · ( 0 | e_1 − e_2 )
```

Read off the two halves. The secret slot is `3 − 3 = 0`: the secret cancels,
exactly because the shuffle never moved it. What survives is a pure difference
vector `e_1 − e_2` of two share slots, up to the scalar `4`, which you divide out
since `4 · 4 ≡ 1`. So the share difference `e_1 − e_2` is forced into `W`.

Now keep shuffling that one difference vector. Other swaps turn `e_1 − e_2` into
the four independent vectors

```
e_1 − e_0 = (−1, 1,  0,  0,  0)
e_1 − e_2 = ( 0, 1, −1,  0,  0)
e_1 − e_3 = ( 0, 1,  0, −1,  0)
e_1 − e_4 = ( 0, 1,  0,  0, −1)
```

each summing to 0, which together span the entire 4-dimensional sum-zero space.
Hence `dim W >= 4`. The intended degree-2 code (dimension 3) itself sits inside
sum-zero, so admitting one shuffle swallows it whole into the dim-4 sum-zero space,
and the secret leading-coefficient functional is no longer well-defined on the
enlarged code.

So the instant your sharing contains one non-constant pattern, the shuffles breed
all the difference vectors and the dimension jumps straight to at least 4. It
overshoots 3. There is no way to stop at 2 or 3.

#### Step 3: the dichotomy

Every vector is either constant or not:

- if `W` has only constant vectors, then `W` is contained in the all-ones line, so
  `dim W <= 1`.
- if `W` has any non-constant vector, the Step-2 blow-up gives `dim W >= 4`.

So an invariant subspace of the 5 shuffled positions has dimension in
`{0, 1, 4, 5}`, never 2, never 3. Restoring the secret coordinate in the `1 + 5`
layout shifts this up by one, so the secret-carrying invariant codes are
`{1, 2, 5, 6}`, never the 3 or 4 you need.

#### Connecting it back to the masks

The whole purpose of the masks is to spread the secret unevenly across the
positions, since that is what hides it. So any genuine masking pattern is
non-constant by design. The shuffle, applied to a non-constant pattern, mixes the
positions and, by the differencing above, forces in every `e_i − e_j`, smearing
the carefully tuned dim-3 sharing across the full dim-4 sum-zero space. The only
masking patterns the shuffle leaves alone are the two useless extremes: every
position identical (dim 1, the secret in the clear) or anything summing to zero
with no finer structure (dim 4, no clean threshold). A symmetric mask cannot carve
out the intermediate 2- or 3-dimensional slice that a real threshold needs.

#### This is the file's proof made numerical

- `tperm_diff`: `v − τ·v = (v_i − v_j) · (e_i − e_j)`, which is Step 2's
  `4 · (e_1 − e_2)`.
- `nonconst_diff_in`: a non-constant codeword forces a difference vector in.
- `diff_actE` and `all_diff_in`: 2-transitivity breeds all difference vectors,
  the four spanners of sum-zero.
- `rank4_of_diff` then `perm_module_no_dim23`: hence `dim >= 4`, so dimensions 2
  and 3 are impossible.
