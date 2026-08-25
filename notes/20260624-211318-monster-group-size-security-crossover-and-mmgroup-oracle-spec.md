# Monster group: size-vs-security crossover, and the mmgroup oracle demo spec

Date: 2026-06-24 21:13

This note records one Q&A exchange about whether the Monster group's enormous
size helps a card-shuffling protocol, followed by the verified implementation
spec for an untrusted "deal cards with the Monster from inside Rocq" demo.

---

## Question (grammar-fixed)

> But there must be a regime where the group size is too small and therefore
> insecure, and there must be a crossover between "smaller is better" and
> "bigger is better."

## Answer

You're right, and I over-compressed. "Smaller is better" was only true among
groups that already clear the security bar. Below the bar, bigger is mandatory.
So there are genuinely two opposing forces and a crossover. Both can be made
precise using the protocol's own bounds.

### The floor (too small means insecure): two lower bounds on size

1. **Hiding-entropy floor.** To hide a secret of H bits, the achievable/fiber
   set the cut mixes over must have at least 2^H equally-likely arrangements. A
   group too small literally cannot represent enough distinguishable-yet-hidden
   states. den Boer hides 1 bit with C5 (5 arrangements), which is fine. Try to
   hide 128 bits with a 5-element group and there is no security to be had,
   mixing or not.

2. **Collusion floor (from the slide).** The collusion bound is eps + 2T/N for
   T colluders on N positions. That term blows up when N <= 2T: the coalition
   simply sees the whole deck. So you need **N > 2T**, a hard lower bound on the
   deck (hence usually on the group) set by how many colluders you must resist.
   Small N means insecure against collusion, independent of mixing.

So the floor is set by the task parameters (H, T, eps), not by |G| in the
abstract. More to hide, or more colluders, forces a bigger group.

### The ceiling (too big means wasteful or unmixable)

Cost to reach eps-uniform is L >~ (1/lambda) * (log sqrt(N) + log 1/eps), and
L >~ log_d |G| just to cover the group. For an expander, mixing time is about
log|G|/lambda, so the entropy you can actually hide per cut is about lambda (the
spectral gap), constant in size. Hiding H bits costs about H/lambda cuts. Past
the size you need, extra elements buy no security and only add cuts. With
product or bad-gap structure (S5 x S5) you never mix at all.

### The crossover

Pick the **smallest good-expander group whose size >= 2^H, with N >~ 2T/eps.**

- Below it: insecure (cannot hide enough, or colluders win). Bigger is better here.
- Above it: secure, but each extra factor of size costs about 1/lambda more cuts
  for nothing. Smaller is better here.
- At it: minimum cuts for the security target. den Boer sits essentially at its
  floor, the smallest transitive group hiding its 1 bit, one cut, eps = 0. That
  is why it is elegant.

The figure of merit is roughly hidden bits ~ lambda * L, so you choose the group
by the security you need (which sets the floor) and then minimize size to
minimize cuts. Size is a cost you pay to clear the floor, not a benefit.

### Where the Monster sits

Its size (~2^180) only matches a target of hiding ~180 bits. But even at a
genuine 180-bit task it loses, because the crossover selects on structure, not
just size. A symmetric group like S36 (36! is about 2^132, push n a little
higher for 180) or a product of moderate groups gives the same hiding ceiling
with a far better gap, feasible cuts, and a usable sum-mod-style recovery. The
Monster gives you the size but a recovery that reads ~2.6 bits and a mixing time
you cannot pay. So the size-vs-security tradeoff is real, and you were right to
insist on it, but it never lands on the Monster. The Monster is always strictly
past the crossover, for every H and T.

---

## Appended: verified implementation spec (Monster product-class oracle demo)

Scope chosen during brainstorming: an **untrusted runnable demo** whose
mechanism is a **live Rocq oracle plugin** that calls mmgroup mid-session and
reflects the result back into Rocq as a term, aiming at a **full instance plus
recovery if feasible**. The validation below establishes what is feasible and
what the blockers are. Kernel verification is explicitly out of scope (the
result enters via an oracle, the kernel does not re-check it).

### A. mmgroup capability (verified against source + Seysen arXiv:2203.04223v3)

- **Representation.** Dimension 196884 (= 196883 + trivial), entries in Z[1/2].
  `MM('r')` gives a random Monster element. Vectors are `MMVector` (factory
  `MMV(p)`); the action is right multiplication `v * g`. Allowed moduli p in
  {3, 7, 15, 31, 127, 255}; the working modulus is 15.
- **Smallest faithful permutation rep.** Degree 97239461142009186000 (~9.72e19),
  acting on the 2A involutions (Fischer transpositions), equivalently the cosets
  of the centralizer 2.B. mmgroup's `AXIS_ORBIT_SIZES` (12 G_x0-orbits) sum to
  exactly this number.
- **Point -> vector (REAL).** A point is a 2A involution; its axis vector is
  `mmgroup.axes.Axis('i', involution).v15` (an `MMVector` mod 15). Apply an
  element with `axis * g` or `axis.v15 * g`. Recover the involution from the axis
  via `axis.g_axis`.
- **Vector -> point label (PARTIAL).** `axis.axis_type()` returns only the 12-way
  G_x0 orbit watermark (`'2A','2B','4A',...`), not a unique point. The actual
  point is recovered as a group element via `axis.g_axis`.
- **Dense integer index (DOES NOT EXIST).** There is no bijection between the
  ~9.72e19 points and integers in [0, 9.72e19). The functions
  `get_vector_from_point_index` / `decode_vector_to_index` are not mmgroup API,
  and a "point index" integer like 241559192842912464 is fictional. The stable
  name of a point is its canonical reduced-word **string** `str(g.reduce())`
  (under 256 bits, equality-testable, stable within a package version).
  `MM.as_int()` exists but is 255-bit, over elements (not points), and version
  non-portable, so it is not a usable point index.
- **Canonical form / equality (REAL).** `MM.reduce()` gives a unique reduced
  form; `==` compares reduced elements. Stable serialization is `str(...)`.
- **Performance.** Vector times one generator < 160 microseconds; a full reduced
  element multiply < 30 ms. No table of size 1e20 is stored or storable.

### B. Recovery design (the nonabelian analog of sum-mod)

- A naive "secret = which fiber element" fails: the Monster is transitive on the
  2A points (one orbit), so there is no nontrivial M-equivariant fibration to
  hide a secret in the appearance channel.
- **Rescue.** Encode the secret as a conjugation-invariant of the dealt tuple.
  The cut is conjugation by a random Monster element g (action t -> t^g). For
  two dealt involutions t1, t2, the order/class of their product is cut-invariant:
  ord(t1^g * t2^g) = ord((t1 t2)^g) = ord(t1 t2). mmgroup computes it directly.
  This is the nonabelian analog of den Boer's translation-invariant sum-mod.
  Products of two 2A involutions fall in 9 classes of orders {1,2,3,4,5,6}, so
  the secret carries about log2(6) ~ 2.6 bits.
- Operationally the full instance plus recovery IS demoable: show in Rocq that
  recovery returns the secret regardless of the random cut. The formal anonymity
  proof is out of scope (asserted, not proven), consistent with the existing
  external/axiom treatment of S5 and S5 x S5 security.

### C. Rocq oracle mechanism

- An OCaml plugin (vernacular command, or an Ltac2 `external`) spawns a
  persistent Python+mmgroup worker via `Unix.open_process`, speaks a simple line
  protocol, and reflects results back into Rocq as terms.
- Card = canonical reduced-word string; deck = `list string`. Two commands:
  - `MMDeal deck` : apply a fresh random cut g (a short Monster word), return the
    shuffled deck as Rocq strings.
  - `MMRecover c1 c2` : return the product order/class as a small Rocq `nat` (or
    a small inductive).
- Demonstrate over several random cuts that `MMRecover (MMDeal ...)` is invariant
  (a sampled demonstration, not a proof). Pattern is the same as `hammer` /
  SMTCoq shelling out to external solvers, minus the certificate re-check.

### D. Blockers, ranked

1. **No integer index.** Cards must be ~256-bit canonical word strings, not
   65-bit integers. (Representation change; the demo still runs.)
2. **No reuse of the verified pipeline.** The framework's
   `pgg_rho : {morphism >-> {perm 'I_N}}` bakes in a materialized permutation on
   'I_N and cannot be instantiated for N ~ 1e20. The Monster demo is a separate
   oracle-backed layer over `string` handles that shares the protocol shape, not
   the code. Honest framing: small groups are kernel-checked (vm_compute), the
   Monster is runnable-in-principle via an untrusted oracle, decoupled from the
   verified pipeline.
3. **Untrusted plus low entropy.** Anonymity is asserted not proven, and the
   secret is ~2.6 bits. It is a mechanism demonstration, not a strong
   secret-sharing scheme.

### E. What the Monster actually demonstrates (the point of building it)

Not a better protocol (it has no shuffling or security advantage, see the Q&A
above). The Monster is the unique instance that:

1. Has no small permutation representation (smallest faithful degree ~1e20), so
   it forces the action-oracle execution model and validates the claim that the
   deal needs only `apply(g, point)`, never the group table or a materialized
   rho(g).
2. Decouples "runnable" from "kernel-checked", which are conflated in all four
   small instances. It is the existence proof that the framework's
   group-agnosticism is real, because it is the first instance where the kernel
   cannot secretly do the group theory.

### Sources

- Seysen, "A fast implementation of the Monster group", arXiv:2203.04223v3 (2024).
  https://arxiv.org/pdf/2203.04223
- mmgroup source (master): mm_space.py, mm_group.py, tests/axes/axis.py.
  https://github.com/Martin-Seysen/mmgroup ; docs https://mmgroup.readthedocs.io
- Wikipedia, "Monster group" (permutation degree 97239461142009186000 and its
  factorization). https://en.wikipedia.org/wiki/Monster_group
