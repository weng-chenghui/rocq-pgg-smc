#!/usr/bin/env python3
# infotheo: information theory and error-correcting codes in Rocq
# Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later
r"""
pgl_leakage_targets.py

Exact mutual-information values I(secret ; view_C) of the eight-card
PGL(2,7) orbit scheme of pgg-smc/instances/pgl27/, for every reveal set C.

This script is the numerical component of a hybrid verification. The values
themselves live in an abstract realType in Rocq, where log, addition and
multiplication never reduce, so there is no kernel computation to run; the
combinatorial data the values are read off from is certified in Rocq by
pgg-smc/instances/pgl27/pgl27_leakage_census.v.

Governing identity. With G the shuffle group, |G| = 336, and
  A = { g restricted to C           : g in G },
  B = { tau composed with g on C    : g in G },   tau the deal of secret true,
  m = |A cap B|,
each conditional view law is uniform on |G| points and
  I(secret ; view_C) = 1 - m / |G|   bits.

Validity guard. The identity holds only for |C| >= 3. Below size three the
restriction map g |-> g|_C is not injective, the two conditional laws are no
longer uniform on |G| points, and the formula reports a positive value where
the true one is 0. The report below recomputes sizes 1 to 3 from the explicit
joint distribution instead, and prints whether the closed form applies.

Kernel-certified inputs. pgl27_leakage_census.v certifies, axiom-free:
the 336 group tables by size, uniqueness, identity membership and generator
closure (pgl27_group_table_size, _uniq, _id, _closed); the orbit census, two
orbits of sizes 42 and 28 covering the seventy four-subsets, one orbit on the
fifty-six five-subsets and one on the twenty-eight six-subsets
(pgl27_orbit_four_cover, pgl27_five_subset_orbitE, pgl27_six_subset_orbitE);
the four collision counts m = 96, 72, 36, 12 with the injectivity side
conditions (pgl27_collisions_harmonic and siblings, pgl27_views_uniq_harmonic
and siblings); the ramp ends m = 336 at size three and m = 0 at size seven;
and the rational identities (336 - m) * q = p * 336 that put 1 - m/336 in
lowest terms (pgl27_collision_ratio_harmonic and siblings). Constancy of the
value along an orbit is a check of this script only, not a Rocq theorem.

The model mirrors pgl27_secrecy.v exactly:

  pgl27P        = uniform bool  (x)  uniform on pgg_G pgl27_M
  pgl27_secret  (s,g) = s
  pgl27_view C  (s,g) = [ffun i => if i \in C then tnth (orbit_encode s) (g i)
                                   else ord0]

with the three generators read off pgl27_group.v as permutation TABLES of
'I_8 (tbl_fun tbl i = tbl[i]), and orbit_encode from pgl27_orbit.v:

  orbit_encode false = [0;1;2;3;4;5;6;7]   (identity arrangement)
  orbit_encode true  = [0;1;2;4;3;5;6;7]   (the transposition (3 4))

Point 7 is the point at infinity of P^1(F_7).
"""

from fractions import Fraction
from itertools import combinations
from math import log2

# ---------------------------------------------------------------- generators
# tbl[i] is the image of i, matching Local Definition tbl_fun in pgl27_group.v
TR = (1, 2, 3, 4, 5, 6, 0, 7)   # z |-> z+1
SC = (0, 3, 6, 2, 5, 1, 4, 7)   # z |-> 3z
IV = (7, 6, 3, 2, 5, 4, 1, 0)   # z |-> -1/z
GENS = (TR, SC, IV)

IDENT = tuple(range(8))


def compose(p, q):
    """(p*q) as a map: first q, then p  -- i.e. (p o q)(i) = p[q[i]]."""
    return tuple(p[q[i]] for i in range(8))


def generate(gens):
    seen = {IDENT}
    frontier = [IDENT]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = compose(g, x)
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return sorted(seen)


G = generate(GENS)
assert len(G) == 336, len(G)

# The two dealt arrangements (position -> card).
DECK = {False: IDENT, True: (0, 1, 2, 4, 3, 5, 6, 7)}
TAU = DECK[True]                      # the transposition (3 4)
assert compose(TAU, TAU) == IDENT

# --------------------------------------------------------- sanity: the group
# sharp 3-transitivity: 8*7*6 = 336 ordered distinct triples, each hit once.
triples = {}
for g in G:
    triples.setdefault((g[0], g[1], g[2]), 0)
    triples[(g[0], g[1], g[2])] += 1
assert len(triples) == 8 * 7 * 6 and set(triples.values()) == {1}

# --------------------------------------------- cross ratio / classifier (Rocq)
INV7 = (0, 1, 4, 5, 2, 3, 6)


def sub7(a, b):
    return (a + 7 - b) % 7


def mul7(a, b):
    return (a * b) % 7


def div7(a, b):
    return mul7(a, INV7[b])


def crn(x1, x2, x3, x4):
    if x1 == 7:
        return div7(sub7(x2, x4), sub7(x2, x3))
    if x2 == 7:
        return div7(sub7(x1, x3), sub7(x1, x4))
    if x3 == 7:
        return div7(sub7(x2, x4), sub7(x1, x4))
    if x4 == 7:
        return div7(sub7(x1, x3), sub7(x2, x3))
    return div7(mul7(sub7(x1, x3), sub7(x2, x4)),
                mul7(sub7(x1, x4), sub7(x2, x3)))


def subset_class(S):
    """Rocq subset_class: equianharmonic verdict of the ascending quadruple."""
    L = sorted(S)
    if len(L) != 4:
        return False
    lam = crn(*L)
    return lam == 3 or lam == 5


# ------------------------------------------------------ orbits on k-subsets
def orbits_on_subsets(k):
    allS = [frozenset(c) for c in combinations(range(8), k)]
    todo = set(allS)
    out = []
    while todo:
        s0 = min(todo, key=lambda s: sorted(s))
        orb = {frozenset(g[i] for i in s0) for g in G}
        out.append((tuple(sorted(s0)), orb))
        todo -= orb
    return out


# ------------------------------------------------------ exact mutual info
def leakage(C):
    """I(secret ; view_C) in bits, exactly, as a Fraction.

    Both conditionals are uniform over |G| distinct restrictions when
    |C| >= 3 (the restriction map is injective by sharp 3-transitivity), so
        I = H(mixture) - log|G| = (1 - m/|G|) bits,
    with m = |A cap B|, A = {g|_C}, B = {tau o g|_C}.
    The value is also recomputed from the raw joint below.
    """
    Cs = tuple(sorted(C))
    A = {tuple(g[i] for i in Cs) for g in G}
    B = {tuple(TAU[g[i]] for i in Cs) for g in G}
    m = len(A & B)
    closed = (len(A) == len(G))          # restriction map injective
    return m, closed, Fraction(len(G) - m, len(G))


def leakage_bruteforce(C):
    """I(secret ; view_C) recomputed from the explicit joint distribution."""
    Cs = tuple(sorted(C))
    joint = {}
    for s in (False, True):
        d = DECK[s]
        for g in G:
            v = tuple(d[g[i]] for i in Cs)
            joint[(s, v)] = joint.get((s, v), 0) + 1
    tot = 2 * len(G)
    ps = {s: sum(n for (t, _), n in joint.items() if t == s) for s in (False, True)}
    pv = {}
    for (_, v), n in joint.items():
        pv[v] = pv.get(v, 0) + n
    I = 0.0
    for (s, v), n in joint.items():
        p = n / tot
        I += p * log2(p / ((ps[s] / tot) * (pv[v] / tot)))
    return I


def report():
    print("|G| =", len(G))
    print()
    census = {}
    rows = []
    for k in (4, 5, 6):
        orbs = orbits_on_subsets(k)
        census[k] = [len(o) for _, o in orbs]
        print(f"--- reveal sets of size {k}: {len(orbs)} orbit class(es), "
              f"sizes {census[k]} (total {sum(census[k])} = C(8,{k}))")
        for rep, orb in orbs:
            m, closed, val = leakage(rep)
            bf = leakage_bruteforce(rep)
            cls = subset_class(rep) if k == 4 else None
            rows.append((k, rep, len(orb), m, val, bf, cls))
            tag = "" if cls is None else \
                ("  [equianharmonic]" if cls else "  [harmonic]")
            print(f"    rep {rep}  |orbit|={len(orb):3d}  m={m:3d}  "
                  f"restriction-injective={closed}  "
                  f"I = {val} bits = {float(val):.10f}  "
                  f"(brute force {bf:.10f}){tag}")
        print()
    print("CENSUS:", {k: len(v) for k, v in census.items()},
          "-> total", sum(len(v) for v in census.values()), "classes")
    print()
    # The "+1+1" half of the census is a corollary of transitivity on the
    # COMPLEMENTARY subsets: 3-transitivity gives one orbit on 3-subsets hence
    # on 5-subsets, 2-transitivity gives one orbit on 2-subsets hence on
    # 6-subsets.  No enumeration needed to land those two in the kernel.
    print("Complement route (no BFS needed to land sizes 5 and 6):")
    for k in (2, 3, 4):
        orbs = orbits_on_subsets(k)
        print(f"  orbits on {k}-subsets: {len(orbs)} of sizes "
              f"{[len(o) for _, o in orbs]}  ->  same for {8-k}-subsets")
    print()
    print("Constancy check on every orbit (not just the representative):")
    for k in (4, 5, 6):
        for rep, orb in orbits_on_subsets(k):
            vals = {leakage(tuple(sorted(S)))[2] for S in orb}
            print(f"  size {k} rep {rep}: distinct leakage values on the "
                  f"orbit = {sorted(vals)}")
    print()
    # Below size three the restriction map g |-> g|_C is NOT injective, so the
    # closed form 1 - m/|G| does not apply; use the raw joint instead.
    print("Sizes 1..3 (must be 0, matching pgl27_view_indep):")
    for k in (1, 2, 3):
        vals = {round(leakage_bruteforce(c), 12) for c in combinations(range(8), k)}
        print(f"  size {k}: {sorted(vals)}  (closed form applicable: "
              f"{all(leakage(c)[1] for c in combinations(range(8), k))})")
    print()
    print("Size 7 and 8 (the determined end of the ramp):")
    for k in (7, 8):
        vals = {leakage(c)[2] for c in combinations(range(8), k)}
        bf = {round(leakage_bruteforce(c), 12) for c in combinations(range(8), k)}
        print(f"  size {k}: {sorted(vals)}  (brute force {sorted(bf)})")
    return rows


if __name__ == "__main__":
    report()
