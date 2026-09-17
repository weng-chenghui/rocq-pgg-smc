# Outside-the-kernel exploration: how the leakage of the PGL(2,7) scheme depends
# on the choice of the fixed pair of decks (D_false, D_true), and what the
# all-decks (orbit-uniform) dealer leaks. Conventions follow pgl27_leakage_census.v.
from itertools import permutations
from collections import Counter
from fractions import Fraction
from math import log2

gens = [(1,2,3,4,5,6,0,7), (0,3,6,2,5,1,4,7), (7,6,3,2,5,4,1,0)]
comp = lambda t1, t2: tuple(t2[x] for x in t1)          # code_comp
G = {tuple(range(8))}; frontier = list(G)
while frontier:
    new = []
    for t in frontier:
        for g in gens:
            u = comp(t, g)
            if u not in G: G.add(u); new.append(u)
    frontier = new
G = sorted(G); assert len(G) == 336

orbit = lambda S: {frozenset(t[x] for x in S) for t in G}
equi = orbit((0,1,2,4)); harm = orbit((0,1,2,3))
assert len(equi) == 28 and len(harm) == 42
cls = lambda D: frozenset(p for p in range(8) if D[p] < 4) in equi   # orbit_class

reps = {"4h": (0,1,2,3), "4e": (0,1,2,4), "5": (0,1,2,3,4),
        "6": (0,1,2,3,4,5), "7": (0,1,2,3,4,5,6)}
views = lambda D, S: {tuple(D[t[x]] for x in S) for t in G}

# census sanity check: the repo's pair (code_id, code_tau)
Did, Dtau = tuple(range(8)), (0,1,2,4,3,5,6,7)
base = tuple(len(views(Did, S) & views(Dtau, S)) for S in reps.values())
print("repo pair collisions (expect 96,72,36,12,0):", base)

# decks modulo the shuffle: right G-orbits, split by class
seen, orbs = set(), {False: [], True: []}
for D in permutations(range(8)):
    if D in seen: continue
    seen.update(tuple(D[g[x]] for x in range(8)) for g in G)
    orbs[cls(D)].append(D)
print("shuffle-orbits of decks: class false", len(orbs[False]), " class true", len(orbs[True]))

V = {D: {k: views(D, S) for k, S in reps.items()} for c in orbs for D in orbs[c]}
prof = Counter()
for Df in orbs[False]:
    for Dt in orbs[True]:
        prof[tuple(len(V[Df][k] & V[Dt][k]) for k in reps)] += 1
print("\nfixed pairs (D_false, D_true) up to shuffling:", sum(prof.values()))
print("distinct collision profiles (4h,4e,5,6,7) -> #pairs, leakage = 1 - m/336:")
for p, n in sorted(prof.items(), key=lambda x: -x[1]):
    leak = [1 - Fraction(m, 336) for m in p]
    # smallest size at which EVERY coalition determines the secret (m = 0)
    size_ok = {4: p[0] == 0 and p[1] == 0, 5: p[2] == 0, 6: p[3] == 0, 7: p[4] == 0}
    r = min(k for k in (4, 5, 6, 7) if all(size_ok[j] for j in range(k, 8)))
    avg4 = (42 * leak[0] + 28 * leak[1]) / 70
    print("  ", p, "x", n, "  leak:", [str(x) for x in leak],
          "  recovery threshold r =", r, "  mean over the 70 four-subsets =", avg4)

# all-decks dealer: uniform deck of the secret's class (shuffle is absorbed)
print("\nall-decks dealer, I(secret; view) in bits, uniform prior:")
decks = {c: [D for D in permutations(range(8)) if cls(D) == c] for c in (False, True)}
for k, S in reps.items():
    P = {c: Counter(tuple(D[x] for x in S) for D in decks[c]) for c in decks}
    n = {c: len(decks[c]) for c in decks}
    HSV = 0.0
    for v in set(P[False]) | set(P[True]):
        a, b = P[False][v] / n[False] / 2, P[True][v] / n[True] / 2
        for q in (a, b):
            if q > 0: HSV -= q * log2(q / (a + b))
    print("  ", k, round(1 - HSV, 6))
