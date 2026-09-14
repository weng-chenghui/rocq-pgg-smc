"""Exhaustive checks for candidate second instances of the orbit-class family.

Positions are 0..n-1. A permutation is a tuple p with p[i] = image of i.
Group closure by BFS on generators (fine up to ~10^5 elements).
"""
from itertools import combinations, permutations
from collections import deque
import sys

def compose(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(len(p)))

def closure(gens):
    n = len(gens[0])
    e = tuple(range(n))
    seen = {e}
    dq = deque([e])
    while dq:
        g = dq.popleft()
        for s in gens:
            h = compose(s, g)
            if h not in seen:
                seen.add(h)
                dq.append(h)
    return seen

def transitivity(G, n, t):
    """Number of orbits on ordered distinct t-tuples (1 = t-transitive)."""
    tuples = set(permutations(range(n), t))
    orbits = 0
    while tuples:
        x = next(iter(tuples))
        orb = {tuple(g[i] for i in x) for g in G}
        tuples -= orb
        orbits += 1
    return orbits

def subset_orbits(G, n, k):
    subs = set(frozenset(c) for c in combinations(range(n), k))
    sizes = []
    while subs:
        x = next(iter(subs))
        orb = {frozenset(g[i] for i in x) for g in G}
        subs -= orb
        sizes.append(len(orb))
    return sorted(sizes)

# ---- 12-card deck operations (position i holds card i initially) --------
n = 12
# Reversal of the pile: position i -> n-1-i.
rev = tuple(n - 1 - i for i in range(n))
# Mongean shuffle: take cards from the top of the old pile one at a time;
# the first goes into the hand, the next on TOP, the next UNDER, alternating.
# Old top = position 0. Resulting new pile (top to bottom) for 12 cards:
# 10,8,6,4,2,0,1,3,5,7,9,11  (0-based).
def mongean(n):
    pile = []
    for c in range(n):
        if c == 0:
            pile = [c]
        elif c % 2 == 1:
            pile = [c] + pile      # on top
        else:
            pile = pile + [c]      # under
    # new position j holds old card pile[j]; as a permutation of POSITIONS,
    # old position pile[j] -> new position j.
    p = [0] * n
    for j, c in enumerate(pile):
        p[c] = j
    return tuple(p)
mon = mongean(n)
print("mongean (old pos -> new pos):", mon)
print("new pile top->bottom (old positions):",
      [mon.index(j) for j in range(n)])

G = closure([mon, rev])
print("|<mongean, rev>| on 12 =", len(G))
for t in (4, 5, 6):
    print(f"  orbits on ordered {t}-tuples:", transitivity(G, n, t))
print("  orbits on 6-subsets:", subset_orbits(G, n, 6))
print("  orbits on 5-subsets:", subset_orbits(G, n, 5))

# Perfect (faro) shuffles on 12 for comparison.
def out_shuffle(n):
    h = n // 2
    p = [0] * n
    for i in range(h):
        p[i] = 2 * i
        p[h + i] = 2 * i + 1
    return tuple(p)
def in_shuffle(n):
    h = n // 2
    p = [0] * n
    for i in range(h):
        p[i] = 2 * i + 1
        p[h + i] = 2 * i
    return tuple(p)
H = closure([in_shuffle(n), out_shuffle(n)])
print("|<in, out>| on 12 =", len(H))

# ---- M_11 on 11 points via two generators (ATLAS standard: not needed);
# here derive as point stabiliser of M_12.
M11 = {g for g in G if g[11] == 11}
print("|stab(11)| =", len(M11))
G11 = {g[:11] for g in M11}
for t in (3, 4, 5):
    print(f"  M11 orbits on ordered {t}-tuples:", transitivity(G11, 11, t))
print("  M11 orbits on 5-subsets:", subset_orbits(G11, 11, 5))

# ---- AGL(3,2) on 8 points = F_2^3, comparison at the PGL(2,7) deck size.
n8 = 8
def xor_tr(v):
    return tuple(i ^ v for i in range(n8))
# GL(3,2) generators: two matrices acting on bit-vectors.
def mat_act(M):
    def act(x):
        bits = [(x >> k) & 1 for k in range(3)]
        y = 0
        for r in range(3):
            s = sum(M[r][c] * bits[c] for c in range(3)) % 2
            y |= s << r
        return y
    return tuple(act(x) for x in range(n8))
A = mat_act([[0, 0, 1], [1, 0, 0], [0, 1, 0]])   # cyclic coordinate shift
B = mat_act([[1, 1, 0], [0, 1, 0], [0, 0, 1]])   # transvection
AGL = closure([xor_tr(1), A, B])
print("|AGL(3,2)| =", len(AGL))
for t in (3, 4):
    print(f"  AGL(3,2) orbits on ordered {t}-tuples:", transitivity(AGL, 8, t))
print("  AGL(3,2) orbits on 4-subsets:", subset_orbits(AGL, 8, 4))
