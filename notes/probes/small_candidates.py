"""Small multiply-transitive candidates that keep the enumerated L=200 walk.

For each candidate: |G|, transitivity degree t, orbit split of (t+1)-subsets,
BFS closure cost proxy (|G|^2 for the seq-based visited list), and the exact
total-variation distance to uniform of the L-step uniform walk on G over the
symmetrized alphabet, computed in floating point on |G| states.
"""
from itertools import combinations, permutations
from collections import deque
from fractions import Fraction
import math

def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))

def inverse(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return tuple(q)

def closure(gens):
    n = len(gens[0]); e = tuple(range(n)); seen = {e}; dq = deque([e])
    while dq:
        g = dq.popleft()
        for s in gens:
            h = compose(s, g)
            if h not in seen:
                seen.add(h); dq.append(h)
    return seen

def n_orbits_tuples(G, n, t):
    tuples = set(permutations(range(n), t)); k = 0
    while tuples:
        x = next(iter(tuples))
        tuples -= {tuple(g[i] for i in x) for g in G}; k += 1
    return k

def subset_orbits(G, n, k):
    subs = set(frozenset(c) for c in combinations(range(n), k)); out = []
    while subs:
        x = next(iter(subs))
        orb = {frozenset(g[i] for i in x) for g in G}
        subs -= orb; out.append(len(orb))
    return sorted(out)

def walk_tv(G, alphabet, L):
    """TV distance between the L-step walk from identity and uniform on G."""
    Gl = list(G); idx = {g: i for i, g in enumerate(Gl)}; N = len(Gl)
    succ = [[idx[compose(a, g)] for a in alphabet] for g in Gl]
    dist = [0.0] * N; dist[idx[tuple(range(len(Gl[0])))]] = 1.0
    m = len(alphabet)
    for _ in range(L):
        nd = [0.0] * N
        for i, p in enumerate(dist):
            if p:
                w = p / m
                for j in succ[i]:
                    nd[j] += w
        dist = nd
    u = 1.0 / N
    return 0.5 * sum(abs(p - u) for p in dist)

def symmetrize(gens):
    out = []
    for g in gens:
        out.append(g)
        gi = inverse(g)
        if gi != g:
            out.append(gi)
    return out

# ---------- projective-line groups PGL(2,p), prime p, on p+1 points ----------
def pgl2_gens(p, primitive_root):
    inf = p
    tr = tuple([(z + 1) % p for z in range(p)] + [inf])
    sc = tuple([(primitive_root * z) % p for z in range(p)] + [inf])
    def inv(z):
        if z == inf: return 0
        if z == 0: return inf
        return (-pow(z, p - 2, p)) % p
    iv = tuple(inv(z) for z in range(p + 1))
    return [tr, sc, iv]

# ---------- AGL(3,2) on F_2^3 = 8 points ----------
def agl32_gens():
    n = 8
    def xor_tr(v): return tuple(i ^ v for i in range(n))
    def mat_act(M):
        def act(x):
            bits = [(x >> k) & 1 for k in range(3)]; y = 0
            for r in range(3):
                y |= (sum(M[r][c] * bits[c] for c in range(3)) % 2) << r
            return y
        return tuple(act(x) for x in range(n))
    A = mat_act([[0, 0, 1], [1, 0, 0], [0, 1, 0]])
    B = mat_act([[1, 1, 0], [0, 1, 0], [0, 0, 1]])
    return [xor_tr(1), xor_tr(2), xor_tr(4), A, B]

# ---------- PGL(2,9) and M10 on P^1(F_9) = 10 points ----------
# F_9 = F_3[i]/(i^2+1); element a+bi encoded as a+3b, 0..8; infinity = 9.
def f9_mul(x, y):
    a, b = x % 3, x // 3; c, d = y % 3, y // 3
    return ((a * c - b * d) % 3) + 3 * ((a * d + b * c) % 3)
def f9_add(x, y):
    return ((x % 3 + y % 3) % 3) + 3 * ((x // 3 + y // 3) % 3)
def f9_neg(x): return ((-x % 3) % 3) + 3 * ((-(x // 3)) % 3)
def f9_inv(x):
    for y in range(9):
        if f9_mul(x, y) == 1: return y
    raise ValueError
def f9_frob(x): return f9_mul(f9_mul(x, x), x)  # x^3

def pgl29_gens():
    inf = 9
    tr = tuple([f9_add(z, 1) for z in range(9)] + [inf])
    # primitive element: 1+i = 4 (order 8)
    sc = tuple([f9_mul(4, z) for z in range(9)] + [inf])
    def inv(z):
        if z == inf: return 0
        if z == 0: return inf
        return f9_neg(f9_inv(z))
    iv = tuple(inv(z) for z in range(10))
    return [tr, sc, iv]

def m10_gens():
    inf = 9
    tr = tuple([f9_add(z, 1) for z in range(9)] + [inf])
    sq = f9_mul(4, 4)  # square of primitive: scaling by a square, in PSL
    sc2 = tuple([f9_mul(sq, z) for z in range(9)] + [inf])
    def inv(z):
        if z == inf: return 0
        if z == 0: return inf
        return f9_neg(f9_inv(z))
    iv = tuple(inv(z) for z in range(10))
    # M10 = PSL(2,9) extended by (Frobenius composed with non-square scaling)
    fs = tuple([f9_mul(4, f9_frob(z)) for z in range(9)] + [inf])
    return [tr, sc2, iv, fs]

# ---------- AGL(2,3) on F_3^2 = 9 points (the SET-game group) ----------
def agl23_gens():
    n = 9
    def tr(v): return tuple(((i % 3 + v % 3) % 3) + 3 * ((i // 3 + v // 3) % 3) for i in range(n))
    def mat(M):
        def act(x):
            a, b = x % 3, x // 3
            return ((M[0][0] * a + M[0][1] * b) % 3) + 3 * ((M[1][0] * a + M[1][1] * b) % 3)
        return tuple(act(x) for x in range(n))
    return [tr(1), tr(3), mat([[0, 1], [1, 0]]), mat([[1, 1], [0, 1]]), mat([[2, 0], [0, 1]])]

L = 200
cands = [
    ("PGL(2,7) on 8  [landed]", pgl2_gens(7, 3), 8),
    ("PGL(2,9) on 10", pgl29_gens(), 10),
    ("M10 on 10", m10_gens(), 10),
    ("PGL(2,11) on 12", pgl2_gens(11, 2), 12),
    ("PGL(2,13) on 14", pgl2_gens(13, 2), 14),
    ("AGL(3,2) on 8", agl32_gens(), 8),
    ("AGL(2,3) on 9", agl23_gens(), 9),
    ("PSL(2,7) on 8", [pgl2_gens(7, 3)[0], tuple([(2 * z) % 7 for z in range(7)] + [7]), pgl2_gens(7, 3)[2]], 8),
]
print(f"{'candidate':26} {'|G|':>6} {'t':>2} {'(t+1)-subset orbits':>28} {'|G|^2':>10} {'letters':>7} {'TV@200':>10} {'log2':>6}")
for name, gens, n in cands:
    G = closure(gens)
    t = 1
    while n_orbits_tuples(G, n, t + 1) == 1:
        t += 1
    split = subset_orbits(G, n, t + 1)
    alpha = symmetrize(gens)
    tv = walk_tv(G, alpha, L)
    print(f"{name:26} {len(G):6d} {t:2d} {str(split):>28} {len(G)**2:10d} {len(alpha):7d} {tv:10.3e} {math.log2(tv) if tv > 0 else float('-inf'):6.1f}")
