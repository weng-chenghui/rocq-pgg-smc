"""Section 3 of the spec: r4 and m6 inside M12, and which of the two
PSL(2,11) Steiner systems is the M12 hexad system."""
import re, itertools
from pathlib import Path

src = (Path(__file__).resolve().parent.parent / "psl211_tables.v").read_text()
def parse_perm(name):
    m = re.search(name + r"\s*:\s*seq nat\s*:=\s*\[::([^\]]*)\]", src)
    return tuple(int(x) for x in m.group(1).replace(";", " ").split())
def parse_table(name):
    m = re.search(name + r"\s*:\s*seq \(seq nat\)\s*:=\s*\[::(.*?)\]\]\.", src, re.S)
    rows = re.findall(r"\[::([^\]]*)\]", m.group(1) + "]")
    return [tuple(int(x) for x in r.replace(";", " ").split()) for r in rows]
r4, m6 = parse_perm("r4_tbl"), parse_perm("m6_tbl")
tblA, tblB = parse_table("tblA"), parse_table("tblB")
n = 12; e = tuple(range(n))
def comp(p, q): return tuple(p[q[x]] for x in range(n))
def closure(gens):
    S = {e}; fr = [e]
    while fr:
        nf = []
        for g in fr:
            for s in gens:
                h = comp(s, g)
                if h not in S: S.add(h); nf.append(h)
        fr = nf
    return S

# Monge ("mongean") up shuffle on 12 and the whole-pile reversal, as in
# m12_check.py, the generators of M12.
def mongean(m):
    pile = []
    for c in range(m):
        if c == 0: pile = [c]
        elif c % 2 == 1: pile = [c] + pile
        else: pile = pile + [c]
    p = [0] * m
    for j, c in enumerate(pile): p[c] = j
    return tuple(p)
u = mongean(12)
z = tuple(range(11, -1, -1))
M12 = closure([u, z])
print("|M12| =", len(M12))
print("r4 in M12:", r4 in M12, "   m6 in M12:", m6 in M12)
G = closure([r4, m6])
print("|<r4,m6>| =", len(G), "   <r4,m6> subset M12:", G <= M12)

A = {frozenset(b) for b in tblA}; B = {frozenset(b) for b in tblB}
for name, blocks, rep in (("tblA", A, frozenset({2, 3, 5, 7, 8, 9})),
                          ("tblB", B, frozenset({0, 1, 3, 7, 10, 11}))):
    print(f"{name}: spec representative {sorted(rep)} is a block:", rep in blocks)
    orb = {frozenset(g[i] for i in rep) for g in M12}
    print(f"   M12-orbit of it has {len(orb)} blocks; equals {name}:", orb == blocks)

# PGL(2,11) exchanges the two systems?  Use the spec's relabelling pi.
pi = (0, 5, 11, 9, 6, 2, 8, 7, 4, 1, 10, 3)
p, inf = 11, 11
def mob(f): return tuple(f(z) for z in range(12))
tr = mob(lambda z: (z + 1) % p if z != inf else inf)
sc3 = mob(lambda z: (3 * z) % p if z != inf else inf)
def invz(z):
    if z == inf: return 0
    if z == 0: return inf
    return (-pow(z, p - 2, p)) % p
PSL = closure([tr, sc3, mob(invz)])
sc2 = mob(lambda z: (2 * z) % p if z != inf else inf)
print("|PSL(2,11)| =", len(PSL), "  2 is a non-residue mod 11:",
      2 not in {(x * x) % 11 for x in range(1, 11)})
pinv = [0] * 12
for i, j in enumerate(pi): pinv[j] = i
pinv = tuple(pinv)
# transport tblA, tblB to P^1(F_11) labels
SA = {frozenset(pi[i] for i in b) for b in A}
SB = {frozenset(pi[i] for i in b) for b in B}
print("pi conjugates <r4,m6> onto PSL(2,11):",
      {comp(pi, comp(g, pinv)) for g in G} == PSL)
print("z -> 2z maps the A-system onto the B-system:",
      {frozenset(sc2[i] for i in b) for b in SA} == SB)
print("the Carmichael block {inf,1,3,4,5,9} lies in:",
      "A" if frozenset({inf, 1, 3, 4, 5, 9}) in SA else
      ("B" if frozenset({inf, 1, 3, 4, 5, 9}) in SB else "neither"))
