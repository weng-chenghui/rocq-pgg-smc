
# Spot-check: E: y^2 = x^3 - x over GF(9), char 3.
# GF(9) = GF(3)[t]/(t^2 + 1), since -1 = 2 is a non-square mod 3.
# Elements are pairs (a,b) meaning a + b*t, a,b in {0,1,2}. t^2 = -1 = 2.

P = 3

def add(u, v): return ((u[0]+v[0]) % P, (u[1]+v[1]) % P)
def neg(u):    return ((-u[0]) % P, (-u[1]) % P)
def sub(u, v): return add(u, neg(v))
def mul(u, v):
    a, b = u; c, d = v
    # (a+bt)(c+dt) = ac + bd t^2 + (ad+bc) t = (ac + 2bd) + (ad+bc) t
    return ((a*c + 2*b*d) % P, (a*d + b*c) % P)

ZERO = (0, 0)
ONE  = (1, 0)
T    = (0, 1)

ELTS = [(a, b) for a in range(P) for b in range(P)]

def is_zero(u): return u == ZERO

def inv(u):
    for v in ELTS:
        if mul(u, v) == ONE:
            return v
    raise ValueError("no inverse for %r" % (u,))

# ---- curve: y^2 = x^3 - x ----
def rhs(x):
    x3 = mul(mul(x, x), x)
    return sub(x3, x)                      # x^3 - x

def sq(y): return mul(y, y)

# affine points
affine = []
for x in ELTS:
    r = rhs(x)
    for y in ELTS:
        if sq(y) == r:
            affine.append((x, y))
points = affine + ["O"]                    # O = point at infinity
print("GF(9) size:", len(ELTS))
print("#affine points:", len(affine))
print("#E(GF(9)) incl O:", len(points))

# ---- automorphisms fixing O: phi_{u,r}(x,y) = (u^2 x + r, u^3 y), u^4=1, r in GF(3) ----
u4 = [u for u in ELTS if not is_zero(u) and mul(mul(u,u),mul(u,u)) == ONE]   # u^4 = 1
print("4th roots of unity (u^4=1):", u4)
rs = [(a, 0) for a in range(P)]            # r in prime field GF(3)

def make_phi(u, r):
    u2 = mul(u, u); u3 = mul(u2, u)
    def phi(pt):
        if pt == "O": return "O"
        x, y = pt
        return (add(mul(u2, x), r), mul(u3, y))
    return phi, (u, r)

autos = [make_phi(u, r) for u in u4 for r in rs]
print("#automorphisms fixing O:", len(autos))

# sanity: each auto maps E -> E (permutes the point set) and fixes O
ptset = set(points)
for phi, tag in autos:
    img = set(phi(pt) for pt in points)
    assert img == ptset, ("not a permutation", tag)
    assert phi("O") == "O"
print("all autos permute E and fix O: OK")

# ---- group structure check: non-abelian, unique involution (=> non-dihedral, dicyclic) ----
# represent each auto as a permutation tuple over an indexed point list
idx = {pt: i for i, pt in enumerate(points)}
def as_perm(phi): return tuple(idx[phi(pt)] for pt in points)
perms = {tag: as_perm(phi) for phi, tag in autos}
plist = list(perms.values())

def compose(p, q):   # (p o q)(i) = p[q[i]]
    return tuple(p[q[i]] for i in range(len(p)))
identity = tuple(range(len(points)))

# closure / order
G = set(plist)
changed = True
while changed:
    changed = False
    for a in list(G):
        for b in list(G):
            c = compose(a, b)
            if c not in G:
                G.add(c); changed = True
print("group order (closure):", len(G))

# abelian?
non_abelian = any(compose(a,b) != compose(b,a) for a in plist for b in plist)
print("non-abelian:", non_abelian)

# count involutions (order exactly 2)
def order(p):
    n = 1; cur = p
    while cur != identity:
        cur = compose(cur, p); n += 1
    return n
involutions = [p for p in G if order(p) == 2]
print("#involutions:", len(involutions), "(Dic_3/dicyclic has 1; D_6 has 7)")

# ---- orbits of the full group on all points ----
def orbit(start):
    seen = {start}; frontier = [start]
    while frontier:
        pt = frontier.pop()
        for phi, _ in autos:
            q = phi(pt)
            if q not in seen:
                seen.add(q); frontier.append(q)
    return seen

remaining = set(points); orbits = []
while remaining:
    s = next(iter(remaining))
    o = orbit(s); orbits.append(o); remaining -= o
orbits.sort(key=len)
print("orbit sizes on all", len(points), "points:", [len(o) for o in orbits])
print("O in singleton orbit?:", any(o == {"O"} for o in orbits))

# ---- candidate AG scheme (genus 1): secret at O, D on one affine orbit, eval = rest ----
# genus g=1 => dim L(D) = deg D for deg D >= 1; gap = 2g = 2.
aff_orbits = [o for o in orbits if "O" not in o]
print("\naffine orbit sizes:", [len(o) for o in aff_orbits])
for i, Dorb in enumerate(aff_orbits):
    supp = len(Dorb)
    eval_pts = [pt for pt in points if pt not in Dorb]      # includes O (secret) + other affine orbits
    n = len(eval_pts)
    # choose deg D = m*supp style: pick smallest deg D giving k>=2 and k<n-2g (room for gap)
    for degD in range(2, n):
        k = degD                    # dim L(D), genus 1
        # AG code length n, dim k, designed distance d >= n - degD; privacy ~ n-degD, recon ~ n-degD+2g
        if 2 <= k <= n-3:
            print(f"D-orbit#{i} |supp|={supp}: n={n}, deg D={degD} => k={k}, gap=2, "
                  f"T~{n-degD+2} vs priv~{n-degD}  (secret=O fixed by all 12 autos)")
            break
