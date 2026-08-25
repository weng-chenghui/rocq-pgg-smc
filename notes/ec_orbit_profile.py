
# Dic_3-orbit decomposition of coalitions on the 12 shares.
# E : y^2 = x^3 - x over GF(9); Dic_3 = Stab(T0); code C_L(O+T1+T2), [13,3,10].
# For each Dic_3-orbit of k-subsets of the 12 share positions, print orbit size, a
# representative, and whether coalitions in that orbit RECONSTRUCT the secret or learn NOTHING.
from itertools import combinations

P=3
def add(u,v): return ((u[0]+v[0])%P,(u[1]+v[1])%P)
def neg(u):   return ((-u[0])%P,(-u[1])%P)
def sub(u,v): return add(u,neg(v))
def mul(u,v):
    a,b=u; c,d=v; return ((a*c+2*b*d)%P,(a*d+b*c)%P)
ZERO=(0,0); ONE=(1,0)
ELTS=[(a,b) for a in range(P) for b in range(P)]
def is0(u): return u==ZERO
def inv(u):
    for v in ELTS:
        if mul(u,v)==ONE: return v
    raise ValueError(u)
def rhs(x): return sub(mul(mul(x,x),x),x)
def sq(y): return mul(y,y)
affine=[(x,y) for x in ELTS for y in ELTS if sq(y)==rhs(x)]
points=affine+["O"]; T0=(ZERO,ZERO)
u4=[u for u in ELTS if not is0(u) and mul(mul(u,u),mul(u,u))==ONE]
def make_phi(u,r):
    u2=mul(u,u); u3=mul(u2,u)
    def phi(pt):
        if pt=="O": return "O"
        x,y=pt; return (add(mul(u2,x),r),mul(u3,y))
    return phi
autosO=[make_phi(u,r) for u in u4 for r in [(a,0) for a in range(P)]]
A=neg(ONE)
def ecadd(Pp,Qp):
    if Pp=="O": return Qp
    if Qp=="O": return Pp
    x1,y1=Pp; x2,y2=Qp
    if x1==x2 and add(y1,y2)==ZERO: return "O"
    lam=mul(A,inv(mul((2,0),y1))) if Pp==Qp else mul(sub(y2,y1),inv(sub(x2,x1)))
    x3=sub(sub(mul(lam,lam),x1),x2); return (x3,sub(mul(lam,sub(x1,x3)),y1))
def ecneg(Pp): return "O" if Pp=="O" else (Pp[0],neg(Pp[1]))
Gs=[]
for phi in autosO:
    Q=ecadd(T0,ecneg(phi(T0))); Gs.append(lambda pt,phi=phi,Q=Q: ecadd(phi(pt),Q))
def orbits_pts(els):
    rem=set(points); out=[]
    while rem:
        s=next(iter(rem)); seen={s}; fr=[s]
        while fr:
            p=fr.pop()
            for g in els:
                q=g(p)
                if q not in seen: seen.add(q); fr.append(q)
        out.append(seen); rem-=seen
    return sorted(out,key=len)
orb12=[o for o in orbits_pts(Gs) if len(o)==12][0]
evalpts=[T0]+list(orb12); n=len(evalpts)
idx={pt:i for i,pt in enumerate(evalpts)}

# induced permutations on the 13 indices; share positions are 1..12
def as_perm(g): return tuple(idx[g(pt)] for pt in evalpts)
perms=[as_perm(g) for g in Gs]

# generator columns G_j = (1, h1, h2), h1=y/(x-1), h2=y/(x^2-1)
def h1(pt): x,y=pt; return mul(y,inv(sub(x,ONE)))
def h2(pt): x,y=pt; return mul(y,inv(sub(mul(x,x),ONE)))
cols=[(ONE,h1(pt),h2(pt)) for pt in evalpts]
g0=cols[0]  # (1,0,0)

def rank(vs):
    b=[]
    for v in vs:
        w=list(v)
        for r in b:
            piv=next(i for i in range(len(r)) if r[i]!=ZERO)
            if w[piv]!=ZERO:
                c=mul(w[piv],inv(r[piv])); w=[sub(w[i],mul(c,r[i])) for i in range(len(w))]
        if any(x!=ZERO for x in w): b.append(w)
    return len(b)
def reconstructs(Aset):
    base=[cols[j] for j in Aset]
    return rank(base+[g0])==rank(base)   # g0 in span of the chosen columns

def orbit_of(subset):        # Dic_3-orbit of a subset of {1..12}
    seen=set(); fr=[frozenset(subset)]; seen.add(frozenset(subset))
    while fr:
        s=fr.pop()
        for pm in perms:
            t=frozenset(pm[i] for i in s)
            if t not in seen: seen.add(t); fr.append(t)
    return seen

def profile(k):
    shares=list(range(1,n))
    remaining=set(frozenset(c) for c in combinations(shares,k))
    orbits=[]
    while remaining:
        rep=next(iter(remaining))
        orb=orbit_of(rep)
        orbits.append((sorted(rep), len(orb), reconstructs(rep)))
        remaining-=orb
    orbits.sort(key=lambda o:(o[2],o[1]))
    total=sum(o[1] for o in orbits)
    rec=sum(o[1] for o in orbits if o[2])
    print(f"\n=== size {k}: {total} coalitions, {len(orbits)} Dic_3-orbits "
          f"({rec} reconstruct / {total-rec} learn nothing) ===")
    for rep,sz,rc in orbits:
        tag="RECONSTRUCT" if rc else "safe (nothing)"
        print(f"  orbit size {sz:>3}   rep {rep}   -> {tag}")

for k in (1,2,3,4):
    profile(k)
