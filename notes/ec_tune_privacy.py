
# Same curve E:y^2=x^3-x/GF(9), same group Dic_3=Stab(T0), same 13 eval points.
# Vary ONLY the divisor: D_m = m*(O+T1+T2), deg 3m, code C_L(D_m) = L(D)^m (D deg 3 = 2g+1
# is projectively normal, so products of the L(D) basis span L(mD)). Show privacy t moves.

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
def orbits(els):
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
orb12=[o for o in orbits(Gs) if len(o)==12][0]
evalpts=[T0]+list(orb12); n=len(evalpts)

# L(D) basis values at eval points
def uu(pt): x,y=pt; return mul(y,inv(sub(x,ONE)))          # y/(x-1)
def vv(pt): x,y=pt; return mul(y,inv(sub(mul(x,x),ONE)))   # y/(x^2-1)
one=[ONE]*n; U=[uu(pt) for pt in evalpts]; V=[vv(pt) for pt in evalpts]

def vecmul(a,b): return [mul(a[i],b[i]) for i in range(n)]

# monomial bases for L(mD) = span of products of {1,U,V} of total degree <= m ... actually
# L(mD) basis = { U^i V^j : i+j <= m } has (m+1)(m+2)/2 elts; keep an independent set of size 3m.
def basis_for(m):
    mons=[]
    for i in range(m+1):
        for j in range(m+1-i):
            # U^i V^j
            w=one[:]
            for _ in range(i): w=vecmul(w,U)
            for _ in range(j): w=vecmul(w,V)
            mons.append(w)
    return mons

# GF(9) rank / span
def rank(vecs):
    b=[]
    for v in vecs:
        w=list(v)
        for r in b:
            piv=next(i for i in range(len(r)) if r[i]!=ZERO)
            if w[piv]!=ZERO:
                c=mul(w[piv],inv(r[piv])); w=[sub(w[i],mul(c,r[i])) for i in range(len(w))]
        if any(x!=ZERO for x in w): b.append(w)
    return b
def reduce_to_basis(vecs):
    b=rank(vecs); return b

from itertools import combinations
def profile(rows):
    k=len(rows)
    cols=[tuple(rows[r][j] for r in range(k)) for j in range(n)]
    g0=cols[0]
    def rk(vs): return len(rank([list(v) for v in vs]))
    def qual(A):
        base=[cols[j] for j in A]; return rk(base+[g0])==rk(base)
    shares=list(range(1,n))
    prof={}
    tpriv=0; rrec=len(shares)+1
    for size in range(0,len(shares)+1):
        tot=rec=0
        for Aset in combinations(shares,size):
            tot+=1
            if qual(Aset): rec+=1
        prof[size]=(tot,rec,tot-rec)
    # thresholds
    for size in range(0,len(shares)+1):
        if prof[size][2]==prof[size][0]: tpriv=size
        else: break
    for size in range(len(shares),-1,-1):
        if prof[size][1]==prof[size][0]: rrec=size
        else: break
    return k,prof,tpriv,rrec

for m in (1,2,3):
    mons=basis_for(m)
    B=reduce_to_basis(mons)          # basis of L(mD)
    k,prof,t,r=profile(B)
    print(f"\n=== divisor D_{m} = {m}*(O+T1+T2), deg {3*m}: code [n=13, k={k}] ===")
    print(f"  dim L({m}D) = {k} (expect {3*m if 3*m< n else 'n/a'})")
    print(f"  privacy t = {t}, reconstruction r = {r}, gap = {r-t-1} (= 2g = 2)")
    row=" ".join(f"{s}:{prof[s][1]}/{prof[s][0]}" for s in range(1,min(6,n)))
    print(f"  size:recon/total  {row} ...")
print("\nSame curve, same Dic_3, same 13 points throughout; only the divisor changed.")
