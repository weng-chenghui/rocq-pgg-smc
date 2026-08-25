
# Full coalition profile for the [13,3] scheme: for each coalition size, how many
# coalitions reconstruct the secret vs learn nothing. Linear scheme => clean dichotomy
# (full recovery OR zero information; never partial).

P = 3
def add(u,v): return ((u[0]+v[0])%P,(u[1]+v[1])%P)
def neg(u):   return ((-u[0])%P,(-u[1])%P)
def sub(u,v): return add(u,neg(v))
def mul(u,v):
    a,b=u; c,d=v
    return ((a*c+2*b*d)%P,(a*d+b*c)%P)
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
points=affine+["O"]
T0=(ZERO,ZERO)
u4=[u for u in ELTS if not is0(u) and mul(mul(u,u),mul(u,u))==ONE]
def make_phi(u,r):
    u2=mul(u,u); u3=mul(u2,u)
    def phi(pt):
        if pt=="O": return "O"
        x,y=pt; return (add(mul(u2,x),r), mul(u3,y))
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
def ecneg(Pp):
    return "O" if Pp=="O" else (Pp[0],neg(Pp[1]))
Gs=[]
for phi in autosO:
    Q=ecadd(T0,ecneg(phi(T0)))
    Gs.append(lambda pt,phi=phi,Q=Q: ecadd(phi(pt),Q))
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
evalpts=[T0]+list(orb12)
def h0(pt): return ONE
def h1(pt): x,y=pt; return mul(y,inv(sub(x,ONE)))
def h2(pt): x,y=pt; return mul(y,inv(sub(mul(x,x),ONE)))
Gm=[[h(pt) for pt in evalpts] for h in (h0,h1,h2)]
n=len(evalpts)
cols=[tuple(Gm[r][j] for r in range(3)) for j in range(n)]
g0=cols[0]

def rank(vecs):
    b=[]
    for v in vecs:
        w=list(v)
        for r in b:
            piv=next(i for i in range(len(r)) if r[i]!=ZERO)
            if w[piv]!=ZERO:
                c=mul(w[piv],inv(r[piv])); w=[sub(w[i],mul(c,r[i])) for i in range(len(w))]
        if any(x!=ZERO for x in w): b.append(w)
    return len(b)
def qualified(A):  # secret column in span of coalition columns
    base=[cols[j] for j in A]
    return rank(base+[g0])==rank(base)

from itertools import combinations
shareidx=list(range(1,n))   # 12 shares
print("coalition profile over the 12 shares (secret coord excluded):")
print(" size | #coalitions | reconstruct | learn-nothing")
for size in range(0,len(shareidx)+1):
    tot=recon=0
    for Aset in combinations(shareidx,size):
        tot+=1
        if qualified(Aset): recon+=1
    print(f"  {size:2d}  |    {tot:4d}     |   {recon:4d}      |   {tot-recon:4d}")
print("\nGuaranteed private (every coalition of this size learns nothing): sizes 0,1")
print("Mixed (some reconstruct, some do not): the ramp")
print("Guaranteed reconstruct (every coalition of this size recovers): from the first all-recon size up")
