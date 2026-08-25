
# Worked example: [13,3] functional AG code C_L(D) on E: y^2 = x^3 - x over GF(9),
# with Dic_3 = Stab(T0) recon-symmetry fixing the secret T0=(0,0). Everything computed.

P = 3
def add(u,v): return ((u[0]+v[0])%P,(u[1]+v[1])%P)
def neg(u):   return ((-u[0])%P,(-u[1])%P)
def sub(u,v): return add(u,neg(v))
def mul(u,v):
    a,b=u; c,d=v
    return ((a*c+2*b*d)%P,(a*d+b*c)%P)   # w^2 = -1 = 2
ZERO=(0,0); ONE=(1,0); W=(0,1)
ELTS=[(a,b) for a in range(P) for b in range(P)]
def is0(u): return u==ZERO
def inv(u):
    for v in ELTS:
        if mul(u,v)==ONE: return v
    raise ValueError(u)
def pretty(u):
    a,b=u
    if b==0: return str(a)
    base = ("" if a==0 else str(a)+"+") + ("w" if b==1 else str(b)+"w")
    return base
def rhs(x): return sub(mul(mul(x,x),x),x)
def sq(y): return mul(y,y)

affine=[(x,y) for x in ELTS for y in ELTS if sq(y)==rhs(x)]
points=affine+["O"]
T0=(ZERO,ZERO); T1=(ONE,ZERO); T2=((2,0),ZERO)
assert T0 in affine and T1 in affine and T2 in affine
print("#points:",len(points),"  T0,T1,T2 on curve:",T0 in affine,T1 in affine,T2 in affine)

# automorphisms fixing O
u4=[u for u in ELTS if not is0(u) and mul(mul(u,u),mul(u,u))==ONE]
def make_phi(u,r):
    u2=mul(u,u); u3=mul(u2,u)
    def phi(pt):
        if pt=="O": return "O"
        x,y=pt; return (add(mul(u2,x),r), mul(u3,y))
    return phi
autosO=[make_phi(u,r) for u in u4 for r in [(a,0) for a in range(P)]]

# EC group law (to build Stab(T0))
A=neg(ONE)
def ecadd(Pp,Qp):
    if Pp=="O": return Qp
    if Qp=="O": return Pp
    x1,y1=Pp; x2,y2=Qp
    if x1==x2 and add(y1,y2)==ZERO: return "O"
    if Pp==Qp:
        lam=mul(A,inv(mul((2,0),y1)))
    else:
        lam=mul(sub(y2,y1),inv(sub(x2,x1)))
    x3=sub(sub(mul(lam,lam),x1),x2); y3=sub(mul(lam,sub(x1,x3)),y1)
    return (x3,y3)
def ecneg(Pp):
    if Pp=="O": return "O"
    x,y=Pp; return (x,neg(y))

# Stab(T0) = { tau_{T0 - phi(T0)} o phi : phi in Aut(E,O) }, fixes T0
def stab(P0):
    els=[]
    for phi in autosO:
        Q=ecadd(P0, ecneg(phi(P0)))
        g=lambda pt,phi=phi,Q=Q: ecadd(phi(pt),Q)
        assert g(P0)==P0
        els.append(g)
    return els
G_stab=stab(T0)

# orbits of Stab(T0)
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
orbs=orbits(G_stab)
print("Stab(T0) orbit sizes:",[len(o) for o in orbs])
orb3=[o for o in orbs if len(o)==3][0]; orb12=[o for o in orbs if len(o)==12][0]
print("size-3 orbit (= D support):",sorted([("O" if p=="O" else "("+pretty(p[0])+","+pretty(p[1])+")") for p in orb3]))
print("O in size-3 orbit:", "O" in orb3, " T1,T2 in it:", T1 in orb3, T2 in orb3)

# ---- evaluation points: T0 first (secret, position 0), then the 12-orbit ----
evalpts=[T0]+[p for p in orb12]   # 13 points, all affine
assert "O" not in evalpts and T1 not in evalpts and T2 not in evalpts
n=len(evalpts); print("n (eval points):",n)

# ---- basis of L(D): h0=1, h1=y/(x-1), h2=y/(x^2-1) ----
def h0(pt): return ONE
def h1(pt):
    x,y=pt; return mul(y, inv(sub(x,ONE)))
def h2(pt):
    x,y=pt; return mul(y, inv(sub(mul(x,x),ONE)))
basis=[h0,h1,h2]; k=len(basis)

# generator matrix G: k x n over GF(9)
Gm=[[h(pt) for pt in evalpts] for h in basis]
print("\ngenerator matrix G (rows h0,h1,h2; columns = eval points, col 0 = secret T0):")
for r,row in enumerate(Gm):
    print("  h%d:"%r,[pretty(v) for v in row])
print("column 0 (secret T0) =",[pretty(Gm[r][0]) for r in range(k)], "-> secret reads constant coeff")

# ---- GF(9) linear algebra ----
def vsub(a,b): return tuple(sub(a[i],b[i]) for i in range(len(a)))
def vscale(c,a): return tuple(mul(c,x) for x in a)
def rowspace(vecs):
    basis_=[]
    for v in vecs:
        w=list(v)
        for b in basis_:
            # find pivot of b
            piv=next(i for i in range(len(b)) if b[i]!=ZERO)
            if w[piv]!=ZERO:
                c=mul(w[piv],inv(b[piv]))
                w=[sub(w[i],mul(c,b[i])) for i in range(len(w))]
        if any(x!=ZERO for x in w):
            basis_.append(w)
    return basis_
def in_span(v,vecs):
    b=rowspace(vecs);
    b2=rowspace(vecs+[list(v)])
    return len(b2)==len(b)
def rank(vecs): return len(rowspace([list(v) for v in vecs]))

cols=[tuple(Gm[r][j] for r in range(k)) for j in range(n)]   # column vectors in GF(9)^3
print("\nrank G =",rank(cols),"(expect 3)")

# ---- minimum distance of C = rowspace(G): enumerate 9^3 messages ----
def codeword(m): return [ sub(sub(mul(m[0],Gm[0][j]),neg(mul(m[1],Gm[1][j]))), neg(mul(m[2],Gm[2][j]))) for j in range(n)]
def wt(c): return sum(1 for v in c if v!=ZERO)
mind=n+1
for m in [(a,b,c) for a in ELTS for b in ELTS for c in ELTS if (a,b,c)!=(ZERO,ZERO,ZERO)]:
    mind=min(mind,wt(codeword(m)))
print("min distance d(C) =",mind,"  => reconstruction-ish n-d+1 =",n-mind+1)

# ---- dual distance d^perp = min # of dependent columns of G ----
from itertools import combinations
dperp=None
for size in range(1,k+2):
    found=False
    for S in combinations(range(n),size):
        if rank([cols[j] for j in S])<size:
            found=True; break
    if found: dperp=size; break
print("dual distance d^perp =",dperp,"  => privacy threshold d^perp - 2 =",dperp-2)

# ---- Massey secret sharing: secret at position 0 ----
g0=cols[0]
# thresholds over the 12 SHARE coordinates (indices 1..n-1)
shareidx=list(range(1,n))
def qualified(A): return in_span(g0,[cols[j] for j in A])
# privacy threshold t = max size with ALL |A|=t unqualified
# reconstruction r = min size with ALL |A|=r qualified
t_priv=0
for size in range(0,len(shareidx)+1):
    if all(not qualified(A) for A in combinations(shareidx,size)):
        t_priv=size
    else: break
r_rec=len(shareidx)+1
for size in range(len(shareidx),-1,-1):
    if all(qualified(A) for A in combinations(shareidx,size)):
        r_rec=size
    else: break
print("\nMassey thresholds over 12 shares: privacy t =",t_priv," reconstruction r =",r_rec," gap =",r_rec-t_priv-1,"(2g=2 region)")

# ---- concrete deal + recover ----
secret=W                       # secret s = w  (a nontrivial GF(9) element)
m=(secret,(2,0),ONE)           # m0=secret, m1=2, m2=1  (dealer randomness m1,m2)
c=codeword(m)
print("\nsecret s =",pretty(secret))
print("codeword c =",[pretty(v) for v in c])
print("c[0] (secret coord) =",pretty(c[0]),"  == s?",c[0]==secret)
shares={j:c[j] for j in shareidx}
# a qualified coalition: smallest set whose columns span g0
qcoal=None
for size in range(1,len(shareidx)+1):
    for A in combinations(shareidx,size):
        if qualified(A): qcoal=A;break
    if qcoal: break
# solve sum lam_j g_j = g0
def solve_combo(A):
    # find lam over GF(9) with sum lam_j cols[j] = g0
    import itertools
    # brute force small: |A| up to ~ small
    for lam in itertools.product(ELTS,repeat=len(A)):
        acc=(ZERO,ZERO,ZERO)
        for idx,j in enumerate(A):
            acc=tuple(add(acc[t],mul(lam[idx],cols[j][t])) for t in range(3))
        if acc==g0: return lam
    return None
lam=solve_combo(qcoal)
rec=(ZERO)
acc=ZERO
for idx,j in enumerate(qcoal):
    acc=add(acc,mul(lam[idx],shares[j]))
print("qualified coalition (share indices):",qcoal," size",len(qcoal))
print("  recovered s = sum lam_j*share_j =",pretty(acc)," == s?",acc==secret)
# an unqualified coalition of size t_priv
uncoal=next(A for A in combinations(shareidx,t_priv) if not qualified(A)) if t_priv>0 else ()
print("unqualified coalition of size",t_priv,":",uncoal," qualified?",qualified(uncoal))

# ---- verify Dic_3 permutes the 13 columns, fixes col 0, preserves the code ----
idx={pt:i for i,pt in enumerate(evalpts)}
def is_group_abelian(els):
    perms=[tuple(idx[g(p)] for p in evalpts) for g in els]
    return all(tuple(a[b[i]] for i in range(n))==tuple(b[a[i]] for i in range(n)) for a in perms for b in perms)
ok_perm=True; ok_fix0=True; ok_code=True
Crows=[list(Gm[r]) for r in range(k)]
for g in G_stab:
    # induced permutation on eval indices
    try:
        pi=[idx[g(p)] for p in evalpts]
    except KeyError:
        ok_perm=False; continue
    if sorted(pi)!=list(range(n)): ok_perm=False
    if pi[0]!=0: ok_fix0=False
    # permuted generator: column j -> position pi[j]; check rows still in rowspace(G)
    Gp=[[None]*n for _ in range(k)]
    for j in range(n):
        for r in range(k): Gp[r][pi[j]]=Gm[r][j]
    if any(not in_span(tuple(Gp[r]),[tuple(row) for row in Crows]) for r in range(k)): ok_code=False
print("\nDic_3 action: permutes 13 columns:",ok_perm," fixes column 0 (secret):",ok_fix0,
      " preserves code (pure permutation):",ok_code)
print("Dic_3 abelian?",is_group_abelian(G_stab),"(expect False)")
