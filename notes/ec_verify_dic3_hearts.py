
# Run the shuffle-matters verification template on a Dic_3 hearts candidate.
# Tuple:
#   G       = Dic_3 (order 12), acting regularly on Omega = 12 positions
#   deck M  = 3 hearts, 9 clubs (composition-blind)
#   S       = {0,1}
#   E(1)    = hearts on a rotation triple (a C_3-orbit)   [analog of "consecutive"]
#   E(0)    = hearts on a generic (non-rotation) triple, same 3-heart composition
#   shuffle = uniform g in Dic_3
#   R(set)  = 1 if heart-set is a rotation triple (C_3-orbit) else 0   [Dic_3-invariant]
from itertools import combinations

# ---- build Dic_3 = Stab(T0) on E:y^2=x^3-x/GF(9), restricted to the 12-orbit ----
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
orb12=sorted([o for o in orbits_pts(Gs) if len(o)==12][0], key=str)
idx={pt:i for i,pt in enumerate(orb12)}          # positions 0..11
N=12
# induced permutations of Dic_3 on the 12 positions
perms=[tuple(idx[g(pt)] for pt in orb12) for g in Gs]
assert all(sorted(p)==list(range(N)) for p in perms)

def compose(p,q): return tuple(p[q[i]] for i in range(N))
def act_set(g, S): return frozenset(g[i] for i in S)     # image of a position-set under perm g
def cyc_subgroup(g):
    H=[tuple(range(N))]; cur=g
    while cur!=tuple(range(N)):
        H.append(cur); cur=compose(g,cur)
    return H
ID=tuple(range(N))

# order-3 element and its rotation triples (= C_3 orbits)
def order(p):
    k=1; cur=p
    while cur!=ID: cur=compose(p,cur); k+=1
    return k
g3=next(p for p in perms if order(p)==3)
C3=cyc_subgroup(g3)
def orbit_of_point(H,i):
    return frozenset(h[i] for h in H)
rot_triples=set()
for i in range(N): rot_triples.add(orbit_of_point(C3,i))
rot_triples=[sorted(t) for t in rot_triples]        # the 4 rotation triples (partition of 12)

# secret encodings (both 3 hearts): s=1 a rotation triple, s=0 a generic triple
HS1=frozenset(rot_triples[0])                          # rotation triple
HS0=None
for t in combinations(range(N),3):
    if frozenset(t) not in set(map(frozenset,rot_triples)):
        HS0=frozenset(t); break
HEART={1:HS1, 0:HS0}
def is_rot_triple(S): return sorted(S) in rot_triples
def R(hset): return 1 if is_rot_triple(hset) else 0

print("="*70)
print("CANDIDATE: Dic_3 hearts, N=12, deck 3 hearts/9 clubs")
print(f"  rotation triples (C_3 orbits): {rot_triples}")
print(f"  E(1) hearts = {sorted(HS1)}  (rotation triple)")
print(f"  E(0) hearts = {sorted(HS0)}  (generic triple)")
print("="*70)

# ---------- R0 ----------
comp_ok = (len(HS1)==len(HS0)==3)
act_ok  = all(sorted(p)==list(range(N)) for p in perms) and len(perms)==12
print(f"\n[R0] well-formed & composition-blind: action_ok={act_ok}, "
      f"same composition (3 hearts each)={comp_ok}  -> {'PASS' if act_ok and comp_ok else 'FAIL'}")

# ---------- R1 ----------
inv1 = all(R(act_set(g,HS1))==1 for g in perms)
inv0 = all(R(act_set(g,HS0))==0 for g in perms)
print(f"[R1] correct & shuffle-invariant recovery: "
      f"R(g.E(1))==1 all g={inv1}, R(g.E(0))==0 all g={inv0}  -> {'PASS' if inv1 and inv0 else 'FAIL'}")

# ---------- privacy machinery ----------
def view_dist(H, hset, A):
    # distribution over patterns (A ∩ h.hset) as h ranges over H
    from collections import Counter
    c=Counter()
    for h in H:
        img=act_set(h,hset)
        c[frozenset(A)&img]+=1
    return c
def private_at(H, A):                # distributions identical for s=0,1
    return view_dist(H,HEART[1],A)==view_dist(H,HEART[0],A)
def reconstructs_at(H, A):           # supports disjoint -> view always identifies s
    s1=set(view_dist(H,HEART[1],A).keys()); s0=set(view_dist(H,HEART[0],A).keys())
    return s1.isdisjoint(s0)
def privacy_threshold(H):
    k=0
    for m in range(1,N+1):
        if all(private_at(H,set(A)) for A in combinations(range(N),m)): k=m
        else: break
    return k
def recon_threshold(H):
    T=N+1
    for m in range(N,0,-1):
        if all(reconstructs_at(H,set(A)) for A in combinations(range(N),m)): T=m
        else: break
    return T

DIC3=perms
kG=privacy_threshold(DIC3); TG=recon_threshold(DIC3)

# ---------- R2 ----------
# (a) with shuffle: private up to kG (kG>=1)
# (b) without shuffle (H={id}): some |A|<=kG leaks
noshuf=[ID]
b_leak=any(not private_at(noshuf,set(A)) for m in range(1,kG+1) for A in combinations(range(N),m))
r2 = (kG>=1) and b_leak
print(f"[R2] shuffle-sourced privacy: with-shuffle k={kG} (>=1: {kG>=1}); "
      f"without-shuffle leaks at size<=k: {b_leak}  -> {'PASS' if r2 else 'FAIL'}")

# ---------- R3 ----------
r3 = (kG>=1) and (TG<=N) and (kG<TG)
print(f"[R3] genuine (k,T) ramp: k={kG}, T={TG}, N={N}; gray zone sizes {kG+1}..{TG-1}"
      f"  -> {'PASS' if r3 else 'FAIL'}")
# profile
print("     size | all-private | all-reconstruct")
for m in range(1,N+1):
    ap=all(private_at(DIC3,set(A)) for A in combinations(range(N),m))
    ar=all(reconstructs_at(DIC3,set(A)) for A in combinations(range(N),m))
    print(f"     {m:>4} |   {str(ap):>5}     |   {str(ar):>5}")

# ---------- R4 ----------
r4 = (len({0,1})>=2) and (R(HS1)!=R(HS0))
print(f"[R4] non-trivial: |S|=2, read-off non-constant (R(E1)={R(HS1)},R(E0)={R(HS0)})"
      f"  -> {'PASS' if r4 else 'FAIL'}")

# ---------- R5(i): cyclic subgroups ----------
cyc_subs={}
for p in perms:
    H=tuple(sorted(cyc_subgroup(p)))
    cyc_subs[H]=len(H)
print(f"[R5(i)] cyclic-subgroup irreducibility (does any cyclic C match Dic_3 privacy k={kG}?):")
any_match=False
for H,sz in sorted(cyc_subs.items(), key=lambda x:x[1]):
    kC=privacy_threshold(list(H))
    match = kC>=kG
    any_match = any_match or (sz< len(DIC3) and match)
    print(f"        cyclic C order {sz:>2}: privacy k_C={kC}  {'>= k_G  (matches!)' if match else '< k_G'}")
r5i = not any_match
print(f"        -> {'PASS (no cyclic subgroup matches)' if r5i else 'FAIL (a cyclic subgroup matches Dic_3 privacy)'}")

# ---------- R5(ii): cyclic C_12 benchmark (den Boer analog: 3 consecutive on a 12-cycle) ----------
rot12=tuple((i+1)%12 for i in range(12))
C12=cyc_subgroup(rot12)
HS1_c=frozenset({0,1,2})                     # 3 consecutive = "rotation" analog for C_12
HS0_c=frozenset({0,1,3})                     # non-consecutive generic triple
def priv_thr_generic(H,h1,h0):
    def vd(hset,A):
        from collections import Counter
        c=Counter()
        for h in H: c[frozenset(A)&act_set(h,hset)]+=1
        return c
    k=0
    for m in range(1,N+1):
        if all(vd(h1,set(A))==vd(h0,set(A)) for A in combinations(range(N),m)): k=m
        else: break
    return k
def recon_thr_generic(H,h1,h0):
    def sup(hset,A): return set(frozenset(set(A)&act_set(h,hset)) for h in H)
    T=N+1
    for m in range(N,0,-1):
        if all(sup(h1,set(A)).isdisjoint(sup(h0,set(A))) for A in combinations(range(N),m)): T=m
        else: break
    return T
kC12=priv_thr_generic(C12,HS1_c,HS0_c); TC12=recon_thr_generic(C12,HS1_c,HS0_c)
print(f"[R5(ii)] cyclic C_12 benchmark (3-consecutive vs generic on a 12-cycle): "
      f"k={kC12}, T={TC12}")
print(f"         Dic_3 (k,T)=({kG},{TG}) vs C_12 (k,T)=({kC12},{TC12}) -> "
      f"{'Dic_3 beats benchmark' if (kG,N-TG)>(kC12,N-TC12) else 'Dic_3 does NOT beat benchmark'}")

print("\n" + "="*70)
gates=[('R0',act_ok and comp_ok),('R1',inv1 and inv0),('R2',r2),('R3',r3),('R4',r4),('R5i',r5i)]
verdict = all(g for _,g in gates)
print("CERTIFICATE:", " ".join(f"{n}={'P' if v else 'F'}" for n,v in gates))
print("OVERALL:", "PASS (genuine non-cyclic shuffle-matters (k,T))" if verdict
      else "FAIL (rejected at the first F above)")
print("="*70)
