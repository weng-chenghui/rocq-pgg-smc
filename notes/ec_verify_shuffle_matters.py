
# Shuffle-matters verification template (corrected R5), run on two candidates:
#   (1) Dic_3 on 12 points  (expected: FAIL at corrected R5, cyclic-grade privacy k=1)
#   (2) A5 = PSL(2,5) on 6 points (expected: k>=2, beats cyclic; a non-solvable candidate)
from itertools import combinations
from collections import Counter

# ============================ generic verifier ============================
def cyc_subgroup(g, N):
    ID=tuple(range(N)); H=[ID]; cur=g
    while cur!=ID: H.append(cur); cur=tuple(g[cur[i]] for i in range(N))
    return H
def act_set(g,S): return frozenset(g[i] for i in S)
def view_dist(H, hset, A):
    c=Counter()
    for h in H: c[frozenset(A)&act_set(h,hset)]+=1
    return c
def private_at(H,HS1,HS0,A): return view_dist(H,HS1,A)==view_dist(H,HS0,A)
def reconstructs_at(H,HS1,HS0,A):
    return set(view_dist(H,HS1,A)).isdisjoint(set(view_dist(H,HS0,A)))
def privacy_threshold(H,HS1,HS0,N):
    k=0
    for m in range(1,N+1):
        if all(private_at(H,HS1,HS0,set(A)) for A in combinations(range(N),m)): k=m
        else: break
    return k
def recon_threshold(H,HS1,HS0,N):
    T=N+1
    for m in range(N,0,-1):
        if all(reconstructs_at(H,HS1,HS0,set(A)) for A in combinations(range(N),m)): T=m
        else: break
    return T

def cyclic_benchmark_k(N, h):
    # single N-cycle, consecutive h-block vs one-gap block (same composition)
    ID=tuple(range(N)); rot=tuple((i+1)%N for i in range(N)); CN=cyc_subgroup(rot,N)
    HS1=frozenset(range(h))                      # consecutive
    HS0=frozenset(list(range(h-1))+[h])          # one gap
    return privacy_threshold(CN,HS1,HS0,N), CN

def verify(name, N, perms, HS1, HS0, is_special, h):
    print("="*72); print(f"CANDIDATE: {name}  (N={N}, |G|={len(perms)})")
    print(f"  E(1) hearts={sorted(HS1)} special={is_special(HS1)}   "
          f"E(0) hearts={sorted(HS0)} special={is_special(HS0)}")
    print("="*72)
    ID=tuple(range(N))
    # R0
    comp=(len(HS1)==len(HS0)==h)
    act=all(sorted(p)==list(range(N)) for p in perms)
    r0=comp and act
    print(f"[R0] well-formed & composition-blind ({h} hearts each): {r0}")
    # R1
    inv1=all(is_special(act_set(g,HS1)) for g in perms)
    inv0=all(not is_special(act_set(g,HS0)) for g in perms)
    r1=inv1 and inv0
    print(f"[R1] correct & shuffle-invariant recovery: {r1}")
    # privacy under full G
    kG=privacy_threshold(perms,HS1,HS0,N); TG=recon_threshold(perms,HS1,HS0,N)
    # R2
    noshuf=[ID]
    bleak=any(not private_at(noshuf,HS1,HS0,set(A))
              for m in range(1,kG+1) for A in combinations(range(N),m))
    r2=(kG>=1) and bleak
    print(f"[R2] shuffle-sourced privacy: k={kG}(>=1:{kG>=1}), leaks w/o shuffle:{bleak} -> {r2}")
    # R3
    r3=(kG>=1) and (TG<=N) and (kG<TG)
    print(f"[R3] genuine ramp: k={kG}, T={TG}, gray {kG+1}..{TG-1} -> {r3}")
    # R4
    r4=(is_special(HS1) and not is_special(HS0))
    print(f"[R4] non-trivial (invariant separates the two secrets): {r4}")
    # R5 corrected: k_G > k_cyclic (equal-N single-cycle benchmark); headline k_G>=2
    kcyc,_=cyclic_benchmark_k(N,h)
    r5=(kG>kcyc)
    # subgroup diagnostic
    subs={}
    for p in perms: subs[tuple(sorted(cyc_subgroup(p,N)))]=len(cyc_subgroup(p,N))
    submax=max((privacy_threshold(list(H),HS1,HS0,N) for H,sz in subs.items() if sz<len(perms)),
               default=0)
    print(f"[R5] non-cyclic: k_G={kG} vs cyclic C_{N} benchmark k={kcyc}  "
          f"(best proper cyclic subgroup k={submax}); headline k_G>=2: {kG>=2}")
    print(f"     decisive k_G>{kcyc}? -> {r5}")
    gates=[('R0',r0),('R1',r1),('R2',r2),('R3',r3),('R4',r4),('R5',r5)]
    ok=all(v for _,v in gates)
    print("CERTIFICATE:", " ".join(f"{n}={'P' if v else 'F'}" for n,v in gates))
    print("OVERALL:", "PASS" if ok else "FAIL",
          "" if ok else "(rejected at first F)")
    print()
    return ok

# ============================ candidate 1: Dic_3 on 12 ============================
P=3
def add(u,v): return ((u[0]+v[0])%P,(u[1]+v[1])%P)
def negc(u):  return ((-u[0])%P,(-u[1])%P)
def subc(u,v):return add(u,negc(v))
def mulc(u,v):
    a,b=u; c,d=v; return ((a*c+2*b*d)%P,(a*d+b*c)%P)
Z=(0,0); I1=(1,0); EL=[(a,b) for a in range(P) for b in range(P)]
def invc(u):
    for v in EL:
        if mulc(u,v)==I1: return v
def rhs(x): return subc(mulc(mulc(x,x),x),x)
aff=[(x,y) for x in EL for y in EL if mulc(y,y)==rhs(x)]
pts=aff+["O"]; T0=(Z,Z)
u4=[u for u in EL if u!=Z and mulc(mulc(u,u),mulc(u,u))==I1]
def mkphi(u,r):
    u2=mulc(u,u); u3=mulc(u2,u)
    def phi(pt):
        if pt=="O": return "O"
        x,y=pt; return (add(mulc(u2,x),r),mulc(u3,y))
    return phi
autos=[mkphi(u,r) for u in u4 for r in [(a,0) for a in range(P)]]
AA=negc(I1)
def eadd(Pp,Qp):
    if Pp=="O": return Qp
    if Qp=="O": return Pp
    x1,y1=Pp; x2,y2=Qp
    if x1==x2 and add(y1,y2)==Z: return "O"
    lam=mulc(AA,invc(mulc((2,0),y1))) if Pp==Qp else mulc(subc(y2,y1),invc(subc(x2,x1)))
    x3=subc(subc(mulc(lam,lam),x1),x2); return (x3,subc(mulc(lam,subc(x1,x3)),y1))
def eneg(Pp): return "O" if Pp=="O" else (Pp[0],negc(Pp[1]))
Gd=[]
for phi in autos:
    Q=eadd(T0,eneg(phi(T0))); Gd.append(lambda pt,phi=phi,Q=Q: eadd(phi(pt),Q))
def orbs(els):
    rem=set(pts); out=[]
    while rem:
        s=next(iter(rem)); seen={s}; fr=[s]
        while fr:
            p=fr.pop()
            for g in els:
                q=g(p)
                if q not in seen: seen.add(q); fr.append(q)
        out.append(seen); rem-=seen
    return sorted(out,key=len)
orb12=sorted([o for o in orbs(Gd) if len(o)==12][0],key=str)
idxd={pt:i for i,pt in enumerate(orb12)}
perms_dic=[tuple(idxd[g(pt)] for pt in orb12) for g in Gd]
def order(p,N):
    k=1; cur=p
    while cur!=tuple(range(N)): cur=tuple(p[cur[i]] for i in range(N)); k+=1
    return k
g3=next(p for p in perms_dic if order(p,12)==3); C3=cyc_subgroup(g3,12)
rot_tri=set(frozenset(h[i] for h in C3) for i in range(12))
HS1d=sorted(next(iter(rot_tri))); HS0d=None
for t in combinations(range(12),3):
    if frozenset(t) not in rot_tri: HS0d=list(t); break
is_rot=lambda S: frozenset(S) in rot_tri
verify("Dic_3 hearts on 12 points", 12, perms_dic,
       frozenset(HS1d), frozenset(HS0d), is_rot, 3)

# ============================ candidate 2: A5 = PSL(2,5) on 6 points ============================
# points 0..4 = F_5, 5 = infinity
def mobius(mat, x):
    a,b,c,d=mat
    if x==5:  # infinity
        return 5 if c%5==0 else (a*pow(c,3,5))%5   # a/c ; 3 = inverse-ish placeholder
    num=(a*x+b)%5; den=(c*x+d)%5
    if den==0: return 5
    return (num*pow(den,3,5))%5   # den^{-1}=den^3 mod5 (since den^4=1)
# fix inverse: in F_5, inverse of z is z^3 (z^4=1). a/c = a*c^3.
def mob(mat,x):
    a,b,c,d=mat
    if x==5:
        return 5 if c%5==0 else (a*pow(c%5,3,5))%5
    num=(a*x+b)%5; den=(c*x+d)%5
    return 5 if den==0 else (num*pow(den,3,5))%5
def perm_of(mat): return tuple(mob(mat,x) for x in range(6))
T=perm_of((1,1,0,1))       # x -> x+1
S=perm_of((0,4,1,0))       # x -> -1/x
def comp(p,q): return tuple(p[q[i]] for i in range(6))
ID6=tuple(range(6)); Gset={ID6}; frontier=[ID6]
gens=[T,S]
while frontier:
    a=frontier.pop()
    for g in gens:
        c=comp(a,g)
        if c not in Gset: Gset.add(c); frontier.append(c)
perms_a5=sorted(Gset)
print(f"[A5 build] |PSL(2,5) on 6 pts| = {len(perms_a5)} (expect 60); "
      f"T={T}, S={S}")
# orbits of 3-subsets under A5
tri=list(combinations(range(6),3)); seen=set(); tri_orbits=[]
for t in tri:
    ft=frozenset(t)
    if ft in seen: continue
    orb=set()
    fr=[ft]
    while fr:
        s=fr.pop()
        if s in orb: continue
        orb.add(s)
        for g in perms_a5: fr.append(act_set(g,s))
    tri_orbits.append(sorted(orb, key=lambda z:sorted(z))); seen|=orb
print(f"[A5] 3-subset orbits: {len(tri_orbits)} orbit(s), sizes {[len(o) for o in tri_orbits]}")
if len(tri_orbits)>=2:
    orb1=set(tri_orbits[0])
    HS1a=next(iter(tri_orbits[0])); HS0a=next(iter(tri_orbits[1]))
    is_orb1=lambda S: frozenset(S) in orb1
    verify("A5=PSL(2,5) hearts on 6 points", 6, perms_a5,
           frozenset(HS1a), frozenset(HS0a), is_orb1, 3)
else:
    print("[A5] triples form a single orbit -> invariant collapses on 6 points; "
          "need a larger (non-2-transitive) A5 action. Not run.")

# ============= candidate 3 (LARGER): PGL(2,7) on 8 points, aim k=3 =============
# points 0..6 = F_7, 7 = infinity.  PGL(2,7) is sharply 3-transitive on 8 points.
def mob7(mat,x):
    a,b,c,d=mat
    if x==7:  # infinity -> a/c
        return 7 if c%7==0 else (a*pow(c%7,5,7))%7   # z^{-1}=z^5 in F_7
    num=(a*x+b)%7; den=(c*x+d)%7
    return 7 if den==0 else (num*pow(den,5,7))%7
def perm7(mat): return tuple(mob7(mat,x) for x in range(8))
def comp8(p,q): return tuple(p[q[i]] for i in range(8))
T7=perm7((1,1,0,1))     # x -> x+1
S7=perm7((0,6,1,0))     # x -> -1/x
D7=perm7((3,0,0,1))     # x -> 3x  (3 is a non-square, lifts PSL to PGL)
ID8=tuple(range(8)); Gp={ID8}; fr8=[ID8]
for g in (T7,S7,D7):
    pass
frontier8=[ID8]
while frontier8:
    a=frontier8.pop()
    for g in (T7,S7,D7):
        c=comp8(a,g)
        if c not in Gp: Gp.add(c); frontier8.append(c)
perms_pgl=sorted(Gp)
print(f"[PGL(2,7) build] |G on 8 pts| = {len(perms_pgl)} (expect 336); "
      f"T={T7}, S={S7}, D={D7}")
# 4-subset orbits (cross-ratio classes)
quad=list(combinations(range(8),4)); seenq=set(); q_orbits=[]
for t in quad:
    ft=frozenset(t)
    if ft in seenq: continue
    orb=set(); frq=[ft]
    while frq:
        s=frq.pop()
        if s in orb: continue
        orb.add(s)
        for g in perms_pgl: frq.append(act_set(g,s))
    q_orbits.append(sorted(orb,key=lambda z:sorted(z))); seenq|=orb
print(f"[PGL(2,7)] 4-subset orbits: {len(q_orbits)} orbit(s), sizes {[len(o) for o in q_orbits]}")
if len(q_orbits)>=2:
    orbA=set(q_orbits[0])
    HS1p=next(iter(q_orbits[0])); HS0p=next(iter(q_orbits[1]))
    is_orbA=lambda S: frozenset(S) in orbA
    verify("PGL(2,7) hearts on 8 points", 8, perms_pgl,
           frozenset(HS1p), frozenset(HS0p), is_orbA, 4)
else:
    print("[PGL(2,7)] 4-subsets a single orbit -> invariant collapses; not run.")
