"""Design-strength census: privacy threshold without transitivity.

Under the all-decks dealer, a coalition C's view law depends on the secret only
through the law of H ∩ C, H the heart set drawn uniformly from its orbit. If
the orbit is a t-design, the number of blocks meeting C in a given A ⊆ C
(|C| <= t) is fixed by (v, h, t, b), so two orbits of the same block size h
that are both t-designs give identical view laws for every coalition of size
<= t. Privacy threshold of a secret pair = min design strength of the pair.
"""
exec(open('small_candidates.py').read().split('L = 200')[0])
from itertools import combinations
import math
def out_shuffle(m):
    h=m//2; p=[0]*m
    for i in range(h): p[i]=2*i; p[h+i]=2*i+1
    return tuple(p)
def in_shuffle(m):
    h=m//2; p=[0]*m
    for i in range(h): p[i]=2*i+1; p[h+i]=2*i
    return tuple(p)
def mongean(m):
    pile=[]
    for c in range(m):
        if c==0: pile=[c]
        elif c%2==1: pile=[c]+pile
        else: pile=pile+[c]
    p=[0]*m
    for j,c in enumerate(pile): p[c]=j
    return tuple(p)
def rev(m): return tuple(m-1-i for i in range(m))
def cut(m): return tuple((i+1)%m for i in range(m))
def cyc(n,*cs):
    p=list(range(n))
    for c in cs:
        for i in range(len(c)): p[c[i]]=c[(i+1)%len(c)]
    return tuple(p)
def strength(blocks, v):
    """largest t such that every t-subset of range(v) lies in the same number of blocks"""
    h=len(next(iter(blocks)))
    best=0
    for t in range(1,h+1):
        cnt={}
        for B in blocks:
            for S in combinations(sorted(B),t): cnt[S]=cnt.get(S,0)+1
        vals=set(cnt.values())
        if len(cnt)==math.comb(v,t) and len(vals)==1: best=t
        else: break
    return best
def closure_guard(gens, cap=200000):
    n=len(gens[0]); e=tuple(range(n)); seen={e}; dq=deque([e])
    while dq:
        g=dq.popleft()
        for s_ in gens:
            h=compose(s_,g)
            if h not in seen:
                seen.add(h); dq.append(h)
                if len(seen)>cap: return None
    return seen
def census(name, gens, n, hs, max_orbits=12):
    G=closure_guard(gens)
    if G is None:
        print(f"\n{name}: |G| > 200000, skipped"); return None
    t=1; t=1
    while t<n and n_orbits_tuples(G,n,t+1)==1: t+=1
    rows=[]
    for h in hs:
        subs=set(frozenset(c) for c in combinations(range(n),h)); orbs=[]
        while subs:
            x=next(iter(subs)); orb={frozenset(g[i] for i in x) for g in G}; subs-=orb; orbs.append(orb)
        st=sorted(((strength(o,n),len(o)) for o in orbs), reverse=True)
        # best secret pair: two orbits with the largest min strength
        best=None
        for i in range(len(st)):
            for j in range(i+1,len(st)):
                k=min(st[i][0],st[j][0])
                if best is None or k>best[0]: best=(k,st[i][1],st[j][1])
        rows.append((h,len(orbs),st[:max_orbits],best))
    print(f"\n{name}: |G|={len(G)}, tuple-transitivity t={t}")
    for h,no,st,best in rows:
        print(f"  h={h}: {no} orbits on {h}-subsets; (strength,size) top={st}; best secret pair -> privacy k={best[0] if best else None} sizes={best[1:] if best else None}")
    return G
n8=8
census("cyclic C_7 (one cut)", [cut(7)], 7, [3])
census("dihedral D_7 (cut + reverse)", [cut(7),rev(7)], 7, [3])
census("cyclic C_11", [cut(11)], 11, [5])
census("faro <I,O> on 8", [in_shuffle(8),out_shuffle(8)], 8, [4])
census("faro <I,O> on 10", [in_shuffle(10),out_shuffle(10)], 10, [5])
census("faro <I,O> on 12", [in_shuffle(12),out_shuffle(12)], 12, [6])
census("Monge <u,z> on 8", [mongean(8),rev(8)], 8, [4])
#census("Monge <u,z> on 9", [mongean(9),rev(9)], 9, [4])
#census("Monge <u,z> on 11", [mongean(11),rev(11)], 11, [5])
census("faro+swap = AGL(3,2) on 8", [in_shuffle(8),out_shuffle(8),(0,1,2,3,5,4,7,6)], 8, [4])
def psl2_gens(p, sq):
    inf=p
    tr=tuple([(z+1)%p for z in range(p)]+[inf]); sc=tuple([(sq*z)%p for z in range(p)]+[inf])
    def inv(z):
        if z==inf: return 0
        if z==0: return inf
        return (-pow(z,p-2,p))%p
    return [tr,sc,tuple(inv(z) for z in range(p+1))]
census("PSL(2,7) on 8", psl2_gens(7,2), 8, [4])
census("PGL(2,7) on 8", pgl2_gens(7,3), 8, [4])
census("PSL(2,11) on 12", psl2_gens(11,3), 12, [4,6])
# AGammaL(1,8): x+1, x*alpha, x^2 on F_8 (alpha root of x^3+x+1)
def mulx(i):
    j=i<<1
    if j&8: j^=0b1011
    return j
def f8_mul(a,b):
    r=0
    for k in range(3):
        if (b>>k)&1: r^=a
        a=mulx(a)
    return r
census("AGammaL(1,8) on 8 (cut-7 + pair swaps + Frobenius)", [tuple(i^1 for i in range(8)), tuple(mulx(i) for i in range(8)), tuple(f8_mul(i,i) for i in range(8))], 8, [4])
census("M11 on 11", [cyc(11,tuple(range(11))), cyc(11,(2,6,10,7),(3,9,4,5))], 11, [5])
