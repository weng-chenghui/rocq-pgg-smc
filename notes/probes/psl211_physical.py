"""PSL(2,11) on twelve cards from two label-free physical operations."""
exec(open('small_candidates.py').read().split('L = 200')[0])
from fractions import Fraction
from collections import Counter, deque
import math
n=12; e=tuple(range(n))
def mongean(m):
    pile=[]
    for c in range(m):
        if c==0: pile=[c]
        elif c%2==1: pile=[c]+pile
        else: pile=pile+[c]
    p=[0]*m
    for j,c in enumerate(pile): p[c]=j
    return tuple(p)
def on_blocks(blocks, local_fn):
    p=list(range(n))
    for blk in blocks:
        loc=local_fn(len(blk))
        for i,j in enumerate(loc): p[blk[i]]=blk[j]
    return tuple(p)
r4=on_blocks([[0,1,2,3],[4,5,6,7],[8,9,10,11]], lambda m:tuple(range(m-1,-1,-1)))
m6=on_blocks([[0,1,2,3,4,5],[6,7,8,9,10,11]], mongean)
def cycles(q):
    seen=set(); out=[]
    for i in range(n):
        if i in seen: continue
        c=[i]; seen.add(i); j=q[i]
        while j!=i: c.append(j); seen.add(j); j=q[j]
        if len(c)>1: out.append(c)
    return out
def order(p):
    q=p; k=1
    while q!=e: q=compose(p,q); k+=1
    return k
print("r4 =",cycles(r4),"order",order(r4)); print("m6 =",cycles(m6),"order",order(m6))
G=closure([r4,m6]); print("|<r4,m6>| =",len(G))
t=1
while n_orbits_tuples(G,n,t+1)==1: t+=1
print("tuple-transitivity:",t)
# 6-subset orbits and their design strengths
subs=set(frozenset(c) for c in combinations(range(n),6)); orbs=[]
while subs:
    x=next(iter(subs)); orb={frozenset(g[i] for i in x) for g in G}; subs-=orb; orbs.append(orb)
def strength(blocks):
    best=0
    for tt in range(1,7):
        cnt=Counter(S for B in blocks for S in combinations(sorted(B),tt))
        if len(cnt)==math.comb(n,tt) and len(set(cnt.values()))==1: best=tt
        else: break
    return best
orbs.sort(key=len)
print("6-subset orbits (size, design strength):",[(len(o),strength(o)) for o in orbs])
A,B=[o for o in orbs if len(o)==132]
HA=min(A,key=sorted); HB=min(B,key=sorted)
print("representative blocks:",sorted(HA),sorted(HB))
# colour-only view, fixed representative + uniform g
def law(H,C):
    c=Counter(frozenset(g[i] for i in H)&C for g in G); return {k:Fraction(v,len(G)) for k,v in c.items()}
for k in range(1,7):
    same=all(law(HA,frozenset(C))==law(HB,frozenset(C)) for C in combinations(range(n),k))
    print(f"  colour view law equal at |C|={k}: {same}")
amb=all(any((X-frozenset(pq))==(Y-frozenset(pq)) for X in A for Y in B) for pq in combinations(range(n),2))
print("10 reveals never determine:",amb)
# permutation isomorphism with PSL(2,11) on P^1(F_11)
p=11; inf=11
tr=tuple([(z+1)%p for z in range(p)]+[inf]); sc=tuple([(3*z)%p for z in range(p)]+[inf])
def inv(z):
    if z==inf: return 0
    if z==0: return inf
    return (-pow(z,p-2,p))%p
PSL=closure([tr,sc,tuple(inv(z) for z in range(12))])
elevens=[g for g in G if order(g)==11]
found=None
for c in elevens[:20]:
    fix=[i for i in range(n) if c[i]==i][0]
    for k in range(1,11):
        ck=e
        for _ in range(k): ck=compose(c,ck)
        for p0 in range(n):
            if p0==fix: continue
            pi=[0]*n; pi[fix]=inf; x=p0
            for i in range(11): pi[x]=i; x=ck[x]
            pi=tuple(pi); pinv=[0]*n
            for i,j in enumerate(pi): pinv[j]=i
            pinv=tuple(pinv)
            img={compose(pi,compose(g,pinv)) for g in G}
            if img==PSL: found=pi; break
        if found: break
    if found: break
print("relabelling pi with pi G pi^-1 = PSL(2,11):", found)
if found:
    pi=found
    print("  image of block A rep:",sorted(pi[i] for i in HA)," image of B rep:",sorted(pi[i] for i in HB))
    squares={inf,1,3,4,5,9}
    SA={frozenset(pi[i] for i in S) for S in A}
    print("  A maps to the Carmichael system (orbit of {inf,1,3,4,5,9}):", frozenset(squares) in SA)
# mixing
Gl=list(G); idx={g:i for i,g in enumerate(Gl)}; N=len(Gl)
for name,alpha in [("{r4, m6, m6^-1}",[r4,m6,inverse(m6)]),("{r4, m6}",[r4,m6])]:
    succ=[[idx[compose(a,g)] for a in alpha] for g in Gl]
    dist=[0.0]*N; dist[idx[e]]=1.0; m=len(alpha); res=None
    for L in range(1,600):
        nd=[0.0]*N
        for i,pp in enumerate(dist):
            if pp:
                w=pp/m
                for j in succ[i]: nd[j]+=w
        dist=nd
        tv=0.5*sum(abs(x-1/N) for x in dist)
        if L in (100,200): print(f"  {name} TV@{L}=2^{math.log2(tv):.1f}")
        if tv<=2**-40: print(f"  {name} L for 2^-40: {L}"); break
# Cayley diameter
d={e:0}; dq=deque([e])
while dq:
    g=dq.popleft()
    for s in (r4,m6,inverse(m6)):
        h=compose(s,g)
        if h not in d: d[h]=d[g]+1; dq.append(h)
print("Cayley diameter {r4,m6,m6^-1}:",max(d.values()))
