"""Pairs of physical 12-card operations generating an order-660 group with two
132-orbits on 6-subsets (the search that found <reverse quarters, Monge halves>).
Pool: contiguous block reversals, cuts, Monge, in/out faro, equal-block swaps,
and the same operation applied to every block of an equal partition. 520 ops."""
from collections import deque
from itertools import combinations
import time
n=12; e=tuple(range(n))
def compose(p,q): return tuple(p[q[i]] for i in range(n))
def mongean(m):
    pile=[]
    for c in range(m):
        if c==0: pile=[c]
        elif c%2==1: pile=[c]+pile
        else: pile=pile+[c]
    p=[0]*m
    for j,c in enumerate(pile): p[c]=j
    return tuple(p)
def out_shuffle(m):
    h=m//2; p=[0]*m
    for i in range(h): p[i]=2*i; p[h+i]=2*i+1
    return tuple(p)
def in_shuffle(m):
    h=m//2; p=[0]*m
    for i in range(h): p[i]=2*i+1; p[h+i]=2*i
    return tuple(p)
def on_blocks(blocks, local_fn):
    p=list(range(n))
    for blk in blocks:
        loc=local_fn(len(blk))
        for i,j in enumerate(loc): p[blk[i]]=blk[j]
    return tuple(p)
pool={}
def add(p,name):
    if p!=e: pool.setdefault(p,name)
for m in range(2,13):
    for a in range(0,13-m):
        blk=[list(range(a,a+m))]
        add(on_blocks(blk,lambda m:tuple(range(m-1,-1,-1))),f"rev[{a}..{a+m-1}]")
        add(on_blocks(blk,mongean),f"monge[{a}..{a+m-1}]")
        if m%2==0:
            add(on_blocks(blk,out_shuffle),f"outfaro[{a}..{a+m-1}]"); add(on_blocks(blk,in_shuffle),f"infaro[{a}..{a+m-1}]")
        for k in range(1,m): add(on_blocks(blk,lambda mm,k=k:tuple((i+k)%mm for i in range(mm))),f"cut{k}[{a}..{a+m-1}]")
for m in (2,3,4,6):
    blocks=[list(range(a,a+m)) for a in range(0,12,m)]
    add(on_blocks(blocks,lambda m:tuple(range(m-1,-1,-1))),f"rev-each-{m}block")
    for k in range(1,m): add(on_blocks(blocks,lambda mm,k=k:tuple((i+k)%mm for i in range(mm))),f"cut{k}-each-{m}block")
    add(on_blocks(blocks,mongean),f"monge-each-{m}block")
for m in (1,2,3,4,6):
    for a in range(0,13-2*m):
        for b in range(a+m,13-m):
            p=list(range(n))
            for i in range(m): p[a+i]=b+i; p[b+i]=a+i
            add(tuple(p),f"swap[{a}..{a+m-1}]<->[{b}..{b+m-1}]")
print("pool size:",len(pool))
def closure_cap(gens,cap=700):
    seen={e}; dq=deque([e])
    while dq:
        g=dq.popleft()
        for s in gens:
            h=compose(s,g)
            if h not in seen:
                seen.add(h); dq.append(h)
                if len(seen)>cap: return None
    return seen
def hexorbits(G):
    subs=set(frozenset(c) for c in combinations(range(n),6)); out=[]
    while subs:
        x=next(iter(subs)); orb={frozenset(g[i] for i in x) for g in G}; subs-=orb; out.append(len(orb))
    return sorted(out,reverse=True)
P=list(pool); t0=time.time(); hits=[]
for i in range(len(P)):
    for j in range(i+1,len(P)):
        G=closure_cap([P[i],P[j]])
        if G and len(G)==660: hits.append((pool[P[i]],pool[P[j]],hexorbits(G)))
print("pairs done in %.0fs; order-660 pairs:"%(time.time()-t0),len(hits))
for h in hits: print("  ",h)
