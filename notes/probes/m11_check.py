exec(open('small_candidates.py').read().split('L = 200')[0])
import math, time
n=11
def cyc(*cs):
    p=list(range(n))
    for c in cs:
        for i in range(len(c)): p[c[i]]=c[(i+1)%len(c)]
    return tuple(p)
c11=cyc(tuple(range(11)))
g2=cyc((2,6,10,7),(3,9,4,5))          # GAP generator (3,7,11,8)(4,10,5,6), 0-based
G=closure([c11,g2]); print("|<c11,g2>| =",len(G))
t=1
while n_orbits_tuples(G,n,t+1)==1: t+=1
print("transitivity t =",t," 5-subset orbits:",subset_orbits(G,n,5)," 6-subset orbits:",subset_orbits(G,n,6))
Gset=set(G)
def cycles(p):
    seen=set(); out=[]
    for i in range(n):
        if i in seen: continue
        c=[i]; seen.add(i); j=p[i]
        while j!=i: c.append(j); seen.add(j); j=p[j]
        if len(c)>1: out.append(tuple(c))
    return out
# --- physical operations: which of them lie in M11 (for some placement)? ---
found={}
# reversal of a contiguous block of length m starting at a (cyclic positions)
for m in range(2,12):
    for a in range(11):
        blk=[(a+i)%11 for i in range(m)]
        p=list(range(n))
        for i in range(m): p[blk[i]]=blk[m-1-i]
        if tuple(p) in Gset: found.setdefault(f"reverse block len {m}",[]).append(a)
# cut of a contiguous sub-pile of length m by one (m-cycle on consecutive positions)
for m in range(2,11):
    for a in range(11):
        blk=tuple((a+i)%11 for i in range(m))
        if cyc(blk) in Gset: found.setdefault(f"cut sub-pile len {m}",[]).append(a)
# two disjoint contiguous sub-pile cuts of length 4 (like g2 but contiguous)
for a in range(11):
    for b in range(11):
        A=tuple((a+i)%11 for i in range(4)); B=tuple((b+i)%11 for i in range(4))
        if len(set(A)|set(B))==8 and cyc(A,B) in Gset: found.setdefault("two contiguous 4-cuts",[]).append((a,b))
# swap of two contiguous blocks of length 4 (as a block move)
for a in range(11):
    for b in range(11):
        A=[(a+i)%11 for i in range(4)]; B=[(b+i)%11 for i in range(4)]
        if len(set(A)|set(B))==8:
            p=list(range(n))
            for i in range(4): p[A[i]]=B[i]; p[B[i]]=A[i]
            if tuple(p) in Gset: found.setdefault("swap two 4-blocks",[]).append((a,b))
# Monge up shuffle and faro-like on 11 (odd) for completeness
def mongean(n):
    pile=[]
    for c in range(n):
        if c==0: pile=[c]
        elif c%2==1: pile=[c]+pile
        else: pile=pile+[c]
    p=[0]*n
    for j,c in enumerate(pile): p[c]=j
    return tuple(p)
print("monge in M11:", mongean(11) in Gset)
for k,v in found.items(): print("  IN M11:",k,"placements",v[:6],"..." if len(v)>6 else "")
print("involution cycle types:", sorted({tuple(sorted(len(c) for c in cycles(g))) for g in G if compose(g,g)==tuple(range(n)) and g!=tuple(range(n))}))
print("element orders present:", sorted({ (lambda g: next(k for k in range(1,12) if all(x==y for x,y in zip(__import__('functools').reduce(lambda a,b:compose(a,b),[g]*k),range(n))))) (g) for g in G}))
