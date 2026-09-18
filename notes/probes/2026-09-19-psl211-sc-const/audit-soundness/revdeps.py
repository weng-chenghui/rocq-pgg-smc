import re, os, sys, collections
REPO="/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc"
dfile=os.path.join(REPO,".Makefile.rocq.d")
txt=open(dfile).read()
txt=txt.replace("\\\n"," ")
# direct deps: target: prereqs
deps=collections.defaultdict(set)
for line in txt.splitlines():
    if ":" not in line: continue
    lhs,rhs=line.split(":",1)
    targets=[t for t in lhs.split() if t.endswith(".vo")]
    prereqs=[p for p in rhs.split() if p.endswith(".vo")]
    for t in targets:
        for p in prereqs:
            if p!=t: deps[t].add(p)
# reverse closure of X = all .vo that transitively depend on X
rev=collections.defaultdict(set)
for t,ps in deps.items():
    for p in ps: rev[p].add(t)
def closure(x):
    seen=set(); stack=[x]
    while stack:
        c=stack.pop()
        for r in rev.get(c,()):
            if r not in seen:
                seen.add(r); stack.append(r)
    return seen
targets=sys.argv[1:]
for x in targets:
    c=closure(x)
    endp = "instances/psl211/psl211_endpoints.vo" in c
    print(f"{x}: {len(c)} reverse-dependants; psl211_endpoints in closure: {endp}")
    for f in sorted(c)[:200]:
        print("   ",f)
