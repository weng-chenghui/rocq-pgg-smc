# For D_false = identity deck, classify every class-true deck D_true by its
# leakage curve and report the simplest representatives of each curve.
from itertools import permutations
exec(open("encodings.py").read().split("# census sanity check")[0])   # G, cls, reps, views

names = {(48,84,12,0,0): "A", (80,0,0,0,0): "B", (96,72,36,12,0): "C", (48,72,0,0,0): "D"}
Vid = {k: views(tuple(range(8)), S) for k, S in reps.items()}

def cycles(D):                       # cycle type of the position permutation p -> D[p]
    seen, out = set(), []
    for p in range(8):
        if p in seen or D[p] == p: continue
        c, q = [], p
        while q not in seen: seen.add(q); c.append(q); q = D[q]
        out.append(tuple(c))
    return out

best = {}
for D in permutations(range(8)):
    if not cls(D): continue
    prof = tuple(len(Vid[k] & views(D, S)) for k, S in reps.items())
    cyc = cycles(D); cost = sum(len(c) - 1 for c in cyc)     # number of transpositions
    best.setdefault(names[prof], []).append((cost, D, cyc))
for c in "ABCD":
    L = sorted(best[c]); m = L[0][0]
    mins = [x for x in L if x[0] == m]
    print(f"curve {c}: {len(L)} decks of class true; fewest transpositions = {m}; {len(mins)} such decks")
    for cost, D, cyc in mins[:6]:
        hearts = sorted(p for p in range(8) if D[p] < 4)
        print("    D_true =", D, " cycles", cyc, " heart positions", hearts)
