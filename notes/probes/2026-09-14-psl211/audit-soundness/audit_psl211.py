"""Independent soundness audit of the PSL(2,11) twelve-card chirality spec.

Rebuilds the group and both 132-blocks orbits from the generator tables that
psl211_tables.v actually contains (parsed out of that file, not recomputed
from the python generator script), then checks every numerical claim the spec
and the probe statements rest on.  Nothing here imports the spec's own
scratch script, so an error in that script cannot propagate.
"""
import re, sys, math, itertools
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
TABLES = HERE.parent / "psl211_tables.v"

# ---------------------------------------------------------------- parse .v --
src = TABLES.read_text()

def parse_perm(name):
    m = re.search(name + r"\s*:\s*seq nat\s*:=\s*\[::([^\]]*)\]", src)
    return tuple(int(x) for x in m.group(1).replace(";", " ").split())

def parse_table(name):
    m = re.search(name + r"\s*:\s*seq \(seq nat\)\s*:=\s*\[::(.*?)\]\]\.", src, re.S)
    body = m.group(1) + "]"
    rows = re.findall(r"\[::([^\]]*)\]", body)
    return [tuple(int(x) for x in r.replace(";", " ").split()) for r in rows]

r4  = parse_perm("r4_tbl")
m6  = parse_perm("m6_tbl")
m6i = parse_perm("m6i_tbl")
tblA = parse_table("tblA")
tblB = parse_table("tblB")
n = 12
e = tuple(range(n))
def comp(p, q):           # (p o q)(x) = p(q(x))
    return tuple(p[q[x]] for x in range(n))

print("== parsed from psl211_tables.v ==")
print("r4  =", r4)
print("m6  =", m6)
print("m6i =", m6i)
print("len tblA, tblB =", len(tblA), len(tblB))
print("m6 o m6i = id :", comp(m6, m6i) == e, " m6i o m6 = id :", comp(m6i, m6) == e)
print("r4 o r4 = id  :", comp(r4, r4) == e)

# ------------------------------------------------------------------ group --
G = {e}
frontier = [e]
while frontier:
    nf = []
    for g in frontier:
        for s in (r4, m6):
            h = comp(s, g)
            if h not in G:
                G.add(h); nf.append(h)
    frontier = nf
G = sorted(G)
print("|G| =", len(G))

def ntrans(t):
    """number of orbits on ordered t-tuples of distinct points"""
    tups = set(itertools.permutations(range(n), t))
    k = 0
    while tups:
        x = next(iter(tups))
        orb = {tuple(g[i] for i in x) for g in G}
        tups -= orb; k += 1
    return k
print("orbits on ordered pairs / triples:", ntrans(2), ntrans(3))

# -------------------------------------------------------------- the orbits --
A = {frozenset(b) for b in tblA}
B = {frozenset(b) for b in tblB}
print("tblA rows distinct:", len(A) == len(tblA), " tblB rows distinct:", len(B) == len(tblB))
print("tblA, tblB disjoint:", not (A & B))
HA, HB = frozenset(tblA[0]), frozenset(tblB[0])
orbA = {frozenset(g[i] for i in HA) for g in G}
orbB = {frozenset(g[i] for i in HB) for g in G}
print("orbit(tblA[0]) == set(tblA):", orbA == A, " size", len(orbA))
print("orbit(tblB[0]) == set(tblB):", orbB == B, " size", len(orbB))
print("G-stable: A ->A", all(frozenset(g[i] for i in b) in A for g in G for b in A))
print("G-stable: B ->B", all(frozenset(g[i] for i in b) in B for g in G for b in B))

def strength(blocks):
    best = 0
    for t in range(1, 7):
        cnt = Counter(S for Bk in blocks for S in itertools.combinations(sorted(Bk), t))
        if len(cnt) == math.comb(n, t) and len(set(cnt.values())) == 1:
            best = t
        else:
            break
    return best
print("design strength A, B:", strength(A), strength(B))
for t in range(1, 6):
    la = Counter(S for Bk in A for S in itertools.combinations(sorted(Bk), t))
    lb = Counter(S for Bk in B for S in itertools.combinations(sorted(Bk), t))
    print(f"  lambda_{t}: A {set(la.values())}  B {set(lb.values())}")

# stabiliser orders (orbit-stabiliser: the fibre over a block is a coset)
stabA = sum(1 for g in G if frozenset(g[i] for i in HA) == HA)
stabB = sum(1 for g in G if frozenset(g[i] for i in HB) == HB)
print("stabiliser orders:", stabA, stabB, " |G|/|orbit| =", len(G)//len(orbA), len(G)//len(orbB))
fibA = Counter(frozenset(g[i] for i in HA) for g in G)
fibB = Counter(frozenset(g[i] for i in HB) for g in G)
print("every fibre of g |-> g(HA) has size", set(fibA.values()), " of g |-> g(HB)", set(fibB.values()))

# ---------------------------------------- 1. intersection-pattern counting --
def counts(blocks, C):
    return Counter(frozenset(b) & C for b in blocks)

print("\n== pattern counts, A vs B ==")
for k in range(0, 7):
    bad = []
    for C in itertools.combinations(range(n), k):
        Cs = frozenset(C)
        if counts(A, Cs) != counts(B, Cs):
            bad.append(C)
    print(f"  |C|={k}: equal for all {math.comb(n,k)} coalitions: {not bad}"
          + (f"   first witness {bad[0]}: A {dict(counts(A,frozenset(bad[0])))} "
             f"B {dict(counts(B,frozenset(bad[0])))}" if bad else ""))

# design-theoretic prediction of the count, from (v,k,t,b) only
def predicted(C, A_pat, v=12, kk=6, t=5, b=132):
    """inclusion-exclusion:  N(C,A) = sum_{A<=D<=C} (-1)^{|D|-|A|} lambda_{|D|}"""
    def lam(i):
        return Fraction(b * math.comb(kk, i), math.comb(v, i))
    rest = sorted(set(C) - set(A_pat))
    tot = Fraction(0)
    for r in range(len(rest) + 1):
        for extra in itertools.combinations(rest, r):
            D = len(A_pat) + r
            tot += (-1) ** r * lam(D)
    return tot
ok = True
for k in range(0, 6):
    for C in itertools.combinations(range(n), k):
        Cs = frozenset(C)
        ca = counts(A, Cs)
        for r in range(k + 1):
            for P in itertools.combinations(C, r):
                if ca.get(frozenset(P), 0) != predicted(C, P):
                    ok = False
print("design-parameter prediction matches every A-count for |C|<=5:", ok)

# ------------------------------- 2. colour view law, fixed-representative --
def colour_law(H, C):
    """law of the heart-pattern a coalition C sees when the dealer fixes the
       representative deck with heart set H and the shuffle g is uniform"""
    c = Counter(frozenset(i for i in C if g[i] in H) for g in G)
    return {k: Fraction(v, len(G)) for k, v in c.items()}
print("\n== colour view law, fixed representative + uniform shuffle ==")
for k in range(1, 7):
    same = all(colour_law(HA, frozenset(C)) == colour_law(HB, frozenset(C))
               for C in itertools.combinations(range(n), k))
    print(f"  |C|={k}: laws equal: {same}")
# and that the law equals (#blocks with that pattern)/132
agree = True
for k in range(0, 7):
    for C in itertools.combinations(range(n), k):
        Cs = frozenset(C)
        law = colour_law(HA, Cs)
        cnt = Counter(b & Cs for b in orbA)       # note: g(HA) ranges over orbA
        if law != {p: Fraction(v, len(orbA)) for p, v in cnt.items()}:
            agree = False
print("  law(C) == #{B in orbit : B cap C = pattern}/132 :", agree)

# ---------------------------------------------- 3. raw CODE view, leak/no --
def code_law_fixed(deck, C):
    """deck : position -> code.  Fixed representative + uniform shuffle."""
    c = Counter(tuple(deck[g[i]] for i in sorted(C)) for g in G)
    return {k: Fraction(v, len(G)) for k, v in c.items()}
# a concrete pair of representative decks: identity code assignment with
# hearts (codes 0..5) placed on the block, clubs elsewhere, in increasing order
def rep_deck(H):
    d = [None] * n
    hs, cs = 0, 6
    for i in range(n):
        if i in H: d[i] = hs; hs += 1
        else:      d[i] = cs; cs += 1
    return d
dA, dB = rep_deck(HA), rep_deck(HB)
print("\n== raw CODE view, fixed representative + uniform shuffle ==")
for k in range(1, 6):
    bad = None
    for C in itertools.combinations(range(n), k):
        if code_law_fixed(dA, C) != code_law_fixed(dB, C):
            bad = C; break
    print(f"  |C|={k}: laws equal: {bad is None}" + (f"   witness C={bad}" if bad else ""))

# same question under the ALL-DECKS dealer (deck uniform over the class)
print("\n== raw CODE view, all-decks dealer (no shuffle needed) ==")
def alldecks_code_law(blocks, C):
    """Uniform over every uniq deck whose heart set is a block of `blocks`.
       Count decks by the values on C; normalise."""
    Cs = sorted(C)
    c = Counter()
    for b in blocks:
        # choose the values on C: hearts on C cap b, clubs elsewhere
        hs = [x for x in Cs if x in b]
        cl = [x for x in Cs if x not in b]
        for hv in itertools.permutations(range(6), len(hs)):
            for cv in itertools.permutations(range(6, 12), len(cl)):
                key = {}
                for p, v in zip(hs, hv): key[p] = v
                for p, v in zip(cl, cv): key[p] = v
                # number of completions is the same for every choice
                c[tuple(key[x] for x in Cs)] += 1
    tot = sum(c.values())
    return {k: Fraction(v, tot) for k, v in c.items()}
for k in range(1, 6):
    bad = None
    for C in itertools.combinations(range(n), k):
        if alldecks_code_law(A, C) != alldecks_code_law(B, C):
            bad = C; break
    print(f"  |C|={k}: laws equal: {bad is None}" + (f"   witness C={bad}" if bad else ""))
badC = None
for C in itertools.combinations(range(n), 6):
    if alldecks_code_law(A, C) != alldecks_code_law(B, C):
        badC = C; break
print(f"  |C|=6: laws equal: {badC is None}" + (f"   witness C={badC}" if badC else ""))

# ------------------------------------- 4. the re-deal (ts_private) at k<=5 --
print("\n== existential re-deal with DISTINCT CODES (ts_private shape) ==")
worst = None
for k in range(0, 6):
    for C in itertools.combinations(range(n), k):
        Cs = frozenset(C)
        for H in A:
            pat = H & Cs
            if not any((Hp & Cs) == pat for Hp in B):
                worst = (C, sorted(H)); break
        if worst: break
    if worst: break
print("  every A-block/coalition(<=5) pattern is matched by some B-block:", worst is None,
      "" if worst is None else worst)
# and at size 6 it fails
fail6 = None
for C in itertools.combinations(range(n), 6):
    Cs = frozenset(C)
    for H in A:
        if not any((Hp & Cs) == (H & Cs) for Hp in B):
            fail6 = (C, sorted(H)); break
    if fail6: break
print("  at |C|=6 some A-pattern has no B-block:", fail6)

# -------------------------------------------- 5. the recovery ladder 6..11 --
print("\n== recovery ladder ==")
# 10 reveals: for every pair of hidden positions, an A-block and a B-block
# agreeing off that pair
amb = all(any((X - frozenset(pq)) == (Y - frozenset(pq)) for X in A for Y in B)
          for pq in itertools.combinations(range(n), 2))
print("  ten reveals never determine the class (colour view):", amb)
# 11 reveals, colour-only pigeonhole: the 12th colour is forced
print("  eleven reveals: |H|=6 forces the last colour, so the heart set and")
print("    hence the class are determined  (all blocks have size 6:",
      len({len(b) for b in A | B}) == 1, ")")
# is the ambiguity at 10 a 1-swap pair?
swaps = 0
for X in A:
    for Y in B:
        if len(X ^ Y) == 2: swaps += 1
print("  #(A-block,B-block) pairs differing by a single swap:", swaps)

# ------------------------------------- 6. section-2 criterion, b-dependence --
print("\n== section 2 criterion sanity ==")
print("  lambda_5/b for A:", Fraction(1, 132), " C(6,5)/C(12,5) =",
      Fraction(math.comb(6, 5), math.comb(12, 5)))
print("  the M12 pair (792,5)+(132,5) would have EQUAL normalised laws but")
print("    UNEQUAL raw counts: 792 vs 132 -> a count-equality certificate fails there.")
