
# Plain-English check: are the dangerous pairs exactly the "mirror-partner" pairs,
# i.e. the transpositions of the scheme's UNIQUE involution (order-2 shuffle)?
from itertools import combinations
exec(open("ec_orbit_profile.py").read().split("def profile")[0])  # reuse setup + perms + cols + reconstructs

# find the unique involution among the 12 shuffles (order 2, != identity)
def is_identity(pm): return all(pm[i]==i for i in range(len(pm)))
def order(pm):
    k=1; cur=pm
    while not is_identity(cur):
        cur=tuple(pm[cur[i]] for i in range(len(pm))); k+=1
    return k
invs=[pm for pm in perms if order(pm)==2]
print("number of order-2 shuffles (involutions):", len(invs))
z=invs[0]
# its transpositions on the 12 shares (indices 1..12)
pairs=set()
for i in range(1,13):
    j=z[i]
    if j!=i: pairs.add(frozenset((i,j)))
mirror=sorted(sorted(p) for p in pairs)
print("mirror-partner pairs (swapped by the involution):", mirror)

# which size-2 coalitions reconstruct?
danger=sorted(sorted(c) for c in combinations(range(1,13),2) if reconstructs(set(c)))
print("size-2 coalitions that RECONSTRUCT :", danger)
print("mirror pairs == dangerous pairs ?  ", mirror==danger)
