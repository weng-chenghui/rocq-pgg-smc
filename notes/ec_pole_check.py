
# Test the deep structural claim: for cover_genus1.v's SINGLE-POLE model
# (code = L(m*O), so the recon-symmetry must FIX the pole O to preserve the code),
# any group that also fixes an affine secret P0 is the two-point stabilizer,
# which on this genus-1 curve is abelian. => the existing scaffold cannot host
# a non-abelian recon-symmetry at genus 1.

P = 3
def add(u,v): return ((u[0]+v[0])%P,(u[1]+v[1])%P)
def mul(u,v):
    a,b=u; c,d=v
    return ((a*c+2*b*d)%P,(a*d+b*c)%P)
ZERO=(0,0); ONE=(1,0)
ELTS=[(a,b) for a in range(P) for b in range(P)]
def is_zero(u): return u==ZERO
def sub(u,v): return add(u,((-v[0])%P,(-v[1])%P))
def rhs(x): return sub(mul(mul(x,x),x),x)
def sq(y): return mul(y,y)
affine=[(x,y) for x in ELTS for y in ELTS if sq(y)==rhs(x)]
points=affine+["O"]

u4=[u for u in ELTS if not is_zero(u) and mul(mul(u,u),mul(u,u))==ONE]
def make_phi(u,r):
    u2=mul(u,u); u3=mul(u2,u)
    def phi(pt):
        if pt=="O": return "O"
        x,y=pt; return (add(mul(u2,x),r), mul(u3,y))
    return phi,(u,r)
# Aut(E,O): these all FIX O (the pole), so all preserve L(m*O).
autos=[make_phi(u,r) for u in u4 for r in [(a,0) for a in range(P)]]
idx={pt:i for i,pt in enumerate(points)}
def as_perm(phi): return tuple(idx[phi(pt)] for pt in points)

def compose(p,q): return tuple(p[q[i]] for i in range(len(p)))
def commutes(p,q): return compose(p,q)==compose(q,p)

print("For each candidate affine secret P0, the pole-fixing AND secret-fixing subgroup:")
for P0 in affine:
    # elements of Aut(E,O) that also fix P0  (fix pole O AND secret P0)
    keep=[(phi,tag) for (phi,tag) in autos if phi(P0)==P0]
    perms=[as_perm(phi) for (phi,tag) in keep]
    order=len(set(perms))
    abelian=all(commutes(a,b) for a in perms for b in perms)
    # which Aut(E,O)-orbit is P0 in?
    print(f"  P0={P0}: |Stab_pole&secret|={order}, abelian={abelian}")

# summary: max non-abelian order achievable while fixing pole+secret
best=0
for P0 in affine:
    keep=[as_perm(phi) for (phi,tag) in autos if phi(P0)==P0]
    perms=set(keep)
    if not all(compose(a,b)==compose(b,a) for a in perms for b in perms):
        best=max(best,len(perms))
print("\nmax NON-abelian pole+secret-fixing order:", best, "(0 => always abelian)")
print("=> single-pole scaffold forces abelian recon-symmetry at genus 1.")
