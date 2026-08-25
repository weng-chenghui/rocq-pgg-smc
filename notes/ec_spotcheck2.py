
# Extend the spot-check: verify an AFFINE secret placement fits cover_genus1.v's
# affine-points model. E: y^2 = x^3 - x over GF(9). Compute the group law, the
# point-stabilizer Stab(P0) of an affine point P0, its orbits, and where O lands.

P = 3
def add(u,v): return ((u[0]+v[0])%P,(u[1]+v[1])%P)
def neg(u):   return ((-u[0])%P,(-u[1])%P)
def sub(u,v): return add(u,neg(v))
def mul(u,v):
    a,b=u; c,d=v
    return ((a*c+2*b*d)%P,(a*d+b*c)%P)
ZERO=(0,0); ONE=(1,0); T=(0,1)
ELTS=[(a,b) for a in range(P) for b in range(P)]
def is_zero(u): return u==ZERO
def inv(u):
    for v in ELTS:
        if mul(u,v)==ONE: return v
    raise ValueError(u)

def rhs(x): return sub(mul(mul(x,x),x), x)      # x^3 - x
def sq(y):  return mul(y,y)

affine=[]
for x in ELTS:
    r=rhs(x)
    for y in ELTS:
        if sq(y)==r: affine.append((x,y))
points=affine+["O"]

# ---- elliptic curve addition, y^2 = x^3 + a*x, a = -1, char 3 ----
A=neg(ONE)   # a = -1
def ecadd(Pp,Qp):
    if Pp=="O": return Qp
    if Qp=="O": return Pp
    x1,y1=Pp; x2,y2=Qp
    if x1==x2 and add(y1,y2)==ZERO: return "O"
    if Pp==Qp:
        # lambda = (3 x1^2 + a)/(2 y1); 3 x1^2 = 0 in char 3
        num=A; den=mul((2,0),y1)
        lam=mul(num,inv(den))
    else:
        lam=mul(sub(y2,y1), inv(sub(x2,x1)))
    x3=sub(sub(mul(lam,lam),x1),x2)
    y3=sub(mul(lam,sub(x1,x3)),y1)
    return (x3,y3)

# sanity: point group has order 16 and O is identity
def ecmul(n,Pp):
    R="O"
    for _ in range(n): R=ecadd(R,Pp)
    return R
orders=[]
for Pp in points:
    k=1; R=Pp
    while R!="O": R=ecadd(R,Pp); k+=1
    orders.append(k)
print("point-group size:", len(points), " element orders:", sorted(set(orders)))

# ---- automorphisms fixing O ----
u4=[u for u in ELTS if not is_zero(u) and mul(mul(u,u),mul(u,u))==ONE]
def make_phi(u,r):
    u2=mul(u,u); u3=mul(u2,u)
    def phi(pt):
        if pt=="O": return "O"
        x,y=pt; return (add(mul(u2,x),r), mul(u3,y))
    return phi
autos=[make_phi(u,r) for u in u4 for r in [(a,0) for a in range(P)]]

# ---- Stab(P0) for an affine P0: g = tau_{P0 - phi(P0)} o phi, fixes P0 ----
def translate(Q):
    return lambda pt: ecadd(pt,Q)
def stab_elements(P0):
    els=[]
    for phi in autos:
        Q=sub_pt(P0, phi(P0))          # P0 - phi(P0) in the point group
        tau=translate(Q)
        g=lambda pt,phi=phi,tau=tau: tau(phi(pt))
        assert g(P0)==P0
        els.append(g)
    return els
def sub_pt(Pp,Qp):                     # Pp - Qp in EC group
    return ecadd(Pp, neg_pt(Qp))
def neg_pt(Pp):
    if Pp=="O": return "O"
    x,y=Pp; return (x, neg(y))

def orbits_of(els):
    remaining=set(points); orbs=[]
    while remaining:
        s=next(iter(remaining)); seen={s}; frontier=[s]
        while frontier:
            pt=frontier.pop()
            for g in els:
                q=g(pt)
                if q not in seen: seen.add(q); frontier.append(q)
        orbs.append(seen); remaining-=seen
    return sorted(orbs,key=len)

# try each affine P0, report orbit sizes and where O lands
print("\nsecret=affine P0, recon-symmetry = Stab(P0):")
seen_shapes=set()
for P0 in affine:
    els=stab_elements(P0)
    # verify it is a group of order 12, non-abelian
    idx={pt:i for i,pt in enumerate(points)}
    perms=set(tuple(idx[g(pt)] for pt in points) for g in els)
    orbs=orbits_of(els)
    sizes=tuple(len(o) for o in orbs)
    Oorbit=[len(o) for o in orbs if "O" in o][0]
    shape=(len(perms), sizes, Oorbit)
    if shape not in seen_shapes:
        seen_shapes.add(shape)
        print(f"  |Stab|={len(perms)}  orbit sizes={sizes}  O is in the size-{Oorbit} orbit  (P0={P0})")

print("\nInterpretation:")
print("  secret=P0 (singleton), D on the size-3 orbit, eval = P0 + size-12 orbit.")
print("  If O is in the size-3 orbit -> D-support contains O, all 13 eval points affine (fits model).")
print("  If O is in the size-12 orbit -> eval would contain O (needs O-as-coordinate).")
