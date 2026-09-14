"""Exact-integer walk on the 660 states, in the form the kernel certificate
checks.  Finds the least L meeting each of the two bound conventions, so the
spec's L = 570 can be read against the certificate the pgl27_mixing.v shape
actually encodes."""
import re, itertools
from pathlib import Path

src = (Path(__file__).resolve().parent.parent / "psl211_tables.v").read_text()
def parse_perm(name):
    m = re.search(name + r"\s*:\s*seq nat\s*:=\s*\[::([^\]]*)\]", src)
    return tuple(int(x) for x in m.group(1).replace(";", " ").split())
r4, m6, m6i = parse_perm("r4_tbl"), parse_perm("m6_tbl"), parse_perm("m6i_tbl")
n = 12
e = tuple(range(n))
def comp(p, q): return tuple(p[q[x]] for x in range(n))

G = {e}; fr = [e]
while fr:
    nf = []
    for g in fr:
        for s in (r4, m6):
            h = comp(s, g)
            if h not in G: G.add(h); nf.append(h)
    fr = nf
Gl = sorted(G); idx = {g: i for i, g in enumerate(Gl)}; N = len(Gl)
alpha = [r4, m6, m6i]
preds = [[] for _ in range(N)]
for k, g in enumerate(Gl):
    for a in alpha:
        preds[idx[comp(a, g)]].append(k)
assert all(len(p) == 3 for p in preds), "not 3-regular"

c = [0] * N; c[idx[e]] = 1
print("L   |  S(L) = sum|660*c - 3^L|   2^40*S <= 660*3^L ? | 2^39*S <= 660*3^L ?")
hit40 = hit39 = None
for L in range(1, 900):
    c = [sum(c[k] for k in p) for p in preds]
    D = 3 ** L
    S = sum(abs(N * x - D) for x in c)
    a = (2 ** 40) * S <= N * D          # pgl27_mixing.v shape: TV <= 2^-41
    b = (2 ** 39) * S <= N * D          # TV <= 2^-40
    if b and hit39 is None: hit39 = L
    if a and hit40 is None: hit40 = L
    if L in (200, 570, 571) or (a and L <= (hit40 or 0) + 1):
        tv = S / (2 * N * D)
        print(f"{L:4d}  TV = {tv:.3e}  pgl27-shape(2^40): {a}   2^39 form: {b}")
    if a and hit39 is not None: break
print("least L with 2^39*S <= 660*3^L  (TV <= 2^-40):", hit39)
print("least L with 2^40*S <= 660*3^L  (TV <= 2^-41, the pgl27_mixing.v shape):", hit40)
