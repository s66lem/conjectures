r"""Verify the counterexample to Manna--Mandal Problem 7.10, second question (arXiv:2611.27642v1).

P = Z_9^2 x {0, 1, 2} with (v, i)(w, j) = (v + s^i(w) + [i + j >= 3] u, (i + j) mod 3),
s(a, b) = (-b, a - b), u = (-3, 3) = (6, 3). K = P x Z_5 (m_3 = 5), G = P x Z_10.
Standalone stdlib-only verifier; run with `python -O -W error verify.py`.
"""
import sys
from math import gcd

CHECKS = 0


def require(cond, msg):
    global CHECKS
    CHECKS += 1
    if not cond:
        sys.stderr.write("FAIL: " + msg + "\n")
        sys.exit(1)


def phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def s(v):
    a, b = v
    return ((-b) % 9, (a - b) % 9)


Z = (6, 3)  # = (-3, 3) mod 9
SP = [lambda v: v, s, lambda v: s(s(v))]
ELP = [((a, b), i) for a in range(9) for b in range(9) for i in range(3)]
IDX = {g: n for n, g in enumerate(ELP)}
NP = len(ELP)
E_P = IDX[((0, 0), 0)]


def mulP(g, h):
    (v, i), (w, j) = g, h
    u = SP[i](w)
    c = 1 if i + j >= 3 else 0
    return (((v[0] + u[0] + c * Z[0]) % 9, (v[1] + u[1] + c * Z[1]) % 9), (i + j) % 3)


require(NP == 243, "|P| = 243")
require(s(s(s((1, 0)))) == (1, 0) and s(s(s((0, 1)))) == (0, 1), "s^3 = id")
require(s(Z) == Z, "s fixes u")
T = [[IDX[mulP(g, h)] for h in ELP] for g in ELP]
assoc = all(
    T[T[x][y]][zz] == T[x][T[y][zz]]
    for x in range(NP) for y in range(NP) for zz in range(NP)
)
require(assoc, "associativity of P (all 243^3 triples)")
require(all(T[E_P][x] == x == T[x][E_P] for x in range(NP)), "identity")
require(all(any(T[x][y] == E_P for y in range(NP)) for x in range(NP)), "inverses")


def powers(x, tab, e):
    L, y = [e], x
    while y != e:
        L.append(y)
        y = tab[y][x]
    return L


cycP = [frozenset(powers(x, T, E_P)) for x in range(NP)]
ordP = [len(c) for c in cycP]
subsP = set(cycP)
ordcount = {}
for o in ordP:
    ordcount[o] = ordcount.get(o, 0) + 1
require(ordcount == {1: 1, 3: 8, 9: 234}, "element orders of P: 1x1, 8x3, 234x9")
N3 = sum(1 for C in subsP if len(C) == 3)
require(N3 == 4, "N_3(P) = 4")
outside = [x for x in range(NP) if ELP[x][1] != 0]
require(all(ordP[x] == 9 for x in outside), "every element outside A has order 9")
require(
    all(set(powers(x, T, E_P)) >= {IDX[(Z, 0)]} for x in outside),
    "every element outside A has cube in <u>",
)
ZC = cycP[IDX[(Z, 0)]]


def children(C):
    return [D for D in subsP if C < D and len(D) == 3 * len(C)]


cZ = len(children(ZC))
require(cZ == 30, "c_P(<u>) = 30")
prof = {}
for C in subsP:
    k = (len(C), len(children(C)))
    prof[k] = prof.get(k, 0) + 1
require(prof == {(1, 4): 1, (3, 30): 1, (3, 3): 3, (9, 0): 39}, "children profile of H(P)")
require(len(children(frozenset([E_P]))) == N3, "root children = N_3")

m3 = 5
require(N3 <= 2 * m3, "(H1) holds for p = 3")
H2_fail = [C for C in subsP if len(C) > 1 and len(children(C)) > 2 * phi(len(C)) * m3 - 1]
require(H2_fail == [ZC], "(H2) fails for p = 3 exactly at C = <u> (30 > 19)")
require(1 <= 2 * 243 and 0 <= 2 * phi(5) * 243 - 1, "(H1),(H2) hold for p = 5")
require(30 > 2 * 2 * 7 - 1 and 30 <= 2 * 2 * 11 - 1, "range of m remark")

EL = [(x, t) for x in range(NP) for t in range(10)]
GI = {g: n for n, g in enumerate(EL)}
NG = len(EL)
E_G = GI[(E_P, 0)]


def cyc_G(a):
    L, y = [E_G], a
    while y != E_G:
        L.append(y)
        x1, t1 = EL[y]
        x0, t0 = EL[a]
        y = GI[(T[x1][x0], (t1 + t0) % 10)]
    return frozenset(L)


cycG = [cyc_G(a) for a in range(NG)]
require(len(set(len(c) for c in cycG)) > 1 and max(len(c) for c in cycG) == 90, "orders in G")
adj = [set() for _ in range(NG)]
for a in range(NG):
    for b in cycG[a]:
        if b != a and cycG[b] < cycG[a]:
            idx = len(cycG[a]) // len(cycG[b])
            if idx in (2, 3, 5):
                adj[a].add(b)
                adj[b].add(a)


def Omega(n):
    k, d = 0, 2
    while n > 1:
        while n % d == 0:
            n //= d
            k += 1
        d += 1
    return k


require(
    all(Omega(len(cycG[a])) % 2 != Omega(len(cycG[b])) % 2 for a in range(NG) for b in adj[a]),
    "Gamma(G) bipartite",
)
require(sum(len(x) for x in adj) // 2 > 0, "Gamma(G) has edges")
zidx = [x for x in range(NP) if cycP[x] == ZC and x != E_P]
S = {GI[(x, t)] for x in zidx for t in range(10)}
require(len(S) == 20, "|S| = 20")
seen, comps = set(S), 0
for a in range(NG):
    if a in seen:
        continue
    comps += 1
    stack = [a]
    seen.add(a)
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
require(comps == 31, "Gamma(G) - S has 31 components")
require(comps > len(S), "=> Gamma(G) has no Hamiltonian cycle")
require(comps > len(S) + 1, "=> Gamma(G) has no Hamiltonian path")
seen = {0}
stack = [0]
while stack:
    u = stack.pop()
    for w in adj[u]:
        if w not in seen:
            seen.add(w)
            stack.append(w)
require(len(seen) == NG, "Gamma(G) connected")
print("ALL CHECKS PASSED (%d checks)" % CHECKS)
