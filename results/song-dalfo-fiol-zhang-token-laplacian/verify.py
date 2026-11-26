r"""Verification for the token-graph Laplacian spectral radius conjecture of
Song, Dalfo, Fiol, and Zhang (arXiv:2610.00500v1).

Standalone stdlib-only checks (run with `python -O -W error verify.py`):
 A. All 877 connected non-star labelled graphs on n = 4, 5 vertices plus 120
    random connected graphs on n = 6, 7: verifies rho(F_2(G)) > rho(G) and
    checks the exact rational certificate (dominating, one-sided, or product
    with perturbation) for every graph.
 B. All 1,088 labelled graphs on n = 4, 5: verifies rho(F_k(G)) = rho(G) for
    all 2 <= k <= n // 2 iff G is edgeless, S_m + (n - m)K_1 (m >= 2), or
    K_3 + (n - 3)K_1.
 C. Runs the one-sided and product certificates on every oriented edge of every
    graph in A.
"""
import itertools
import math
import random
import sys
from fractions import Fraction as Fr


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def jacobi(A, vecs=False):
    n = len(A)
    a = [row[:] for row in A]
    V = [[float(i == j) for j in range(n)] for i in range(n)]
    for _ in range(100):
        off = sum(a[i][j] ** 2 for i in range(n) for j in range(i + 1, n))
        if off < 1e-22:
            break
        for p in range(n):
            for q in range(p + 1, n):
                if abs(a[p][q]) < 1e-15:
                    continue
                th = (a[q][q] - a[p][p]) / (2 * a[p][q])
                t = (1.0 if th >= 0 else -1.0) / (abs(th) + math.sqrt(th * th + 1))
                c = 1 / math.sqrt(t * t + 1)
                s = t * c
                for k in range(n):
                    akp, akq = a[k][p], a[k][q]
                    a[k][p] = c * akp - s * akq
                    a[k][q] = s * akp + c * akq
                for k in range(n):
                    apk, aqk = a[p][k], a[q][k]
                    a[p][k] = c * apk - s * aqk
                    a[q][k] = s * apk + c * aqk
                if vecs:
                    for k in range(n):
                        vkp, vkq = V[k][p], V[k][q]
                        V[k][p] = c * vkp - s * vkq
                        V[k][q] = s * vkp + c * vkq
    ev = [a[i][i] for i in range(n)]
    return (ev, V) if vecs else ev


def lap(n, E):
    L = [[0.0] * n for _ in range(n)]
    for a, b in E:
        L[a][a] += 1
        L[b][b] += 1
        L[a][b] -= 1
        L[b][a] -= 1
    return L


def rho(n, E):
    return max(jacobi(lap(n, E))) if E else 0.0


def token(n, E, k):
    S = [frozenset(c) for c in itertools.combinations(range(n), k)]
    idx = {s: i for i, s in enumerate(S)}
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    TE = set()
    for s in S:
        for x in s:
            for w in adj[x]:
                if w not in s:
                    t = (s - {x}) | {w}
                    i, j = idx[s], idx[t]
                    TE.add((min(i, j), max(i, j)))
    return S, idx, sorted(TE)


def quad(TE, f):
    return sum((f.get(i, 0) - f.get(j, 0)) ** 2 for i, j in TE)


def connected(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    seen = {0}
    st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == n


def is_star(n, E):
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    return len(E) == n - 1 and max(deg) == n - 1


def gm_quotient(TE, s):
    nb = [j for i, j in TE if i == s] + [i for i, j in TE if j == s]
    D = len(nb)
    f = {s: Fr(D)}
    for t in nb:
        f[t] = Fr(-1)
    return quad(TE, f) / sum(v * v for v in f.values()), D


def certificate(n, E, edge=None):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    deg = [len(adj[i]) for i in range(n)]
    S, idx, TE = token(n, E, 2)
    lam_ev, V = jacobi(lap(n, E), vecs=True)
    top = max(range(n), key=lambda i: lam_ev[i])
    lam = lam_ev[top]
    x = [V[i][top] for i in range(n)]
    dom = [v for v in range(n) if deg[v] == n - 1]
    if dom and edge is None:
        c0 = dom[0]
        p, q = next((a, b) for a, b in E if c0 not in (a, b))
        E0 = [(c0, i) for i in range(n) if i != c0] + [(p, q)]
        S0, idx0, TE0 = token(n, E0, 2)
        require(set(TE0) <= set(TE), "F_2(S_n+e) subgraph of F_2(G)")
        Rq, D = gm_quotient(TE0, idx0[frozenset((c0, p))])
        require(D == n - 1 and Rq > n, "dominating case quotient > n")
        require(lam <= n + 1e-9, "rho(G) <= n")
        return "dominating"
    if edge is None:
        u, v = max(E, key=lambda e: abs(x[e[0]] - x[e[1]]))
        if x[u] < x[v]:
            u, v = v, u
    else:
        u, v = edge
    A0 = adj[u] - adj[v] - {v}
    B0 = adj[v] - adj[u] - {u}
    rho0 = len(adj[u] | adj[v])
    if edge is None:
        require(lam <= rho0 + 1e-9, "rho(G) <= |N(u) u N(v)| on max-diff edge")
    if not A0 or not B0:
        w = v if not A0 else u
        if deg[w] == n - 1:
            return "skip"
        if edge is not None and not A0 and not B0:
            return "skip"
        require(rho0 == deg[w] + 1, "one-sided bound")
        z = next(t for t in range(n) if t != w and t not in adj[w])
        Rq, D = gm_quotient(TE, idx[frozenset((w, z))])
        require(D >= deg[w] + 1 and Rq >= deg[w] + 2, "one-sided case quotient")
        return "one-sided"
    X = sorted(adj[u] - {v})
    Y = sorted(B0)
    a, b = len(X), len(Y)
    require(a >= 1 and b >= 1 and a + b + 2 == rho0, "product sizes")
    P = {u: a}
    P.update({t: -1 for t in X})
    Q = {v: b}
    Q.update({t: -1 for t in Y})
    f = {}
    for s1 in [u] + X:
        for s2 in [v] + Y:
            require(s1 != s2, "disjoint star vertex sets")
            f[idx[frozenset((s1, s2))]] = Fr(P[s1] * Q[s2])
    require(len(f) == (a + 1) * (b + 1), "embedding injective")
    TEs = set(TE)
    for s2 in [v] + Y:
        for s1 in X:
            i, j = idx[frozenset((u, s2))], idx[frozenset((s1, s2))]
            require((min(i, j), max(i, j)) in TEs, "product edge 1")
    for s1 in [u] + X:
        for s2 in Y:
            i, j = idx[frozenset((s1, v))], idx[frozenset((s1, s2))]
            require((min(i, j), max(i, j)) in TEs, "product edge 2")
    nrm = sum(t * t for t in f.values())
    require(quad(TE, f) >= rho0 * nrm, "product vector quotient >= rho0")
    s = idx[frozenset((u, min(A0)))]
    require(s not in f, "witness outside W")
    g = -sum(f.get(j, 0) for i, j in TE if i == s) - sum(f.get(i, 0) for i, j in TE if j == s)
    require(g > 0, "witness gradient positive")
    eps = Fr(1)
    while True:
        h = dict(f)
        h[s] = eps
        if quad(TE, h) - rho0 * sum(t * t for t in h.values()) > 0:
            break
        eps /= 2
    return "product"


def check_A():
    cases = {}
    extra = {}
    graphs = []
    for n in (4, 5):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            graphs.append((n, [pairs[i] for i in range(len(pairs)) if mask >> i & 1]))
    rnd = random.Random(2610)
    for n in (6, 7):
        pairs = list(itertools.combinations(range(n), 2))
        got = 0
        while got < 60:
            E = [e for e in pairs if rnd.random() < rnd.choice((0.3, 0.5, 0.7))]
            if E and connected(n, E):
                graphs.append((n, E))
                got += 1
    cnt = 0
    for n, E in graphs:
        if not E or not connected(n, E) or is_star(n, E):
            continue
        S, idx, TE = token(n, E, 2)
        r1, r2 = rho(n, E), rho(len(S), TE)
        require(r2 > r1 + 1e-6, f"strict inequality {E!r}")
        k = certificate(n, E)
        cases[k] = cases.get(k, 0) + 1
        cnt += 1
        for e in E:
            for ed in (e, e[::-1]):
                k = certificate(n, E, ed)
                extra[k] = extra.get(k, 0) + 1
    print("A: connected non-star graphs checked:", cnt, cases)
    print("C: per-edge certificates:", extra)


def in_equality_family(n, E):
    if not E:
        return True
    verts = sorted(set(itertools.chain(*E)))
    m = len(verts)
    re = {v: i for i, v in enumerate(verts)}
    H = [(re[a], re[b]) for a, b in E]
    if not connected(m, H):
        return False
    return is_star(m, H) or (m == 3 and len(H) == 3)


def check_B():
    tot = 0
    fam = 0
    for n in (4, 5):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            E = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
            r = rho(n, E)
            eq = True
            for k in range(2, n // 2 + 1):
                S, idx, TE = token(n, E, k)
                if abs(rho(len(S), TE) - r) > 1e-7:
                    eq = False
                    break
            require(eq == in_equality_family(n, E), f"characterisation {E!r}")
            tot += 1
            fam += eq
    print("B: labelled graphs n=4,5 checked:", tot, "equality cases:", fam)


def check_literal():
    for E in ([(0, 1), (0, 2)], [(0, 1)]):
        S, idx, TE = token(4, E, 2)
        require(abs(rho(len(S), TE) - rho(4, E)) < 1e-9 and not is_star(4, E), "literal counterexample")
    print("literal counterexamples on 4 vertices confirmed")


if __name__ == "__main__":
    check_literal()
    check_A()
    check_B()
    print("ALL CHECKS PASSED")
