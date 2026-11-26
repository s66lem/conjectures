r"""Standalone verifier for Clifton-Harris-Khaqan Question 5.2 (arXiv:2611.29890v1).

Run: python -O -W error verify.py   (stdlib only; uses require(), never assert)
"""
import itertools
import sys
from functools import lru_cache
from math import comb


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def outcome(a):
    n = len(a)
    spot = [0] * (n + 1)
    for i, p in enumerate(a, 1):
        if spot[p] == 0:
            spot[p] = i
        else:
            j = spot[p]
            spot[p] = i
            s = 1
            while spot[s]:
                s += 1
            spot[s] = j
    return tuple(spot[1:])


def L(a):
    seen = set()
    for t, v in enumerate(a):
        if v in seen:
            return t
        seen.add(v)
    return len(a)


def brute_polys(n):
    P = {}
    for a in itertools.product(range(1, n + 1), repeat=n):
        d = P.setdefault(outcome(a), {})
        l = L(a)
        d[l] = d.get(l, 0) + 1
    return P


def count_dp(pi):
    n = len(pi)

    @lru_cache(None)
    def f(state):
        i = max(state) if state else 0
        if i == 0:
            return 1
        q = state.index(i)
        m = state.index(0) if 0 in state else n
        s = list(state)
        s[q] = 0
        tot = f(tuple(s))
        for l in range(m):
            if l != q:
                t = list(state)
                t[q] = t[l]
                t[l] = 0
                tot += f(tuple(t))
        return tot

    return f(tuple(pi)) if n else 1


def padd(*ps):
    r = {}
    for p in ps:
        for k, v in p.items():
            r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v}


def Phi(P):
    r = {}
    for j, c in P.items():
        for e in range(1, j + 2):
            r[e] = r.get(e, 0) + c
    return r


def yshift(P):
    return {k + 1: v for k, v in P.items()}


NMAX_BRUTE = 7
polys = {0: {(): {0: 1}}}
for n in range(1, NMAX_BRUTE + 1):
    polys[n] = brute_polys(n)
    require(sum(sum(d.values()) for d in polys[n].values()) == n ** n, "all lists park")

for n in range(1, NMAX_BRUTE + 1):
    for pi, d in polys[n].items():
        require(count_dp(pi) == sum(d.values()), f"dp vs brute {pi}")
print("1. backward DP == brute force for all outcomes, n <= 7")

for n in range(1, NMAX_BRUTE + 1):
    for sigma in itertools.permutations(range(1, n)):
        Ps = polys[n - 1].get(sigma, {})
        rhs = yshift(Ps)
        for l, c in Ps.items():
            rhs = padd(rhs, {r: c for r in range(1, l + 1)})
        lhs = polys[n].get((1,) + tuple(s + 1 for s in sigma), {})
        require(lhs == rhs, f"Lemma A sigma={sigma}")
        require(lhs == Phi(Ps), "Lemma A in operator form")
print("2. Lemma A (general car-1 reduction) holds for every sigma, n <= 7")


def delta(n):
    return tuple(range(n, 0, -1))


for n in range(2, NMAX_BRUTE + 1):
    lhs = polys[n][delta(n)]
    rhs = padd(yshift(polys[n - 1][delta(n - 1)]), polys[n - 1][(1,) + tuple(range(n - 1, 1, -1))])
    require(lhs == rhs, f"Lemma B n={n}")
print("3. Lemma B (decreasing outcomes) holds, n <= 7")

NN = 40
Mot = [1, 1]
for n in range(2, NN):
    Mot.append(Mot[-1] + sum(Mot[i] * Mot[n - 2 - i] for i in range(n - 1)))
Cat = [comb(2 * n, n) // (n + 1) for n in range(NN)]


def mpow(r, N):
    v = [1] + [0] * N
    for _ in range(r):
        v = [sum(v[i] * Mot[j - i] for i in range(j + 1)) for j in range(N + 1)]
    return v[N]


def B(r, i):
    return comb(r + i, i) * (r - i + 1) // (r + 1)


for r in range(1, 15):
    for i in range(r + 1):
        require(B(r, i) == sum(B(r - 1, t) for t in range(min(i, r - 1) + 1)), "Catalan triangle recurrence")


def T_formula(n, k):
    if k == 0:
        return Mot[n]
    return sum(B(k - 1, i) * mpow(k + 1 - i, n - k) for i in range(k))


def pi_k(n, k):
    return tuple(list(range(1, k + 1)) + list(range(n, k, -1)))


for n in range(1, NMAX_BRUTE + 1):
    for k in range(1, n + 1):
        require(polys[n][pi_k(n, k)] == Phi(polys[n - 1][pi_k(n - 1, k - 1)]), f"A_k recursion {n},{k}")

for n in range(0, NMAX_BRUTE + 1):
    for k in range(n + 1):
        require(T_formula(n, k) == sum(polys[n][pi_k(n, k)].values()), f"formula vs brute {n},{k}")
for n in range(1, 15):
    for k in range(n + 1):
        require(T_formula(n, k) == count_dp(pi_k(n, k)), f"formula vs dp {n},{k}")
print("4. closed form == counts: brute n <= 7, DP n <= 14 (all k)")

J = 30
c = [[1] * (J + 14)]
for k in range(1, 13):
    c.append([sum(c[k - 1][r] for r in range(1, j + 2)) for j in range(J + 13 - k)])
    for j in range(J + 1):
        require(c[k][j] == (j + 1) * comb(2 * k + j, k) // (k + j + 1), "ballot closed form")
        rhs = sum(B(k - 1, i) * comb(j + k - i, k - i) for i in range(k))
        require(c[k][j] == rhs, f"G_k identity k={k} j={j}")
print("5. G_k(p) identity checked k <= 12, coefficients p^j, j <= 30")

for n in range(1, 30):
    for k in range(max(0, n - 2), n + 1):
        require(T_formula(n, k) == Cat[n], "Thm 1.6 Catalan cases")
    require(T_formula(n, 0) == Mot[n], "Thm 1.8")
    require(T_formula(n, 1) == Mot[n + 1] - Mot[n], "Cor 1.9")
    if n >= 2:
        require(T_formula(n, 2) == Mot[n + 2] - 2 * Mot[n + 1] + Mot[n] - Mot[n - 1], "Cor 1.10")
    if n >= 3:
        require(T_formula(n, 3) == Mot[n + 3] - 3 * Mot[n + 2] + 3 * Mot[n + 1] - 3 * Mot[n]
                + 2 * Mot[n - 1] - 2 * Mot[n - 2], "linear form k=3")
    if n >= 4:
        require(T_formula(n, 4) == Mot[n + 4] - 4 * Mot[n + 3] + 6 * Mot[n + 2] - 7 * Mot[n + 1]
                + 7 * Mot[n] - 7 * Mot[n - 1] + 5 * Mot[n - 2] - 5 * Mot[n - 3], "linear form k=4")
print("6. agrees with paper Thm 1.6, Thm 1.8, Cor 1.9, Cor 1.10 and linear forms k=3,4")
print("ALL CHECKS PASSED")
