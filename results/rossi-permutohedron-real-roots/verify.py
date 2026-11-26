r"""Standalone verifier for Rossi's Conjecture 6.16 (arXiv:2611.25741v1).

Stdlib only; uses require() rather than assert. Run: python -O -W error verify.py
Checks:
  1. Brute-force Moebius function on the permutohedron face lattice (n <= 5) vs Theorem 6.11(1).
  2. Exact Moebius transform identity (z-1)^n chi_n(z/(z-1)) = M_n(z) = (1-z)A_n(z) + z^n (n <= 40).
  3. Exact integer Sturm sequences for M_n: n-2 negative roots, 1 root > 1, squarefree (3 <= n <= 63).
  4. Polylogarithm pole expansion agreement for Li_{-n}(-sigma).
  5. Analytic inequalities of Regimes A and B (64 <= n <= 3000), junction ordering, and Stirling bound.
  6. Exact sign alternation of M_n at rationalized test points for n in {64, 65, 100, 101, 128, 157, 200}.
"""
import math
import sys
from fractions import Fraction
from itertools import product


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def eulerian(n):
    E = [1]
    for m in range(2, n + 1):
        E = [
            (k + 1) * (E[k] if k < len(E) else 0) + (m - k) * (E[k - 1] if k >= 1 else 0)
            for k in range(m)
        ]
    return E


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += x
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return r


def ppow(a, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, a)
    return r


def peval(c, x):
    v = 0
    for a in reversed(c):
        v = v * x + a
    return v


def Mpoly(n):
    E = eulerian(n)
    return [E[k] - (E[k - 1] if k else 0) for k in range(n)]


def chi_closed(n):
    E = eulerian(n)
    c = [0] * n + [1]
    for i, a in enumerate(E):
        term = pmul(ppow([-1, 1], i), [0] * (n - 1 - i) + [1])
        c = padd(c, [-a * x for x in term])
    return c


def ordered_partitions(n):
    elems = list(range(n))
    res = []
    for labels in product(range(n), repeat=n):
        k = max(labels) + 1
        if set(labels) == set(range(k)):
            res.append(tuple(frozenset(e for e in elems if labels[e] == b) for b in range(k)))
    return res


def leq(x, y):
    i = 0
    for B in y:
        acc = set()
        while i < len(x) and acc != B:
            if not x[i] <= B:
                return False
            acc |= x[i]
            i += 1
        if acc != B:
            return False
    return i == len(x)


for n in range(1, 6):
    P = ordered_partitions(n)
    P.sort(key=lambda x: -len(x))
    mu = {}
    for x in P:
        mu[x] = -1 - sum(mu[z] for z in mu if z != x and leq(z, x))
    chi = [0] * (n + 1)
    chi[n] += 1
    for x in P:
        rk = n - len(x)
        chi[n - 1 - rk] += mu[x]
    if n >= 2:
        require(chi == chi_closed(n), f"chi_{n} brute force vs Thm 6.11(1)")
print("1. face-lattice chi_n matches closed form for n <= 5")

for n in range(3, 41):
    chi = chi_closed(n)
    tot = [0]
    for k, a in enumerate(chi):
        tot = padd(tot, [a * x for x in pmul([0] * k + [1], ppow([-1, 1], n - k))])
    require(tot == Mpoly(n), f"transform identity n={n}")
    E = eulerian(n)
    lhs = padd(pmul([1, -1], E), [0] * n + [1])
    require(lhs == Mpoly(n), f"M_n = (1-z)A_n + z^n at n={n}")
print("2. (z-1)^n chi_n(z/(z-1)) = (1-z)A_n(z) + z^n for 3 <= n <= 40")


def content(p):
    g = 0
    for a in p:
        g = math.gcd(g, a)
    return g or 1


def prem_neg(a, b):
    a = a[:]
    lb, db = b[-1], len(b) - 1
    s = abs(lb)
    while len(a) - 1 >= db and any(a):
        k = len(a) - 1 - db
        la = a[-1]
        a = [x * s for x in a]
        f = la * s // lb
        for i in range(len(b)):
            a[i + k] -= f * b[i]
        a.pop()
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    a = [-x for x in a]
    g = content(a)
    return [x // g for x in a]


def sturm(p):
    d = [i * p[i] for i in range(1, len(p))]
    seq = [p, d]
    while len(seq[-1]) > 1 or seq[-1][0] == 0:
        r = prem_neg(seq[-2], seq[-1])
        if r == [0]:
            break
        seq.append(r)
    return seq


def sgn(x):
    return (x > 0) - (x < 0)


def variations(vals):
    v = [s for s in vals if s]
    return sum(1 for i in range(1, len(v)) if v[i] != v[i - 1])


def at_inf(seq, neg):
    return [sgn(q[-1]) * ((-1) ** (len(q) - 1) if neg else 1) for q in seq]


for n in range(3, 64):
    p = Mpoly(n)
    seq = sturm(p)
    require(len(seq[-1]) == 1, f"M_{n} squarefree")
    vm = variations(at_inf(seq, True))
    v0 = variations([sgn(peval(q, 0)) for q in seq])
    v1 = variations([sgn(peval(q, 1)) for q in seq])
    vp = variations(at_inf(seq, False))
    require(vm - v0 == n - 2, f"M_{n}: {vm - v0} negative roots")
    require(v1 - vp == 1 and v0 - v1 == 0, f"M_{n}: positive roots")
print("3. Sturm: M_n has n-2 negative roots, 1 root > 1, all simple, 3 <= n <= 63")

for n in (1, 2, 5, 9):
    for sig in (0.05, 0.3, 0.7, 0.95):
        s = -Fraction(sig)
        direct = float(s * peval(eulerian(n), s) / (1 - s) ** (n + 1))
        L = -math.log(sig)
        poles = 2 * math.factorial(n) * sum(((L + 1j * math.pi * j) ** (-(n + 1))).real
                                            for j in range(1, 200001, 2))
        require(abs(direct - poles) <= 1e-6 * max(1.0, abs(direct)), f"pole n={n} s={sig}")
print("4. pole expansion of Li_{-n}(-sigma) agrees numerically")


def g_tail(beta):
    return math.exp(-beta) * (1 + 3 / (2 * (2 * beta - 1)))


for n in range(64, 3001):
    K = (n - 1) // 2
    m0 = max(m for m in range(0, K + 1) if (m + 1) ** 2 <= n / 4)
    require(1 <= m0 < K, f"regime split n={n}")
    for m in range(1, m0 + 1):
        logrho = (n / 2) * math.log1p(-1 / (m + 1) ** 2)
        require(logrho <= -2, f"A rho n={n} m={m}")
        logT = (n / 2) * (2 * math.log(m + 1) + m * math.log(m / (m + 2)))
        require(logT + math.log(1 - 2 * math.exp(-2)) > 0, f"A size n={n} m={m}")
    beta = 4 * n * (n + 1) / ((n + 1) ** 2 + 8 * n)
    require(beta > 0.5 and g_tail(beta) <= 0.038, f"B tail n={n}")
    log_phi = (
        math.log(4 * (1 - 0.038))
        + 0.5 * math.log(2 * math.pi)
        - math.log(math.pi)
        + math.log(n)
        + n * math.log(n / (n + 1))
        + (n / 2) * (math.log(n) - 2 - 2 * math.log(math.pi))
    )
    require(log_phi > 0, f"Stirling phi n={n}")
    le = (n / 2) * math.log(m0 / (m0 + 2))
    lb = -math.pi / math.tan((m0 + 2) * math.pi / (n + 1))
    require(le < lb, f"junction n={n}")
print("5. Regime A/B inequalities and Stirling bound hold for 64 <= n <= 3000")


def test_points(n):
    K = (n - 1) // 2
    pts = []
    for m in range(1, K + 1):
        if (m + 1) ** 2 <= n / 4:
            s = (m / (m + 2)) ** (n / 2)
        else:
            th = (m + 1) * math.pi / (n + 1)
            s = 1.0 if 2 * (m + 1) == n + 1 else math.exp(-math.pi / math.tan(th))
        pts.append((m, Fraction(s) if s < 1 else Fraction(1)))
    return pts


for n in (64, 65, 100, 101, 128, 157, 200):
    A = eulerian(n)
    M = Mpoly(n)
    prev = Fraction(0)
    signs_in, signs_out = [], []
    for m, s in test_points(n):
        require(s > prev, f"test points increasing n={n}")
        prev = s
        a = peval(A, -s)
        require(sgn(a) == (-1) ** m and (1 + s) * abs(a) > 1, f"A_n(-s) n={n} m={m}")
        signs_in.append(sgn(peval(M, -s)))
        signs_out.append(sgn(peval(M, -1 / s)))
    K = (n - 1) // 2
    require(signs_in == [(-1) ** m for m in range(1, K + 1)], f"inner signs n={n}")
    require(signs_out == [(-1) ** (n + m + 1) for m in range(1, K + 1)], f"outer signs n={n}")
print("6. exact sign alternation of M_n at test points for n in {64, 65, 100, 101, 128, 157, 200}")
print("ALL CHECKS PASSED")
