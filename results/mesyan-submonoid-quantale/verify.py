r"""Standalone verification for Mesyan, arXiv:2611.31109v1, Question 34.

Question 34 (verbatim):
  "For a domain R, is R being commutative equivalent to M(R) being commutative?
   (See Proposition 22 (3) and subsequent comments.) More broadly, for which
   (semi)rings R is M(R) commutative?"

Here M(R) is the quantale of additive submonoids of the (possibly nonunital)
semiring R, with S * T = { sum s_i t_i } (Definition 4).

Answer to the first part:
  - Ring domains: YES (Theorem A, proved in PROOF.md and Lean 4).
  - Semiring domains: NO (Theorem B, 14-element counterexample R14).

Checks:
  1. The 14-element semiring R14 = {0, oo} U (Z_3 x Z_2^2) with twist
     beta(g, h) = (-1)^(g_1 * h_2) satisfies all semiring axioms, has no
     zero divisors, is noncommutative, and has commutative M(R14) over all
     90 additive submonoids.
  2. Example 6 of Mesyan, X(F_3), is noncommutative with commutative M (28
     subgroups), but has zero divisors (showing the domain hypothesis is
     essential in Theorem A).
  3. The mechanism of Theorem A on quantum planes F_p<x, y> / (yx - q xy)
     for p in {3, 5, 7}: <yx> = <xy>, yet <y(x + x^2)> != <(x + x^2)y>.

Run with: python -O -W error verify.py
"""
import itertools
import sys


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


# ---------- 1. The 14-element semiring domain R14 ----------
ZERO, INF = "0", "oo"
G = [(0, 0), (0, 1), (1, 0), (1, 1)]
R14 = [ZERO, INF] + [(i, g) for g in G for i in range(3)]


def gadd(g, h):
    return ((g[0] + h[0]) % 2, (g[1] + h[1]) % 2)


def beta(g, h):
    return 2 if (g[0] * h[1]) % 2 else 1  # -1 = 2 in Z_3


def add14(x, y):
    if x == ZERO:
        return y
    if y == ZERO:
        return x
    if x == INF or y == INF or x[1] != y[1]:
        return INF
    return ((x[0] + y[0]) % 3, x[1])


def mul14(x, y):
    if x == ZERO or y == ZERO:
        return ZERO
    if x == INF or y == INF:
        return INF
    return ((x[0] * y[0] * beta(x[1], y[1])) % 3, gadd(x[1], y[1]))


def check_semiring(R, add, mul, zero):
    for x in R:
        require(add(zero, x) == x, "0 is additive identity")
        require(mul(zero, x) == zero and mul(x, zero) == zero, "0 is absorbing")
        for y in R:
            require(add(x, y) == add(y, x), "+ commutative")
            for z in R:
                require(add(add(x, y), z) == add(x, add(y, z)), "+ associative")
                require(mul(mul(x, y), z) == mul(x, mul(y, z)), "* associative")
                require(mul(x, add(y, z)) == add(mul(x, y), mul(x, z)), "left distributive")
                require(mul(add(x, y), z) == add(mul(x, z), mul(y, z)), "right distributive")


def closure(gens, add, zero):
    S = {zero} | set(gens)
    while True:
        new = {add(a, b) for a in S for b in S} - S
        if not new:
            return frozenset(S)
        S |= new


def all_submonoids(R, add, zero):
    cyc = {closure([r], add, zero) for r in R}
    subs = set(cyc) | {frozenset([zero])}
    frontier = set(subs)
    while frontier:
        nxt = set()
        for A in frontier:
            for C in cyc:
                J = closure(A | C, add, zero)
                if J not in subs:
                    subs.add(J)
                    nxt.add(J)
        frontier = nxt
    return subs


def quantale_commutative(R, add, mul, zero):
    subs = sorted(all_submonoids(R, add, zero), key=lambda s: (len(s), sorted(map(str, s))))
    for S in subs:
        for T in subs:
            ST = closure({mul(s, t) for s in S for t in T}, add, zero)
            TS = closure({mul(t, s) for s in S for t in T}, add, zero)
            if ST != TS:
                return False, len(subs)
    return True, len(subs)


require(len(R14) == 14, "|R14| = 14")
check_semiring(R14, add14, mul14, ZERO)
for x in R14:
    for y in R14:
        if x != ZERO and y != ZERO:
            require(mul14(x, y) != ZERO, "R14 has no zero divisors")

a, b = (1, (1, 0)), (1, (0, 1))
require(mul14(a, b) != mul14(b, a), "R14 noncommutative")
require(mul14(a, b) == (2, (1, 1)) and mul14(b, a) == (1, (1, 1)), "witness products")
ok, n14 = quantale_commutative(R14, add14, mul14, ZERO)
require(ok and n14 == 90, "M(R14) commutative over 90 submonoids")

r = (1, (0, 0))
require(
    add14(add14(add14(r, r), r), r) == r and add14(add14(r, r), r) != r,
    "R14 lies outside Prop. 22(3)",
)
print("R14: semiring, domain, noncommutative; M(R14) commutative over", n14, "submonoids")

# ---------- 2. Example 6, X(F_3): domain hypothesis is essential ----------
X = list(itertools.product(range(3), repeat=3))


def addX(u, v):
    return tuple((s + t) % 3 for s, t in zip(u, v))


def mulX(u, v):
    return (0, 0, (u[0] * v[1] - u[1] * v[0]) % 3)


check_semiring(X, addX, mulX, (0, 0, 0))
require(mulX((1, 0, 0), (0, 1, 0)) != mulX((0, 1, 0), (1, 0, 0)), "X(F_3) noncommutative")
okX, nX = quantale_commutative(X, addX, mulX, (0, 0, 0))
require(okX and nX == 28, "M(X(F_3)) commutative over 28 subgroups")
require(mulX((1, 0, 0), (1, 0, 0)) == (0, 0, 0), "X(F_3) has zero divisors")
print("X(F_3): M commutative (28 subgroups), but x*x = 0 (not a domain)")

# ---------- 3. Theorem A mechanism on quantum planes F_p<x, y> / (yx - q xy) ----------
def qmul(u, v, q, p):
    out = {}
    for (i, j), c in u.items():
        for (k, l), d in v.items():
            key = (i + k, j + l)
            out[key] = (out.get(key, 0) + c * d * pow(q, j * k, p)) % p
    return {k: c for k, c in out.items() if c}


def proportional(u, v, p):
    return any({k: (c * m) % p for k, c in v.items() if (c * m) % p} == u for m in range(p))


for p in (3, 5, 7):
    for q in range(2, p):
        xx = {(1, 0): 1, (2, 0): 1}
        yy = {(0, 1): 1}
        require(
            not proportional(qmul(yy, xx, q, p), qmul(xx, yy, q, p), p),
            "y(x + x^2) not in F_p (x + x^2)y",
        )
        require(
            proportional(qmul(yy, {(1, 0): 1}, q, p), qmul({(1, 0): 1}, yy, q, p), p),
            "yx in F_p xy",
        )
print("Quantum planes p in {3, 5, 7}: <yx> = <xy> yet <y(x + x^2)> != <(x + x^2)y>")
print("ALL CHECKS PASSED")
