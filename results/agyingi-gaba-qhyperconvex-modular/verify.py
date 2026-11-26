r"""Exact checks for the resolution of Question q:modular of arXiv:2611.32417.

Coordinatewise order on [0,1]^3 is the reverse of the specialization order <=_q
of the quasi-metric q(g,h) = max_k(h_k - g_k)^+. Both Y and S are fixed sets of
monotone, deflationary, idempotent, q-nonexpansive retractions rho:

  Y = {g in [0,1]^3 : two largest coordinates equal}  (Isbell hull, Lemma lem:Y)
  S = {g in [0,1]^3 : g_3 <= max(g_1, g_2)}           (bounded q-hyperconvex space)

Under <=_q: meet_q(g, h) = max(g, h) and join_q(g, h) = rho(min(g, h)).
Stdlib only; all arithmetic uses exact Fractions.
"""
import itertools
import random
from fractions import Fraction as F


def require(cond, msg):
    if not cond:
        raise SystemExit("FAILED: " + msg)


def cmax(g, h):
    return tuple(max(a, b) for a, b in zip(g, h))


def cmin(g, h):
    return tuple(min(a, b) for a, b in zip(g, h))


def q(g, h):
    return max(max(b - a, F(0)) for a, b in zip(g, h))


def spec_le(g, h):
    # g <=_q h  <=>  q(g, h) == 0  <=>  h <=_coord g
    return q(g, h) == 0


def in_Y(g):
    s = sorted(g)
    return s[1] == s[2]


def rho_Y(g):
    return tuple(min(g[k], max(g[j] for j in range(3) if j != k)) for k in range(3))


def in_S(g):
    return g[2] <= max(g[0], g[1])


def rho_S(g):
    return (g[0], g[1], min(g[2], max(g[0], g[1])))


def v(g):
    return max(g) + min(g)


def grid(N):
    return list(itertools.product([F(i, N) for i in range(N + 1)], repeat=3))


# 1. rho_Y and rho_S: retraction, monotone, deflationary, q-nonexpansive.
for N in (2, 3, 4):
    P = grid(N)
    for name, rho, inn in (("Y", rho_Y, in_Y), ("S", rho_S, in_S)):
        for g in P:
            r = rho(g)
            require(inn(r) and spec_le(g, r), f"rho_{name} lands in set above g under <=_q")
            require((r == g) == inn(g), f"rho_{name} fixes exactly the set")
            require(rho(r) == r, f"rho_{name} idempotent")
        for g in P:
            for h in P:
                require(q(rho(g), rho(h)) <= q(g, h), f"rho_{name} nonexpansive")
                if spec_le(g, h):
                    require(spec_le(rho(g), rho(h)), f"rho_{name} monotone under <=_q")

# 2. Lattice operations under <=_q: meet_q = cmax and join_q = rho(cmin).
for N in (2, 3, 4):
    P = grid(N)
    for name, rho, inn in (("Y", rho_Y, in_Y), ("S", rho_S, in_S)):
        L = [g for g in P if inn(g)]
        for g in L:
            for h in L:
                m_q, j_q = cmax(g, h), rho(cmin(g, h))
                require(inn(m_q) and inn(j_q), f"{name} closed under meet_q/join_q")
                lb = [x for x in L if spec_le(x, g) and spec_le(x, h)]
                ub = [x for x in L if spec_le(g, x) and spec_le(h, x)]
                require(all(spec_le(x, m_q) for x in lb), f"{name} meet_q is glb")
                require(all(spec_le(j_q, x) for x in ub), f"{name} join_q is lub")


# 3. Theorem A: v = max + min is a strictly antimonotone valuation on (Y, <=_q).
def key_identity(g, h):
    return max(min(a, b) for a, b in zip(g, h)) == min(max(g), max(h))


rng = random.Random(62)
samples = [g for g in grid(6) if in_Y(g)]
for _ in range(400):
    t, u = F(rng.randint(0, 997), 997), F(rng.randint(0, 997), 997)
    t, u = max(t, u), min(t, u)
    k = rng.randrange(3)
    g = [t, t, t]
    g[k] = u
    samples.append(tuple(g))
for g in samples:
    for h in samples[::7]:
        require(key_identity(g, h), "max of min = min of max on Y")
        require(v(cmax(g, h)) + v(rho_Y(cmin(g, h))) == v(g) + v(h), "valuation identity on Y")
        if spec_le(g, h) and g != h:
            require(v(h) < v(g), "v strictly antimonotone on (Y, <=_q)")

# 4. Modular law on (Y, <=_q), exhaustively on grids.
for N in (2, 3, 4, 5):
    L = [g for g in grid(N) if in_Y(g)]
    for a in L:
        for c in L:
            if not spec_le(a, c):
                continue
            for b in L:
                # a join_q (b meet_q c) == (a join_q b) meet_q c
                lhs = rho_Y(cmin(a, cmax(b, c)))
                rhs = cmax(rho_Y(cmin(a, b)), c)
                require(lhs == rhs, f"modular law on (Y, <=_q) grid N={N}")

# 5. (Y, <=_q) is not distributive: explicit M3 sublattice.
z, one = (F(0),) * 3, (F(1),) * 3
E = [(F(0), F(1), F(1)), (F(1), F(0), F(1)), (F(1), F(1), F(0))]
for x, y in itertools.combinations(E, 2):
    require(cmax(x, y) == one and rho_Y(cmin(x, y)) == z, "M3 in (Y, <=_q)")
require(all(in_Y(x) for x in E + [z, one]), "M3 elements in Y")

# 6. Theorem B: explicit N5 sublattice of (S, <=_q).
qt = F(1, 4)
t = (qt, qt, qt)
c = (F(0), qt, qt)
a = (F(0), qt, F(0))
b = (qt, F(0), qt)
o = z
require(all(in_S(x) for x in (t, c, a, b, o)), "N5 elements in S")
require(spec_le(c, a) and c != a, "c <_q a")
require(not spec_le(c, b) and not spec_le(b, c), "b incomparable to c")
require(not spec_le(a, b) and not spec_le(b, a), "b incomparable to a")
require(cmax(c, b) == t and cmax(a, b) == t, "c meet_q b = a meet_q b = t")
require(rho_S(cmin(c, b)) == o and rho_S(cmin(a, b)) == o, "c join_q b = a join_q b = o")
# Modular law fails: c join_q (b meet_q a) = c != a = (c join_q b) meet_q a.
lhs_N5 = rho_S(cmin(c, cmax(b, a)))
rhs_N5 = cmax(rho_S(cmin(c, b)), a)
require(lhs_N5 == c and rhs_N5 == a and lhs_N5 != rhs_N5, "modular law fails in (S, <=_q)")


# 7. q-hyperconvexity witnesses for S and Y on 12,000 random compatible double-ball families.
def double_ball_box(fam):
    L = [max([F(0)] + [y[k] - s for y, r, s in fam]) for k in range(3)]
    U = [min([F(1)] + [y[k] + r for y, r, s in fam]) for k in range(3)]
    return L, U


def witness_S(U):
    return (U[0], U[1], min(U[2], max(U[0], U[1])))


def witness_Y(U):
    return rho_Y(U)


pool = [g for g in grid(8)]
for name, inn, wit in (("S", in_S, witness_S), ("Y", in_Y, witness_Y)):
    pts = [g for g in pool if inn(g)]
    tested = 0
    while tested < 6000:
        fam = [
            (rng.choice(pts), F(rng.randint(0, 8), 8), F(rng.randint(0, 8), 8))
            for _ in range(rng.randint(1, 4))
        ]
        if not all(q(y1, y2) <= r1 + s2 for y1, r1, _ in fam for y2, _, s2 in fam):
            continue
        tested += 1
        L, U = double_ball_box(fam)
        require(all(L[k] <= U[k] for k in range(3)), "compatible family gives nonempty box")
        w = wit(U)
        require(inn(w), f"witness in {name}")
        require(all(L[k] <= w[k] <= U[k] for k in range(3)), f"witness of {name} in box")
        require(
            all(q(y, w) <= r and q(w, y) <= s for y, r, s in fam),
            f"witness of {name} lies in all double balls",
        )

print("ALL CHECKS PASSED")
