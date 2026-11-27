r"""Standalone verifier for the two-alternative line-metric distortion conjecture
of Abbaszadeh, Ansarifar, Latifian, and Seddighin (arXiv:2601.02095v1, Section 6).

Claim: for alpha in (0, 1], the rule f^tal_alpha has metric distortion exactly
M(alpha) = max((3 - alpha) / (1 + alpha), 1 + 2 * alpha) on two-alternative
elections in R^1 under mandatory elicitation, and no deterministic rule achieves
strictly smaller distortion.

Checks (exact rational arithmetic, stdlib only):
 1. Per-type suprema of g_t(x) = |x| - t|x - 1| match the closed forms.
 2. Worst-case distortion formula dist(a1) = max(1, R1, R2) against fine grid
    placements of agents for random small profiles.
 3. Coefficientwise key pairing inequality B_i(n) + B_j(sigma n) <= 0 at t = M(alpha).
 4. Exhaustive check min(dist(a1), dist(a2)) <= M(alpha) over all integer profiles
    with sum <= 14, plus exact tightness at (1, 1, 0, 0) and (0, 0, 1, 1).
"""
from fractions import Fraction as F
import itertools
import random


def require(cond, msg):
    if not cond:
        raise SystemExit("CHECK FAILED: " + msg)


def g(t, x):
    return abs(x) - t * abs(x - 1)


def type_sets(al):
    """Membership predicates for agent position x with a1 = 0, a2 = 1."""
    d1 = lambda x: abs(x)
    d2 = lambda x: abs(x - 1)
    return {
        "a1>a2": lambda x: d2(x) >= d1(x) > al * d2(x),
        "a2>a1": lambda x: d1(x) >= d2(x) > al * d1(x),
        "a1>>a2": lambda x: d1(x) <= al * d2(x),
        "a2>>a1": lambda x: d2(x) <= al * d1(x),
    }


def sup_closed(al, t):
    """Closed-form suprema of g_t over each type set (t >= 1)."""
    u = (1 - t * al) / (1 + al)
    out = {"a1>a2": (1 - t) / 2, "a1>>a2": (al - t) / (1 + al), "a2>>a1": F(1)}
    out["a2>a1"] = u if al == 1 else max(u, (1 - t * al) / (1 - al))
    return out


def ratios(al, n):
    """R1, R2 of the paper as exact fractions; None if denominator vanishes."""
    a = 1 / al
    n1, n2, n3, n4 = n
    res = []
    den = (a + 1) * n1 + 2 * n2 + 2 * a * n3
    res.append(None if den == 0 else ((a + 1) * n1 + 2 * a * n2 + 2 * n3 + (2 + 2 * a) * n4) / den)
    if al != 1:
        c = (1 + a) / (a - 1)
        den = (a + 1) * n1 + 2 * c * n2 + 2 * a * n3
        res.append(None if den == 0 else ((a + 1) * n1 + 2 * a * c * n2 + 2 * n3 + (2 + 2 * a) * n4) / den)
    return res


INF = None


def dist_a1(al, n):
    """Worst-case distortion of a1 = max(1, R1, R2); INF if SC(a2) can vanish with SC(a1) > 0."""
    rs = ratios(al, n)
    if any(r is None for r in rs):
        return INF if n[3] > 0 else F(1)
    return max([F(1)] + rs)


def A(al, t, n):
    s = sup_closed(al, t)
    return n[0] * s["a1>a2"] + n[1] * s["a2>a1"] + n[2] * s["a1>>a2"] + n[3] * s["a2>>a1"]


def M(al):
    return max((3 - al) / (1 + al), 1 + 2 * al)


def sig(n):
    return (n[1], n[0], n[3], n[2])


def main():
    rnd = random.Random(73)
    alphas = [F(k, 40) for k in range(1, 41)] + [F(1, 3), F(2, 5), F(1, 7), F(41, 99)]
    grid = [F(k, 120) for k in range(-600, 841)]

    # 1. Per-type suprema
    for al in [F(1, 5), F(1, 3), F(1, 2), F(7, 10), F(1)]:
        S = type_sets(al)
        pts = list(grid)
        if al != 1:
            pts.append(-al / (1 - al))
        pts += [al / (1 + al), F(1, 2), 1 / (1 + al), F(1)]
        if al != 1:
            pts.append(1 / (1 - al))
        for t in [F(1), F(3, 2), M(al), F(3), F(5)]:
            cl = sup_closed(al, t)
            for name, pred in S.items():
                vals = [g(t, x) for x in pts if pred(x)]
                if al == 1 and name in ("a1>a2", "a2>a1"):
                    require(len(vals) == 0, "normal type nonempty at alpha=1")
                    continue
                require(len(vals) > 0, "empty type set")
                require(max(vals) <= cl[name], "grid exceeds closed-form sup %s" % name)
                require(cl[name] - max(vals) <= F(1, 10), "closed-form sup not approached %s" % name)
    print("[1] per-type suprema OK")

    # 2. Worst-case distortion equivalence and grid tightness
    for _ in range(300):
        al = rnd.choice(alphas)
        n = tuple(rnd.randint(0, 4) for _ in range(4))
        if sum(n) == 0:
            continue
        d = dist_a1(al, n)
        if d is INF:
            require(A(al, F(10 ** 6), n) > 0, "INF case")
            continue
        require(A(al, d, n) <= 0, "A_t <= 0 at t = dist")
        if d > 1:
            require(A(al, d - F(1, 10 ** 6), n) > 0, "A_t > 0 just below dist")

    coarse = [F(k, 24) for k in range(-96, 145)]
    for al in [F(1, 4), F(1, 2), F(3, 4)]:
        S = type_sets(al)
        names = ["a1>a2", "a2>a1", "a1>>a2", "a2>>a1"]
        eps = F(1, 10 ** 6)
        brk = [-al / (1 - al), al / (1 + al), F(1, 2), 1 / (1 + al), F(1), 1 / (1 - al)]
        pts2 = coarse + [b + e for b in brk for e in (-eps, F(0), eps)]
        for n in [(1, 1, 0, 0), (0, 1, 1, 0), (1, 0, 1, 1), (0, 1, 2, 1), (2, 1, 0, 1)]:
            d = dist_a1(al, n)
            for t, sgn in [(d, 0), (d - F(1, 50), 1)]:
                tot = F(0)
                for k, name in enumerate(names):
                    if n[k]:
                        tot += n[k] * max(g(t, x) for x in pts2 if S[name](x))
                if sgn == 0:
                    require(tot <= 0, "placement beats dist bound")
                elif d > 1:
                    require(tot > 0, "dist bound not tight on grid")
    print("[2] worst-case distortion formula OK")

    # 3. Coefficientwise key pairing inequality at t = M(alpha)
    for al in alphas + [F(k, 1000) for k in range(1, 1001, 7)]:
        t = M(al)
        s = sup_closed(al, t)
        wvals = [(1 - t * al) / (1 + al)] + ([] if al == 1 else [(1 - t * al) / (1 - al)])
        for wi in wvals:
            for wj in wvals:
                coeffs = [s["a1>a2"] + wj, wi + s["a1>a2"], s["a1>>a2"] + 1, 1 + s["a1>>a2"]]
                require(all(c <= 0 for c in coeffs), "key inequality fails at alpha=%s" % al)
        require((3 - al) / (1 + al) >= (3 + al) / (1 + 3 * al), "auxiliary bound")
    print("[3] key pairing inequality B_i(n) + B_j(sigma n) <= 0 OK")

    # 4. Exhaustive check over all profiles with sum <= 14 and tightness witnesses
    for al in alphas:
        m = M(al)
        for n in itertools.product(range(15), repeat=4):
            if sum(n) == 0 or sum(n) > 14 or (al == 1 and n[0] + n[1] > 0):
                continue
            d1, d2 = dist_a1(al, n), dist_a1(al, sig(n))
            vals = [x for x in (d1, d2) if x is not INF]
            require(len(vals) > 0 and min(vals) <= m, "upper bound fails alpha=%s n=%s" % (al, n))
        e1 = min(dist_a1(al, (1, 1, 0, 0)), dist_a1(al, sig((1, 1, 0, 0))))
        e2 = min(dist_a1(al, (0, 0, 1, 1)), dist_a1(al, sig((0, 0, 1, 1))))
        if al != 1:
            require(e1 == (3 - al) / (1 + al), "tightness (1,1,0,0)")
        require(e2 == 1 + 2 * al, "tightness (0,0,1,1)")
        require(max(e2, e1 if al != 1 else F(0)) == m, "max equals M")
    print("[4] exhaustive small profiles & tightness at (1,1,0,0) and (0,0,1,1) OK")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
