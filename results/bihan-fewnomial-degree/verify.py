r"""Exact integer verification of the resolution of Bihan (arXiv:2611.34336v1),
first open case n = k = 3 and general 3D bound |deg F| <= floor((3V - 8) / 4).

Checks:
  1. Bihan's Theorem 1.3 degree formula is independent of the generic ray u
     and agrees with the signed spherical-triangle geodesic count.
  2. The Gauss-Bonnet identity 4*deg = 2*sum_v w_v - F+ + F-, the local
     winding bound 2*w_v <= p_v - 1, and |deg| <= floor((3V - 8) / 4) on all
     explicit witnesses and > 2000 random integer instances.
  3. Exact integer realizations of |deg F| = 0, 1, 2, 3 for N = 7 (proving
     D(3, 3) = {0, 1, 2, 3}) and extremal realizations for V = 8, 9, 10, 12.

Run: python -O -W error verify.py
"""
import random
from itertools import combinations


def require(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)


def sgn(x):
    return (x > 0) - (x < 0)


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def lifted_det(p, q, r, s):
    r"""det of the 4x4 matrix with columns (1,p), (1,q), (1,r), (1,s)."""
    sub = lambda x: (x[0] - p[0], x[1] - p[1], x[2] - p[2])
    return det3(sub(q), sub(r), sub(s))


def UA(A):
    return all(lifted_det(*[A[i] for i in q]) != 0
               for q in combinations(range(len(A)), 4))


def UC(C):
    return all(det3(*[C[i] for i in q]) != 0
               for q in combinations(range(len(C)), 3))


def outward_facets(A):
    r"""Facets of conv(A) (all triangles under (UA)), each ordered
    counterclockwise seen from outside."""
    out = []
    for s in combinations(range(len(A)), 3):
        sides = {sgn(lifted_det(*[A[i] for i in s], A[j]))
                 for j in range(len(A)) if j not in s}
        if len(sides) == 1:
            i, j, k = s
            out.append((i, j, k) if sides == {-1} else (i, k, j))
    return out


def in_cone(u, a, b, c):
    d = det3(a, b, c)
    return all(sgn(x) == sgn(d) for x in (det3(u, b, c), det3(a, u, c), det3(a, b, u)))


def degree_bihan(A, C, u):
    r"""Theorem 1.3 of arXiv:2611.34336v1 with n = 3."""
    tot = 0
    for f in outward_facets(A):
        s = tuple(sorted(f))
        if in_cone(u, *[C[t] for t in s]):
            i = next(j for j in range(len(A)) if j not in s)
            eps = sgn(lifted_det(*[A[t] for t in s], A[i]))
            tot += sgn(det3(*[C[t] for t in s])) * eps
    return -tot


def generic_u(C, cands):
    for u in cands:
        if all(det3(u, C[a], C[b]) != 0 for a, b in combinations(range(len(C)), 2)):
            yield u


def degree_checked(A, C):
    cands = [(7, -3, 11), (-5, 13, 2), (1, 1, -17), (3, 5, 7), (-11, -2, 9), (2, -19, -5)]
    vals = {degree_bihan(A, C, u) for u in generic_u(C, cands)}
    require(len(vals) == 1, "Theorem 1.3 value depends on u: %r" % (vals,))
    return vals.pop()


def angle_data(A, C):
    r"""Compute per-vertex winding numbers w_v, positive facet counts p_v,
    F+, F-, geodesic degree, V, and F."""
    F = outward_facets(A)
    verts = sorted({i for f in F for i in f})
    pos = {f: sgn(det3(*[C[t] for t in f])) for f in F}
    w, p = {}, {}
    for v in verts:
        nxt = {}
        p[v] = 0
        for f in F:
            if v in f:
                r = f.index(v)
                a, b = f[(r + 1) % 3], f[(r + 2) % 3]
                nxt[a] = b
                p[v] += pos[f] > 0
        c = C[v]
        ref = next(r for r in [(1, 2, 3), (5, -7, 2), (-3, 11, 13), (17, 1, -4), (2, 9, -23)]
                   if all(det3(c, C[a], r) != 0 for a in nxt))
        wind = 0
        for a, b in nxt.items():
            s = sgn(det3(c, C[a], C[b]))
            require(s != 0, "degenerate link step")
            if sgn(det3(c, C[a], ref)) == s and sgn(det3(c, ref, C[b])) == s:
                wind += s
        start = next(iter(nxt))
        x = nxt[start]
        n = 1
        while x != start:
            x = nxt[x]
            n += 1
        require(n == len(nxt), "link is not a single cycle")
        w[v] = wind
    Fp = sum(1 for f in F if pos[f] > 0)
    Fm = len(F) - Fp
    u = next(generic_u(C, [(7, -3, 11), (-5, 13, 2), (1, 1, -17)]))
    dgeo = sum(pos[f] for f in F if in_cone(u, *[C[t] for t in f]))
    return w, p, Fp, Fm, dgeo, len(verts), len(F)


def check_instance(A, C, expect=None, label=""):
    require(UA(A) and UC(C), label + ": (UA)/(UC) fail")
    d = degree_checked(A, C)
    w, p, Fp, Fm, dgeo, V, F = angle_data(A, C)
    require(F == 2 * V - 4, label + ": not a simplicial 3-polytope")
    require(d == dgeo, label + ": Theorem 1.3 value differs from geodesic count")
    require(4 * d == 2 * sum(w.values()) - Fp + Fm, label + ": angle identity fails")
    require(all(2 * w[v] <= p[v] - 1 for v in w), label + ": vertex bound fails")
    require(4 * d <= F + Fp - V, label + ": 4d <= F + F+ - V fails")
    require(4 * abs(d) <= 3 * V - 8, label + ": |deg| <= (3V-8)/4 fails")
    if expect is not None:
        require(abs(d) == expect, label + ": expected |deg| = %d, got %d" % (expect, d))
    return d, V


# |deg F| = 0..3 with N = 7 monomials (n = k = 3)
N7 = {
    3: ([(3, 1, 3), (11, 4, -1), (-4, 2, 6), (-5, 3, -5), (-10, -3, 9), (0, -7, 2), (3, 2, -7)],
        [(-13, 15, -22), (10, -25, 14), (-20, 0, 23), (11, 17, -22), (-8, -26, 13), (9, 28, 5), (-24, -15, 10)]),
    2: ([(-2, -8, 0), (-7, -4, 4), (4, -3, 0), (3, 0, 7), (8, -1, -7), (-1, 8, 7), (7, 7, -3)],
        [(-12, 9, -26), (5, 21, 21), (19, -5, 23), (-8, -26, 11), (-19, 21, -10), (26, -1, -14), (-30, 1, 2)]),
    1: ([(-2, 8, 6), (-16, -11, -1), (-3, 1, 1), (13, -7, -2), (12, 4, 4), (-3, -10, 1), (1, -7, -4)],
        [(-2, -30, -3), (6, 2, -29), (-13, 21, 17), (-20, 18, -12), (16, -19, 17), (-25, -3, 17), (2, 8, -29)]),
    0: ([(1, -1, 4), (1, -3, 2), (8, 6, -4), (-8, -4, 0), (-14, -1, -7), (-4, -3, -2), (2, 6, -1)],
        [(26, -13, 7), (23, 2, -19), (-26, -13, 6), (-29, -6, -5), (24, 9, 16), (-15, -2, 26), (18, -15, 18)]),
}

# Extremal realizations attaining floor((3V - 8) / 4) for V = 8, 9, 10, 12
SHARP = [
    (4, [(-3, 2, 3), (11, -5, -5), (-2, 6, 2), (-10, 4, -4), (2, -2, 4), (4, -3, -9), (6, -1, -7), (-1, 5, -3)],
        [(23, 8, 17), (16, -25, -2), (-15, 26, 6), (-4, -30, -2), (-15, -12, -23), (7, 28, 8), (-16, -25, 5), (19, 13, -19)]),
    (4, [(8, 2, 5), (-1, 1, 13), (-13, 0, -9), (-8, -8, -2), (-3, 2, 7), (0, -10, 0), (1, 3, -5), (0, -2, -8), (2, -9, 4)],
        [(-4, 24, 18), (-4, -29, -8), (-5, -18, 24), (-5, 30, 0), (12, 24, -12), (-27, -12, 5), (-21, -14, -16), (28, -2, -11), (19, -19, 14)]),
    (5, [(2, -7, -4), (4, -6, -3), (-1, 4, 1), (9, 14, -6), (5, -11, 4), (3, 9, -2), (9, -6, 11), (7, -1, -3), (1, 0, 6), (5, 13, 13)],
        [(24, 17, 1), (11, 7, -27), (1, 27, -14), (-29, 8, -2), (-21, 22, 1), (24, -18, -2), (21, 0, -22), (-7, -16, 24), (-10, -28, 3), (2, -2, 30)]),
    # Perturbed icosahedron mapped to its Galois conjugate (great icosahedron {3, 5/2}, density 7)
    (7, [(-1, 1002, 1625), (991, 1623, -2), (1610, -4, 994), (2, 1006, -1620), (1003, -1610, -6), (-1609, -2, 991),
         (-3, -996, 1617), (-1004, 1621, -4), (1611, -5, -995), (-5, -1005, -1627), (-1009, -1621, -3), (-1622, -4, -1000)],
        [(1, 997, -610), (997, -622, -3), (-615, 0, 991), (2, 1004, 614), (995, 617, -7), (619, 0, 1009),
         (-9, -999, -625), (-1000, -616, 0), (-612, 1, -1004), (6, -994, 614), (-1008, 617, -9), (620, 3, -1009)]),
]


def main():
    seen = set()
    for e, (A, C) in N7.items():
        require(len(A) == 7 and len(C) == 7, "N != 7")
        d, V = check_instance(A, C, e, "N7 deg %d" % e)
        seen.add(abs(d))
    require(seen == {0, 1, 2, 3}, "D(3,3) values")
    print("N=7 (n=k=3): |deg F| = 0,1,2,3 realized; bound floor((3*7-8)/4) = 3 < 4 (Bihan Thm 2)")

    for e, A, C in SHARP:
        d, V = check_instance(A, C, e, "sharp V=%d" % len(A))
        require(abs(d) == (3 * V - 8) // 4, "not extremal")
        print("V=%d: |deg F| = %d = floor((3V-8)/4)" % (V, abs(d)))

    rng = random.Random(20261126)
    count = 0
    for N in range(4, 10):
        for _ in range(500 if N < 8 else 250):
            A = [tuple(rng.randint(-20, 20) for _ in range(3)) for _ in range(N)]
            C = [tuple(rng.randint(-20, 20) for _ in range(3)) for _ in range(N)]
            if not (UA(A) and UC(C)):
                continue
            check_instance(A, C, None, "random N=%d" % N)
            count += 1
    require(count > 2000, "too few random instances")
    print("random instances: %d, identity and bound hold" % count)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
