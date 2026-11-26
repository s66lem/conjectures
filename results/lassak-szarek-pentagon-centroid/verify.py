r"""Exact Q(sqrt(5)) verifier for the disproof of Lassak-Szarek's conjecture:
    d_BM^cen(F, T) < eta = (7 - sqrt(5))/2
for an affine-regular pentagon F and a triangle T (arXiv:2611.21947v1).

All decisive checks use exact arithmetic in Q(sqrt(5)); floating-point math is
used only to cross-check the regular-pentagon coordinates and the analytic
rotated equilateral triangle bound (1 + cos 24 deg) / cos 36 deg.
"""
import math
from fractions import Fraction as Fr


def require(cond, msg="check failed"):
    if not cond:
        raise SystemExit(f"CHECK FAILED: {msg}")


class Q5:
    """Exact element a + b*sqrt(5) with rational a, b."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(self, other):
        o = q(other)
        return Q5(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-q(other))

    def __rsub__(self, other):
        return q(other) - self

    def __mul__(self, other):
        o = q(other)
        return Q5(self.a * o.a + 5 * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def inv(self):
        n = self.a * self.a - 5 * self.b * self.b
        require(n != 0, "division by zero in Q(sqrt(5))")
        return Q5(self.a / n, -self.b / n)

    def __truediv__(self, other):
        return self * q(other).inv()

    def __rtruediv__(self, other):
        return q(other) * self.inv()

    def sign(self):
        sa = (self.a > 0) - (self.a < 0)
        sb = (self.b > 0) - (self.b < 0)
        if sa == sb or sb == 0:
            return sa
        if sa == 0:
            return sb
        return sa if self.a * self.a > 5 * self.b * self.b else sb

    def __eq__(self, other):
        o = q(other)
        return self.a == o.a and self.b == o.b

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(5)


def q(x):
    return x if isinstance(x, Q5) else Q5(x)


R5 = Q5(0, 1)
PHI = (1 + R5) / 2
ETA = (7 - R5) / 2
C72 = (R5 - 1) / 4

# Affine-regular pentagon F' = L(F_reg) with L(x, y) = (x, y / sin(72 deg)).
F = [
    (Q5(1), Q5(0)),
    (C72, Q5(1)),
    (-PHI / 2, 1 / PHI),
    (-PHI / 2, -1 / PHI),
    (C72, Q5(-1)),
]

# Rational-vertex certificate triangle T0 (centroid 0).
T0 = [
    (q(Fr(112, 200)), q(Fr(127, 200))),
    (q(Fr(-161, 200)), q(Fr(35, 200))),
    (q(Fr(49, 200)), q(Fr(-162, 200))),
]
LAM = Fr(19, 8)


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def inside(poly, x):
    n = len(poly)
    return all(cross(poly[i], poly[(i + 1) % n], x).sign() >= 0 for i in range(n))


def gauge(poly, x):
    n = len(poly)
    vals = []
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        nx, ny = b[1] - a[1], a[0] - b[0]
        h = nx * a[0] + ny * a[1]
        require(h.sign() > 0, "origin not in interior")
        vals.append((nx * x[0] + ny * x[1]) / h)
    m = vals[0]
    for v in vals[1:]:
        if (v - m).sign() > 0:
            m = v
    return m


def bary(tri, p):
    a, b, c = tri
    d = cross(a, b, c)
    return (cross(p, b, c) / d, cross(a, p, c) / d, cross(a, b, p) / d)


def check_pentagon():
    for i in range(5):
        require(cross(F[i], F[(i + 1) % 5], F[(i + 2) % 5]).sign() > 0, "pentagon convexity")
    s72 = math.sin(2 * math.pi / 5)
    for k, (x, y) in enumerate(F):
        t = 2 * math.pi * k / 5
        require(abs(float(x) - math.cos(t)) < 1e-12, "pentagon x coordinate")
        require(abs(float(y) - math.sin(t) / s72) < 1e-12, "pentagon y coordinate")
    # Determinant-1 cyclic symmetry matrix A = [[c, -(1-c^2)], [1, c]] fixing cen(F') = 0.
    a11, a12, a21, a22 = C72, -(1 - C72 * C72), Q5(1), C72
    for k in range(5):
        x, y = F[k]
        require((a11 * x + a12 * y, a21 * x + a22 * y) == F[(k + 1) % 5], f"symmetry k={k}")
    require(a11 * a22 - a12 * a21 == 1, "det(A) = 1")
    require(((a11 - 1) * (a22 - 1) - a12 * a21).sign() != 0, "det(A - I) != 0")


def check_certificate():
    require(sum((v[0] for v in T0), Q5(0)) == 0, "T0 centroid x = 0")
    require(sum((v[1] for v in T0), Q5(0)) == 0, "T0 centroid y = 0")
    require(cross(*T0).sign() > 0, "T0 nondegenerate ccw")
    for v in T0:
        require(inside(F, v), "T0 vertex in F'")
    lt = [(LAM * x, LAM * y) for x, y in T0]
    for p in F:
        require(inside(lt, p), "F' vertex in (19/8)*T0")
    require((ETA - LAM).sign() > 0, "19/8 < (7 - sqrt(5))/2")

    # Verify explicit convex combination weights used in Lean 4.
    for v in T0:
        found = False
        for i in range(1, 4):
            w = bary((F[0], F[i], F[i + 1]), v)
            if all(c.sign() >= 0 for c in w):
                require(sum(w, Q5(0)) == 1, "T0 weights sum to 1")
                px = w[0] * F[0][0] + w[1] * F[i][0] + w[2] * F[i + 1][0]
                py = w[0] * F[0][1] + w[1] * F[i][1] + w[2] * F[i + 1][1]
                require((px, py) == v, "T0 convex combination exact match")
                found = True
                break
        require(found, "T0 vertex in fan of F'")
    for p in F:
        w = bary(lt, p)
        require(all(c.sign() >= 0 for c in w) and sum(w, Q5(0)) == 1, "F' weights nonnegative & sum to 1")
        px = w[0] * lt[0][0] + w[1] * lt[1][0] + w[2] * lt[2][0]
        py = w[0] * lt[0][1] + w[1] * lt[1][1] + w[2] * lt[2][1]
        require((px, py) == p, "F' convex combination exact match")


def check_authors_eta():
    """Verify that Lassak's configuration [L 24c] gives exactly eta = (7 - sqrt(5))/2."""
    p1, p2 = F[1], F[2]
    t = (Q5(Fr(-1, 2)) - p1[0]) / (p2[0] - p1[0])
    y = p1[1] + t * (p2[1] - p1[1])
    ta = [(Q5(1), Q5(0)), (Q5(Fr(-1, 2)), y), (Q5(Fr(-1, 2)), -y)]
    for v in ta:
        require(inside(F, v), "Lassak triangle inside F'")
    lam = None
    for p in F:
        g = gauge(ta, p)
        if lam is None or (g - lam).sign() > 0:
            lam = g
    require(lam == ETA, "Lassak configuration equals eta")


def check_equilateral():
    """Verify the analytic rotated equilateral triangle bound (1 + cos 24 deg) / cos 36 deg."""
    c, s, r = math.cos, math.sin, math.radians
    pent = [(c(r(72 * k)), s(r(72 * k))) for k in range(5)]
    rad = c(r(36)) / c(r(12))
    eq = [(rad * c(r(a)), rad * s(r(a))) for a in (48, 168, 288)]

    def g_float(poly, x):
        n = len(poly)
        vals = []
        for i in range(n):
            a, b = poly[i], poly[(i + 1) % n]
            nx, ny = b[1] - a[1], a[0] - b[0]
            vals.append((nx * x[0] + ny * x[1]) / (nx * a[0] + ny * a[1]))
        return max(vals)

    inner = max(g_float(pent, v) for v in eq)
    outer = max(g_float(eq, p) for p in pent)
    lam_star = (1 + c(r(24))) / c(r(36))
    require(abs(inner - 1.0) < 1e-12, "equilateral inner gauge = 1")
    require(abs(outer - lam_star) < 1e-12, "equilateral outer gauge = lam_star")
    require(lam_star < float(LAM) < float(ETA), "lam_star < 19/8 < eta")


def main():
    check_pentagon()
    check_certificate()
    check_authors_eta()
    check_equilateral()
    lam_star = (1 + math.cos(math.radians(24))) / math.cos(math.radians(36))
    print(f"d_BM^cen(F, T) <= {lam_star:.6f} < 19/8 = {float(LAM):.6f} < eta = {float(ETA):.6f}")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
