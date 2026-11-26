"""Checks for the proof of the A401897 asymptotic (see NOTES.md). Stdlib only."""
from math import gcd, isqrt, pi, sqrt, log

OEIS_DATA = [1, 5, 7, 10, 13, 17, 22, 24, 29, 32, 37, 40, 45, 44, 55, 56, 61, 63, 71, 72, 74, 81, 85,
             87, 96, 97, 102, 108, 109, 116, 121, 125, 123, 133, 135, 137, 148, 145, 155, 159, 164,
             162, 169, 176, 179, 181, 193, 190, 198, 198, 205, 211, 215, 217, 226, 227, 236, 236]


def require(cond, msg):
    if not cond:
        raise SystemExit('FAILED: ' + msg)


def wedge(nmax_norm):
    pts = [(a, b) for a in range(isqrt(nmax_norm) + 1) for b in range(a + 1)
           if 0 < a * a + b * b <= nmax_norm]
    pts.sort(key=lambda p: (p[0] ** 2 + p[1] ** 2, p[1]))
    return pts


def a_direct(z):
    """Definition: w with N(w) < N(z) and gcd(Re(z-w), Im(z-w)) = 1."""
    u, v = z; N = u * u + v * v; r = isqrt(N)
    return sum(1 for x in range(-r, r + 1) for y in range(-r, r + 1)
               if x * x + y * y < N and gcd(u - x, v - y) == 1)


def mobius(n):
    m, res, p = n, 1, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            res = -res
        p += 1
    return -res if m > 1 else res


def a_mobius(z):
    """Identity (2) of NOTES: a(z) = sum_{d < 2R} mu(d) L(z, d), L = #{u : |d u - z|^2 < N}."""
    u, v = z; N = u * u + v * v; tot = 0; d = 1
    while d * d < 4 * N:
        mu = mobius(d)
        if mu:
            R = isqrt(N) + 1
            L = sum(1 for x in range(-(2 * R) // d - 1, (2 * R) // d + 2)
                    for y in range(-(2 * R) // d - 1, (2 * R) // d + 2)
                    if (d * x - u) ** 2 + (d * y - v) ** 2 < N)
            tot += mu * L
        d += 1
    return tot


# 1. Definition reproduces the published terms (fixes the indexing and tie order).
W = wedge(400)
require([a_direct(W[i]) for i in range(len(OEIS_DATA))] == OEIS_DATA, 'OEIS data mismatch')

# 2. Möbius identity (2) agrees with the definition.
for z in W[:120]:
    require(a_mobius(z) == a_direct(z), 'Mobius identity at %s' % (z,))

# 3. Lemma 1 (Gauss bound) on many open/closed disks with rational centres z/d, radius R/d.
for z in W[:150]:
    u, v = z; N = u * u + v * v
    for d in range(1, 2 * isqrt(N) + 3):
        r = sqrt(N) / d; B = 2 * isqrt(N) // d + 3
        for strict in (True, False):
            c = sum(1 for x in range(-B, B + 1) for y in range(-B, B + 1)
                    if ((d * x - u) ** 2 + (d * y - v) ** 2 < N if strict
                        else (d * x - u) ** 2 + (d * y - v) ** 2 <= N))
            require(abs(c - pi * r * r) <= pi * (sqrt(2) * r + 0.5) + 1e-9, 'Lemma 1 at %s d=%d' % (z, d))

# 4. Proposition A: |a(z) - 6N/pi| <= pi*R*(2 + sqrt2 + sqrt2*log(2R)) for R >= 1.
W2 = wedge(1300)
for z in W2:
    N = z[0] ** 2 + z[1] ** 2; R = sqrt(N)
    require(abs(a_direct(z) - 6 * N / pi) <= pi * R * (2 + sqrt(2) + sqrt(2) * log(2 * R)), 'Prop A at %s' % (z,))

# 5. Proposition B: |n - pi N/8| <= 2 sqrt(N) for the n-th wedge point of norm N.
W3 = wedge(40000)
for i, z in enumerate(W3):
    N = z[0] ** 2 + z[1] ** 2
    require(abs((i + 1) - pi * N / 8) <= 2 * sqrt(N), 'Prop B at n=%d' % (i + 1))

# 6. Lemma 2 (8-fold symmetry count): 8 W(X) = P(X) + Lambda(X), 0 <= Lambda <= 7 sqrt(X).
for X in range(1, 900):
    r = isqrt(X)
    P = sum(1 for x in range(-r, r + 1) for y in range(-r, r + 1) if 0 < x * x + y * y <= X)
    Wc = sum(1 for a in range(r + 1) for b in range(a + 1) if 0 < a * a + b * b <= X)
    lam = 8 * Wc - P
    require(0 <= lam <= 7 * sqrt(X), 'Lemma 2 at X=%d' % X)

# 7. Ratio trend toward 1 (illustration; the proof gives the rate O(log N / sqrt N)).
z = W3[-1]; n = len(W3); N = z[0] ** 2 + z[1] ** 2
ratio = a_mobius(z) / (48 * n / pi ** 2)
require(abs(ratio - 1) < 0.05, 'ratio at n=%d is %f' % (n, ratio))
print('n=%d z=%s a(n)/(48n/pi^2)=%.5f' % (n, z, ratio))
print('ALL CHECKS PASSED')
