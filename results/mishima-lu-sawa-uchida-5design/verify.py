"""Verification for Strike 58A: odd antipodal rational 5-designs for the Chebyshev measure.

Run:  python -O -W error verify.py   (stdlib only; prints ALL CHECKS PASSED)

An n-point antipodal rational 5-design for d(mu) = dt / (pi sqrt(1-t^2)) on (-1,1) is a set
X = -X of n distinct rationals in (-1,1) with (1/n) sum_X t^2 = 1/2 and (1/n) sum_X t^4 = 3/8
(odd moments vanish by antipodality). For odd n = 2N+1 this means X = {0} u {+-x_1..+-x_N} with
    sum x_i^2 = (2N+1)/4,   sum x_i^4 = 3(2N+1)/16.
"""
from fractions import Fraction as Fr
from itertools import product


def require(cond, msg):
    if not cond:
        raise SystemExit("CHECK FAILED: " + msg)


def moments_ok(xs, odd):
    n = 2 * len(xs) + (1 if odd else 0)
    return (sum(x * x for x in xs) * 2 == Fr(n, 2)
            and sum(x ** 4 for x in xs) * 2 == Fr(3 * n, 8))


def check_design(xs, odd, label):
    require(len(set(xs)) == len(xs), label + ": distinct")
    require(all(0 < x < 1 for x in xs), label + ": in (0,1)")
    require(moments_ok(xs, odd), label + ": moments")
    # full point set, direct check of the quadrature for 1, t, ..., t^5
    X = ([Fr(0)] if odd else []) + xs + [-x for x in xs]
    n = len(X)
    cheb = [Fr(1), Fr(0), Fr(1, 2), Fr(0), Fr(3, 8), Fr(0)]
    for k in range(6):
        require(sum(t ** k for t in X) == n * cheb[k], label + ": moment %d" % k)


# --- 1. explicit base designs (pairs N, denominator D, numerators) -------------------
BASES = {
    # Mishima-Lu-Sawa-Uchida (arXiv:2503.21151v4, eq. (8.1)): 35 points
    "N17_paper": (17, 1092, [9, 65, 91, 195, 531, 669, 689, 729, 837, 871, 923, 933,
                             1001, 1027, 1053, 1066, 1079]),
    # new, found by the four-list search (gowag/main.go)
    "N17_new": (17, 1092, [55, 87, 171, 305, 533, 575, 733, 753, 765, 881, 905, 966,
                           981, 985, 1083, 1085, 1089]),
    "N18": (18, 240, [15, 57, 61, 69, 93, 129, 141, 147, 151, 183, 199, 209, 211, 215,
                      234, 235, 238, 239]),
    "N19": (19, 420, [47, 93, 108, 113, 129, 153, 161, 305, 309, 343, 353, 357, 365, 366,
                      369, 395, 405, 408, 413]),
    "N19_alt": (19, 1092, [33, 159, 221, 231, 273, 309, 724, 785, 821, 840, 899, 903, 939,
                           957, 979, 1006, 1051, 1061, 1089]),
}
for name, (N, D, nums) in BASES.items():
    require(len(nums) == N, name + ": size")
    check_design([Fr(a, D) for a in nums], True, name)

# --- 2. six-point blocks {+-a_t, +-b_t, +-c_t} ----------------------------------------
# a_t = (2t^2-22t-13)/den, b_t = (-13t^2-4t+11)/den, c_t = (11t^2+26t+2)/den, den = 14(t^2+t+1)
PA, PB, PC = [-13, -22, 2], [11, -4, -13], [2, 26, 11]   # coefficients, low degree first
PDEN = [14, 14, 14]


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def padd(*ps):
    r = [0] * max(len(p) for p in ps)
    for p in ps:
        for i, x in enumerate(p):
            r[i] += x
    return r


def pscale(c, p):
    return [c * x for x in p]


require(padd(PA, PB, PC) == [0, 0, 0], "a+b+c = 0 identically")
# a^2 + ab + b^2 = 3/4  <=>  4(A^2 + AB + B^2) = 3 DEN^2
lhs = pscale(4, padd(pmul(PA, PA), pmul(PA, PB), pmul(PB, PB)))
require(lhs == pscale(3, pmul(PDEN, PDEN)), "a^2+ab+b^2 = 3/4 identically")

# triple identity: x^4+y^4+(x+y)^4 = (x^2+y^2+(x+y)^2)^2 / 2 (degree 4 in each variable,
# so agreement on a 6x6 grid proves the polynomial identity)
for x, y in product(range(-3, 3), repeat=2):
    x, y = Fr(x, 2), Fr(y, 3)
    require(2 * (x ** 4 + y ** 4 + (x + y) ** 4) == (x * x + y * y + (x + y) ** 2) ** 2,
            "triple identity")


def block(t):
    den = 14 * (t * t + t + 1)
    vals = [Fr(sum(c * t ** i for i, c in enumerate(p)), den) for p in (PA, PB, PC)]
    return [abs(v) for v in vals]


for t in range(-50, 51):
    if t * t + t + 1 == 0:
        continue
    xs = block(t)
    s2 = sum(v * v for v in xs)
    s4 = sum(v ** 4 for v in xs)
    # = the even-design equations with N = 3 pairs (sum x^2 = 3/2, sum x^4 = 9/8)
    require(s2 == Fr(3, 2) and s4 == Fr(9, 8), "block moments t=%d" % t)

# --- 3. explicit constructions for every odd n = 2N+1 with 17 <= N <= 80 ------------
base_by_res = {17 % 3: BASES["N17_new"], 18 % 3: BASES["N18"], 19 % 3: BASES["N19"]}
for N in range(17, 81):
    N0, D, nums = base_by_res[N % 3]
    xs = [Fr(a, D) for a in nums]
    t = 1
    while len(xs) < N:
        t += 1
        b = block(t)
        if 0 in b or max(b) >= 1 or len(set(b)) < 3 or set(b) & set(xs):
            continue
        xs += b
    require(len(xs) == N, "construction size N=%d" % N)
    check_design(xs, True, "construction N=%d" % N)

# --- 4. residue facts used in the non-existence proof for N <= 16 --------------------
for y in range(256):
    if y % 2:
        require(y * y % 8 == 1 and y ** 4 % 16 == 1, "odd y residues")
        t = (y * y - 1) // 8
        require(y ** 4 == 1 + 16 * t + 64 * t * t, "(1+8t)^2 expansion")
    else:
        require(y ** 4 % 16 == 0, "even y^4")
        require(y * y % 8 == (4 if y % 4 == 2 else 0), "even y^2 mod 8")
for F in range(1, 256, 2):
    require(F * F % 8 == 1 and F ** 4 % 16 == 1, "odd F residues")
# case e = 1 (sum y^2 = M F^2, sum y^4 = 3 M F^4): r = #odd y, j = #(y = 2 mod 4);
# r = 3M (mod 8) and r + 4j = M (mod 8) has no solution for odd M
for M in range(1, 64, 2):
    for r in range(8):
        for j in range(2):
            require(not (r % 8 == 3 * M % 8 and (r + 4 * j - M) % 8 == 0), "e=1 case")
# case e >= 2, N = 16 (all 16 numerators odd, sum y^2 = 16 + 8 T1, sum y^4 = 16 + 16 T1 + 64 T2)
M = 33
for F in range(1, 64, 2):
    require((16 - 4 * M * F * F) % 8 != 0, "N=16, e=2")          # 16+8T1 = 4MF^2 impossible mod 8
for T1 in range(32):
    for T2 in range(32):
        # e >= 3: sum y^2 = 0 mod 16 forces T1 even; sum y^4 = 0 mod 256 forces 1+T1+4T2 = 0 mod 16
        require(not ((16 + 8 * T1) % 16 == 0 and (1 + T1 + 4 * T2) % 16 == 0), "N=16, e>=3")

print("ALL CHECKS PASSED")
