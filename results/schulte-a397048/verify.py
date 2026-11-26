r"""Standalone checker for OEIS A397048 (Werner Schulte, Conjectures 1-3 and the general shift theorem).

Run: python -O -W error verify.py   (stdlib only; uses require(), never assert)
"""
import sys
from math import comb, factorial


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


N = 40  # rows checked for the conjectures
S = 14  # shifts checked for the general lemma

# Stirling numbers from their defining recurrences.
M = 2 * N + 2
S2 = [[0] * (M + 1) for _ in range(M + 1)]  # A048993
s1 = [[0] * (M + 1) for _ in range(M + 1)]  # A048994 (signed)
S2[0][0] = s1[0][0] = 1
for n in range(M):
    for k in range(1, n + 2):
        S2[n + 1][k] = S2[n][k - 1] + k * S2[n][k]
        s1[n + 1][k] = s1[n][k - 1] - n * s1[n][k]
bell = [sum(S2[j][: j + 1]) for j in range(M + 1)]

# Spot-check against OEIS data.
require([s1[3][k] for k in range(4)] == [0, 2, -3, 1], "A048994 row 3")
require([S2[4][k] for k in range(5)] == [0, 1, 7, 6, 1], "A048993 row 4")
require(bell[:8] == [1, 1, 2, 5, 15, 52, 203, 877], "Bell numbers")


def T(n, k, c=None):
    """OEIS definition with base point c (c = n gives A397048)."""
    c = n if c is None else c
    tot = sum((-1) ** i * comb(k, i) * (c + i) ** n for i in range(k + 1)) * (-1) ** k
    require(tot % factorial(k) == 0, "T not integral")
    return tot // factorial(k)


def ff(x, k):
    r = 1
    for i in range(k):
        r *= x - i
    return r


oeis = [1, 1, 1, 4, 5, 1, 27, 37, 12, 1, 256, 369, 151, 22, 1, 3125, 4651, 2190, 425, 35, 1]
require([T(n, k) for n in range(6) for k in range(n + 1)] == oeis, "A397048 data")
a134980 = [1, 2, 10, 77, 799, 10427, 163967, 3017562, 63625324, 1512354975, 40012800675]

checks = 0
for n in range(N + 1):
    row = [T(n, k) for k in range(n + 1)]
    # Vanishing for i > n.
    for i in range(n + 1, n + 4):
        require(T(n, i) == 0, f"vanishing n={n} i={i}")
    # Binomial-Stirling formula: T(n,k) = sum_j C(n,j) n^(n-j) S(j,k).
    for k in range(n + 1):
        require(row[k] == sum(comb(n, j) * n ** (n - j) * S2[j][k] for j in range(n + 1)), f"binom-Stirling {n},{k}")
    # Conjecture 1.
    for k in range(n + 1):
        rhs = sum(s1[n][k + i] * S2[n + k + i][n + k] for i in range(n - k + 1))
        require(row[k] == rhs, f"Conj 1 n={n} k={k}")
        checks += 1
    # Conjecture 2.
    rs = sum(row)
    require(rs == sum(comb(n, j) * n ** (n - j) * bell[j] for j in range(n + 1)), f"Conj 2 n={n}")
    if n < len(a134980):
        require(rs == a134980[n], f"Conj 2 vs A134980 data n={n}")
    # Conjecture 3 (all k up to 2n+2, including k > n).
    for k in range(2 * n + 3):
        lhs = sum(T(n, i) * (factorial(k) // factorial(k - i)) for i in range(k + 1))
        require(lhs == (n + k) ** n, f"Conj 3 n={n} k={k}")
        checks += 1

# Shift splitting: (x)_c (x-c)_k = (x)_{c+k} at integer points.
for c in range(10):
    for k in range(10):
        for x in range(-5, c + k + 6):
            require(ff(x, c) * ff(x - c, k) == ff(x, c + k), f"shift splitting c={c} k={k} x={x}")

# General shift theorem: coeff of (x)_k in (x+c)^n equals sum_m s(c,m) S(n+m, c+k).
for c in range(S + 1):
    for n in range(S + 1):
        for k in range(n + 1):
            rhs = sum(s1[c][m] * S2[n + m][c + k] for m in range(c + 1))
            require(T(n, k, c) == rhs, f"shift theorem c={c} n={n} k={k}")
            checks += 1

print(f"OK: A397048 Conjectures 1-3 verified for n <= {N}; shift theorem for c,n <= {S}; {checks} identities")
