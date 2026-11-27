r"""Verify the disproof of Runbo Li's Conjecture 1.1 (NNTDM 32(3) (2026) 544-555) at C = 30.

Claim: for every positive integer q, q^30 + 2 is not practical. Hence no practical q has
q^30 and q^30 + 2 both practical, and the same holds for every C divisible by 30.
Also verifies the sharpness theorem (local obstruction mod {4,9,5,7,11,13} holds iff 30 | C)
and positive small-exponent witnesses for C in {1, 2, 3, 4, 5, 6}.

Run: python -O -W error verify.py   (stdlib only, no assert statements)
"""
import sys
from itertools import combinations


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def is_practical_brute(n):
    """Definition: every 1..n is a sum of distinct divisors of n (subset-sum bitset)."""
    if n < 1:
        return False
    reach = 1
    for d in range(1, n + 1):
        if n % d == 0:
            reach |= reach << d
    full = (1 << (n + 1)) - 1
    return reach & full == full


# 0. Sanity: brute-force practical numbers match OEIS A005153 initial terms.
A005153 = [1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, 32, 36, 40, 42, 48, 54, 56, 60,
           64, 66, 72, 78, 80, 84, 88, 90, 96, 100, 104, 108, 112, 120, 126, 128, 132,
           140, 144, 150, 156, 160, 162, 168, 176, 180, 192, 196, 198, 200]
require([n for n in range(1, 201) if is_practical_brute(n)] == A005153, "A005153 mismatch")

# 1. Residue facts (exhaustive over residue classes, so they hold for all integers q).
for r in range(0, 4, 2):
    require((r ** 30 + 2) % 4 == 2, "q even => q^30+2 = 2 mod 4")
for r in range(9):
    require((r ** 30 + 2) % 9 != 0, "9 never divides q^30+2")
for m in (5, 7, 11, 13):
    for r in range(m):
        require((r ** 30 + 2) % m != 0, f"{m} never divides q^30+2")
require((1 ** 30 + 2) % 2 == 1 and (2 ** 30 + 2) % 2 == 0, "parity of q^30+2 follows q")

# 2. Key lemma: if n is even, 4 ∤ n, 9 ∤ n, gcd(n, 5*7*11*13) = 1, then the divisors of n
#    that are <= 13 lie in {1,2,3,6}; their sum is <= 12, so 13 is not a sum of distinct
#    divisors. Check modulo lcm(1..13) = 360360.
L = 360360
for n_mod in range(0, L, 2):
    if n_mod % 4 == 0 or n_mod % 9 == 0 or any(n_mod % p == 0 for p in (5, 7, 11, 13)):
        continue
    small = [d for d in range(1, 14) if n_mod % d == 0]
    require(set(small) <= {1, 2, 3, 6}, f"small divisors {small}")
require(sum({1, 2, 3, 6}) == 12, "sum 12")
for k in range(1, 5):
    for c in combinations((1, 2, 3, 6), k):
        require(sum(c) != 13, "13 representable?")

# 3. Direct check of the witness for q = 1..400 (exact big integers).
for q in range(1, 401):
    n = q ** 30 + 2
    divs = [d for d in range(1, 14) if n % d == 0]
    if q % 2:
        require(n % 2 == 1 and n >= 3, f"q={q}: odd n>=3, so 2 is unrepresentable")
    else:
        require(set(divs) <= {1, 2, 3, 6} and n >= 13, f"q={q}: divisors {divs}")

# 4. Small-scale cross-check of the witness logic with brute force on n in the lemma class.
for n in range(14, 3000):
    if n % 2 == 0 and n % 4 and n % 9 and all(n % p for p in (5, 7, 11, 13)):
        require(not is_practical_brute(n), f"lemma-class n={n} is practical?")

# 5. Sharpness: verify local obstruction mod {4,9,5,7,11,13} fails for every 1 <= C < 30.
for C in range(1, 61):
    obstructed = all(
        all((pow(r, C, m) + 2) % m != 0 for r in range(0, 2 * m, 2))
        for m in (4, 9, 5, 7, 11, 13)
    )
    require(obstructed == (C % 30 == 0), f"sharpness mismatch at C={C}")

# 6. Positive contrast: explicit practical triples (q, q^C, q^C + 2) for C in {1, 2, 3, 4, 5, 6}.
for C, q in [(1, 2), (2, 2), (3, 4), (4, 2), (5, 4), (6, 2)]:
    require(
        is_practical_brute(q) and is_practical_brute(q ** C) and is_practical_brute(q ** C + 2),
        f"small witness failed for C={C}, q={q}",
    )

# 7. Multiples of 30: q^(30t) + 2 = (q^t)^30 + 2.
for q in range(1, 30):
    for t in range(1, 4):
        n = (q ** t) ** 30 + 2
        require(n == q ** (30 * t) + 2, "power identity")
        divs = [d for d in range(1, 14) if n % d == 0]
        require((n % 2 == 1) or set(divs) <= {1, 2, 3, 6}, f"q={q} t={t}")

print("ALL CHECKS PASSED")
