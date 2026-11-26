r"""Verify the proof of both conjectures in OEIS A401159 (R. J. Mathar, Nov 18 2026).

A(n,m,k) = number of binary n x m matrices with at most k 1's in each row and column.
A401159 is T(n,m) = A(n,m,2). Conjectures:
  T(n,2) = A086601(n) = A000124(n)^2
  T(n,3) = 1 + n + 11 n^2/4 + 13 n^3/8 + n^4/8 + 3 n^5/8 + n^6/8
Theorem verified here:
  (a) m <= k:  A(n,m,k) = s(n,k)^m,  s(n,k) = sum_{i<=k} C(n,i)
  (b) m = k+1: A(n,k+1,k) = sum_{j=0..k} (-1)^j C(n,j) s(n-j,k-j)^(k+1)
Checks: brute force over all matrices (small), a row-by-row DP (larger),
the published OEIS terms, and the exact polynomial identities for k=2.
Stdlib only; uses require() so it is safe under python -O.
"""
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb


def require(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)


def brute(n, m, k):
    cnt = 0
    for bits in product((0, 1), repeat=n * m):
        rows_ok = all(sum(bits[r * m:(r + 1) * m]) <= k for r in range(n))
        if rows_ok and all(sum(bits[r * m + c] for r in range(n)) <= k for c in range(m)):
            cnt += 1
    return cnt


def dp(n, m, k):
    # State: sorted column fill counts (capped at k); rows added one at a time.
    @lru_cache(maxsize=None)
    def go(rows_left, state):
        if rows_left == 0:
            return 1
        total = 0
        for row in product((0, 1), repeat=m):
            if sum(row) > k or any(row[c] and state[c] >= k for c in range(m)):
                continue
            total += go(rows_left - 1, tuple(sorted(state[c] + row[c] for c in range(m))))
        return total
    return go(n, tuple([0] * m))


def s(n, k):
    return sum(comb(n, i) for i in range(k + 1)) if k >= 0 else 0


def formula(n, m, k):
    if m <= k:
        return s(n, k) ** m
    require(m == k + 1, "formula only for m <= k+1")
    return sum((-1) ** j * comb(n, j) * s(n - j, k - j) ** (k + 1) for j in range(min(n, k) + 1))


def conj3(n):
    v = (1 + n + Fraction(11, 4) * n**2 + Fraction(13, 8) * n**3
         + Fraction(1, 8) * n**4 + Fraction(3, 8) * n**5 + Fraction(1, 8) * n**6)
    require(v.denominator == 1, "conj3 not integral")
    return int(v)


def main():
    # Brute force: every binary matrix enumerated (including n = 0).
    for k in (1, 2, 3):
        for m in range(0, k + 2):
            for n in range(0, 7):
                if n * m <= 18:
                    require(brute(n, m, k) == formula(n, m, k), f"brute n={n} m={m} k={k}")
    # Row DP to larger n.
    for k in (1, 2, 3):
        for m in range(1, k + 2):
            for n in range(0, 16):
                require(dp(n, m, k) == formula(n, m, k), f"dp n={n} m={m} k={k}")
    # Published A401159 rows (Mathar 2014 Table 2) for columns m = 1,2,3.
    oeis = {1: (2,), 2: (4, 16), 3: (7, 49, 265), 4: (11, 121, 1081), 5: (16, 256, 3481),
            6: (22, 484, 9367), 7: (29, 841, 22009), 8: (37, 1369, 46585), 9: (46, 2116, 90811)}
    for n, row in oeis.items():
        for m, v in enumerate(row, 1):
            require(formula(n, m, 2) == v, f"oeis n={n} m={m}")
    # Conjecture 1: T(n,2) = A086601(n) = (n(n+1)/2 + 1)^2.
    for n in range(0, 2000):
        require(formula(n, 2, 2) == (n * (n + 1) // 2 + 1) ** 2, f"conj2 n={n}")
    # Conjecture 2: f^3 - n^4 + C(n,2) equals the sextic.
    for n in range(0, 2000):
        f = (n * n + n + 2) // 2
        require(formula(n, 3, 2) == f**3 - n**4 + comb(n, 2), f"closed n={n}")
        require(formula(n, 3, 2) == conj3(n), f"conj3 n={n}")
    print("OK: A401159 conjectures T(n,2)=A086601(n) and T(n,3)=sextic verified; theorem (a),(b) checked k<=3")


if __name__ == "__main__":
    main()
    sys.exit(0)
