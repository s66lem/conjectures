#!/usr/bin/env python3
r"""Standalone, -O-safe exact verification script for Conjecture 7.4 of
Gil-Liang-Odetola-Weiner (arXiv:2609.01562v1, "Points of maximal traffic on
a grid with obstruction").

Uses ONLY Python standard library (math, fractions, time) and exact integer /
rational arithmetic (zero floating-point reliance for any proof step).
No `assert` statements are used for checks, so `python -O verify.py` executes
every verification identically.
"""

import math
import time
from fractions import Fraction


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i + j] += x * y
    return res


def poly_pow(a: list[int], k: int) -> list[int]:
    res = [1]
    for _ in range(k):
        res = poly_mul(res, a)
    return res


def main() -> None:
    t0 = time.perf_counter()

    # CHECK 1: Exact refactorization identity (Lemma 1)
    for n in [2, 3, 5, 8, 9, 15, 50, 100, 200, 495, 496, 497]:
        m = n // 2
        W_n = Fraction(math.comb(n, m) ** 2, math.comb(2 * n, n))
        D_n = Fraction(1, n) * math.comb(2 * n - 2, n - 1)
        for a in range(1, (n + 1) // 2):
            d = n - 2 * a
            G_na = Fraction(n - 2 * a + 1, n - a) * math.comb(n, a) * math.comb(n - 2, a - 1)
            R_def = G_na / D_n
            R_ref = (
                Fraction(2 * n - 1, n - 1)
                * Fraction((n - d) * (d + 1), n)
                * W_n
                * Fraction(math.comb(n, a), math.comb(n, m)) ** 2
            )
            R_int = Fraction(
                2 * (2 * n - 1) * a * (n - 2 * a + 1) * (math.comb(n, a) ** 2),
                n * (n - 1) * math.comb(2 * n, n),
            )
            require(R_def == R_ref == R_int, f"Lemma 1 identity mismatch at n={n}, a={a}")
    print("[PASS] Check 1: Exact refactorization identity (Lemma 1) verified.")

    # CHECK 2: Polynomial monotonicity of (n+1)*W(n)^2 (Lemma 2)
    num_even = poly_mul([4], poly_mul([3, 2], poly_pow([1, 2], 5)))
    den_even = poly_mul(
        poly_pow([1, 1], 2),
        poly_mul(poly_pow([1, 4], 2), poly_pow([3, 4], 2)),
    )
    diff_even = [d - nu for nu, d in zip(num_even, den_even)]
    require(diff_even == [-3, -14, -7, 32, 32, 0, 0], f"Even poly diff mismatch: {diff_even}")
    p_shifted = [0] * 5
    for deg, coeff in enumerate(diff_even[:5]):
        term = poly_pow([1, 1], deg)
        for i, c in enumerate(term):
            p_shifted[i] += coeff * c
    require(all(c > 0 for c in p_shifted), f"Shifted even poly not all positive: {p_shifted}")

    num_odd = poly_pow([1, 2], 5)
    den_odd = poly_mul([2], poly_mul(poly_pow([1, 1], 3), poly_pow([1, 4], 2)))
    diff_odd = [d - nu for nu, d in zip(num_odd, den_odd)]
    require(diff_odd == [1, 12, 46, 66, 32, 0], f"Odd poly diff mismatch: {diff_odd}")
    require(all(c >= 0 for c in diff_odd) and diff_odd[0] > 0, "Odd poly not strictly positive")

    for m in [1, 2, 10, 50, 100]:
        W_2m = Fraction(math.comb(2 * m, m) ** 2, math.comb(4 * m, 2 * m))
        W_2m1 = Fraction(math.comb(2 * m + 1, m) ** 2, math.comb(4 * m + 2, 2 * m + 1))
        W_2m2 = Fraction(math.comb(2 * m + 2, m + 1) ** 2, math.comb(4 * m + 4, 2 * m + 2))
        require(
            W_2m2 / W_2m == Fraction(2 * (2 * m + 1) ** 3, (m + 1) * (4 * m + 1) * (4 * m + 3)),
            f"W(2m+2)/W(2m) mismatch at m={m}",
        )
        require(
            W_2m1 / W_2m == Fraction((2 * m + 1) ** 3, 2 * (m + 1) ** 2 * (4 * m + 1)),
            f"W(2m+1)/W(2m) mismatch at m={m}",
        )

    c200 = math.comb(200, 100)
    c400 = math.comb(400, 200)
    require(40 * 201 * (c200 ** 4) < 51 * (c400 ** 2), "Base bound 201*W(200)^2 < 51/40 failed")
    print(f"[PASS] Check 2: Monotonicity of (n+1)*W(n)^2 (shifted coeffs {p_shifted}) and 201*W(200)^2 < 51/40 verified.")

    # CHECK 3: Exact Q(sqrt(2))[eps] discriminant identity (Lemma 4)
    def q2_add(x, y):
        return (x[0] + y[0], x[1] + y[1])

    def q2_mul(x, y):
        return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

    c_poly = [(Fraction(0), Fraction(1, 2)), (Fraction(1, 2), Fraction(0)), (Fraction(2), Fraction(0))]
    c2_poly = [(Fraction(0), Fraction(0))] * 5
    for i in range(3):
        for j in range(3):
            c2_poly[i + j] = q2_add(c2_poly[i + j], q2_mul(c_poly[i], c_poly[j]))
    expr = [(Fraction(0), Fraction(0))] * 5
    for i in range(5):
        expr[i] = q2_add(expr[i], (2 * c2_poly[i][0], 2 * c2_poly[i][1]))
    for i in range(3):
        expr[i + 1] = q2_add(expr[i + 1], (-2 * c_poly[i][0], -2 * c_poly[i][1]))
    expr[2] = q2_add(expr[2], (Fraction(-4), Fraction(0)))
    expected = [
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0)),
        (Fraction(-9, 2), Fraction(4)),
        (Fraction(0), Fraction(0)),
        (Fraction(8), Fraction(0)),
    ]
    require(expr == expected, f"Lemma 4 Q(sqrt(2))[eps] identity failed: {expr}")
    require(32 * 4 > 81, "4*sqrt(2) > 9/2 check failed")
    print("[PASS] Check 3: Exact Q(sqrt(2))[eps] discriminant identity (Lemma 4) verified.")

    # CHECK 4: Pure rational verification of the analytic closure for all n >= 800 (Lemma 5)
    require(14142 ** 2 < 2 * (10000 ** 2), "sqrt(2) lower bound failed")
    require(28 ** 2 < 801, "sqrt(801) lower bound failed")
    e_half_lower = Fraction(1) + Fraction(1, 2) + Fraction(1, 8) + Fraction(1, 48) + Fraction(1, 384)
    require(e_half_lower == Fraction(211, 128), f"exp(1/2) partial sum mismatch: {e_half_lower}")
    rhs_sq = (
        Fraction(1599, 799) ** 2
        * Fraction(51, 40)
        * Fraction(801, 800) ** 2
        * (Fraction(1) / e_half_lower) ** 2
        * (Fraction(10000, 14142) + Fraction(1, 56) + Fraction(2, 801)) ** 2
    )
    require(rhs_sq < 1, f"Analytic upper bound >= 1: {float(rhs_sq)}")
    print(f"[PASS] Check 4: Pure rational bound R_n(a)^2 < {float(rhs_sq):.10f} < 1 for ALL n >= 800 verified.")

    # CHECK 5: Exact integer verification for ALL 496 <= n <= 799 and ALL 1 <= a < n/2 (Lemma 6)
    worst_ratio = Fraction(0)
    worst_pair = (-1, -1)
    total_pairs_496_799 = 0
    for n in range(496, 1001):
        c2n = math.comb(2 * n, n)
        rhs = n * (n - 1) * c2n
        cn_a = 1
        for a in range(1, (n + 1) // 2):
            cn_a = cn_a * (n - a + 1) // a
            lhs = 2 * (2 * n - 1) * a * (n - 2 * a + 1) * (cn_a * cn_a)
            require(lhs < rhs, f"R_n(a) >= 1 at n={n}, a={a}!")
            if n <= 799:
                total_pairs_496_799 += 1
                if lhs * worst_ratio.denominator > worst_ratio.numerator * rhs:
                    worst_ratio = Fraction(lhs, rhs)
                    worst_pair = (n, a)
    print(
        f"[PASS] Check 5: Exact integer verification for ALL 496 <= n <= 799 "
        f"({total_pairs_496_799} pairs) + extra sanity 800..1000 PASSED! "
        f"Worst in [496,799]: n={worst_pair[0]}, a={worst_pair[1]}, R={float(worst_ratio):.10f}."
    )

    # CHECK 6: Sharpness at n = 495 and full reproduction of paper's [376, 495] exception list
    n495, a495 = 495, 240
    lhs495 = 2 * (2 * n495 - 1) * a495 * (n495 - 2 * a495 + 1) * (math.comb(n495, a495) ** 2)
    rhs495 = n495 * (n495 - 1) * math.comb(2 * n495, n495)
    require(lhs495 > rhs495, "Expected R_495(240) > 1 (sharpness of 496)")
    exceptions = []
    for n in range(376, 496):
        c2n = math.comb(2 * n, n)
        rhs = n * (n - 1) * c2n
        cn_a = 1
        has_anom = False
        for a in range(1, (n + 1) // 2):
            cn_a = cn_a * (n - a + 1) // a
            if 2 * (2 * n - 1) * a * (n - 2 * a + 1) * (cn_a * cn_a) > rhs:
                has_anom = True
                break
        if not has_anom:
            exceptions.append(n)
    expected_exc = [376, 378] + list(range(423, 464, 2)) + list(range(466, 495, 2))
    require(exceptions == expected_exc, f"Exception list mismatch: {exceptions}")
    print(
        f"[PASS] Check 6: Sharpness verified (R_495(240) = {float(Fraction(lhs495, rhs495)):.10f} > 1; "
        f"all 38 exceptions in [376,495] match paper)."
    )

    elapsed = time.perf_counter() - t0
    print(f"\nALL 6 VERIFICATION CHECKS PASSED IN {elapsed:.3f}s (exact arithmetic, -O safe).")


if __name__ == "__main__":
    main()
