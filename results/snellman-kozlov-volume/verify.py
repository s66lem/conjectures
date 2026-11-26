r"""Independent stdlib-only verifier for Result #32:
Snellman's NV-monotonicity conjecture for rank-two Kozlov polytopes
(arXiv:2611.26110v1, Nov 19 2026, Conjecture `conj-nv-monotone`).

Checks:
1. Reproduces every normalized volume in Table `tab:volumes` of arXiv:2611.26110v1
   (n = 3, 4, 5) and all Euclidean volumes for n = 6 (including vol(Koz(6; 0, 4)) = 270000).
2. Verifies for all 2 <= n <= 100 and 0 <= d <= n - 2:
   - the cleared-denominator termwise ratio identity (d + j) * t_{d+1}(j) = (n + d) * C(n, j+d+1) * t_d(j),
   - termwise non-decrease t_{d+1}(j) >= t_d(j) for all 1 <= j <= n - d - 1,
   - the exact last-cell gain identity t_{d+1}(n - d - 1) = t_d(n - d - 1) + C(n, d) * t_d(n - d),
   - the quantitative lower bound T(n, d + 1) >= T(n, d) + (C(n, d) - 1) * t_d(n - d),
   - exact strictness pattern (strict except the sole equality (n, d) = (2, 0), NV = 2).
3. Verifies boundary identities T(n, 0) = 2^(n - 1) and
   NV(Koz(n; 0, n - 1)) = C(2n - 2, n - 1) * NV(Koz(n))^2 for all 1 <= n <= 100.

Run with:
    python -O -W error results/snellman-kozlov-volume/verify.py
"""

from fractions import Fraction
from math import comb, factorial, prod


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(f"VERIFICATION FAILED: {msg}")


def nv_koz(n: int) -> int:
    return prod(comb(n, k) for k in range(2, n + 1))


def cell_factor(n: int, d: int, j: int) -> int:
    return comb(n - 1 + d, d + j - 1) * prod(comb(n, k) for k in range(j + 1, j + d + 1))


def rank2_sum(n: int, d: int) -> int:
    return sum(cell_factor(n, d, j) for j in range(1, n - d + 1))


def nv_rank2(n: int, d: int) -> int:
    return nv_koz(n) * rank2_sum(n, min(d, n - 1))


def main() -> None:
    # 1. Paper's Table `tab:volumes`
    table_nv = {
        3: [12, 36, 54],
        4: [192, 1248, 6720, 11520],
        5: [8000, 102500, 1287500, 9625000, 17500000],
    }
    for n, row in table_nv.items():
        for d, expected in enumerate(row):
            require(nv_rank2(n, d) == expected, f"NV table mismatch at n={n}, d={d}")

    table_euc_6 = [7200, 29475, 107550, 256500, 270000, 50625]
    for d, expected in enumerate(table_euc_6):
        got = Fraction(nv_rank2(6, d), factorial(6 - 1 + d))
        require(got == expected, f"Euclidean vol mismatch at n=6, d={d}: {got} != {expected}")

    # Unique equality case (n, d) = (2, 0)
    require(nv_rank2(2, 0) == 2 and nv_rank2(2, 1) == 2, "n=2 equality check failed")

    # 2. Boundary identities and full proof steps for 1 <= n <= 100
    n_max = 100
    for n in range(1, n_max + 1):
        require(rank2_sum(n, 0) == 1 << (n - 1), f"T({n}, 0) != 2^(n-1)")
        require(
            nv_rank2(n, n - 1) == comb(2 * n - 2, n - 1) * nv_koz(n) ** 2,
            f"product regime mismatch at n={n}",
        )
        for d in range(0, n - 1):
            for j in range(1, n - d):
                lhs = (d + j) * cell_factor(n, d + 1, j)
                rhs = (n + d) * comb(n, j + d + 1) * cell_factor(n, d, j)
                require(lhs == rhs, f"ratio identity failed at n={n}, d={d}, j={j}")
                require(
                    cell_factor(n, d + 1, j) >= cell_factor(n, d, j),
                    f"termwise monotonicity failed at n={n}, d={d}, j={j}",
                )
            lhs_last = cell_factor(n, d + 1, n - d - 1)
            rhs_last = cell_factor(n, d, n - d - 1) + comb(n, d) * cell_factor(n, d, n - d)
            require(lhs_last == rhs_last, f"last-cell identity failed at n={n}, d={d}")

            diff = rank2_sum(n, d + 1) - rank2_sum(n, d)
            lb = (comb(n, d) - 1) * cell_factor(n, d, n - d)
            require(diff >= lb, f"lower bound failed at n={n}, d={d}")
            if (n, d) == (2, 0):
                require(diff == 0, "expected equality at (2, 0)")
            else:
                require(diff > 0, f"expected strict increase at n={n}, d={d}")

    print(
        f"ALL CHECKS PASSED: Table tab:volumes (n=3..6), boundary identities, ratio & "
        f"last-cell identities, quantitative lower bound, and exact strictness pattern "
        f"verified for all 1 <= n <= {n_max}."
    )


if __name__ == "__main__":
    main()
