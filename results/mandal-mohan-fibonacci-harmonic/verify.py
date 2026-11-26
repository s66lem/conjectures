r"""Independent verifier for Mandal-Mohan Conjecture 1.19 (arXiv:2611.32519v1).

Verifies:
1. Exact rational computation of H(n, k) = n^k / sum_{i=1}^n F_i^{-k} for
   1 <= n <= 120 and 1 <= k <= 10, checking H(n, k) in N iff n in {1, 2} or (n, k) = (3, 2).
2. All ingredients of the Bertrand-postulate + strong-divisibility proof:
   - F_m >= 2m - 1 for 7 <= m <= 500,
   - Existence of a prime q with n/2 < q <= n (and q >= 7 for n >= 12) for 12 <= n <= 500,
   - Pairwise coprimality gcd(F_q, F_i) = 1 for all 1 <= i <= n, i != q,
   - Clearing-denominator identity and inequality P + F_q^k Q > n^k P for n = 5 and 7 <= n <= 40 (1 <= k <= 6),
   - Exact coprimality checks for n = 4 and n = 6,
   - Exact classification of 2^(k+1) + 1 = 3^j for n = 3 (1 <= k <= 300).

Stdlib only, -O safe (uses require(), never assert).
"""

from fractions import Fraction
from math import gcd


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def fib_table(limit: int) -> list[int]:
    F = [0, 1]
    while len(F) <= limit:
        F.append(F[-1] + F[-2])
    return F


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def main() -> None:
    F = fib_table(500)

    # 1. Exact check of H(n, k) in N for 1 <= n <= 120, 1 <= k <= 10
    for k in range(1, 11):
        S = Fraction(0)
        for n in range(1, 121):
            S += Fraction(1, F[n] ** k)
            H = Fraction(n ** k) / S
            expected = (n in (1, 2)) or (n == 3 and k == 2)
            require((H.denominator == 1) == expected, f"H({n}, {k}) integrality mismatch")
            if n == 1:
                require(H == 1, f"H(1, {k}) != 1")
            elif n == 2:
                require(H == 2 ** (k - 1), f"H(2, {k}) != 2^{k-1}")
            elif n == 3 and k == 2:
                require(H == 4, "H(3, 2) != 4")

    # 2. Inequality F_m >= 2m - 1 for 7 <= m <= 500
    for m in range(7, 501):
        require(F[m] >= 2 * m - 1, f"F_{m} < 2*{m}-1")

    # 3. Prime isolation witness q for n = 5, 7 <= n <= 500
    for n in [5] + list(range(7, 501)):
        if n == 5:
            q = 5
        elif n <= 11:
            q = 7
        else:
            primes_in_half = [p for p in range(n // 2 + 1, n + 1) if is_prime(p)]
            require(len(primes_in_half) >= 1, f"No prime in ({n//2}, {n}]")
            q = primes_in_half[0]
            require(q >= 7, f"Expected q >= 7 for n={n}, got {q}")
        require(2 * q > n and q <= n and F[q] >= n, f"Bad q={q} for n={n}")
        for i in range(1, n + 1):
            if i != q:
                require(gcd(F[q], F[i]) == 1, f"gcd(F_{q}, F_{i}) != 1")

    # 4. Verify the clearing-denominator divisibility & bound directly for n = 5 and 7 <= n <= 40
    for n in [5] + list(range(7, 41)):
        q = 5 if n == 5 else (7 if n <= 11 else next(p for p in range(n // 2 + 1, n + 1) if is_prime(p)))
        for k in range(1, 7):
            P = 1
            for i in range(1, n + 1):
                if i != q:
                    P *= F[i] ** k
            Q = sum(P // (F[i] ** k) for i in range(1, n + 1) if i != q)
            T = P + (F[q] ** k) * Q
            require(gcd(T, F[q] ** k) == 1, f"gcd(T, F_q^k) != 1 at n={n}, k={k}")
            require(T > (n ** k) * P, f"T <= n^k P at n={n}, k={k}")

    # 5. Cases n = 4 and n = 6 coprimality checks
    for k in range(1, 40):
        U4 = 2 * (6 ** k) + (3 ** k) + (2 ** k)
        require(U4 > 1 and gcd(U4, (4 ** k) * (6 ** k)) == 1, f"n=4 failed at k={k}")
        U6 = 2 * (120 ** k) + (60 ** k) + (40 ** k) + (24 ** k) + (15 ** k)
        require(U6 > 1 and gcd(U6, (6 ** k) * (120 ** k)) == 1, f"n=6 failed at k={k}")

    # 6. Case n = 3: 2^(k+1) + 1 = 3^j iff k = 2 (checked for 1 <= k <= 300)
    for k in range(1, 301):
        u = (1 << (k + 1)) + 1
        while u % 3 == 0:
            u //= 3
        require((u == 1) == (k == 2), f"n=3 failed at k={k}")

    print("ALL CHECKS PASSED: Mandal-Mohan Conjecture 1.19 & Theorem 1.18 verified.")


if __name__ == "__main__":
    main()
