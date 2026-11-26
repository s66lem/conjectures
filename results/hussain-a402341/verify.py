r"""Independent stdlib-only verifier for Result #30:
2-adic valuation of central coefficients of (1 + x + ... + x^(2^r - 1))^(2m)
and OEIS A402341 (Sajid Khan Hussain, Nov 17 2026).

Checks:
1. Published initial terms of OEIS A402341 (n = 0..19) against direct polynomial
   exponentiation and inclusion-exclusion.
2. Homogenized polynomial identities evalY(2^k, R_k) == 1 + x^(2^k) and
   evalY(2^r - 1, Q_r) == 1 + x + ... + x^(2^r - 1) for r = 1..6.
3. Admissibility of R_k and Q_r, and strong admissibility of Q_r^2, for r = 1..6.
4. Exact congruence a_r(2m) == comb(2N, N) (mod 2^(s_2(N) + 1)) and exact valuation
   v_2(a_r(2m)) == s_2(N) for:
   - r = 1..5 over dense ranges of even n,
   - OEIS A402341 (r = 4) for every even n in 0..160 via polynomial powers, and
   - selected large even exponents up to n = 2048 via inclusion-exclusion.
5. Odd-n sharpness remark: A402341(3) = 192 has v_2(192) = 6 != s_2(22) = 3.

Run with:
    python -O -W error results/hussain-a402341/verify.py
"""

from math import comb


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(f"VERIFICATION FAILED: {msg}")


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] += ai * bj
    return res


def poly_sub(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(n):
        if i < len(a):
            res[i] += a[i]
        if i < len(b):
            res[i] -= b[i]
    while len(res) > 1 and res[-1] == 0:
        res.pop()
    return res


def s2(n: int) -> int:
    return n.bit_count()


def v2(n: int) -> int:
    require(n > 0, f"v2 called on non-positive integer {n}")
    return (n & -n).bit_length() - 1


def build_R(k: int) -> list[int]:
    """Build R_k(y) with R_0 = 1 and R_{k+1} = R_k^2 - 2 y^(2^k)."""
    R = [1]
    for j in range(k):
        sq = poly_mul(R, R)
        mon = [0] * (1 << j) + [2]
        R = poly_sub(sq, mon)
    return R


def build_Q(r: int) -> list[int]:
    Q = [1]
    for k in range(r):
        Q = poly_mul(Q, build_R(k))
    return Q


def eval_Y(D: int, F: list[int]) -> list[int]:
    """Compute sum_j F[j] * x^j * (1 + x)^(D - 2j)."""
    out = [0] * (D + 1)
    for j, c in enumerate(F):
        if c == 0:
            continue
        require(2 * j <= D, f"degree bound violated: 2*{j} > {D}")
        rem = D - 2 * j
        for t in range(rem + 1):
            out[j + t] += c * comb(rem, t)
    return out


def central_coeff_inc_excl(L: int, n: int) -> int:
    """[x^(floor((L-1)n/2))] (1 + x + ... + x^(L-1))^n via inclusion-exclusion."""
    if n == 0:
        return 1
    h = ((L - 1) * n) // 2
    return sum(
        ((-1) ** j) * comb(n, j) * comb(n - 1 + h - L * j, n - 1)
        for j in range(h // L + 1)
    )


def check_published_oeis_terms() -> None:
    oeis_a402341 = [
        1,
        1,
        16,
        192,
        2736,
        39280,
        577744,
        8582336,
        128912240,
        1947652092,
        29632604816,
        452466790336,
        6942916764720,
        106788367505456,
        1648570691046736,
        25491847538274240,
        395320344293410544,
        6137695417757646851,
        95516115829966102480,
        1487718892458984362752,
    ]
    p = [1]
    base = [1] * 16
    for n, expected in enumerate(oeis_a402341):
        h = (15 * n) // 2
        require(p[h] == expected, f"Poly mismatch at n={n}: {p[h]} != {expected}")
        require(max(p) == expected, f"Central coeff not maximum at n={n}")
        ie = central_coeff_inc_excl(16, n)
        require(ie == expected, f"Inclusion-exclusion mismatch at n={n}")
        if n + 1 < len(oeis_a402341):
            p = poly_mul(p, base)
    # Odd-n sharpness remark
    require(v2(oeis_a402341[3]) == 6 and s2(22) == 3, "Odd n=3 remark check failed")


def check_polynomial_identities_and_admissibility() -> None:
    for k in range(6):
        Rk = build_R(k)
        require(Rk[0] == 1, f"R_{k}(0) != 1")
        for j, c in enumerate(Rk):
            require(c % (1 << s2(j)) == 0, f"R_{k} not admissible at j={j}")
        ev = eval_Y(1 << k, Rk)
        target = [0] * ((1 << k) + 1)
        target[0] = 1
        target[1 << k] = 1
        require(ev == target, f"evalY(2^{k}, R_{k}) != 1 + x^(2^{k})")

    for r in range(1, 7):
        Qr = build_Q(r)
        require(Qr[0] == 1, f"Q_{r}(0) != 1")
        for j, c in enumerate(Qr):
            require(c % (1 << s2(j)) == 0, f"Q_{r} not admissible at j={j}")
        Qsq = poly_mul(Qr, Qr)
        require(Qsq[0] == 1, f"Q_{r}^2(0) != 1")
        for j in range(1, len(Qsq)):
            require(
                Qsq[j] % (1 << (s2(j) + 1)) == 0,
                f"Q_{r}^2 not strongly admissible at j={j}",
            )
        ev = eval_Y((1 << r) - 1, Qr)
        require(ev == [1] * (1 << r), f"evalY(2^{r}-1, Q_{r}) != 1+...+x^(2^{r}-1)")


def check_congruence_and_valuation(r: int, n: int, coeff: int) -> None:
    require(n % 2 == 0, f"Expected even n, got {n}")
    N = ((1 << r) - 1) * (n // 2)
    mod = 1 << (s2(N) + 1)
    cb = comb(2 * N, N)
    require((coeff - cb) % mod == 0, f"Congruence failed at r={r}, n={n}")
    require(v2(coeff) == s2(N), f"Valuation failed at r={r}, n={n}")


def check_families() -> None:
    # Dense direct polynomial power checks for r = 1..5
    limits = {1: 80, 2: 60, 3: 40, 4: 160, 5: 24}
    for r, max_n in limits.items():
        L = 1 << r
        base = [1] * L
        base2 = poly_mul(base, base)
        p = [1]
        for n in range(0, max_n + 1, 2):
            N = (L - 1) * (n // 2)
            check_congruence_and_valuation(r, n, p[N])
            if n + 2 <= max_n:
                p = poly_mul(p, base2)

    # Large even exponents for r = 4 (OEIS A402341) and r = 5 via inclusion-exclusion
    large_even = (254, 256, 258, 510, 512, 514, 1022, 1024, 1026, 1500, 1502, 2048)
    for n in large_even:
        check_congruence_and_valuation(4, n, central_coeff_inc_excl(16, n))
    for n in (64, 128, 256, 512):
        check_congruence_and_valuation(5, n, central_coeff_inc_excl(32, n))


def main() -> None:
    check_published_oeis_terms()
    check_polynomial_identities_and_admissibility()
    check_families()
    print(
        "ALL CHECKS PASSED: OEIS A402341 terms (n=0..19), R_k/Q_r identities and "
        "strong admissibility (r=1..6), dense polynomial powers (r=1..5, including "
        "A402341 for all even n <= 160), and large inclusion-exclusion cases up to n = 2048."
    )


if __name__ == "__main__":
    main()
