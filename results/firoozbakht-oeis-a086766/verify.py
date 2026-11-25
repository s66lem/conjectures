"""Standalone stdlib-only (-O-safe) verifier for the disproof of
Farideh Firoozbakht's 2015 OEIS A086766 conjecture.
"""


def require(cond, msg=""):
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def f_cand(n, r):
    s = str(n)
    return int(s * r + "1")


def is_primitive_str(s):
    d = len(s)
    return all(s != s[:p] * (d // p) for p in range(1, d) if d % p == 0)


def verify_diff_squares(name, n, k, c, e, g1o, g2o, g1e, g2e, expect_primitive=True):
    M = 10 ** (2 * k) - 1
    require(10 ** (2 * k - 1) < n < 10 ** (2 * k), f"{name}: digit range")
    require(10 * n == c * c, f"{name}: 10n != c^2")
    require(c * c - e * e == M and 0 <= e < c, f"{name}: c^2 - e^2 != M")
    require(g1o * g2o == M and g1e * g2e == M, f"{name}: divisor split product")
    require((c * 10**k - e) % g1o == 0 and (c * 10**k + e) % g2o == 0, f"{name}: odd divisibility")
    require((c - e) % g1e == 0 and (c + e) % g2e == 0, f"{name}: even divisibility")
    require(g1o < c * 10**k - e and g2o < c * 10**k + e, f"{name}: odd factor > 1")
    require(g1e < c * 10 ** (2 * k) - e and g2e < c * 10 ** (2 * k) + e, f"{name}: even factor > 1")
    if expect_primitive:
        require(is_primitive_str(str(n)), f"{name}: not primitive")
    for r in range(1, 7):
        val = f_cand(n, r)
        g1, g2 = (g1o, g2o) if r % 2 == 1 else (g1e, g2e)
        a1 = c * 10 ** (k * r) - e
        a2 = c * 10 ** (k * r) + e
        require(a1 % g1 == 0 and a2 % g2 == 0, f"{name} r={r}: divisibility")
        q1, q2 = a1 // g1, a2 // g2
        require(q1 > 1 and q2 > 1 and q1 * q2 == val, f"{name} r={r}: factorization")


def main():
    # 1. Verify infinite family n_k = 10 * (10^(2k) - 1) / 99 for k = 2..12
    for k in range(2, 13):
        n = 10 * (10 ** (2 * k) - 1) // 99
        require(10 ** (2 * k - 1) < n < 10 ** (2 * k), f"rep10({k}) range")
        for r in range(1, 7):
            val = f_cand(n, r)
            m = k * r + 1
            if (k * r) % 2 == 0:
                q1, q2 = (10**m - 1) // 9, (10**m + 1) // 11
                require((10**m - 1) % 9 == 0 and (10**m + 1) % 11 == 0, f"rep10({k},{r}) even mod")
            else:
                q1, q2 = (10**m - 1) // 99, 10**m + 1
                require((10**m - 1) % 99 == 0, f"rep10({k},{r}) odd mod")
            require(q1 > 1 and q2 > 1 and q1 * q2 == val, f"rep10({k},{r}) factor")

    # 2. Verify minimal 6-digit primitive witness n = 104040
    verify_diff_squares(
        "primitive_104040",
        n=104040, k=3, c=1020, e=201,
        g1o=99, g2o=10101, g1e=819, g2e=1221,
    )

    # 3. Verify giant 78-digit primitive witness
    n78 = 100558839880907801793259217884670002826017800775406752876641328923179557019040
    verify_diff_squares(
        "giant78",
        n=n78, k=39,
        c=1002790306499358826910734486514389551480,
        e=74755593831351630382001287234042424799,
        g1o=82858281,
        g2o=12068799737711189060270270390958267647382160872972974179852946744091879,
        g1e=928034712668007196528733199280347126681,
        g2e=1077545900330710457292735773748431976279,
    )

    print(
        "PASS: verified infinite family rep10(k) (minimal n=1010), "
        "minimal 6-digit primitive n=104040, and 78-digit primitive counterexample to OEIS A086766."
    )


if __name__ == "__main__":
    main()
