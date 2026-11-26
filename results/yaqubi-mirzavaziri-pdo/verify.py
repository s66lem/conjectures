r"""Standalone verifier for Yaqubi--Mirzavaziri Conjecture 6.2 (arXiv:2611.05623v1).

B_k(n) = [q^n] G^k, where G = f_4 f_6^2 / (f_1 f_3 f_12) and f_m = prod_{j>=1} (1 - q^{mj}).
Conjecture 6.2: for every k >= 1, the largest power of 2 dividing all B_k(4n + 3) is
2^{v_2(B_k(3))}, except 2^2 when k == 1 (mod 8) and 2^3 when k == 6 (mod 8).

Standard library only; safe under `python -O -W error verify.py`.
"""

from math import comb

T = 200
KMAX = 160
MOD = 1 << 48


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"Verification failed: {msg}")


def mul(a: list[int], b: list[int], mod: int | None = None) -> list[int]:
    c = [0] * T
    for i, x in enumerate(a):
        if x:
            for j in range(T - i):
                c[i + j] += x * b[j]
    return [x % mod for x in c] if mod is not None else c


def expand(a: list[int], m: int) -> list[int]:
    c = [0] * T
    for i, x in enumerate(a):
        if i * m < T:
            c[i * m] = x
    return c


def eta(m: int) -> list[int]:
    a = [0] * T
    a[0] = 1
    n = 1
    while m * n < T:
        for i in range(T - 1, m * n - 1, -1):
            a[i] -= a[i - m * n]
        n += 1
    return a


def inv(a: list[int]) -> list[int]:
    require(a[0] == 1, "invertible series must have constant term 1")
    b = [0] * T
    b[0] = 1
    for n in range(1, T):
        b[n] = -sum(a[i] * b[n - i] for i in range(1, n + 1))
    return b


def v2(x: int) -> int:
    x %= MOD
    return 48 if x == 0 else (x & -x).bit_length() - 1


def main() -> None:
    f1, f2, f3, f4, f6, f12 = (eta(m) for m in (1, 2, 3, 4, 6, 12))
    G = mul(mul(f4, mul(f6, f6)), inv(mul(mul(f1, f3), f12)))

    # 1. Cross-check G against combinatorial PDO product prod_{t odd} (1 + sum_{m>=1} m q^{tm}).
    comb_G = [1] + [0] * (T - 1)
    for t in range(1, T, 2):
        fac = [0] * T
        fac[0] = 1
        for m in range(1, (T - 1) // t + 1):
            fac[t * m] = m
        comb_G = mul(comb_G, fac)
    require(G == comb_G, "eta quotient G != combinatorial PDO generating function")

    # 2. Check Gauss identities (J1), (J2), psi*psi(q^3), and 2-dissection of G.
    phi = [0] * T
    phi[0] = 1
    k = 1
    while k * k < T:
        phi[k * k] = 2
        k += 1
    phi_neg = [((-1) ** n) * phi[n] for n in range(T)]

    psi = [0] * T
    k = 0
    while k * (k + 1) // 2 < T:
        psi[k * (k + 1) // 2] = 1
        k += 1

    require(mul(f1, psi) == mul(f2, f2), "Gauss (J1): f1 * psi != f2^2")
    require(mul(f2, phi_neg) == mul(f1, f1), "Gauss (J2): f2 * phi(-q) != f1^2")

    lhs_psi = mul(psi, expand(psi, 3))
    term1 = mul(expand(phi, 6), expand(psi, 4))
    term2_raw = mul(expand(phi, 2), expand(psi, 12))
    term2 = [0] + term2_raw[:-1]
    require(lhs_psi == [term1[i] + term2[i] for i in range(T)], "psi(q)*psi(q^3) identity failed")

    inv_denom = inv(mul(phi_neg, f6))
    E1 = mul(mul(expand(phi, 3), expand(psi, 2)), inv_denom)
    O1 = mul(mul(phi, expand(psi, 6)), inv_denom)
    E1_2 = expand(E1, 2)
    O1_2 = expand(O1, 2)
    G_dissect = [E1_2[i] + (O1_2[i - 1] if i >= 1 else 0) for i in range(T)]
    require(G == G_dissect, "2-dissection of G failed")

    # 3. Exact finite certificates for G[:8], B_k(3), and B_k(7).
    require(G[:8] == [1, 1, 2, 4, 5, 8, 12, 16], f"unexpected G[:8] = {G[:8]}")
    Gm1 = [0] + G[1:]
    pows = [[1] + [0] * (T - 1)]
    for _ in range(7):
        pows.append(mul(pows[-1], Gm1))
    c3 = [pows[i][3] for i in range(4)]
    c7 = [pows[i][7] for i in range(8)]
    require(c3 == [0, 4, 4, 1], f"unexpected c3 = {c3}")
    require(c7 == [0, 16, 96, 180, 148, 60, 12, 1], f"unexpected c7 = {c7}")

    def B_poly(kk: int, n: int) -> int:
        return sum(comb(kk, i) * pows[i][n] for i in range(n + 1))

    for kk in range(1, 300):
        require(6 * B_poly(kk, 3) == kk * (kk + 2) * (kk + 7), f"B_k(3) mismatch at k={kk}")

    for j in range(1, 8):
        require(comb(32, j) % 8 == 0, f"8 does not divide C(32, {j})")
        require(comb(64, j) % 16 == 0, f"16 does not divide C(64, {j})")

    for kk in (9, 25):
        val = B_poly(kk, 7)
        require(val % 8 == 4, f"B_{kk}(7) % 8 != 4 (got {val % 8})")
    for kk in (14, 30, 46, 62):
        val = B_poly(kk, 7)
        require(val % 16 == 8, f"B_{kk}(7) % 16 != 8 (got {val % 16})")

    # 4. Empirical check of (P1), (P2), (P3), Lemma 2, and full Conjecture 6.2 for k <= 160, 4n+3 < 200.
    B1 = G
    B2 = mul(G, G)
    require(all(B1[n] % 4 == 0 for n in range(3, T, 4)), "(P1) failed")
    require(all(B2[n] % 4 == 0 for n in range(3, T, 4)), "(P2) failed")

    def conj_exp(kk: int) -> int:
        if kk % 8 == 1:
            return 2
        if kk % 8 == 6:
            return 3
        return v2(kk * (kk + 2) * (kk + 7) // 6)

    P = [1] + [0] * (T - 1)
    Gm = [x % MOD for x in G]
    for kk in range(1, KMAX + 1):
        P = mul(P, Gm, MOD)
        odd_min = min(v2(P[n]) for n in range(1, T, 2))
        require(odd_min >= v2(kk), f"Lemma 2 failed at k={kk}")
        vals = [v2(P[n]) for n in range(3, T, 4)]
        require(min(vals) == conj_exp(kk), f"Conjecture 6.2 failed at k={kk}")
        if kk % 16 == 9:
            require(vals[1] == 2, f"B_k(7) witness failed at k={kk}")
        if kk % 16 == 14:
            require(vals[1] == 3, f"B_k(7) witness failed at k={kk}")

    print(
        "ALL CHECKS PASSED: G == comb_G, Gauss (J1)/(J2), psi*psi(q^3), 2-dissection, "
        f"exact B_k(3) & B_k(7) certificates, and Conjecture 6.2 for 1 <= k <= {KMAX}, 4n+3 < {T}."
    )


if __name__ == "__main__":
    main()
