"""Independent exact verifier for the disproof of OEIS A108569 conjecture.

Conjecture (Farideh Firoozbakht, OEIS A108569, Jul 5 2005; formalized in
google-deepmind/formal-conjectures FormalConjectures/OEIS/108569.lean):
  For A = {n > 0 : phi(n) = phi(n + phi(n))}, except for the first term (n = 1),
  all terms are even.

Counterexample:
  n = 5,095,354,107 = 3 * 1033 * 1,644,193 (odd, > 1)
  phi(n) = 3,393,612,288
  n + phi(n) = 8,488,966,395 = 3 * 5 * 7 * 13 * 19 * 327,317
  phi(n + phi(n)) = 3,393,612,288 = phi(n).

Infinite odd family:
  n_k = 3^k * 5,095,354,107 for all k >= 0.
"""


def is_prime_exhaustive(p: int) -> bool:
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1 if d == 2 else 2
    return True


def factor_exhaustive(x: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            factors[d] = factors.get(d, 0) + 1
            x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        factors[x] = factors.get(x, 0) + 1
    return factors


def euler_phi(x: int) -> int:
    factors = factor_exhaustive(x)
    prod = 1
    for p, e in factors.items():
        assert is_prime_exhaustive(p), f"{p} is not prime!"
        prod *= (p - 1) * (p ** (e - 1))
    # Cross-check factorization reconstructs x exactly
    recon = 1
    for p, e in factors.items():
        recon *= p ** e
    assert recon == x
    return prod


def main() -> None:
    # 1. Verify base counterexample
    n = 5_095_354_107
    assert n > 1 and n % 2 == 1
    assert n == 3 * 1033 * 1_644_193
    for p in (3, 1033, 1_644_193):
        assert is_prime_exhaustive(p)

    phi_n = euler_phi(n)
    assert phi_n == 2 * 1032 * 1_644_192 == 3_393_612_288

    m = n + phi_n
    assert m == 8_488_966_395
    assert m == 3 * 5 * 7 * 13 * 19 * 327_317
    for q in (3, 5, 7, 13, 19, 327_317):
        assert is_prime_exhaustive(q)

    phi_m = euler_phi(m)
    assert phi_m == 2 * 4 * 6 * 12 * 18 * 327_316 == 3_393_612_288
    assert phi_n == phi_m

    # 2. Verify infinite odd family n_k = 3^k * n for k = 0..5
    for k in range(6):
        nk = (3 ** k) * n
        assert nk > 1 and nk % 2 == 1
        pnk = euler_phi(nk)
        assert pnk == (3 ** k) * phi_n
        assert euler_phi(nk + pnk) == pnk

    print("VERIFIED: OEIS A108569 conjecture is FALSE.")
    print(f"  Base odd counterexample: n = {n} = 3 * 1033 * 1644193")
    print(f"  phi(n) = {phi_n}")
    print(f"  n + phi(n) = {m} = 3 * 5 * 7 * 13 * 19 * 327317")
    print(f"  phi(n + phi(n)) = {phi_m}")
    print("  Infinite odd family verified for k = 0..5: n_k = 3^k * 5095354107.")


if __name__ == "__main__":
    main()
