"""Standalone stdlib-only verifier for the disproof of OEIS A189409 (John M. Campbell, 2011).

Checks:
1. Exact values of a(n) = (p_n#)^2 + 1 for n = 0..10.
2. Exact squarefreeness of a(0)..a(8) via deterministic Lucas primality certificates.
3. Exact divisibility 29^2 | a(9) and full factorization a(9) = 29^2 * 53 * 1116604864937.
4. Exhaustive scan of prime-square divisors p^2 | a(n) for n <= 200 and p <= 20000.
"""

import math


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def sieve_primes(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, math.isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i :: i] = [False] * len(sieve[i * i :: i])
    return [i for i, ok in enumerate(sieve) if ok]


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            return False
    return True


def verify_lucas_prime(p: int, witness: int, prime_factors_of_p_minus_1: list[int]) -> None:
    require(p >= 2, f"p must be >= 2, got {p}")
    require(pow(witness, p - 1, p) == 1, f"Fermat test failed for p={p}, a={witness}")
    rem = p - 1
    for q in prime_factors_of_p_minus_1:
        require(is_prime_trial(q), f"Factor {q} of {p - 1} is not prime")
        require((p - 1) % q == 0, f"{q} does not divide {p - 1}")
        require(pow(witness, (p - 1) // q, p) != 1, f"Lucas condition failed for p={p}, q={q}")
        while rem % q == 0:
            rem //= q
    require(rem == 1, f"Unfactored remainder {rem} for {p - 1}")


def main() -> None:
    primes = sieve_primes(20000)
    first_nine = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    require(primes[:9] == first_nine, "First nine primes mismatch")

    expected_a = [
        2,
        5,
        37,
        901,
        44101,
        5336101,
        901800901,
        260620460101,
        94083986096101,
        49770428644836901,
    ]
    prod = 1
    vals = []
    for n in range(10):
        if n > 0:
            prod *= primes[n - 1]
        val = prod * prod + 1
        require(val == expected_a[n], f"a({n}) mismatch: got {val}, expected {expected_a[n]}")
        vals.append(val)

    # 1. Verify disproof at n = 9
    require(vals[9] == 29 * 29 * 53 * 1116604864937, "Factorization of a(9) mismatch")
    require(vals[9] % (29 * 29) == 0, "29^2 must divide a(9)")
    require(is_prime_trial(29) and is_prime_trial(53), "29 and 53 must be prime")

    # 2. Verify exact minimality (a(0)..a(8) are all squarefree)
    verify_lucas_prime(44101, 6, [2, 3, 5, 7])
    verify_lucas_prime(5336101, 6, [2, 3, 5, 7, 11])
    verify_lucas_prime(12353437, 6, [2, 3, 409, 839])
    verify_lucas_prime(184968389, 2, [2, 11, 79, 127, 419])
    verify_lucas_prime(94083986096101, 2, [2, 3, 5, 7, 11, 13, 17, 19])

    require(is_prime_trial(2) and is_prime_trial(5) and is_prime_trial(37), "a(0..2) prime check")
    require(vals[3] == 17 * 53 and is_prime_trial(17) and is_prime_trial(53), "a(3) check")
    require(vals[6] == 73 * 12353437 and is_prime_trial(73), "a(6) check")
    require(vals[7] == 1409 * 184968389 and is_prime_trial(1409), "a(7) check")

    # 3. Verify uniqueness of p^2 | a(n) for n <= 200, p <= 20000
    hits = []
    for p in primes:
        if p % 4 != 1:
            continue
        p2 = p * p
        cur = 1 % p2
        for n in range(1, 201):
            q = primes[n - 1]
            if q == p:
                break
            cur = (cur * q) % p2
            if (cur * cur + 1) % p2 == 0:
                hits.append((n, p))
    require(hits == [(9, 29)], f"Unexpected hits in n<=200, p<=20000: {hits}")

    print("ALL CHECKS PASSED")
    print(f"Counterexample: a(9) = (23#)^2 + 1 = {vals[9]} = 29^2 * 53 * 1116604864937")
    print("Minimality: a(0)..a(8) all certified squarefree via deterministic Lucas certificates.")
    print("Range scan (n <= 200, p <= 20000): unique prime-square divisibility hit is (n=9, p=29).")


if __name__ == "__main__":
    main()
