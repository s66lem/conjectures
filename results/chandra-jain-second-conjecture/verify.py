r"""Standalone numerical verification for the Second Chandra--Jain Conjecture
(arXiv:2608.11372v3, Section 5, conj:chandra-jain-second) and exact degree criterion.

c_k(N) = (1/4) sqrt(2/N) cot(k pi / (2N)) csc^2(k pi / (2N)) lies in K = Q(zeta_M)
for M = 8N. Its algebraic degree [Q(c_k(N)) : Q] equals the size of its orbit under
Gal(K/Q) = {sigma_a : a in (Z/M)^*}.

The Galois orbit is computed directly from sigma_a(zeta_M) = zeta_M^a using:
  - f(y) = cos(y)/sin^3(y) = -4 i (z + z^-1) / (z - z^-1)^3, z = zeta_M^(2k), i = zeta_M^(2N);
  - sqrt(2N) written explicitly as a product of quadratic Gauss sums, zeta_4, and zeta_8 + zeta_8^-1.

Checks:
  1. Explicit Gauss-sum representation of sqrt(2N) for 3 <= N <= 120.
  2. Closed form c_k(N) against the inner product <u_N, psi_{N,k}> for 3 <= N <= 40.
  3. Paper's c_1(N) degree table for 3 <= N <= 16.
  4. Paper's 59 / 48 split of the 107 non-coprime cases with 3 <= N <= 50.
  5. Dichotomy [Q(c_k(N)):Q] in {phi(N0), 2 phi(N0)} for all odd non-coprime 1 <= k < N <= 120.
  6. Coprime degree phi(N) for all odd k coprime to N, 3 <= N <= 120.
  7. Exact criterion (Theorem B) for all odd 1 <= k < N <= 120 (3599 pairs).
  8. Explicit CRT sign-flip witness a = 1 (mod 2 N0) with sigma_a(c) = -c for every odd N0,
     and non-residue CRT witness for every even N0 with some prime p having v_p(d) odd and p not| N0.
"""
import cmath
import math
from math import gcd

NMAX = 120


def require(cond, msg):
    if not cond:
        raise SystemExit("CHECK FAILED: " + msg)


def phi(n):
    return sum(1 for a in range(1, n + 1) if gcd(a, n) == 1)


def factor(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def legendre(n, p):
    n %= p
    if n == 0:
        return 0
    return 1 if pow(n, (p - 1) // 2, p) == 1 else -1


def root(M, e):
    return cmath.exp(2j * math.pi * (e % M) / M)


def sqrt2N_terms(N):
    M = 8 * N
    fac = factor(2 * N)
    m = 1
    q_primes = []
    for p, e in fac.items():
        m *= p ** (e // 2)
        if e % 2:
            q_primes.append(p)
    scalar = complex(m)
    factors = []
    n_minus = 0
    for p in q_primes:
        if p == 2:
            factors.append([(1, M // 8), (1, -M // 8)])
        else:
            factors.append([(legendre(n, p), n * (M // p)) for n in range(1, p)])
            if p % 4 == 3:
                n_minus += 1
    if n_minus % 4:
        factors.append([(1, -(M // 4) * n_minus)])
    return scalar, factors


def sigma_value(N, k, a, sq):
    M = 8 * N
    scalar, factors = sq
    s = scalar
    for fct in factors:
        s *= sum(c * root(M, a * e) for c, e in fct)
    z = root(M, 2 * k * a)
    ii = root(M, 2 * N * a)
    fy = -4 * ii * (z + 1 / z) / (z - 1 / z) ** 3
    return s * fy / (4 * N)


def orbit(N, k, sq, units):
    vals = []
    for a in units:
        v = sigma_value(N, k, a, sq)
        require(abs(v.imag) <= 1e-7 * max(1.0, abs(v)), f"conjugate not real N={N} k={k}")
        vals.append(v.real)
    vals.sort()
    distinct = [vals[0]]
    for v in vals[1:]:
        if abs(v - distinct[-1]) > 1e-8 * max(1.0, abs(v)):
            distinct.append(v)
    return distinct


def closed_form(k, N):
    y = k * math.pi / (2 * N)
    return 0.25 * math.sqrt(2.0 / N) * math.cos(y) / math.sin(y) ** 3


def criterion(k, N):
    d = gcd(k, N)
    N0 = N // d
    if N0 % 2 == 1:
        return phi(N0)
    ok = all(N0 % p == 0 for p, e in factor(d).items() if e % 2 == 1)
    return phi(N0) if ok else 2 * phi(N0)


def main():
    # 1. Explicit Gauss-sum representation of sqrt(2N)
    for N in range(3, NMAX + 1):
        sq = sqrt2N_terms(N)
        s = sq[0]
        for fct in sq[1]:
            s *= sum(c * root(8 * N, e) for c, e in fct)
        require(abs(s - math.sqrt(2 * N)) < 1e-8 * math.sqrt(2 * N), f"sqrt(2N) repr N={N}")

    # 2. Closed form vs inner-product definition c_k(N) = <u_N, psi_{N,k}>
    for N in range(3, 41):
        for k in range(1, N):
            ip = sum(
                (j * (N - j) / 2.0) * math.sqrt(2.0 / N) * math.sin(k * math.pi * j / N)
                for j in range(N + 1)
            )
            want = closed_form(k, N) if k % 2 == 1 else 0.0
            require(abs(ip - want) < 1e-9 * max(1.0, abs(want)), f"closed form N={N} k={k}")

    degs = {}
    split = [0, 0]
    odd_witnesses = 0
    even_double_witnesses = 0

    for N in range(3, NMAX + 1):
        M = 8 * N
        units = [a for a in range(1, M) if gcd(a, M) == 1]
        sq = sqrt2N_terms(N)
        for k in range(1, N, 2):
            orb = orbit(N, k, sq, units)
            g = len(orb)
            c = closed_form(k, N)
            require(any(abs(c - v) <= 1e-8 * max(1.0, abs(c)) for v in orb), f"c in orbit N={N} k={k}")
            degs[(N, k)] = g
            d = gcd(k, N)
            N0 = N // d
            if d == 1:
                require(g == phi(N), f"coprime degree N={N} k={k} g={g}")
            else:
                require(g in (phi(N0), 2 * phi(N0)), f"dichotomy N={N} k={k} g={g}")
                if N <= 50:
                    split[0 if g == phi(N0) else 1] += 1
            want = criterion(k, N)
            require(g == want, f"criterion N={N} k={k} g={g} want={want}")

            if N0 % 2 == 1:
                # Explicit CRT witness: a = 1 (mod N), a = 5 (mod 8)
                a_wit = next(a for a in units if a % N == 1 and a % 8 == 5)
                require(a_wit % (2 * N0) == 1, f"odd witness mod 2N0 N={N} k={k}")
                v = sigma_value(N, k, a_wit, sq).real
                require(abs(v + c) <= 1e-8 * max(1.0, abs(c)), f"odd witness failed N={N} k={k}")
                odd_witnesses += 1
            elif want == 2 * phi(N0):
                # Explicit witness a = 1 (mod 2 N0) with sigma_a(c) = -c
                found = any(
                    a % (2 * N0) == 1 and abs(sigma_value(N, k, a, sq).real + c) <= 1e-8 * max(1.0, abs(c))
                    for a in units
                )
                require(found, f"even 2*phi(N0) witness failed N={N} k={k}")
                even_double_witnesses += 1

    # 3. Paper's c_1(N) degree table (N = 3..16)
    table = [2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8]
    require([degs[(N, 1)] for N in range(3, 17)] == table, "c_1 degree table mismatch")

    # 4. Paper's 59 / 48 split for 107 non-coprime cases with N <= 50
    require(split == [59, 48], f"N<=50 non-coprime split mismatch: {split}")

    print(
        f"Checked {len(degs)} pairs (3 <= N <= {NMAX}); "
        f"N0-odd witnesses: {odd_witnesses}; "
        f"N0-even 2*phi(N0) witnesses: {even_double_witnesses}; "
        f"N<=50 non-coprime split: {split}"
    )
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
