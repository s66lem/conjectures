r"""Standalone verifier for Benjamini–Kozma–Tzalik (Electron. J. Combin. 33(3), 2026, #P3.28 / arXiv:2303.07956v2), Question 9.

Question 9: "How many tiles are contained in the set {1, 2, 4, ..., 2^n}?
Are the only such tiles the sets of size 1 and 2?"

Checks (exact integer arithmetic, stdlib only, -O safe):
  A. {1, 4, 16} tiles Z with T = {-1, 0, 1} + 9Z (answers the second part negatively for all n >= 4).
  B. For every odd k <= 199, {q^d : 0 <= d < k} with q = 2^r, r = ord_{rad k}(2), tiles Z.
  C. Minimal exponent spans (p-1)*ord_p(2) for p = 3, 5, 7, span 16 for k = 9, no size 4/8 tiles, size-3 count formula.
  D. Phi_{2^j} never divides S(x) for normalized power-of-2 sets of size k >= 3.
  E. Exact counts t(n) of tiles inside {1, 2, ..., 2^n} for 0 <= n <= 15.
"""
import sys
from itertools import combinations
from math import comb


def require(cond, msg):
    if not cond:
        sys.stderr.write("FAIL: " + msg + "\n")
        sys.exit(1)


def vp(x, p):
    x = abs(x)
    require(x != 0, "vp of zero")
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def prime_factors(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def mult_order(a, m):
    if m == 1:
        return 1
    x, r = a % m, 1
    while x != 1:
        x = x * a % m
        r += 1
    return r


def newman_tiles(S):
    """Newman (1977): |S| = p^a tiles Z iff pairwise-difference p-adic valuations take <= a values."""
    k = len(S)
    pf = prime_factors(k)
    require(len(pf) == 1, "newman needs prime-power size")
    p = pf[0]
    a = vp(k, p)
    vals = {vp(x - y, p) for x, y in combinations(S, 2)}
    return len(vals) <= a


def main():
    # A. Counterexample {1, 4, 16}
    S = [1, 4, 16]
    T0 = [-1, 0, 1]
    res = sorted((s + t) % 9 for s in S for t in T0)
    require(res == list(range(9)), "S + T0 is not a complete residue system mod 9")
    for z in range(-500, 501):
        reps = [(s, z - s) for s in S if (z - s) % 9 in (8, 0, 1)]
        require(len(reps) == 1, "unique representation fails at %d" % z)
    require(all(x in [2 ** j for j in range(5)] for x in S), "S not inside {1,..,2^4}")
    print("A ok: {1, 4, 16} tiles Z with T = {-1, 0, 1} + 9Z (inside {1, 2, 4, 8, 16})")

    # B. Every odd size k occurs
    for k in range(1, 200, 2):
        rad = 1
        for p in prime_factors(k):
            rad *= p
        r = mult_order(2, rad)
        q = 2 ** r
        g = q - 1
        F = [(q ** d - 1) // g for d in range(k)]
        require(sorted(f % k for f in F) == list(range(k)), "B: F not complete mod %d" % k)
        if k <= 15:
            Sk = [q ** d for d in range(k)]
            period = g * k
            for z in range(0, 2 * period):
                cnt = sum(1 for s in Sk if ((z - s + 1) % period) < g)
                require(cnt == 1, "B: window check k=%d z=%d" % (k, z))
    print("B ok: for all odd k <= 199, {2^(r*d) : d < k} with r = ord_{rad k}(2) tiles Z")

    # C. Newman enumerations & minimal spans
    def min_span(k, maxspan):
        for span in range(1, maxspan + 1):
            for mid in combinations(range(1, span), k - 2):
                C = (0,) + mid + (span,)
                if newman_tiles([2 ** c for c in C]):
                    return span
        return None

    for p in (3, 5, 7):
        r = mult_order(2, p)
        require(min_span(p, (p - 1) * r) == (p - 1) * r, "C: min span for p=%d" % p)
    require(min_span(9, 16) == 16, "C: min span for k=9")
    for k in (4, 8):
        for C in combinations(range(13), k):
            require(not newman_tiles([2 ** c for c in C]), "C: size %d tile found" % k)

    def t3_formula(n):
        tot = 0
        for c in range(n + 1):
            B = (n - c) // 2
            for a in range(1, B + 1):
                for b in range(a + 1, B + 1):
                    e = vp(a, 3)
                    if vp(b, 3) == e and vp(b - a, 3) == e:
                        tot += 1
        return tot

    for n in range(0, 25):
        brute = sum(1 for C in combinations(range(n + 1), 3) if newman_tiles([2 ** c for c in C]))
        require(brute == t3_formula(n), "C: size-3 formula at n=%d" % n)
    print("C ok: min spans 4, 16, 18 (p=3,5,7), 16 (k=9); no size 4/8 tiles; size-3 formula")

    # D. No 2-power cyclotomic factor for normalized power-of-2 sets of size >= 3
    def fiber_ok(S_set, m, h, p):
        cnt = {}
        for s in S_set:
            cnt[s % m] = cnt.get(s % m, 0) + 1
        for rr in {x % h for x in cnt}:
            if len({cnt.get(rr + j * h, 0) for j in range(p)}) > 1:
                return False
        return True

    for k in range(3, 12):
        for mid in combinations(range(1, 12), k - 1):
            Sn = [1] + [2 ** c for c in mid]
            for j in range(1, 14):
                require(not fiber_ok(Sn, 2 ** j, 2 ** (j - 1), 2), "D: Phi_2^%d divides" % j)
    print("D ok: Phi_{2^j} never divides S(x) for normalized power-of-2 sets, k >= 3")

    # E. Exact counts t(n) for n <= 15
    for p in (5, 7, 11, 13):
        require((p - 1) * mult_order(2, p) >= 16, "E: span bound p=%d" % p)
    table = [(n, (n + 1) + comb(n + 1, 2) + t3_formula(n)) for n in range(16)]
    expected = [1, 3, 6, 10, 16, 23, 31, 40, 51, 63, 78, 94, 112, 131, 153, 176]
    require([t for _, t in table] == expected, "E: t(n) mismatch")
    print("E ok: t(n) for n=0..15:", expected)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
