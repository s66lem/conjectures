r"""Standalone verifier for the resolution of Dufour-Heubach Conjecture 1
on Slow A-Nim with A = {k, ..., n} (INTEGERS 26 (2026) #G3, Section 6;
arXiv:2404.06608v3, Conjecture 1 / con:atleastk).

Checks (stdlib only, safe under python -O):
  1. Disproof 1 (parity clause): (0, 1, 2, 2) in SN(4, {2, 3, 4}) is reduced
     and a P-position, yet Conjecture 1 classifies it as N.
  2. Disproof 2 (1 <= o clause & infinite family): for odd k >= 3 and
     n >= (3k - 1)/2, (3k - 1)/2 stacks of height 2 are reduced P-positions
     classified as N by Conjecture 1 (smallest: (2, 2, 2, 2) at n=4, k=3).
  3. Reduction invariance: SN(n, A) and playable graph SN~(n, A) agree.
  4. Exact corrected characterization: for ALL positions p (reduced and
     non-reduced) in SN(n, {k..n}), IsP(p) <=> floor(D(p~)/k) == floor(E(p~)/k),
     verified exhaustively across n <= 6, all 1 <= k <= n.
"""
import sys
from functools import lru_cache
from itertools import combinations

sys.setrecursionlimit(100000)


def require(cond, msg):
    if not cond:
        print("FAILED:", msg)
        sys.exit(1)


def make_isP(n, k):
    A = range(k, n + 1)

    @lru_cache(maxsize=None)
    def isP(p):
        nz = [i for i in range(n) if p[i] > 0]
        for a in A:
            if a > len(nz):
                break
            for S in combinations(nz, a):
                q = list(p)
                for i in S:
                    q[i] -= 1
                if isP(tuple(sorted(q))):
                    return False
        return True

    return isP


def reduced(p, k):
    return k * max(p) <= sum(p)


def reduction(p, k):
    t = max(p)
    while t > 0 and k * t > sum(min(x, t) for x in p):
        t -= 1
    return tuple(sorted(min(x, t) for x in p))


def make_isP_reduced_graph(n, k):
    A = range(k, n + 1)

    @lru_cache(maxsize=None)
    def isP(p):
        nz = [i for i in range(n) if p[i] > 0]
        for a in A:
            if a > len(nz):
                break
            for S in combinations(nz, a):
                q = list(p)
                for i in S:
                    q[i] -= 1
                if isP(reduction(tuple(q), k)):
                    return False
        return True

    return isP


def conjecture_says_P(p, n, k):
    s = sum(p) % (2 * k)
    o = sum(x % 2 for x in p)
    S1 = (s % 2 == o % 2) and 0 <= s < k - 1 and o <= s
    S2 = s == k - 1 and (o % 2 == n % 2) and 1 <= o <= k - 1
    S3 = (s % 2 == o % 2) and k - 1 < s < 2 * k - 1 and o <= 2 * (k - 1) - s
    return S1 or S2 or S3


def corrected_says_P(p, k):
    D = sum((x + 1) // 2 for x in p)
    E = sum(x // 2 for x in p)
    return D // k == E // k


def corrected_so_form(p, k):
    s = sum(p) % (2 * k)
    o = sum(x % 2 for x in p)
    return s <= 2 * k - 2 and o <= min(s, 2 * k - 2 - s)


def positions(n, H):
    def rec(pre, lo):
        if len(pre) == n:
            yield tuple(pre)
            return
        for h in range(lo, H + 1):
            yield from rec(pre + [h], h)
    return rec([], 0)


def main():
    # 1. Counterexample 1 (parity clause)
    p = (0, 1, 2, 2)
    require(reduced(p, 2), "(0,1,2,2) must be reduced for k=2")
    isP42 = make_isP(4, 2)
    require(isP42(p), "(0,1,2,2) must be P in SN(4,{2,3,4})")
    require(not conjecture_says_P(p, 4, 2), "Conjecture 1 must classify (0,1,2,2) as N")
    require(make_isP_reduced_graph(4, 2)(p), "(0,1,2,2) is P in SN~(4,{2,3,4})")

    # 2. Counterexample 2 & infinite family (1 <= o clause)
    p2 = (2, 2, 2, 2)
    require(reduced(p2, 3), "(2,2,2,2) must be reduced for k=3")
    require(make_isP(4, 3)(p2), "(2,2,2,2) must be P in SN(4,{3,4})")
    require(not conjecture_says_P(p2, 4, 3), "Conjecture 1 must classify (2,2,2,2) as N")
    require(make_isP_reduced_graph(4, 3)(p2), "(2,2,2,2) is P in SN~(4,{3,4})")

    for k in (3, 5, 7, 9, 11):
        r = (3 * k - 1) // 2
        for n in (r, r + 1, r + 2):
            fam = (0,) * (n - r) + (2,) * r
            require(reduced(fam, k), "family reduced k=%d n=%d" % (k, n))
            require(corrected_says_P(fam, k), "family P by theorem k=%d n=%d" % (k, n))
            require(not conjecture_says_P(fam, n, k), "Conjecture 1 fails on family k=%d n=%d" % (k, n))

    # 3. Exhaustive verification of the exact corrected theorem (reduced & non-reduced)
    bounds = {2: 24, 3: 14, 4: 10, 5: 7, 6: 5}
    fails_total = 0
    for n in range(2, 7):
        for k in range(1, n + 1):
            isP = make_isP(n, k)
            isPr = make_isP_reduced_graph(n, k)
            for q in positions(n, bounds[n]):
                P = isP(q)
                rq = reduction(q, k)
                require(P == corrected_says_P(rq, k), "theorem fails at %r k=%d" % (q, k))
                if max(q) == 0 or reduced(q, k):
                    require(P == isPr(q), "SN vs SN~ mismatch at %r" % (q,))
                    require(P == corrected_so_form(q, k), "corrected (s,o) fails at %r k=%d" % (q, k))
                    if k >= 2 and P != conjecture_says_P(q, n, k):
                        fails_total += 1
    require(fails_total > 0, "expected Conjecture 1 failures")
    print("Conjecture 1 failures on checked range:", fails_total)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
