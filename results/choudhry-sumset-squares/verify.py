r"""Standalone verifier for Choudhry's Sec. 6 open problem (INTEGERS 26, 2026, #A66 / arXiv:2508.07806)
and Guy's Unsolved Problems in Number Theory D14: sumsets of integers consisting entirely of squares.

Checks:
  1. Five primitive (5, 4) solutions (all primitive solutions with max X <= 10000 in standard form b_1 = 0).
  2. One primitive (6, 4) solution (24 sums all perfect squares, strictly exceeding the (5, 4) question).
  3. All-positive, pairwise disjoint shifted forms of both the minimal (5, 4) and (6, 4) solutions.

Stdlib only, -O safe (uses require() instead of assert).
"""
from functools import reduce
from math import gcd, isqrt


def require(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)


def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n


def check(X, D, label):
    """A = {x^2 : x in X}, B = {0} + D (standard form: b_1 = 0)."""
    A = [x * x for x in X]
    B = [0] + list(D)
    require(len(set(A)) == len(A), label + ": A has repeated elements")
    require(len(set(B)) == len(B), label + ": B has repeated elements")
    roots = []
    for a in A:
        row = []
        for b in B:
            require(is_square(a + b), "%s: %d + %d is not a square" % (label, a, b))
            row.append(isqrt(a + b))
        roots.append(row)
    g = reduce(gcd, A + B)
    require(all(g % (p * p) != 0 for p in range(2, isqrt(g) + 1)), label + ": not primitive")
    return A, B, roots


FIVE_BY_FOUR = [
    ((216, 567, 1128, 1848, 5496), (1198800, 2695680, 22269520)),
    ((126, 714, 3129, 4419, 6834), (713440, 8382528, 105621408)),
    ((872, 1680, 3864, 4980, 8880), (17971200, 24269625, 135475200)),
    ((360, 1215, 3240, 5688, 7160), (3790800, 24076800, 138733056)),
    ((518, 1939, 3748, 4676, 5908), (2696960, 13704320, 139018880)),
]

SIX_BY_FOUR = (
    (2988, 4356, 5787, 11164, 17046, 23948),
    (16594560, 137675520, 1202947200),
)


def main():
    seen_X = set()
    for k, (X, D) in enumerate(FIVE_BY_FOUR):
        A, B, R = check(X, D, "5x4 #%d" % k)
        require(len(A) == 5 and len(B) == 4, "5x4 #%d: wrong sizes" % k)
        require(X not in seen_X, "duplicate 5x4 solution")
        seen_X.add(X)
        if k == 0:
            print("Smallest 5x4 example:")
            print("  A =", A)
            print("  B =", B)
            for a, row in zip(A, R):
                print("  %9d + B -> roots %s" % (a, row))

    A6, B6, R6 = check(*SIX_BY_FOUR, label="6x4")
    require(len(A6) == 6 and len(B6) == 4, "6x4: wrong sizes")
    print("6x4 example:")
    print("  A =", A6)
    print("  B =", B6)
    for a, row in zip(A6, R6):
        print("  %10d + B -> roots %s" % (a, row))

    # Positive, disjoint shifted forms (Choudhry's Lemma 1 with k=1, t=1)
    for label, X, D in [("5x4", *FIVE_BY_FOUR[0]), ("6x4", *SIX_BY_FOUR)]:
        Ap = [x * x - 1 for x in X]
        Bp = [b + 1 for b in [0] + list(D)]
        require(min(Ap + Bp) > 0 and not (set(Ap) & set(Bp)), label + ": shifted sets not positive/disjoint")
        require(all(is_square(a + b) for a in Ap for b in Bp), label + ": shifted sums not squares")
        print("Positive disjoint %s: A' = %s, B' = %s" % (label, Ap, Bp))

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
