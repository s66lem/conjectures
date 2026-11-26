r"""Independent verifier for the negative answer to Basak-Bijender-Kumar Question 4.14
(arXiv:2611.19424v1).

Verifies using exact rational arithmetic (no floats, stdlib only):
1. Headline counterexample (T = 4, r = 13): |B| = 455 components, big-height e = 14,
   alpha(I) = 4, alpha_hat(I) = 26/23 < 17/15 = (alpha + e - 1)/(e + 1).
2. Additional infinite-family instances: (4, 14), (5, 11), (6, 11), (7, 11).
3. Boundary non-violations (4, 12) and (5, 10) where r*(T - 3) <= T*(T - 1).
"""

from fractions import Fraction
from itertools import combinations
from math import comb


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"Verification failed: {msg}")


def compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for i in range(total + 1):
        for rest in compositions(total - i, parts - 1):
            yield (i,) + rest


def check_instance(T: int, r: int, exhaustive_alpha: bool):
    B = list(compositions(T - 1, r))
    require(len(B) == comb(r + T - 2, T - 1), f"component count mismatch for {(T, r)}")
    W = [tuple(x + 1 for x in b) for b in B]
    e = r + 1

    # alpha(I) <= T: x_1^T lies in every q_b
    require(all(w[0] <= T for w in W), f"x_1^T not in I for {(T, r)}")
    if exhaustive_alpha:
        for s in range(T):
            for c in compositions(s, r):
                missed = sum(1 for b in B if all(bj >= cj for bj, cj in zip(b, c)))
                require(s + missed >= T, f"alpha lower bound failed at {(T, r, c)}")
    alpha = T

    # Upper bound witness: prod x_j^(2k) in I^((2r - T + 1)k)
    g = 2 * r - T + 1
    for k in (1, 2, 3):
        for w in W:
            require(sum((2 * k) // wj for wj in w) >= g * k, f"upper bound failed at {(T, r, k)}")
    upper = Fraction(2 * r, g)

    # Lower bound via averaging over the binary orbit O
    orbit = [tuple(1 if j in S else 0 for j in range(r)) for S in combinations(range(r), T - 1)]
    require(len(orbit) == comb(r, T - 1), f"orbit size mismatch for {(T, r)}")
    col_sums = [sum(Fraction(1, b[j] + 1) for b in orbit) for j in range(r)]
    require(len(set(col_sums)) == 1, f"column sums not equal for {(T, r)}")
    lam = col_sums[0]
    require(lam >= 1, f"lam < 1 for {(T, r)}")
    lower = Fraction(len(orbit)) / lam
    require(lower == upper, f"exact alpha_hat mismatch: {lower} vs {upper}")

    rhs = Fraction(alpha + e - 1, e + 1)
    require(upper < rhs, f"no violation for {(T, r)}: {upper} >= {rhs}")
    return alpha, e, upper, rhs, len(B)


def main() -> None:
    alpha, e, ahat, rhs, count = check_instance(4, 13, True)
    require(
        (alpha, e, ahat, rhs, count) == (4, 14, Fraction(26, 23), Fraction(17, 15), 455),
        "headline values mismatch",
    )
    for T, r in ((4, 14), (5, 11), (6, 11), (7, 11)):
        require(r * (T - 3) > T * (T - 1), f"family condition failed for {(T, r)}")
        check_instance(T, r, T <= 5)
    for T, r in ((4, 12), (5, 10)):
        require(r * (T - 3) <= T * (T - 1), f"boundary condition failed for {(T, r)}")
        require(Fraction(2 * r, 2 * r - T + 1) >= Fraction(T + r, r + 2), "boundary inequality")
    print(
        "ALL CHECKS PASSED: headline (T=4, r=13, 455 components, alpha=4, e=14, "
        "alpha_hat=26/23 < 17/15), 4 additional family members, and 2 boundary cases verified."
    )


if __name__ == "__main__":
    main()
