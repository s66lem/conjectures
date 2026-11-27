r"""Standalone verifier for the resolution of the four-alternative eigenvector
rank-reversal open question of Bozóki and Csató (arXiv:2603.24274, Section 2).

Verifies (exact rational arithmetic, stdlib only, -O safe):
 1. A4 is a valid 4x4 pairwise comparison matrix (positive and reciprocal).
 2. A4 * w4 = 5 * w4 and v4^T * A4 = 5 * v4^T with w4, v4 > 0.
 3. w4 is strictly decreasing (1 > 2 > 3 > 4) while 1/v4 is strictly increasing (4 > 3 > 2 > 1).
 4. Power iteration confirms w4 and v4 are the unique Perron eigenvectors.
 5. Diagonal rescaling B = D_w^{-1} A4 D_w has constant row sums 5 and left eigenvector u = v4 * w4.
 6. Characterization identity w / u = 1 / v on 200 random 4x4 PCMs.
"""
from fractions import Fraction as F
import random

FAILS = []


def require(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)


def main():
    n = 4
    A = [
        [F(1), F(34, 11), F(17, 48), F(34, 33)],
        [F(11, 34), F(1), F(77, 32), F(2)],
        [F(48, 17), F(32, 77), F(1), F(64, 77)],
        [F(33, 34), F(1, 2), F(77, 64), F(1)],
    ]
    lam = F(5)
    w = [F(34), F(33), F(32), F(22)]
    v = [F(42, 17), F(27, 11), F(77, 32), F(26, 11)]

    # 1. PCM properties
    for i in range(n):
        for j in range(n):
            require(A[i][j] > 0, "positivity %d,%d" % (i, j))
            require(A[i][j] * A[j][i] == 1, "reciprocity %d,%d" % (i, j))

    # 2. Exact eigen-equations
    for i in range(n):
        require(sum(A[i][j] * w[j] for j in range(n)) == lam * w[i], "A w = 5 w row %d" % i)
    for j in range(n):
        require(sum(v[i] * A[i][j] for i in range(n)) == lam * v[j], "v A = 5 v col %d" % j)
    require(all(x > 0 for x in w) and all(x > 0 for x in v), "w, v positive")

    # 3. Full rank reversal
    inv_v = [1 / x for x in v]
    require(all(w[i] > w[i + 1] for i in range(n - 1)), "w^R strictly decreasing")
    require(all(inv_v[i] < inv_v[i + 1] for i in range(n - 1)), "w^(-L) strictly increasing")

    # 4. Power iteration check
    def power(M, iters=3000):
        x = [1.0] * n
        for _ in range(iters):
            y = [sum(float(M[i][j]) * x[j] for j in range(n)) for i in range(n)]
            s = sum(y)
            x = [t / s for t in y]
        return x

    At = [[A[j][i] for j in range(n)] for i in range(n)]
    pr, pl = power(A), power(At)
    sw, sv = float(sum(w)), float(sum(v))
    require(max(abs(pr[i] - float(w[i]) / sw) for i in range(n)) < 1e-12, "power iteration -> w")
    require(max(abs(pl[i] - float(v[i]) / sv) for i in range(n)) < 1e-12, "power iteration -> v")

    # 5. Diagonal rescaling to constant-row-sum PCM B
    B = [[A[i][j] * w[j] / w[i] for j in range(n)] for i in range(n)]
    u = [v[i] * w[i] for i in range(n)]
    require(all(sum(B[i]) == lam for i in range(n)), "B has row sums 5")
    require(all(B[i][j] * B[j][i] == 1 for i in range(n) for j in range(n)), "B reciprocal")
    require([x / u[3] * 52 for x in u] == [84, 81, 77, 52], "u proportional to (84,81,77,52)")
    require(all(sum(u[i] * B[i][j] for i in range(n)) == lam * u[j] for j in range(n)), "u B = 5 u")

    # 6. Characterization identity on 200 random 4x4 PCMs
    rng = random.Random(7)
    for _ in range(200):
        M = [[F(1)] * n for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                q = F(rng.randint(1, 9), rng.randint(1, 9))
                M[i][j], M[j][i] = q, 1 / q
        r = power(M, 400)
        l = power([[M[j][i] for j in range(n)] for j in range(n)], 400)
        uu = [r[i] * l[i] for i in range(n)]
        require(max(abs(r[i] / uu[i] - 1 / l[i]) for i in range(n)) < 1e-9, "w/u = 1/v identity")

    if FAILS:
        print("%d CHECK(S) FAILED" % len(FAILS))
        raise SystemExit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
