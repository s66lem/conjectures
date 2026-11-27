r"""Standalone verifier for Güday–Şahin (INTEGERS 26, 2026, #A5): Conjectures 1 & 2 and Open Problem 1.

Recurrence (1): q_n = sum_{j=1}^m a[i][j] q_{n-j} for n = i (mod r), n >= m.
Convention: a[i][0] = -1.

Checks:
  1. Exact decimated recurrence & Open Problem 1:
     q_n = sum_{s=1}^m c_s q_{n - s*r}, where
     c_s = sum_{sum d = s*r, sigma_d bijective} sgn(sigma_d) * (-1)^(nz(d)+1) * prod_{d_i>0} a[i][d_i],
     with sigma_d(i) = (i - d_i) mod r. Checked symbolically against the characteristic
     polynomial of the monodromy matrix M = C_{r-1} ... C_0 for 10 (r, m) pairs.
  2. Exact r <= 3 equivalence vs r >= 4 failure of Conjecture 1:
     - For r in {1, 2, 3}, the paper's condition equals bijectivity of sigma_d.
     - For every r >= 4, (0, r-1, 0, 1, 0, ..., 0) satisfies the paper's condition but is not bijective.
     - At r = 4, m = 5, d = 4: conjectured support has 17 terms, true coefficient has 15;
       concrete integer instance has c_1 = 13596 (= 0 mod 3), c_5 = 74844 != 0, nonsingular
       Krylov window, and every choice of +- signs gives A_4 = +-1 (mod 3) != c_1.
  3. Conjecture 2 disproof and corrected formula:
     - Holds for all m <= 5; fails at m = 6, d = 9 (|A_9| = 25 != 22 = 37 - 30/2).
     - Exact corrected formula: 2*|A_d| = 2*w_{3,m}(d) - #{distinct residues mod 3}, verified m <= 12.

Stdlib only, -O safe (uses require() instead of assert).
"""
import itertools
from fractions import Fraction


def require(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)


# ---------- sparse multivariate polynomials over Z: {monomial: coeff}, monomial = sorted tuple of (var, exp)
def padd(p, q, s=1):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, 0) + s * v
        if out[k] == 0:
            del out[k]
    return out


def mmul(x, y):
    d = dict(x)
    for v, e in y:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))


def pmul(p, q):
    out = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = mmul(k1, k2)
            out[k] = out.get(k, 0) + v1 * v2
    return {k: v for k, v in out.items() if v}


def const(c):
    return {(): c} if c else {}


def var(name):
    return {((name, 1),): 1}


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    C = [[{} for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for t in range(k):
            if not A[i][t]:
                continue
            for j in range(m):
                if B[t][j]:
                    C[i][j] = padd(C[i][j], pmul(A[i][t], B[t][j]))
    return C


def charpoly(A):
    """Faddeev-LeVerrier: returns [p_0..p_n] with det(xI - A) = sum p_k x^k (exact over Z)."""
    n = len(A)
    coeffs = [None] * (n + 1)
    coeffs[n] = const(1)
    Mk = [[const(1) if i == j else {} for j in range(n)] for i in range(n)]
    for k in range(1, n + 1):
        AM = matmul(A, Mk)
        tr = {}
        for i in range(n):
            tr = padd(tr, AM[i][i])
        ck = {}
        for mono, v in tr.items():
            require(v % k == 0, "LeVerrier division not exact")
            ck[mono] = -v // k
        coeffs[n - k] = ck
        Mk = [[padd(AM[i][j], ck) if i == j else AM[i][j] for j in range(n)] for i in range(n)]
    return coeffs


def companion(i, m, a):
    C = [[{} for _ in range(m)] for _ in range(m)]
    for j in range(m):
        C[0][j] = a[i][j + 1]
    for t in range(1, m):
        C[t][t - 1] = const(1)
    return C


def sym_a(r, m):
    return [[const(-1)] + [var((i, j)) for j in range(1, m + 1)] for i in range(r)]


def decimated_coeffs(r, m, a):
    """c_s, s=1..m, with q_n = sum_s c_s q_{n-sr}; from char poly of M = C_{r-1}...C_0."""
    M = companion(0, m, a)
    for i in range(1, r):
        M = matmul(companion(i, m, a), M)
    cp = charpoly(M)
    return {s: {k: -v for k, v in cp[m - s].items()} for s in range(1, m + 1)}


def perm_sign(p):
    p, s = list(p), 1
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


def mono_of(d):
    return tuple(sorted(((i, di), 1) for i, di in enumerate(d) if di > 0))


def formula(r, m, s):
    out = {}
    for d in itertools.product(range(m + 1), repeat=r):
        if sum(d) != s * r:
            continue
        sig = [(i - d[i]) % r for i in range(r)]
        if len(set(sig)) < r:
            continue
        nz = sum(1 for x in d if x)
        out[mono_of(d)] = perm_sign(sig) * (-1) ** (nz + 1)
    return out


def conj_condition(d, r):
    i = d[0] % r
    return all(d[k] % r != (k + i) % r for k in range(1, r))


def det_exact(Mx):
    Mx = [row[:] for row in Mx]
    n, dv = len(Mx), Fraction(1)
    for col in range(n):
        piv = next((i for i in range(col, n) if Mx[i][col] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != col:
            Mx[col], Mx[piv] = Mx[piv], Mx[col]
            dv = -dv
        dv *= Mx[col][col]
        for i in range(col + 1, n):
            f = Mx[i][col] / Mx[col][col]
            for j in range(col, n):
                Mx[i][j] -= f * Mx[col][j]
    return dv


def main():
    # 1. Exact decimated recurrence & Open Problem 1
    for (r, m) in [(1, 3), (2, 1), (2, 3), (3, 2), (3, 4), (3, 6), (4, 2), (4, 3), (4, 5), (5, 3)]:
        C = decimated_coeffs(r, m, sym_a(r, m))
        for s in range(1, m + 1):
            require(C[s] == formula(r, m, s), "theorem fails at r=%d m=%d s=%d" % (r, m, s))
    print("T: decimated coefficients match the signed bijection formula for 10 (r,m) pairs")

    for r in (1, 2, 3):
        for m in range(1, 8):
            for d in itertools.product(range(m + 1), repeat=r):
                if sum(d) % r:
                    continue
                bij = len({(i - d[i]) % r for i in range(r)}) == r
                require(conj_condition(d, r) == bij, "r<=3 equivalence")
    print("T: for r <= 3 the paper's condition equals bijectivity (m <= 7)")

    # 2. Conjecture 1 disproof (r = 4, m = 5 and infinite family for r >= 4)
    r, m = 4, 5
    C = decimated_coeffs(r, m, sym_a(r, m))
    for s in range(1, m + 1):
        conj_set = {
            mono_of(d)
            for d in itertools.product(range(m + 1), repeat=r)
            if sum(d) == s * r and conj_condition(d, r)
        }
        require(set(C[s]) <= conj_set, "true support not inside conjectured support")
        missing = conj_set - set(C[s])
        if s == 1:
            require(len(conj_set) == 17 and len(C[s]) == 15, "counts at d=4")
            require(mono_of((0, 3, 0, 1)) in missing and mono_of((1, 0, 1, 2)) in missing, "missing at d=4")
    print("C1: r=4, m=5, d=4: conjectured support has 17 terms, true support has 15; (0,3,0,1) & (1,0,1,2) absent")

    for r_val in range(4, 12):
        d = (0, r_val - 1, 0, 1) + (0,) * (r_val - 4)
        require(conj_condition(d, r_val) and sum(d) == r_val, "family condition")
        require(len({(i - d[i]) % r_val for i in range(r_val)}) < r_val, "family non-bijective")
    print("C1: family (0, r-1, 0, 1, 0, ...) violates conjectured support for 4 <= r <= 11")

    # Concrete integer instance for r = 4, m = 5
    A = [[-1] + [3 * ((7 * i + 5 * j) % 11 + 1) for j in range(1, m + 1)] for i in range(r)]
    A[1][3] = 1
    A[3][1] = 1
    q = [2, -1, 5, 3, 7]
    for n in range(m, 200):
        q.append(sum(A[n % r][j] * q[n - j] for j in range(1, m + 1)))

    numA = [[const(A[i][j]) for j in range(m + 1)] for i in range(r)]
    cnum = decimated_coeffs(r, m, numA)
    c = [None] + [cnum[s].get((), 0) for s in range(1, m + 1)]
    for n in range(m * r + m - 1, 200):
        require(q[n] == sum(c[s] * q[n - s * r] for s in range(1, m + 1)), "true recurrence on instance")
    require(c[5] != 0, "monodromy invertible (c_5 != 0)")
    W0 = [[Fraction(q[4 * j + 20 - 4 * s]) for j in range(5)] for s in range(5)]
    require(det_exact(W0) != 0, "Krylov window W0 nonsingular")
    require(c[1] % 3 == 0, "true coefficient c_1 divisible by 3")

    conj4 = [d for d in itertools.product(range(m + 1), repeat=r) if sum(d) == 4 and conj_condition(d, r)]
    special = (0, 3, 0, 1)
    for d in conj4:
        val = 1
        for i, di in enumerate(d):
            if di:
                val *= A[i][di]
        require(val % 3 == (1 if d == special else 0), "monomial residues mod 3")
    print(
        "C1: instance c_1 = %d (= 0 mod 3), c_5 = %d, det(W0) != 0; every signed sum of the 17 "
        "conjectured terms is +-1 mod 3, so A_4 != c_1 for all sign choices" % (c[1], c[5])
    )

    # 3. Conjecture 2 disproof and corrected formula
    def counts(mm, dd):
        T = [t for t in itertools.product(range(mm + 1), repeat=3) if sum(t) == dd]
        w = len(T)
        wstar = sum(1 for t in T if len(set(t)) == 3)
        Acount = sum(1 for t in T if conj_condition(t, 3))
        return w, wstar, Acount

    w, ws, Ac = counts(6, 9)
    require((w, ws, Ac) == (37, 30, 25), "C2 counts at m=6, d=9")
    require(2 * Ac != 2 * w - ws, "C2 disproof at m=6, d=9")
    for mm in range(1, 6):
        for dd in range(0, 3 * mm + 1, 3):
            w1, ws1, A1 = counts(mm, dd)
            require(2 * A1 == 2 * w1 - ws1, "C2 holds for m <= 5")
    for mm in range(1, 13):
        for dd in range(0, 3 * mm + 1, 3):
            T = [t for t in itertools.product(range(mm + 1), repeat=3) if sum(t) == dd]
            dres = sum(1 for t in T if len({x % 3 for x in t}) == 3)
            require(2 * sum(1 for t in T if conj_condition(t, 3)) == 2 * len(T) - dres, "corrected count")
    C36 = decimated_coeffs(3, 6, sym_a(3, 6))
    require(len(C36[3]) == 25, "r=3, m=6, d=9 true monomial count")
    require(counts(4, 6)[0] == 19 and counts(4, 6)[2] == 13, "Example 5 corrected counts")
    print(
        "C2: m=6, d=9: |A_9| = 25 != 22 = 37 - 30/2; formula holds for m <= 5; "
        "corrected count verified for m <= 12"
    )
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
