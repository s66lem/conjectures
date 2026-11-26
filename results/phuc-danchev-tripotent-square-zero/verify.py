r"""Standalone checker for Phuc-Danchev Problem 4.10 (arXiv:2611.24594v2).

Run: python -O -W error verify.py      (stdlib only; uses require(), never assert)

Matrices over F_2 are tuples of row bitmasks: bit j of row i is entry (i, j).
"""
import itertools
import random
import sys

FAILS = []


def require(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)


# ---------- F_2 linear algebra ----------
def ident(d):
    return tuple(1 << i for i in range(d))


def zero(d):
    return (0,) * d


def madd(X, Y):
    return tuple(x ^ y for x, y in zip(X, Y))


def mmul(X, Y):
    out = []
    for row in X:
        acc, j = 0, 0
        while row:
            if row & 1:
                acc ^= Y[j]
            row >>= 1
            j += 1
        out.append(acc)
    return tuple(out)


def rank(rows):
    rows = [r for r in rows if r]
    rk = 0
    while rows:
        p = rows.pop()
        low = p & -p
        rows = [r ^ p if r & low else r for r in rows]
        rows = [r for r in rows if r]
        rk += 1
    return rk


def transpose(X, d):
    return tuple(sum(((X[i] >> j) & 1) << i for i in range(d)) for j in range(d))


def apply(X, v):
    """X acting on column vector v (bitmask): (Xv)_i = <row_i, v>."""
    return sum((bin(X[i] & v).count("1") & 1) << i for i in range(len(X)))


def kernel(X, d):
    """Basis (bitmasks) of {v : Xv = 0}."""
    piv = {}  # pivot column -> reduced row
    for r in X:
        for c, pr in piv.items():
            if r >> c & 1:
                r ^= pr
        if r:
            c = (r & -r).bit_length() - 1
            for c2 in list(piv):
                if piv[c2] >> c & 1:
                    piv[c2] ^= r
            piv[c] = r
    free = [c for c in range(d) if c not in piv]
    basis = []
    for f in free:
        v = 1 << f
        for c, pr in piv.items():
            if pr >> f & 1:
                v |= 1 << c
        basis.append(v)
    return basis


def dsum(*Ms):
    rows, off = [], 0
    for M in Ms:
        rows += [r << off for r in M]
        off += len(M)
    return tuple(rows)


def frombits(strs):
    return tuple(sum(int(ch) << j for j, ch in enumerate(s)) for s in strs)


def p_of(A):
    d = len(A)
    A2 = mmul(A, A)
    return madd(madd(mmul(A2, A), A2), ident(d))


def is_tripotent(T):
    return mmul(mmul(T, T), T) == T


def is_sqzero(U):
    return not any(mmul(U, U))


C = frombits(["001", "011", "110"])  # matrix (4.1) of the paper
B_OMEGA = frombits(["01", "11"])  # companion matrix of x^2+x+1
d_of = len

# ---------- 1. basic facts ----------
require(p_of(C) == zero(3), "p(C) = 0 for p = x^3+x^2+1")
require(p_of(B_OMEGA) == mmul(B_OMEGA, B_OMEGA), "p(C(x^2+x+1)) = B^2")
require(rank(mmul(B_OMEGA, B_OMEGA)) == 2, "B^2 invertible")
B3 = mmul(mmul(B_OMEGA, B_OMEGA), B_OMEGA)
require(B3 != mmul(B_OMEGA, B_OMEGA), "B^3 != B^2 for B = C(x^2+x+1)")


# polynomial Bezout identity (polys over F_2 as ints): f*(x^3+x) + g*p = 1
def pmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def pdivmod(a, b):
    q = 0
    while a and a.bit_length() >= b.bit_length():
        s = a.bit_length() - b.bit_length()
        q ^= 1 << s
        a ^= b << s
    return q, a


P_POLY, Q_POLY = 0b1101, 0b1010  # x^3+x^2+1, x^3+x
f_inv = next(f for f in range(1, 8) if pdivmod(pmul(f, Q_POLY), P_POLY)[1] == 1)
g_co = pdivmod(pmul(f_inv, Q_POLY) ^ 1, P_POLY)
require(g_co[1] == 0 and pmul(f_inv, Q_POLY) ^ pmul(g_co[0], P_POLY) == 1,
        "explicit Bezout: f(x)(x^3+x) + g(x)p(x) = 1")
print("Bezout: f =", bin(f_inv), " g =", bin(g_co[0]))


# ---------- 2. Lemma A: exhaustive check for d <= 3, random for d <= 9 ----------
def K1_dim(A, U):
    d = len(A)
    E = p_of(A)
    Kb = kernel(E, d)
    if not Kb:
        return 0, 0
    conds = []
    W = U
    for _ in range(3):  # e u, e u a, e u a^2
        EW = mmul(E, W)
        conds.append(EW)
        W = mmul(W, A)
    # dim{x in K : e u a^j x = 0, j=0,1,2}: matrix (stacked conditions) applied to K-basis
    cols = []
    for v in Kb:
        img = 0
        for j, M in enumerate(conds):
            img |= apply(M, v) << (j * d)
        cols.append(img)
    return len(Kb), len(Kb) - rank(cols)


def all_mats(d):
    return (tuple((n >> (d * i)) & ((1 << d) - 1) for i in range(d)) for n in range(1 << (d * d)))


for d in (1, 2, 3, 4):
    trips = [M for M in all_mats(d) if is_tripotent(M)]
    sqz = [M for M in all_mats(d) if is_sqzero(M)]
    worst, eq = -10 ** 9, 0
    for T in trips:
        for U in sqz:
            A = madd(T, U)
            if rank(p_of(A)) == d:
                continue
            k, k1 = K1_dim(A, U)
            require(k1 == 0, f"K1 = 0 (d={d})")
            worst = max(worst, k - 3 * (d - k))
            eq += (k == 3 * (d - k))
    require(worst <= 0, f"Lemma A exhaustive d={d}")
    print(f"Lemma A exhaustive d={d}: {len(trips)} tripotents x {len(sqz)} square-zero, "
          f"max(k-3s) over k>0 = {worst}, equality pairs = {eq}")

rng = random.Random(2611_24594)


def rand_inv(d):
    while True:
        P = tuple(rng.getrandbits(d) for _ in range(d))
        if rank(P) == d:
            return P


def inverse(P, d):
    rows = [(P[i], 1 << i) for i in range(d)]
    for c in range(d):
        piv = next(i for i in range(c, d) if rows[i][0] >> c & 1)
        rows[c], rows[piv] = rows[piv], rows[c]
        for i in range(d):
            if i != c and rows[i][0] >> c & 1:
                rows[i] = (rows[i][0] ^ rows[c][0], rows[i][1] ^ rows[c][1])
    # rows now encode row ops R with R P = I, so R = P^{-1}; R's rows are rows[i][1]
    return tuple(r[1] for r in rows)


tight = 0
for trial in range(3000):
    d = rng.randint(3, 9)
    k0 = rng.randint(0, d)
    D = [0] * d
    for i in range(k0, d):
        D[i] |= 1 << i
    j = k0
    while j + 1 < d:
        if rng.random() < 0.6:
            D[j] |= 1 << (j + 1)
            j += 2
        else:
            j += 1
    P = rand_inv(d)
    T = mmul(mmul(P, tuple(D)), inverse(P, d))
    r = rng.randint(0, d // 2)
    Ub = [0] * d
    for i in range(r):
        Ub[2 * i] |= 1 << (2 * i + 1)
    Q = rand_inv(d)
    U = mmul(mmul(Q, tuple(Ub)), inverse(Q, d))
    require(is_tripotent(T) and is_sqzero(U), "random generator")
    A = madd(T, U)
    k, k1 = K1_dim(A, U)
    require(k1 == 0, "K1 = 0 (random)")
    require(k <= 3 * (d - k), "Lemma A (random)")
    tight += (k > 0 and k == 3 * (d - k))
print("Lemma A random: 3000 instances ok, tight cases:", tight)

# ---------- 3. sharpness examples (explicit decompositions) ----------
EX = {
    "C+[0]": (dsum(C, ((0,))), ["0110", "1011", "1011", "1101"]),
    "C+[1]": (dsum(C, ((1,))), ["0100", "0000", "0111", "0111"]),
    "C2+I2": (dsum(C, C, ident(2)),
              ["01011000", "00001101", "01111011", "00010001", "00011100", "00001101", "01101010", "00010001"]),
    "C2+0_2": (dsum(C, C, zero(2)),
               ["01110010", "00001000", "00101011", "00001101", "00000000", "00000101", "00101110", "00000101"]),
}
for name, (A, Ns) in EX.items():
    N = frombits(Ns)
    T = madd(A, N)
    require(is_sqzero(N) and is_tripotent(T), f"explicit decomposition {name}")
    d = len(A)
    k = d - rank(p_of(A))
    require(k == 3 * (d - k), f"{name} is an equality case of Lemma A")
print("explicit decompositions (equality cases of Lemma A) verified:", ", ".join(EX))

# ---------- 4. Lemma B: noncommutative symbolic computation ----------
# Noncommutative polynomials over F_2: frozenset of words (tuples of letters).
def P_(*words):
    s = set()
    for w in words:
        s ^= {tuple(w)}
    return frozenset(s)


def nadd(*ps):
    s = set()
    for p in ps:
        s ^= set(p)
    return frozenset(s)


def nmul(p, q):
    s = set()
    for a in p:
        for b in q:
            s ^= {a + b}
    return frozenset(s)


Z0, ONE = frozenset(), P_(())
Bs, cs = P_(("B",)), P_(("c",))
G = [P_((f"G{i}",)) for i in (1, 2, 3)]


def MM(X, Y):
    n, m, l = len(X), len(Y), len(Y[0])
    return [[nadd(*[nmul(X[i][k], Y[k][j]) for k in range(m)]) for j in range(l)] for i in range(n)]


def MA(*Xs):
    return [[nadd(*[X[i][j] for X in Xs]) for j in range(len(Xs[0][0]))] for i in range(len(Xs[0]))]


def scal(rows):
    return [[ONE if x else Z0 for x in r] for r in rows]


def word_str(p):
    return " + ".join("".join(w) if w else "1" for w in sorted(p, key=lambda w: (len(w), w))) or "0"


Mc = scal([[0, 1, 0], [0, 0, 1], [1, 0, 1]])  # a1 in coordinates (a1^3 = a1^2 + 1)
BB = nmul(Bs, Bs)


def Nmat(g1, g2, g3):
    return [[cs, Z0, Z0],
            [nadd(BB, nmul(cs, Bs), ONE), Bs, ONE],
            [g1, g2, g3]]


def KK(N):
    Ucol = [[x[0]] for x in MM(N, N)]  # u12 = first column of N^2 (from u11^2 = u12 u21)
    R = [[ONE, Z0, Z0]]  # u21 in coordinates
    UBR = MM(MM(Ucol, [[Bs]]), R)
    M2 = MM(Mc, Mc)
    return MA(MM(M2, Mc), Mc, MM(M2, N), MM(MM(Mc, N), Mc), MM(N, M2), MM(MM(N, Mc), N), UBR, N)


# (ii) first row of KK with unknown third row (G1,G2,G3) of N
row1 = KK(Nmat(*G))[0]
expect = [nadd(G[0], nmul(cs, BB)), nadd(G[1], BB), nadd(G[2], Bs)]
require(row1 == expect, "KK first row = (G1 + cB^2, G2 + B^2, G3 + B)")
print("KK row 1:", [word_str(x) for x in row1])
# (iii) substitute the forced third row
Nf = Nmat(nmul(cs, BB), BB, Bs)
KKf = KK(Nf)
require(all(x == Z0 for x in KKf[0]), "row 1 vanishes after substitution")
require(KKf[2][2] == nadd(BB, nmul(BB, Bs)), "KK(3,3) = B^2 + B^3")
print("KK(3,3) after substitution:", word_str(KKf[2][2]))
N2 = MM(Nf, Nf)
require(all(N2[i][j] == Z0 for i in range(3) for j in (1, 2)), "N^2 has zero 2nd/3rd columns (consistency)")


# (i) numeric cross-check of the coordinate formulas on the equality-case decompositions
def coords_check(A, N, m, r):
    d = len(A)
    k = 3 * m
    mask_K = (1 << k) - 1
    a1 = tuple(row & mask_K for row in A[:k])
    Bm = tuple(row >> k for row in A[k:])
    u11 = tuple(row & mask_K for row in N[:k])
    u21 = tuple(row & mask_K for row in N[k:])
    u22 = tuple(row >> k for row in N[k:])
    # Phi: K -> U^3, x -> (u21 x, u21 a1 x, u21 a1^2 x), as a (3r x k) matrix
    rows = list(u21) + list(mmul(u21, a1)) + list(mmul(mmul(u21, a1), a1))
    require(rank(rows) == k, "Phi bijective")
    # predicted N in coordinates, as 3r x 3r F_2 matrix built from blocks
    I_r = ident(r)
    BBm = mmul(Bm, Bm)
    blocks = [[u22, zero(r), zero(r)],
              [madd(madd(BBm, mmul(u22, Bm)), I_r), Bm, I_r],
              [mmul(u22, BBm), BBm, Bm]]
    pred = []
    for bi in range(3):
        for i in range(r):
            pred.append(sum(blocks[bi][bj][i] << (bj * r) for bj in range(3)))
    # actual: Phi u11 = pred Phi  (as maps K -> U^3)
    Phi = tuple(rows)
    lhs = mmul(Phi, u11)
    rhs = mmul(tuple(pred), Phi)
    require(lhs == rhs, "coordinate formula for u11")
    require(mmul(mmul(Bm, Bm), Bm) == mmul(Bm, Bm), "B^3 = B^2 in an equality case")


for name, m, r in (("C+[0]", 1, 1), ("C+[1]", 1, 1), ("C2+I2", 2, 2), ("C2+0_2", 2, 2)):
    A, Ns = EX[name]
    coords_check(A, frombits(Ns), m, r)
print("coordinate formulas cross-checked on explicit decompositions")

# ---------- 5. the counterexamples for every d >= 7, 3 not | d ----------
for d in range(7, 200):
    if d % 3 == 0:
        continue
    m, r = divmod(d, 3)
    if d == 8:
        A, Bblk = dsum(C, C, B_OMEGA), B_OMEGA
    else:
        Bblk = zero(r)
        A = dsum(*([C] * m), Bblk)
    E = p_of(A)
    s = rank(E)
    k = d - s
    require(k == 3 * m and s == r, f"d={d}: dim ker p(A) = 3m, rank p(A) = r")
    if d == 8:
        require(k == 3 * s, "d=8 is the equality case of Lemma A")
        require(mmul(mmul(Bblk, Bblk), Bblk) != mmul(Bblk, Bblk), "d=8: B^3 != B^2 (Lemma B applies)")
    else:
        require(k > 3 * s, f"d={d}: Lemma A violated, so A not in T_d")
print("counterexamples checked for all d in [7,200), 3 not | d")

if FAILS:
    print(len(FAILS), "FAILURES")
    sys.exit(1)
print("ALL CHECKS PASSED")
