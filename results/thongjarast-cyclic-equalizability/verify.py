r"""Verification for the negative answer to Problem 2 (prob:discard) of
arXiv:2607.18452v1 (S. Thongjarast, "0-Cyclic Equalizability of Binary Words
Characterized by Hamming Weight").

Counterexample family (m >= 3 distinct letters x_0..x_{m-1}, indices mod m):
    u_m = prod_i  x_i x_i x_{i+1}
    v_m = prod_i  x_{i+1} x_i x_{i+1}
For m = 3 (a,b,c): u = aabbbccca, v = babcbcaca.

The proof in PROOF.md is general (all insertion lengths). This script checks
every finite ingredient of that proof and adds independent brute-force
evidence. Stdlib only; safe under python -O (no assert statements).
"""
import itertools
import sys


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def family(m):
    xs = [chr(ord('a') + i) for i in range(m)]
    u, v = [], []
    for i in range(m):
        u += [xs[i], xs[i], xs[(i + 1) % m]]
        v += [xs[(i + 1) % m], xs[i], xs[(i + 1) % m]]
    return xs, tuple(u), tuple(v)


def equalizable(u, v, sigma, Lmax):
    """Brute force: is there a sigma-simultaneous insertion of total length
    <= Lmax making u', v' cyclically equivalent (u'[t] = v'[t+d mod L])?
    Uses the orbit reformulation, which is an exact restatement for a fixed
    (L, d, positions): inserted letters are forced along orbits of t -> t+d.
    Returns (L, d, P) or None."""
    n = len(u)
    if u == v:
        return (n, 0, tuple(range(n)))
    for L in range(n, Lmax + 1):
        for rest in itertools.combinations(range(1, L), n - 1):
            P = (0,) + rest  # a common rotation of u', v' moves P[0] to 0
            orig = [-1] * L
            for j, p in enumerate(P):
                orig[p] = j
            for d in range(1, L):
                ok = True
                for j in range(n):
                    t = P[j]
                    gap = False
                    while True:
                        t = (t + d) % L
                        if orig[t] >= 0:
                            break
                        gap = True
                    b = orig[t]
                    if v[b] != u[j] or (gap and u[j] not in sigma):
                        ok = False
                        break
                if ok:
                    return (L, d, P)
    return None


def orig_free(t, P):
    return t not in P


def realize(u, v, sigma, sol):
    """Turn an orbit solution into explicit words and check them directly."""
    L, d, P = sol
    up, vp = [None] * L, [None] * L
    for j, p in enumerate(P):
        up[p], vp[p] = u[j], v[j]
    changed = True
    while changed:
        changed = False
        for t in range(L):
            s = (t + d) % L
            if up[t] is not None and vp[s] is None:
                vp[s] = up[t]
                changed = True
            if vp[s] is not None and up[t] is None:
                up[t] = vp[s]
                changed = True
            if up[t] is None and vp[t] is not None and orig_free(t, P):
                up[t] = vp[t]
                changed = True
            if vp[t] is None and up[t] is not None and orig_free(t, P):
                vp[t] = up[t]
                changed = True
    fill = sorted(sigma)[0]
    for t in range(L):
        if up[t] is None:
            up[t] = vp[t] = fill
    ins = [t for t in range(L) if t not in P]
    require(all(up[t] == vp[t] and up[t] in sigma for t in ins), "inserted letters valid")
    require([up[p] for p in P] == list(u) and [vp[p] for p in P] == list(v), "originals kept")
    require(all(up[t] == vp[(t + d) % L] for t in range(L)), "cyclic shift")
    return ''.join(up), ''.join(vp)


# ---------------------------------------------------------------- 1. family
for m in range(3, 9):
    xs, u, v = family(m)
    n = 3 * m
    require(u != v, "u != v")
    require(sorted(u) == sorted(v), "permutations of each other (equal Parikh vectors)")
    mism = {(u[j], v[j]) for j in range(n) if u[j] != v[j]}
    require(len(mism) == m, "exactly m mismatch positions")
    require(all((y, x) not in mism for (x, y) in mism), "no swapped mismatch pair (m>=3)")
    for i in range(m):
        c = xs[i]
        U = {j for j in range(n) if u[j] == c}
        V = {j for j in range(n) if v[j] == c}
        al, be, ga, de = (3 * i - 1) % n, 3 * i, 3 * i + 1, (3 * i - 3) % n
        require(U == {al, be, ga}, "U_c = {alpha,beta,gamma}")
        require(V == {al, ga, de}, "V_c = {alpha,gamma,delta}")
        off = [(x - be) % n for x in (be, ga, de, al)]
        require(off == sorted(off) and len(set(off)) == 4, "cyclic order beta<gamma<delta<alpha")
        fpf = []
        for img in itertools.permutations([al, ga, de]):
            phi = dict(zip([al, be, ga], img))
            if all(phi[x] != x for x in phi):
                fpf.append(phi)
        cases = [{al: ga, ga: al, be: de}, {al: ga, ga: de, be: al}, {al: de, ga: al, be: ga}]
        require(len(fpf) == 3 and all(p in cases for p in fpf), "three fixed-point-free bijections")

# ------------------------------------------- 2. arithmetic of Step 3 (finite)
for L in range(2, 400):
    for e in range(1, L):
        r2, r3 = (2 * e) % L, (3 * e) % L
        require(not (0 < r2 < r3 < e), "case (2) impossible")
        require(not (0 < e < r3 < r2), "case (3) impossible")
        if (2 * e) % L == 0:
            require(2 * e == L, "case (1) gives e = L/2")

# ---------------------------------------- 3. brute force (independent check)
for m, Lmax in ((3, 17), (4, 14)):
    xs, u, v = family(m)
    for c in xs:
        sigma = set(xs) - {c}
        require(equalizable(u, v, sigma, Lmax) is None,
                "m=%d discard %s: no insertion of length <= %d" % (m, c, Lmax))
    if m == 3:
        sol = equalizable(u, v, set(xs), 15)
        require(sol is not None, "full alphabet insertion exists for m=3")
        print("m=3 full-alphabet solution:", realize(u, v, set(xs), sol), "offset", sol[1])

# positive controls: the paper's example 012/021
u, v = tuple('012'), tuple('021')
require(equalizable(u, v, {'1', '2'}, 12) is None, "012/021 not {1,2}-equalizable (paper)")
for keep in ({'0', '2'}, {'0', '1'}):
    s = equalizable(u, v, keep, 8)
    require(s is not None, "012/021 equalizable after discarding 1 or 2")
    realize(u, v, keep, s)

# ------------------- 4. no counterexample with n <= 6 (certificates found)
for n in range(3, 7):
    for u in itertools.product('abc', repeat=n):
        if len(set(u)) < 3 or u[0] != 'a':
            continue
        for v in set(itertools.permutations(u)):
            if v == u:
                continue
            good = False
            for c in 'abc':
                sigma = set('abc') - {c}
                s = equalizable(u, v, sigma, n + 6)
                if s is not None:
                    realize(u, v, sigma, s)
                    good = True
                    break
            require(good, "n=%d pair %s/%s has a good letter" % (n, ''.join(u), ''.join(v)))

print("ALL CHECKS PASSED")
