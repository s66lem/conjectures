r"""Stdlib-only verification for the tadpole disproof of Mukherjee-Ray,
arXiv:2611.10985v2, Problem 6.2 ("Is this polynomial always log-concave?"
for unicyclic graphs) and sharp 7-vertex minimality for Problem 6.4.

Run: python -O -W error verify.py
"""
from itertools import combinations


def require(cond, msg):
    if not cond:
        raise SystemExit("FAILED: " + msg)


def closure(n, nb, S):
    B = S
    changed = True
    while changed:
        changed = False
        b = B
        while b:
            v = (b & -b).bit_length() - 1
            b &= b - 1
            w = nb[v] & ~B
            if w and not (w & (w - 1)):
                B |= w
                changed = True
    return B


def connected(nb, S):
    if not S:
        return False
    comp = frontier = S & -S
    while frontier:
        v = (frontier & -frontier).bit_length() - 1
        frontier &= frontier - 1
        new = nb[v] & S & ~comp
        comp |= new
        frontier |= new
    return comp == S


def czf_sets(n, nb):
    full = (1 << n) - 1
    return [S for S in range(1, 1 << n) if connected(nb, S) and closure(n, nb, S) == full]


def poly_from_sets(n, sets):
    z = [0] * (n + 1)
    for S in sets:
        z[bin(S).count("1")] += 1
    return z


def is_lc(z):
    s = z[1:]
    nz = [i for i, x in enumerate(s) if x]
    s = s[nz[0]:nz[-1] + 1]
    if 0 in s:
        return False
    return all(s[i] * s[i] >= s[i - 1] * s[i + 1] for i in range(1, len(s) - 1))


def adj(n, edges):
    nb = [0] * n
    for u, v in edges:
        nb[u] |= 1 << v
        nb[v] |= 1 << u
    return nb


def tadpole(m, l):
    """Cycle c_0..c_{m-1} = vertices 0..m-1; tail t_1..t_l = m..m+l-1, t_1 ~ c_0."""
    edges = [(i, (i + 1) % m) for i in range(m)]
    prev = 0
    for i in range(l):
        edges.append((prev, m + i))
        prev = m + i
    return m + l, adj(m + l, edges)


def formula(m, l):
    """Closed form: Z(k) = N_m(k) + sum_{a=0}^{l} A_m(k - a)."""
    A = {b: (b if b <= m - 1 else 1) for b in range(2, m + 1)}
    N = {b: (m - b if b <= m - 1 else 0) for b in range(2, m + 1)}
    n = m + l
    z = [0] * (n + 1)
    for k in range(n + 1):
        val = N.get(k, 0)
        for a in range(l + 1):
            val += A.get(k - a, 0)
        z[k] = val
    return z


# 1. Smallest counterexample: 7-vertex tadpole T_{5,2}.
n, nb = tadpole(5, 2)
z = poly_from_sets(n, czf_sets(n, nb))
require(z == [0, 0, 5, 7, 10, 8, 5, 1], f"Z_C(T_{{5,2}}) unexpected: {z}")
require(z[3] ** 2 < z[2] * z[4], "49 < 50 at k = 3")
require(not is_lc(z), "T_{5,2} not log-concave")

# 2. Characterization lemma and closed formula by brute force on tadpoles.
for m in range(3, 10):
    for l in range(0, 8):
        n, nb = tadpole(m, l)
        sets = set(czf_sets(n, nb))
        cyc_pairs = [(1 << i) | (1 << ((i + 1) % m)) for i in range(m)]
        char = {
            S
            for S in range(1, 1 << n)
            if connected(nb, S) and any(S & p == p for p in cyc_pairs)
        }
        require(sets == char, f"characterization mismatch (m={m}, l={l})")
        require(poly_from_sets(n, sets) == formula(m, l), f"formula mismatch (m={m}, l={l})")
        require(
            is_lc(formula(m, l)) == (m <= 4 or l <= 1),
            f"LC criterion brute mismatch (m={m}, l={l})",
        )

# 3. Log-concavity criterion on a larger range from the closed formula.
for m in range(3, 61):
    for l in range(0, 61):
        require(
            is_lc(formula(m, l)) == (m <= 4 or l <= 1),
            f"LC criterion formula mismatch (m={m}, l={l})",
        )

# 4. Minimality: every connected graph on <= 6 vertices has log-concave Z_C.
for n in range(1, 7):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        nb = adj(n, [pairs[i] for i in range(len(pairs)) if (mask >> i) & 1])
        if not connected(nb, (1 << n) - 1):
            continue
        require(is_lc(poly_from_sets(n, czf_sets(n, nb))), f"n={n} graph {mask} not log-concave")

# 5. Uniqueness among 7-vertex unicyclic graphs: exactly T_{5,2} fails (2520 labellings).
pairs = list(combinations(range(7), 2))
bad = 0
for es in combinations(range(len(pairs)), 7):
    edges = [pairs[i] for i in es]
    nb = adj(7, edges)
    if not connected(nb, (1 << 7) - 1):
        continue
    z = poly_from_sets(7, czf_sets(7, nb))
    if is_lc(z):
        continue
    bad += 1
    require(z == [0, 0, 5, 7, 10, 8, 5, 1], "failing unicyclic has T_{5,2} polynomial")
    deg = sorted(bin(x).count("1") for x in nb)
    require(deg == [1, 2, 2, 2, 2, 2, 3], "degree sequence of T_{5,2}")
    leaf = next(v for v in range(7) if bin(nb[v]).count("1") == 1)
    mid = (nb[leaf]).bit_length() - 1
    require(bin(nb[mid]).count("1") == 2, "leaf attached to degree-2 tail vertex")
    hub = (nb[mid] & ~(1 << leaf)).bit_length() - 1
    require(bin(nb[hub]).count("1") == 3, "tail attached to degree-3 cycle vertex")
require(bad == 2520, f"expected 2520 failing labelled 7-vertex unicyclic graphs, got {bad}")

print("ALL CHECKS PASSED")
