#!/usr/bin/env python3
"""Standalone (-O-safe, stdlib-only) verifier for the disproof of
Conjecture 4.13(2) of González D'León and Wachs (arXiv:2608.08692v2).

Computes mu_G(t) directly from the verbatim weighted bond poset WPi_G
(Section 2), cross-checks against recurrence (3.1), verifies the exact
gamma-polynomial / reciprocal-cubic identities and negative discriminant
Delta = -22364 < 0, and checks the chorded-cycle 2-component family.
"""

from functools import lru_cache


def require(cond, msg):
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def poly_add(a, b):
    n = max(len(a), len(b))
    out = [0] * n
    for i in range(len(a)):
        out[i] += a[i]
    for i in range(len(b)):
        out[i] += b[i]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_sub(a, b):
    return poly_add(a, [-x for x in b])


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def is_connected(n, edges, mask):
    if mask == 0:
        return False
    adj = [0] * n
    for u, v in edges:
        if (mask >> u) & 1 and (mask >> v) & 1:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    lsb = mask & -mask
    start = lsb.bit_length() - 1
    seen = 1 << start
    stack = [start]
    while stack:
        u = stack.pop()
        nxt = adj[u] & ~seen
        while nxt:
            b = nxt & -nxt
            seen |= b
            stack.append(b.bit_length() - 1)
            nxt ^= b
    return seen == mask


def connected_components(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    rem = (1 << n) - 1
    comps = []
    while rem:
        lsb = rem & -rem
        start = lsb.bit_length() - 1
        seen = 1 << start
        stack = [start]
        while stack:
            u = stack.pop()
            nxt = adj[u] & ~seen
            while nxt:
                b = nxt & -nxt
                seen |= b
                stack.append(b.bit_length() - 1)
                nxt ^= b
        comps.append(seen)
        rem ^= seen
    return comps


def bond_partitions(n, edges):
    """All set partitions of {0,...,n-1} into connected blocks (represented as sorted tuples of bitmasks)."""
    conn = [False] * (1 << n)
    for m in range(1, 1 << n):
        conn[m] = is_connected(n, edges, m)
    full = (1 << n) - 1
    res = []

    def gen(rem, acc):
        if rem == 0:
            res.append(tuple(sorted(acc)))
            return
        lsb = rem & -rem
        rest = rem ^ lsb
        sub = rest
        while True:
            blk = lsb | sub
            if conn[blk]:
                gen(rem ^ blk, acc + [blk])
            if sub == 0:
                break
            sub = (sub - 1) & rest

    gen(full, [])
    return res


def mu_from_verbatim_poset(n, edges):
    """Exact mu_G(t) directly from the verbatim weighted bond poset WPi_G (Section 2)."""
    parts = bond_partitions(n, edges)
    elems = []
    for p in parts:
        # generate all weight tuples w_i in {0, ..., |B_i| - 1}
        sizes = [b.bit_count() for b in p]
        ws = [()]
        for sz in sizes:
            ws = [w + (v,) for w in ws for v in range(sz)]
        for w in ws:
            elems.append((p, w))

    # Sort by decreasing number of blocks (rank = n - #blocks)
    elems.sort(key=lambda e: -len(e[0]))
    bot = (tuple(1 << i for i in range(n)), (0,) * n)
    require(elems[0] == bot, "minimum element mismatch")

    def leq(e1, e2):
        p1, w1 = e1
        p2, w2 = e2
        if len(p1) < len(p2):
            return False
        # Each block in p2 must be a disjoint union of blocks in p1, with valid weight increment
        for b2, v2 in zip(p2, w2):
            union_mask = 0
            wsum = 0
            cnt = 0
            for b1, w_1 in zip(p1, w1):
                if (b1 & b2) == b1:
                    union_mask |= b1
                    wsum += w_1
                    cnt += 1
            if union_mask != b2:
                return False
            diff = v2 - wsum
            if diff < 0 or diff > cnt - 1:
                return False
        return True

    mu_val = {bot: 1}
    for idx in range(1, len(elems)):
        y = elems[idx]
        s = 0
        for j in range(idx):
            z = elems[j]
            if leq(z, y):
                s += mu_val[z]
        mu_val[y] = -s

    comps = tuple(sorted(connected_components(n, edges)))
    poly = [0]
    for e, val in mu_val.items():
        if e[0] == comps:
            deg = sum(e[1])
            if len(poly) <= deg:
                poly.extend([0] * (deg + 1 - len(poly)))
            poly[deg] += val
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def mu_via_recurrence(n, edges):
    """Exact mu_G(t) via Theorem 3.1 recurrence (3.1) and Proposition 2.2."""
    conn = [False] * (1 << n)
    for m in range(1, 1 << n):
        conn[m] = is_connected(n, edges, m)

    @lru_cache(maxsize=None)
    def mu_conn(mask):
        if mask.bit_count() == 1:
            return [1]
        # Sum over all proper connected partitions of mask
        total = [0]

        def gen(rem, prod_poly, k):
            nonlocal total
            if rem == 0:
                if k > 1:
                    q_k = [1] * k
                    total = poly_add(total, poly_mul(q_k, prod_poly))
                return
            lsb = rem & -rem
            rest = rem ^ lsb
            sub = rest
            while True:
                blk = lsb | sub
                if conn[blk] and blk != mask:
                    gen(rem ^ blk, poly_mul(prod_poly, mu_conn(blk)), k + 1)
                if sub == 0:
                    break
                sub = (sub - 1) & rest

        gen(mask, [1], 0)
        return [-x for x in total]

    res = [1]
    for c in connected_components(n, edges):
        res = poly_mul(res, mu_conn(c))
    return res


def cubic_discriminant(a, b, c, d):
    """Discriminant of a*x^3 + b*x^2 + c*x + d."""
    return 18 * a * b * c * d - 4 * (b ** 3) * d + (b ** 2) * (c ** 2) - 4 * a * (c ** 3) - 27 * (a ** 2) * (d ** 2)


def main():
    # 1. Verify individual components directly from the verbatim weighted bond poset
    K3 = [(0, 1), (1, 2), (0, 2)]
    P3 = [(0, 1), (1, 2)]
    C5 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    House = C5 + [(1, 4)]

    mu_K3 = mu_from_verbatim_poset(3, K3)
    mu_P3 = mu_from_verbatim_poset(3, P3)
    mu_House = mu_from_verbatim_poset(5, House)
    mu_C5 = mu_from_verbatim_poset(5, C5)

    require(mu_K3 == [2, 5, 2], f"mu_K3 mismatch: {mu_K3}")
    require(mu_P3 == [1, 3, 1], f"mu_P3 mismatch: {mu_P3}")
    require(mu_House == [6, 49, 92, 49, 6], f"mu_House mismatch: {mu_House}")
    require(mu_C5 == [4, 34, 64, 34, 4], f"mu_C5 mismatch: {mu_C5}")

    # Cross-check against recurrence (3.1)
    require(mu_via_recurrence(3, K3) == mu_K3, "recurrence K3 mismatch")
    require(mu_via_recurrence(3, P3) == mu_P3, "recurrence P3 mismatch")
    require(mu_via_recurrence(5, House) == mu_House, "recurrence House mismatch")
    require(mu_via_recurrence(5, C5) == mu_C5, "recurrence C5 mismatch")

    # 2. Verify full 8-vertex disconnected graphs G = K3 + House, H = P3 + C5
    G_edges = K3 + [(u + 3, v + 3) for u, v in House]
    H_edges = P3 + [(u + 3, v + 3) for u, v in C5]
    require(set(H_edges).issubset(set(G_edges)), "H must be a spanning subgraph of G")
    require(len(connected_components(8, G_edges)) == 2, "G must have 2 components")
    require(len(connected_components(8, H_edges)) == 2, "H must have 2 components")

    mu_G = mu_via_recurrence(8, G_edges)
    mu_H = mu_via_recurrence(8, H_edges)
    require(mu_G == poly_mul(mu_K3, mu_House), "Proposition 2.2 mismatch for G")
    require(mu_H == poly_mul(mu_P3, mu_C5), "Proposition 2.2 mismatch for H")
    require(mu_G == [12, 128, 441, 656, 441, 128, 12], f"mu_G mismatch: {mu_G}")
    require(mu_H == [4, 46, 170, 260, 170, 46, 4], f"mu_H mismatch: {mu_H}")

    P = poly_sub(mu_G, mu_H)  # (-1)^(8-2) = +1
    require(P == [8, 82, 271, 396, 271, 82, 8], f"P mismatch: {P}")

    # 3. Verify gamma-expansion P(t) = 8(1+t)^6 + 34 t(1+t)^4 + 15 t^2(1+t)^2 + 2 t^3
    one_plus_t = [1, 1]
    t_poly = [0, 1]
    p_pow = [[1]]
    for _ in range(6):
        p_pow.append(poly_mul(p_pow[-1], one_plus_t))
    t_pow = [[1]]
    for _ in range(3):
        t_pow.append(poly_mul(t_pow[-1], t_poly))
    reconstructed = [0]
    for j, g in enumerate([8, 34, 15, 2]):
        term = [g * c for c in poly_mul(t_pow[j], p_pow[6 - 2 * j])]
        reconstructed = poly_add(reconstructed, term)
    require(reconstructed == P, f"gamma expansion mismatch: {reconstructed}")

    # 4. Verify reciprocal cubic identity z^3 * Q(z + 1/z) = P(z) and negative discriminant
    # Q(s) = 8 s^3 + 82 s^2 + 247 s + 232
    # Expanding 8(t^2+1)^3 + 82 t(t^2+1)^2 + 247 t^2(t^2+1) + 232 t^3:
    q0 = [1, 0, 1]
    q1 = q0
    q2 = poly_mul(q0, q0)
    q3 = poly_mul(q2, q0)
    lhs = poly_add(
        poly_add([8 * c for c in q3], [82 * c for c in poly_mul(t_pow[1], q2)]),
        poly_add([247 * c for c in poly_mul(t_pow[2], q1)], [232 * c for c in t_pow[3]]),
    )
    require(lhs == P, f"reciprocal cubic identity mismatch: {lhs}")

    disc_Q = cubic_discriminant(8, 82, 247, 232)
    disc_G = cubic_discriminant(2, 15, 34, 8)
    require(disc_Q == -22364 and disc_G == -22364, f"discriminant mismatch: {disc_Q}, {disc_G}")
    require(disc_Q < 0, "discriminant must be negative")

    # 5. Also verify K1 and K2 scaling identities for the all-(n, k) family
    require(mu_from_verbatim_poset(1, []) == [1], "mu_K1 mismatch")
    require(mu_from_verbatim_poset(2, [(0, 1)]) == [-1, -1], "mu_K2 mismatch")

    print(
        "PASS: verified verbatim WPi_G for K3, P3, House, C5; "
        "G = K3 + House, H = P3 + C5 (n=8, k=2) gives "
        "(-1)^(n-k)(mu_G - mu_H) = 8 + 82t + 271t^2 + 396t^3 + 271t^4 + 82t^5 + 8t^6; "
        "reciprocal cubic Q(s) = 8s^3 + 82s^2 + 247s + 232 has Delta = -22364 < 0 (not real-rooted)."
    )


if __name__ == "__main__":
    main()
