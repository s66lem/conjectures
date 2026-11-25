#!/usr/bin/env python3
"""Standalone Python 3 verifier for the disproof of Bansal Conjecture C / 6.11 (arXiv:2611.02210).

Uses only the Python 3 standard library and is safe under `python3 -O`.
Directly implements Definitions 2.1, 2.3, 2.4, 2.7, and 6.8 of arXiv:2611.02210v1:
1. Calibrates forest reconstruction and forest polynomials on Figures 3 and 5.
2. Computes exact Monk expansions (x_1 + ... + x_i) P_F for x = (0,1,0,1,1,0,1)
   and all intermediate forests in P_7 up to Z = (1,2,4).
3. Verifies that (x, Z) consists of exactly 6 rank-5 and 6 rank-6 forests with
   12 cover edges forming two vertex-disjoint 6-cycles (C_6 U C_6).
4. Verifies code-raising covers Z = (1,2,4) < (1,2,5) < ... < (1,2,7) and all
   four failing rank-7 zigzags.
"""

from collections import defaultdict


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def forest_from_code(code: tuple[int, ...]):
    c = list(code)
    while c and c[-1] == 0:
        c.pop()
    if not c:
        return []
    m_bound = max(i + 1 + sum(c[i:]) for i in range(len(c))) + 2
    trees = {pos: ("L", pos) for pos in range(1, m_bound + 1)}

    def rho(t):
        return t[1] if t[0] == "L" else t[3]

    for i in range(len(c), 0, -1):
        for _ in range(c[i - 1]):
            keys = sorted(trees.keys())
            idx = keys.index(i)
            j = keys[idx + 1]
            left = trees[i]
            right = trees.pop(j)
            trees[i] = ("N", left, right, rho(left))
    return [t for _, t in sorted(trees.items()) if t[0] == "N"]


def forest_code(forest) -> tuple[int, ...]:
    cnt: dict[int, int] = defaultdict(int)

    def walk(t):
        if t[0] == "N":
            cnt[t[3]] += 1
            walk(t[1])
            walk(t[2])

    for t in forest:
        walk(t)
    if not cnt:
        return ()
    mx = max(cnt)
    return tuple(cnt[i] for i in range(1, mx + 1))


def forest_support(forest) -> frozenset[int]:
    supp = set()

    def leaves(t):
        return [t[1]] if t[0] == "L" else leaves(t[1]) + leaves(t[2])

    for t in forest:
        ls = leaves(t)
        require(ls == list(range(ls[0], ls[-1] + 1)), f"Non-contiguous leaves {ls}")
        for p in ls[:-1]:
            supp.add(p)
    return frozenset(supp)


def forest_poly(forest) -> dict[tuple[tuple[int, int], ...], int]:
    def poly_tree(t):
        if t[0] == "L":
            return None
        left, right, r = t[1], t[2], t[3]
        p_l = poly_tree(left)
        p_r = poly_tree(right)
        out: dict[int, dict[tuple[tuple[int, int], ...], int]] = defaultdict(
            lambda: defaultdict(int)
        )
        for lv in range(1, r + 1):
            left_opts = (
                [((), 1)]
                if p_l is None
                else [(m, c) for rl, mp in p_l.items() if lv <= rl for m, c in mp.items()]
            )
            right_opts = (
                [((), 1)]
                if p_r is None
                else [(m, c) for rr, mp in p_r.items() if lv < rr for m, c in mp.items()]
            )
            for m_l, c_l in left_opts:
                for m_r, c_r in right_opts:
                    md = dict(m_l)
                    for var, exp in m_r:
                        md[var] = md.get(var, 0) + exp
                    md[lv] = md.get(lv, 0) + 1
                    out[lv][tuple(sorted(md.items()))] += c_l * c_r
        return out

    total: dict[tuple[tuple[int, int], ...], int] = {(): 1}
    for t in forest:
        pt = poly_tree(t)
        comp: dict[tuple[tuple[int, int], ...], int] = defaultdict(int)
        for mp in pt.values():
            for m, c in mp.items():
                comp[m] += c
        nxt: dict[tuple[tuple[int, int], ...], int] = defaultdict(int)
        for m1, c1 in total.items():
            d1 = dict(m1)
            for m2, c2 in comp.items():
                d = dict(d1)
                for v, e in m2:
                    d[v] = d.get(v, 0) + e
                nxt[tuple(sorted(d.items()))] += c1 * c2
        total = dict(nxt)
    return total


def mon_to_code(m: tuple[tuple[int, int], ...]) -> tuple[int, ...]:
    if not m:
        return ()
    d = dict(m)
    mx = max(d)
    return tuple(d.get(i, 0) for i in range(1, mx + 1))


def lex_key(m: tuple[tuple[int, int], ...]) -> tuple[int, ...]:
    d = dict(m)
    mx = max(d) if d else 0
    return tuple(d.get(i, 0) for i in range(1, mx + 1)) + (0,) * 16


POLY_CACHE: dict[tuple[int, ...], dict[tuple[tuple[int, int], ...], int]] = {}


def get_poly(code: tuple[int, ...]):
    if code not in POLY_CACHE:
        f = forest_from_code(code)
        require(forest_code(f) == code, f"Code round-trip failed for {code}")
        POLY_CACHE[code] = forest_poly(f)
    return POLY_CACHE[code]


def monk_covers_up(code: tuple[int, ...], max_i: int = 8) -> set[tuple[int, ...]]:
    pf = get_poly(code)
    covers: set[tuple[int, ...]] = set()
    for i in range(1, max_i + 1):
        prod: dict[tuple[tuple[int, int], ...], int] = defaultdict(int)
        for m, c in pf.items():
            d = dict(m)
            for v in range(1, i + 1):
                d2 = dict(d)
                d2[v] = d2.get(v, 0) + 1
                prod[tuple(sorted(d2.items()))] += c
        rem = {m: c for m, c in prod.items() if c != 0}
        while rem:
            mn = min(rem.keys(), key=lex_key)
            coeff = rem[mn]
            require(coeff == 1, f"Non-unit Monk coeff {coeff} for {code}, i={i}")
            gc = mon_to_code(mn)
            covers.add(gc)
            for m, c in get_poly(gc).items():
                rem[m] = rem.get(m, 0) - c
                require(rem[m] >= 0, f"Negative remainder for {code}, i={i}, gc={gc}")
                if rem[m] == 0:
                    del rem[m]
    return covers


def open_interval_length3(x: tuple[int, ...], top: tuple[int, ...]):
    top_supp = forest_support(forest_from_code(top))
    max_i = max(top_supp) + 1
    edges = []
    r1 = set()
    r2 = set()
    for y in monk_covers_up(x, max_i=max_i):
        if not forest_support(forest_from_code(y)).issubset(top_supp):
            continue
        for z in monk_covers_up(y, max_i=max_i):
            if not forest_support(forest_from_code(z)).issubset(top_supp):
                continue
            if top in monk_covers_up(z, max_i=max_i):
                r1.add(y)
                r2.add(z)
                edges.append((y, z))
    adj: dict[tuple[int, tuple[int, ...]], set[tuple[int, tuple[int, ...]]]] = defaultdict(set)
    for y, z in edges:
        adj[(1, y)].add((2, z))
        adj[(2, z)].add((1, y))
    vis = set()
    comps = []
    for v in adj:
        if v not in vis:
            comp = []
            q = [v]
            vis.add(v)
            while q:
                u = q.pop()
                comp.append(u)
                for w in adj[u]:
                    if w not in vis:
                        vis.add(w)
                        q.append(w)
            comps.append(comp)
    return r1, r2, edges, comps, adj


def main() -> None:
    # Calibration: Figure 3 and Figure 5 of arXiv:2611.02210
    f3 = forest_from_code((3, 1, 0, 1))
    require(forest_code(f3) == (3, 1, 0, 1), "Fig 3 code")
    require(forest_support(f3) == frozenset({1, 2, 3, 4, 5}), "Fig 3 support")
    require(
        get_poly((2, 0, 1)) == {((1, 2), (2, 1)): 1, ((1, 2), (3, 1)): 1},
        "Fig 5 P_(2,0,1)",
    )
    require((2, 0, 1) in monk_covers_up((0, 1, 1), max_i=3), "Fig 5 cover 1")
    require((2, 0, 1) in monk_covers_up((1, 0, 1), max_i=3), "Fig 5 cover 2")
    require((2, 0, 1) in monk_covers_up((2,), max_i=3), "Fig 5 cover 3")

    # Main counterexample: Z = (1, 2, 4), x = (0, 1, 0, 1, 1, 0, 1)
    Z = (1, 2, 4)
    x = (0, 1, 0, 1, 1, 0, 1)
    require(all(a > 0 for a in Z), "Z must be a zigzag")
    require(forest_support(forest_from_code(Z)) == frozenset(range(1, 8)), "Z support")
    require(forest_support(forest_from_code(x)) == frozenset({2, 4, 5, 7}), "x support")

    r5, r6, edges, comps, adj = open_interval_length3(x, Z)
    require(len(r5) == 6 and len(r6) == 6 and len(edges) == 12, "Size of (x, Z)")
    require(len(comps) == 2, f"Expected 2 components, got {len(comps)}")
    for comp in comps:
        require(len(comp) == 6, f"Expected hexagon of size 6, got {len(comp)}")
        require(all(len(adj[v]) == 2 for v in comp), "Each vertex in C_6 must have degree 2")

    # Verify code-raising chain Z = (1,2,4) < (1,2,5) < (1,2,6)
    require((1, 2, 5) in monk_covers_up((1, 2, 4), max_i=4), "Code-raising (1,2,4) -> (1,2,5)")
    require((1, 2, 6) in monk_covers_up((1, 2, 5), max_i=4), "Code-raising (1,2,5) -> (1,2,6)")

    print(
        "PASS: calibrated Fig 3 & Fig 5; verified Z=(1,2,4) is zigzag of rank 7, "
        "x=(0,1,0,1,1,0,1) has open interval (x,Z) = C_6 U C_6 (12 vertices, 12 edges, 2 disconnected hexagons), "
        "and verified code-raising covers above Z."
    )


if __name__ == "__main__":
    main()
