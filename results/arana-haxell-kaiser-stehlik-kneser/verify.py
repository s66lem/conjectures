#!/usr/bin/env python3
"""Verifier for Conjecture 1.3 of arXiv:2610.17884 at k = 3.

Uses explicit runtime checks (safe under `python -O`).
Dependencies: Python 3.10+ (standard library for all isolate, weight, and n=13..19
cases; `python-sat` / CaDiCaL for the two n=12 unrestricted coloring checks).
"""

from functools import lru_cache
from itertools import combinations, product
import sys


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def maximum_without_transversal_pair() -> int:
    def visit(fam, n):
        pairs = [(1 << x) | (1 << y) for x, y in combinations(range(n), 2)]
        trans = [p for p in pairs if all(p & a for a in fam)]
        triples = [sum(1 << x for x in t) for t in combinations(range(n + 1), 3)]
        allowed = [t for t in triples if all(t & a for a in fam)]
        if not trans:
            require(all(t < (1 << n) for t in allowed), "Fresh point introduced without pair transversal")

            def clique(c):
                if not c:
                    return 0
                a = c[0]
                return max(clique(c[1:]), 1 + clique([b for b in c[1:] if b & a]))

            return len(fam) + clique([t for t in allowed if t not in fam])
        choices = min(([t for t in allowed if not (t & p)] for p in trans), key=len)
        return max((visit(fam + [t], max(n, t.bit_length())) for t in choices), default=0)

    seed = [7, 25]  # {0,1,2} and {0,3,4}
    return max(visit(seed + [t], max(5, t.bit_length())) for t in [14, 42])  # {1,2,3} or {1,3,5}


ISOLATE_WEIGHTS = {
    9: [91, 91, 182, 91, 91, 0],
    10: [78, 68, 55, 114, 66, 84, 28, 0],
    11: [0, 48, 98, 72, 76, 4, 28, 54, 88],
    12: [20, 41, 61, 55, 69, 64, 65, 20, 28, 43, 56, 61],
    13: [28, 38, 45, 47, 48, 52, 53, 55, 25, 32, 37, 40, 42],
    14: [28, 35, 38, 41, 39, 43, 40, 44, 46, 47, 25, 31, 33, 34, 35, 35],
}


def check_isolate(m: int) -> bool:
    bit = lambda vs: sum(1 << x for x in vs)
    cyc = [bit(t) for t in combinations(range(m), 3) if all((x + 1) % m not in t for x in t)]
    iso = [(1 << m) | bit(t) for t in combinations(range(m), 2) if all((x + 1) % m not in t for x in t)]
    V = cyc + iso
    idx = {v: i for i, v in enumerate(V)}
    images = [
        {v: (v & (1 << m)) | bit((s * x + j) % m for x in range(m) if v >> x & 1) for v in V}
        for j in range(m)
        for s in (-1, 1)
    ]
    rep = {v: min(g[v] for g in images) for v in V}
    reps = sorted(set(rep.values()))
    orbits = [bit([idx[v] for v in V if rep[v] == r]) for r in reps]
    families = set()
    for a in cyc:
        if a != rep[a]:
            continue
        groups = {p: [] for p in [a ^ (1 << x) for x in range(m) if a >> x & 1]}
        for v in cyc:
            if (v & a) in groups:
                groups[v & a].append(v)
        choices = [[[], *([v] for v in group), group] for group in groups.values()]
        for T in product(*choices):
            fam = [a] + [u for t in T for u in t]
            fam += [b for b in iso if all(b & u for u in fam)]
            common = (1 << (m + 1)) - 1
            for v in fam:
                common &= v
            if not common:
                families.add(min(bit(idx[g[v]] for v in fam) for g in images))

    w = ISOLATE_WEIGHTS[m]
    require(len(w) == len(orbits), f"Weight length mismatch at m={m}")
    planes = [sum(o for o, x in zip(orbits, w) if x >> i & 1) for i in range(max(w).bit_length())]

    def weight(s: int) -> int:
        return sum((s & p).bit_count() << i for i, p in enumerate(planes))

    full = (1 << len(V)) - 1
    q = m - 4
    base = max(weight(f) for f in families)
    print(f"isolate m={m}: |V|={len(V)}, W={weight(full)}, B={base}, q*B={q * base}", flush=True)
    if weight(full) > base * q:
        return False

    family_orbits = []
    for f in families:
        if weight(f) < weight(full) - (q - 1) * base:
            continue
        vertices = [v for v in V if f >> idx[v] & 1]
        orbit = {bit(idx[g[v]] for v in vertices) for g in images}
        family_orbits.append((f, orbit))
    candidates = set.union(*(orbit for _, orbit in family_orbits))
    poses = [sum(1 for f in candidates if f >> i & 1) for i in range(len(V))]
    ordered = sorted(candidates, key=int.bit_count, reverse=True)
    buckets = [[] for _ in V]
    C = set()
    for f in ordered:
        ids = [i for i in range(len(V)) if (f >> i) & 1]
        i = min(ids, key=poses.__getitem__)
        if any((f & g) == f for g in buckets[i]):
            continue
        C.add(f)
        for i in ids:
            buckets[i].append(f)
    full_list = sorted(C)
    initial = [f for f, _ in family_orbits if f in C and q * weight(f) >= weight(full)]

    def dfs(uncovered: int, t: int, left: list[int]) -> bool:
        if not uncovered:
            return True
        need = weight(uncovered) - (t - 1) * base
        if t == 1:
            return any((g & uncovered) == uncovered for g in left)
        possible = [g for g in left if weight(g & uncovered) >= need]
        if not possible:
            return False
        best = None
        for i in sorted((j for j in range(len(V)) if uncovered >> j & 1), key=poses.__getitem__):
            picks = [g for g in possible if g >> i & 1]
            if not picks:
                return False
            if best is None or len(picks) < len(best):
                best = picks
            if len(best) == 1:
                break
        return any(dfs(uncovered ^ (uncovered & g), t - 1, possible) for g in best)

    return any(dfs(full ^ f, q - 1, full_list) for f in initial)


WEIGHTS_N13 = {
    9: [551, 512, 394, 649, 571, 570, 493, 452, 375, 388, 377],
    10: [602, 592, 527, 657, 600, 366, 614, 557, 507, 449, 388, 331, 346],
    11: [638, 595, 616, 489, 604, 298, 519, 391, 285],
}


def mask(points) -> int:
    return sum(1 << i for i in points)


def verify_base_n12() -> None:
    from pysat.solvers import Solver

    for m, r in ((9, 3), (10, 2)):
        n = m + r
        edges = [(i, (i + 1) % m) for i in range(m)] + [(i, i + 1) for i in range(m, n - 1)]
        vertices = [
            mask(t)
            for t in combinations(range(n), 3)
            if all(x not in t or y not in t for x, y in edges)
        ]
        clique = []
        for v in vertices:
            if all(not (v & u) for u in clique):
                clique.append(v)
        rest = [v for v in vertices if v not in clique]
        rest.sort(key=lambda v: -sum(not (v & u) for u in clique))
        order = clique + rest
        q = n - 5
        color = lambda i, c: 1 + i * q + c
        seen = lambda i, c: 1 + (len(order) + i) * q + c
        with Solver(name="cadical195") as solver:
            for i, v in enumerate(order):
                solver.add_clause([color(i, c) for c in range(q)])
                for c in range(q):
                    x, z = color(i, c), seen(i, c)
                    solver.add_clause([-x, z])
                    if c:
                        solver.add_clause([-x, seen(i - 1, c - 1)] if i else [-x])
                    if i:
                        prev = seen(i - 1, c)
                        solver.add_clause([-prev, z])
                        solver.add_clause([-z, x, prev])
                    else:
                        solver.add_clause([-z, x])
                for j, u in enumerate(order[:i]):
                    if not (v & u):
                        for c in range(q):
                            solver.add_clause([-color(i, c), -color(j, c)])
            require(solver.solve() is False, f"Unexpected {q}-coloring found for C_{m} + P_{r}")
        print(f"n=12 UNSAT verified: C_{m} + P_{r} has no {q}-coloring", flush=True)


def check_components(m: int, r: int, second_cycle: bool = False, extra: int = 0) -> None:
    n = m + r + extra
    q = n - 5
    weighted = n == 13
    edges = [(i, (i + 1) % m) for i in range(m)]
    edges += [(i, i + 1) for i in range(m, m + r - 1)]
    if second_cycle:
        edges.append((n - extra - 1, m))
    triples = [
        t
        for t in combinations(range(n), 3)
        if all(x not in t or y not in t for x, y in edges)
    ]
    index = {t: 1 << i for i, t in enumerate(triples)}
    full = (1 << len(triples)) - 1
    stars = [sum(b for t, b in index.items() if x in t) for x in range(n)]
    pair = [[a & b for b in stars] for a in stars]

    def triple(x, y, z):
        return index.get(tuple(sorted((x, y, z))), 0)

    if weighted:
        permutations = [
            [(j + s * x) % m for x in range(m)]
            + [m + (y if d == 1 else r - 1 - y) for y in range(r)]
            for j in range(m)
            for s in (-1, 1)
            for d in (-1, 1)
        ]
        orbit_masks = sorted(
            {
                sum({index[tuple(sorted(p[x] for x in t))] for p in permutations})
                for t in triples
            }
        )
        weights = WEIGHTS_N13[m]
        require(len(weights) == len(orbit_masks), f"Orbit weight mismatch at n=13, m={m}")
        planes = [
            sum(o for o, w in zip(orbit_masks, weights) if w >> i & 1)
            for i in range(max(weights).bit_length())
        ]
        score = lambda f: sum((p & f).bit_count() << i for i, p in enumerate(planes))
        small = 10 * max(weights)
    else:
        score = int.bit_count
        small = max(10, 6 + max(pair[x][y].bit_count() for x, y in combinations(range(n), 2)))

    total = score(full)
    target = (total + q - 1) // q
    classes = set()
    bound = small

    def consider(f):
        nonlocal bound
        value = score(f)
        if value <= small or any((s & f) == f for s in stars):
            return
        bound = max(bound, value)
        if not weighted:
            classes.add(f)

    for a, b, c in combinations(range(n), 3):
        consider(pair[a][b] | pair[a][c] | pair[b][c])
        t = triple(a, b, c)
        if t:
            for x in range(n):
                if x not in (a, b, c):
                    consider(t | pair[x][a] | pair[x][b] | pair[x][c])

    max_pair = max(pair[x][y].bit_count() for x, y in combinations(range(n), 2))
    if weighted or max(bound, 2 * max_pair + 3) >= target:
        for y in range(n):
            for x, a in combinations([v for v in range(n) if v != y], 2):
                base = pair[x][y] | pair[y][a]
                if not weighted and base.bit_count() + 3 <= small:
                    continue
                for u, v in combinations([j for j in range(n) if j not in (x, a, y)], 2):
                    consider(base | triple(y, u, v) | triple(x, a, u) | triple(x, a, v))
    else:
        bound = max(bound, 2 * max_pair + 3)

    if weighted:
        for x, y in combinations(range(n), 2):
            for four in combinations([v for v in range(n) if v not in (x, y)], 4):
                possible = {pair[x][y]}
                for a, b in combinations(four, 2):
                    c, d = [i for i in four if i not in (a, b)]
                    possible = {f | v for f in possible for v in (triple(x, a, b), triple(y, c, d))}
                for f in possible:
                    consider(f)
        require(total > q * bound, f"Weight certificate failed for n=13, m={m}: {total} <= {q * bound}")

    if total <= q * bound:
        @lru_cache(maxsize=None)
        def visit(uncovered, t):
            require(bool(t and uncovered), "Unexpected cover reached")
            required = (uncovered.bit_count() + t - 1) // t
            require(required > small, f"Threshold {required} <= small {small}")
            for f in classes:
                if (f & uncovered).bit_count() >= required:
                    require(t > 1 and bool(uncovered & ~f), "Starless cover found")
                    visit(uncovered & ~f, t - 1)

        first = {f for f in classes if f.bit_count() >= target}
        permutations = [
            [(j + s * x) % m for x in range(m)]
            + [m + (y if d == 1 else r - 1 - y) for y in range(r)]
            + list(range(m + r, n))
            for j in range(m)
            for s in (-1, 1)
            for d in (-1, 1)
        ]
        images = [[index[tuple(sorted(p[x] for x in t))] for t in triples] for p in permutations]
        while first:
            f = first.pop()
            ids = [i for i in range(len(triples)) if f >> i & 1]
            first.difference_update(sum(g[i] for i in ids) for g in images)
            visit(full & ~f, q - 1)


def run_finite(orders) -> int:
    require(maximum_without_transversal_pair() == 10, "No-pair-transversal bound != 10")
    checked = 0
    for n in orders:
        for m in range(9, n - 1):
            r = n - m
            if r < 9:
                check_components(m, r)
                checked += 1
        for m in range(9, n // 2 + 1):
            check_components(m, n - m, second_cycle=True)
            checked += 1
        if n == 19:
            check_components(9, 9, second_cycle=True, extra=1)
            checked += 1
    return checked


def main() -> None:
    args = sys.argv[1:] or ["base", "finite"]
    for arg in args:
        if arg == "base":
            for m in range(9, 15):
                require(check_isolate(m) is False, f"Cover found for C_{m} + K_1")
            verify_base_n12()
        elif arg == "finite":
            count = run_finite(range(13, 20))
            print(f"PASS: all {count} non-isolate cases across orders 13..19 verified.", flush=True)
        else:
            count = run_finite([int(arg)])
            print(f"PASS: order {arg} ({count} cases) verified.", flush=True)


if __name__ == "__main__":
    main()
