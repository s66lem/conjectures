r"""Verifier for the disproof of Li--Nesetril--Yang, arXiv:2611.33681v1, Problem 3.6
and the weak inequality of Problem 3.5.

Definitions (Section 3.2 of the paper). For an oriented graph D, an ordering s of
V(D), and k >= 1:
  * x is weakly (k,+)-reachable from y if x <=_s y and there is a directed y->x path
    with at most k arcs all of whose vertices z satisfy x <=_s z;
  * strongly (k,+)-reachable if moreover every internal vertex z satisfies y <_s z;
  * the (k,-) versions use directed x->y paths (equivalently, the reversed orientation);
  * y belongs to all of its own sets.
  col+_k(D)  = min_s max_y |S^{k,+}(y)|,   wcol+_k(D) = min_s max_y |W^{k,+}(y)|,
  col_k(D)   = min_s max_y |S^{k,+}(y) u S^{k,-}(y)|,  wcol_k(D) likewise with W.
  For an undirected graph G each parameter is the maximum over all orientations of G.

Checks performed (stdlib only; uses require() so it is safe under python -O):
  1. Forest lemma: every orientation of every forest on <= 6 vertices (65,988 pairs)
     has col+_k = wcol+_k = 1 for k = 1..4 via topological ordering.
  2. P4 = a-b-c-d, k = 2..4: wcol_k(P4) = 3, every orientation has wcol+_k = 1,
     so wcol_k(P4) = 3 > 2 = 2 wcol+_k(P4) and no orientation meets Problem 3.6.
  3. Hand case analysis for the directed path a->b->c->d over all 24 orderings.
  4. Halving chain for paths P_{2^t - 1}: exhaustive min over orderings for N = 3, 7,
     and explicit chain construction on random orderings for N = 15, 31, 63.
Run: python -O -W error results/li-nesetril-yang-wcol/verify.py
"""
import itertools
import random
import sys


def require(cond, msg):
    if not cond:
        sys.stderr.write("FAIL: " + msg + "\n")
        sys.exit(1)


def out_lists(n, arcs):
    out = [[] for _ in range(n)]
    for u, v in arcs:
        out[u].append(v)
    return out


def strong_set(out, pos, y, k):
    """Strongly (k,+)-reachable vertices from y (excluding y)."""
    found = set()
    frontier = {y}
    seen = {y}
    for _ in range(k):
        nxt = set()
        for u in frontier:
            for w in out[u]:
                if pos[w] < pos[y]:
                    found.add(w)
                elif pos[w] > pos[y] and w not in seen:
                    seen.add(w)
                    nxt.add(w)
        frontier = nxt
    return found


def weak_set(out, pos, y, k):
    """Weakly (k,+)-reachable vertices from y (excluding y)."""
    n = len(out)
    found = set()
    for x in range(n):
        if pos[x] >= pos[y]:
            continue
        frontier = {y}
        seen = {y}
        hit = False
        for _ in range(k):
            nxt = set()
            for u in frontier:
                for w in out[u]:
                    if pos[w] < pos[x] or w in seen:
                        continue
                    if w == x:
                        hit = True
                    seen.add(w)
                    nxt.add(w)
            frontier = nxt
            if hit or not frontier:
                break
        if hit:
            found.add(x)
    return found


def params(n, arcs, k, orders=None):
    """Return (col+, wcol+, col, wcol) of the oriented graph (min over orderings)."""
    out = out_lists(n, arcs)
    inn = out_lists(n, [(v, u) for u, v in arcs])
    best = [None] * 4
    for order in (orders if orders is not None else itertools.permutations(range(n))):
        pos = [0] * n
        for i, v in enumerate(order):
            pos[v] = i
        cur = [0, 0, 0, 0]
        for y in range(n):
            sp = strong_set(out, pos, y, k)
            sm = strong_set(inn, pos, y, k)
            wp = weak_set(out, pos, y, k)
            wm = weak_set(inn, pos, y, k)
            vals = (1 + len(sp), 1 + len(wp), 1 + len(sp | sm), 1 + len(wp | wm))
            cur = [max(a, b) for a, b in zip(cur, vals)]
        best = [c if b is None else min(b, c) for b, c in zip(best, cur)]
    return tuple(best)


def orientations(edges):
    for bits in itertools.product((0, 1), repeat=len(edges)):
        yield [(u, v) if t == 0 else (v, u) for (u, v), t in zip(edges, bits)]


def is_forest(n, edges):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for u, v in edges:
        a, b = find(u), find(v)
        if a == b:
            return False
        parent[a] = b
    return True


def topological_order(n, arcs):
    indeg = [0] * n
    out = out_lists(n, arcs)
    for _, v in arcs:
        indeg[v] += 1
    stack = [v for v in range(n) if indeg[v] == 0]
    order = []
    while stack:
        u = stack.pop()
        order.append(u)
        for w in out[u]:
            indeg[w] -= 1
            if indeg[w] == 0:
                stack.append(w)
    return order


def check_forest_lemma():
    count = 0
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2))
        for m in range(n):
            for edges in itertools.combinations(pairs, m):
                if not is_forest(n, edges):
                    continue
                for arcs in orientations(list(edges)):
                    order = topological_order(n, arcs)
                    require(len(order) == n, "forest orientation is acyclic")
                    for k in range(1, 5):
                        p = params(n, arcs, k, orders=[order])
                        require(p[0] == 1 and p[1] == 1,
                                "topological order gives col+ = wcol+ = 1 on forest")
                    count += 1
    return count


def check_p4():
    edges = [(0, 1), (1, 2), (2, 3)]
    for k in range(2, 5):
        all_p = [params(4, arcs, k) for arcs in orientations(edges)]
        colp = max(p[0] for p in all_p)
        wcolp = max(p[1] for p in all_p)
        col = max(p[2] for p in all_p)
        wcol = max(p[3] for p in all_p)
        require(colp == 1 and wcolp == 1, "every orientation of P4 has col+ = wcol+ = 1")
        require(col == 2, "col_k(P4) = 2")
        require(wcol == 3, "wcol_k(P4) = 3")
        require(wcol > 2 * wcolp, "Problem 3.5 weak inequality fails on P4")
        target_w = (wcol + 1) // 2
        require(target_w == 2, "Problem 3.6 weak target is 2")
        require(all(p[1] != target_w for p in all_p),
                "no orientation of P4 attains the Problem 3.6 targets")
    return True


def check_hand_case_analysis():
    arcs = [(0, 1), (1, 2), (2, 3)]
    out = out_lists(4, arcs)
    inn = out_lists(4, [(v, u) for u, v in arcs])
    for order in itertools.permutations(range(4)):
        pos = [0] * 4
        for i, v in enumerate(order):
            pos[v] = i
        sizes = [1 + len(weak_set(out, pos, y, 2) | weak_set(inn, pos, y, 2)) for y in range(4)]
        require(max(sizes) >= 3, "case analysis: some vertex has |W| >= 3")
        f = order[0]
        rest = [v for v in order if v != f]
        if f in (1, 2):
            far = 3 if f == 1 else 0
            mid = 2 if f == 1 else 1
            wit = far if pos[mid] < pos[far] else mid
        else:
            g = rest[0]
            near, mid, far = (1, 2, 3) if f == 0 else (2, 1, 0)
            wit = mid if g in (near, far) else near
        require(sizes[wit] >= 3, "named witness has |W| >= 3 (order %s)" % (order,))


def chain_witness(N, order):
    """Halving chain on the path 0-1-...-(N-1); return (y, chain)."""
    pos = [0] * N
    for i, v in enumerate(order):
        pos[v] = i
    lo, hi = 0, N - 1
    chain = []
    while lo <= hi:
        m = min(range(lo, hi + 1), key=lambda v: pos[v])
        chain.append(m)
        if m - lo >= hi - m:
            hi = m - 1
        else:
            lo = m + 1
    return chain[-1], chain


def check_lemma_c():
    for t in (2, 3):
        N = 2 ** t - 1
        arcs = [(i, i + 1) for i in range(N - 1)]
        p = params(N, arcs, N - 1)
        require(p[3] >= t, "wcol_{N-1}(P_N) >= t for N = 2^t - 1")
        require(p[1] == 1, "directed path has wcol+ = 1")
    rng = random.Random(20261126)
    for t in (4, 5, 6):
        N = 2 ** t - 1
        arcs = [(i, i + 1) for i in range(N - 1)]
        out = out_lists(N, arcs)
        inn = out_lists(N, [(v, u) for u, v in arcs])
        for _ in range(40):
            order = list(range(N))
            rng.shuffle(order)
            pos = [0] * N
            for i, v in enumerate(order):
                pos[v] = i
            y, chain = chain_witness(N, order)
            require(len(chain) >= t, "halving chain has length >= t")
            W = weak_set(out, pos, y, N - 1) | weak_set(inn, pos, y, N - 1)
            require(set(chain[:-1]) <= W, "last chain vertex weakly reaches the chain")
    return True


def main():
    nf = check_forest_lemma()
    check_p4()
    check_hand_case_analysis()
    check_lemma_c()
    print("forest orientations checked:", nf)
    print("P4, k=2..4: col+ = wcol+ = 1, col = 2, wcol = 3; Problem 3.6 has no orientation")
    print("Lemma C verified (exhaustive N=3,7; constructive N=15,31,63)")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
