r"""Standalone verifier for the proof of Conjecture 1 of Easlick (arXiv:2610.40321v2).

Checks (stdlib only, -O safe via require()):
1. Exhaustive verification of Easlick's Theorem 1 for n = 3, 4, 5, 6:
   - Builds G_n on all C(2n-1, n) non-standard n-sided dice with face values in [n].
   - Computes all SCCs via Tarjan's algorithm: confirms G_3, G_4, G_5 are DAGs
     (exact vertex/edge counts match Table/Section 2: 10/3, 35/67, 126/620),
     and G_6 (462 vertices, 5491 edges) has exactly two nontrivial SCCs of size 7
     (10 edges each), each having maximum simple directed cycle length exactly 6.
   - Verifies the involutive antiautomorphism f(x_1,...,x_n) = (n+1-x_n,...,n+1-x_1)
     on G_3, G_4, G_5, G_6.
2. Explicit cycle verification for small cases n in {7, 8, 9, 10, 12, 14}, each of
   length n + 1 >= n + 1.
3. Infinite odd 3-die zipper family for all odd n in [11, 101] (cycle length 3(n - 7)).
4. Infinite even 3-die zipper family for all even n in [16, 100] (cycle length 3(n - 10)).
"""

import itertools
import time


def require(cond, msg):
    if not cond:
        raise RuntimeError(f"Verification failed: {msg}")


def min_adv_target(n):
    return (n * n) // 2 + 1


def wins(d1, d2):
    total = 0
    for a in d1:
        for b in d2:
            if a > b:
                total += 1
    return total


def flip_die(n, d):
    return tuple(n + 1 - x for x in reversed(d))


def verify_cycle(n, cyc, expected_len, label):
    T = min_adv_target(n)
    require(len(cyc) == expected_len, f"{label}: len {len(cyc)} != {expected_len}")
    require(len(cyc) >= 3, f"{label}: cycle length < 3")
    seen = set()
    for idx, d in enumerate(cyc):
        dt = tuple(d)
        require(len(dt) == n, f"{label}[{idx}]: length {len(dt)} != {n}")
        require(all(1 <= v <= n for v in dt), f"{label}[{idx}]: value out of [1..{n}]")
        require(list(dt) == sorted(dt), f"{label}[{idx}]: not non-decreasing")
        require(dt not in seen, f"{label}[{idx}]: duplicate die {dt}")
        seen.add(dt)
    for idx in range(len(cyc)):
        u = cyc[idx]
        v = cyc[(idx + 1) % len(cyc)]
        w = wins(u, v)
        require(w == T, f"{label}: edge {idx}->{(idx+1)%len(cyc)} has wins={w} != {T}")
        # Also check antiautomorphism property on every cycle edge
        require(
            wins(flip_die(n, v), flip_die(n, u)) == T,
            f"{label}: flipped edge failed at {idx}",
        )


def tarjan_sccs(num_v, adj):
    index = 0
    stack = []
    on_stack = [False] * num_v
    indices = [-1] * num_v
    lowlink = [0] * num_v
    sccs = []

    for start in range(num_v):
        if indices[start] != -1:
            continue
        # Iterative Tarjan to avoid recursion limit
        call_stack = [(start, 0)]
        indices[start] = lowlink[start] = index
        index += 1
        stack.append(start)
        on_stack[start] = True
        while call_stack:
            v, ei = call_stack[-1]
            if ei < len(adj[v]):
                call_stack[-1] = (v, ei + 1)
                w = adj[v][ei]
                if indices[w] == -1:
                    indices[w] = lowlink[w] = index
                    index += 1
                    stack.append(w)
                    on_stack[w] = True
                    call_stack.append((w, 0))
                elif on_stack[w]:
                    if indices[w] < lowlink[v]:
                        lowlink[v] = indices[w]
            else:
                call_stack.pop()
                if lowlink[v] == indices[v]:
                    comp = []
                    while True:
                        w = stack.pop()
                        on_stack[w] = False
                        comp.append(w)
                        if w == v:
                            break
                    sccs.append(comp)
                if call_stack:
                    parent = call_stack[-1][0]
                    if lowlink[v] < lowlink[parent]:
                        lowlink[parent] = lowlink[v]
    return sccs


def longest_simple_cycle_in_scc(comp, adj):
    comp_set = set(comp)
    sub = {u: [v for v in adj[u] if v in comp_set] for u in comp}
    best = 0
    for start in comp:
        # DFS for simple cycles returning to start with minimum vertex == start
        stack = [(start, [start], {start})]
        while stack:
            u, path, vis = stack.pop()
            for v in sub[u]:
                if v == start and len(path) >= 2:
                    if len(path) > best:
                        best = len(path)
                elif v > start and v not in vis:
                    stack.append((v, path + [v], vis | {v}))
    return best


def check_small_exhaustive():
    expected = {
        3: (10, 3, 0, 0),
        4: (35, 67, 0, 0),
        5: (126, 620, 0, 0),
        6: (462, 5491, 2, 6),
    }
    for n, (exp_v, exp_e, exp_nontriv, exp_max_cyc) in expected.items():
        T = min_adv_target(n)
        dice = list(itertools.combinations_with_replacement(range(1, n + 1), n))
        require(len(dice) == exp_v, f"G_{n}: |V|={len(dice)} != {exp_v}")
        idx_map = {d: i for i, d in enumerate(dice)}
        adj = [[] for _ in range(len(dice))]
        edge_count = 0
        # Fast wins via frequency histograms on [1..n]
        hists = []
        prefixes = []
        for d in dice:
            h = [0] * (n + 1)
            for x in d:
                h[x] += 1
            hists.append(h)
            pref = [0] * (n + 1)
            s = 0
            for v in range(1, n + 1):
                pref[v] = s
                s += h[v]
            prefixes.append(pref)
        for i, hi in enumerate(hists):
            for j, pj in enumerate(prefixes):
                w = 0
                for val in range(1, n + 1):
                    w += hi[val] * pj[val]
                if w == T:
                    adj[i].append(j)
                    edge_count += 1
        require(edge_count == exp_e, f"G_{n}: |E|={edge_count} != {exp_e}")
        # Verify antiautomorphism globally on G_n
        adj_sets = [set(lst) for lst in adj]
        for i, d in enumerate(dice):
            fi = idx_map[flip_die(n, d)]
            for j in adj[i]:
                fj = idx_map[flip_die(n, dice[j])]
                require(fi in adj_sets[fj], f"G_{n}: antiautomorphism failed on ({i},{j})")
        sccs = tarjan_sccs(len(dice), adj)
        nontriv = [c for c in sccs if len(c) > 1]
        require(len(nontriv) == exp_nontriv, f"G_{n}: nontrivial SCCs={len(nontriv)} != {exp_nontriv}")
        max_cyc = 0
        for c in nontriv:
            require(len(c) == 7, f"G_6: SCC size {len(c)} != 7")
            c_edges = sum(1 for u in c for v in adj[u] if v in set(c))
            require(c_edges == 10, f"G_6: SCC edges {c_edges} != 10")
            mc = longest_simple_cycle_in_scc(c, adj)
            if mc > max_cyc:
                max_cyc = mc
        require(max_cyc == exp_max_cyc, f"G_{n}: max cycle={max_cyc} != {exp_max_cyc}")


def build_odd_cycle(n):
    k = (n - 1) // 2
    m = n - 7
    def A(x): return [1] * k + [5] * k + [x]
    def B(y): return [2] * (k - 1) + [3] + [4] * k + [y]
    def C(z): return [2] + [3] * (2 * k - 1) + [z]
    cyc = []
    for q in range(m):
        cyc.append(B(6 if q == 0 else 6 + m - q))
        cyc.append(C(6 + m + 1 - q))
        cyc.append(A(6 + m - q))
    return cyc


def build_even_cycle(n):
    k = n // 2
    m = n - 10
    def A(x): return [1] * (k - 1) + [5] + [8] * (k - 1) + [x]
    def B(y): return [2] * (k - 3) + [3, 3] + [4] + [7] * (k - 1) + [y]
    def C(z): return [2] + [3] * (k - 2) + [6] * k + [z]
    cyc = []
    for q in range(m):
        cyc.append(B(9 if q == 0 else 9 + m - q))
        cyc.append(C(9 + m + 1 - q))
        cyc.append(A(9 + m - q))
    return cyc


SMALL_CYCLES = {
    7: [
        [1,1,1,3,3,4,7], [2,2,2,2,2,2,6], [1,1,1,3,5,5,5], [1,1,2,2,4,4,4],
        [1,1,3,3,3,3,3], [1,2,2,2,2,6,7], [1,1,1,3,5,5,6], [2,2,2,2,3,4,4],
    ],
    8: [
        [1,1,1,2,4,6,6,6], [1,1,3,3,3,3,3,5], [2,2,2,2,2,4,4,4],
        [1,1,1,3,3,3,7,8], [2,2,2,2,2,2,6,7], [1,1,1,2,5,5,5,6],
        [1,2,3,3,4,4,4,4], [1,2,3,3,3,3,3,8], [1,1,2,2,2,7,8,8],
    ],
    9: [
        [1,1,1,1,3,3,3,3,7], [2,2,2,2,2,2,2,2,6], [1,1,1,1,3,5,5,5,5],
        [1,1,2,2,2,4,4,4,4], [1,1,1,2,3,3,3,3,8], [2,2,2,2,2,2,2,2,7],
        [1,1,1,1,3,3,6,6,6], [2,2,2,2,2,2,2,4,5], [1,1,1,1,3,3,4,5,9],
        [2,2,2,2,2,2,2,2,8],
    ],
    10: [
        [1,1,1,1,2,4,4,4,4,4], [1,2,2,3,3,3,3,3,3,3], [1,2,2,2,2,2,2,5,6,6],
        [1,1,1,1,3,4,4,5,5,5], [1,2,2,3,3,3,3,3,3,4], [1,2,2,2,2,2,2,6,6,6],
        [1,1,1,1,2,5,5,5,5,6], [1,2,2,2,4,4,4,4,4,4], [1,3,3,3,3,3,3,3,5,5],
        [2,2,2,2,2,4,4,4,6,6], [1,1,2,2,2,2,3,5,5,5],
    ],
    12: [
        [1,1,1,1,1,2,4,4,4,4,4,4], [1,2,2,2,3,3,3,3,3,3,3,3], [1,1,1,2,2,2,2,2,6,6,6,6],
        [1,1,1,1,1,2,4,4,4,4,4,5], [1,2,3,3,3,3,3,3,3,3,3,3], [1,1,1,2,2,2,2,3,6,6,6,6],
        [1,1,1,1,1,3,4,4,4,5,5,5], [1,1,1,1,3,3,3,3,3,3,3,4], [2,2,2,2,2,2,2,2,2,3,6,6],
        [1,1,1,1,1,2,5,5,5,5,5,6], [1,2,2,2,2,2,2,4,4,4,4,4], [1,1,1,3,3,3,3,3,3,3,3,6],
        [1,1,1,2,2,2,2,2,5,6,6,6],
    ],
    14: [
        [2,2,2,3,3,3,3,6,6,6,6,6,6,8],
        [2,2,3,3,3,3,5,5,5,5,5,5,5,14],
        [1,1,1,1,1,1,4,7,7,7,7,7,7,13],
        [2,2,2,3,3,3,3,6,6,6,6,6,6,12],
        [2,2,3,3,3,3,5,5,5,5,5,5,5,13],
        [1,1,1,1,1,1,4,7,7,7,7,7,7,12],
        [2,2,2,3,3,3,3,6,6,6,6,6,6,11],
        [2,2,3,3,3,3,5,5,5,5,5,5,5,12],
        [1,1,1,1,1,1,4,7,7,7,7,7,7,11],
        [2,2,2,3,3,3,3,6,6,6,6,6,6,10],
        [2,2,3,3,3,3,5,5,5,5,5,5,5,11],
        [1,1,1,1,1,1,4,7,7,7,7,7,7,10],
        [2,2,2,3,3,3,3,6,6,6,6,6,6,9],
        [2,2,3,3,3,3,5,5,5,5,5,5,5,10],
        [1,1,1,1,1,1,4,7,7,7,7,7,7,9],
    ],
}


def main():
    t0 = time.perf_counter()

    # Check 1: Exhaustive Theorem 1 for n = 3, 4, 5, 6
    check_small_exhaustive()
    print("[PASS] Check 1: Exhaustive G_3..G_6 (DAGs for n=3,4,5; max cycle = 6 for n=6; global antiautomorphism)")

    # Check 2: Explicit small cycles for n in {7, 8, 9, 10, 12, 14}
    for n, cyc in SMALL_CYCLES.items():
        verify_cycle(n, cyc, n + 1, f"small-{n}")
    print("[PASS] Check 2: Explicit simple cycles of length n+1 for n in {7, 8, 9, 10, 12, 14}")

    # Check 3: Infinite odd zipper family for odd n = 11..101
    odd_count = 0
    for n in range(11, 102, 2):
        cyc = build_odd_cycle(n)
        exp_len = 3 * (n - 7)
        require(exp_len >= n + 1, f"odd-{n}: {exp_len} < {n+1}")
        verify_cycle(n, cyc, exp_len, f"odd-{n}")
        odd_count += 1
    print(f"[PASS] Check 3: Odd 3-die zipper family verified for all {odd_count} odd n in [11, 101] (len = 3(n-7))")

    # Check 4: Infinite even zipper family for even n = 16..100
    even_count = 0
    for n in range(16, 101, 2):
        cyc = build_even_cycle(n)
        exp_len = 3 * (n - 10)
        require(exp_len >= n + 1, f"even-{n}: {exp_len} < {n+1}")
        verify_cycle(n, cyc, exp_len, f"even-{n}")
        even_count += 1
    print(f"[PASS] Check 4: Even 3-die zipper family verified for all {even_count} even n in [16, 100] (len = 3(n-10))")

    dt = time.perf_counter() - t0
    print(f"ALL CHECKS PASSED in {dt:.3f}s.")


if __name__ == "__main__":
    main()
