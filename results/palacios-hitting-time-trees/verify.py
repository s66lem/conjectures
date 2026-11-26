r"""Independent verifier for the tree hitting-time index theorem (arXiv:2611.34295v1).

Verifies:
1. Exact first-step Markov hitting-time equations vs. the closed-form formula
   H(x, y) = (n - 1) * d(x, y) + D(y) - D(x) on every labeled tree of order 2 <= n <= 6.
2. Closed-form polynomial lower bound for the pendant-path grafting move for all
   1 <= b <= a <= 12, a <= r <= a + 12, plus exact graph evaluation on star-core and path-core trees.
3. Exhaustive check of all 1,441 labeled trees of orders 2 <= n <= 6 (via Prufer codes):
   the selected diameter-deepest-branch move decreases leaf count by 1, strictly increases HT,
   and P_n is the unique maximizer at every order.
"""

from collections import deque
from itertools import product


def require(condition, message):
    if not condition:
        raise RuntimeError(f"Verification failed: {message}")


def adjacency(n, edges):
    neighbors = [[] for _ in range(n)]
    for x, y in edges:
        neighbors[x].append(y)
        neighbors[y].append(x)
    return neighbors


def distances(neighbors, root):
    n = len(neighbors)
    dist = [-1] * n
    dist[root] = 0
    q = deque([root])
    while q:
        v = q.popleft()
        for w in neighbors[v]:
            if dist[w] == -1:
                dist[w] = dist[v] + 1
                q.append(w)
    require(min(dist) >= 0, "disconnected graph")
    return dist


def hitting_time_index(n, edges):
    neighbors = adjacency(n, edges)
    metric = [distances(neighbors, x) for x in range(n)]
    trans = [sum(row) for row in metric]
    total = 0
    for target in range(n):
        hitting = [
            (n - 1) * metric[x][target] + trans[target] - trans[x]
            for x in range(n)
        ]
        require(hitting[target] == 0, "nonzero boundary")
        for x, adj in enumerate(neighbors):
            if x == target:
                continue
            require(
                len(adj) * hitting[x] == len(adj) + sum(hitting[y] for y in adj),
                ("first-step equation failed", edges, x, target),
            )
        for x in range(target):
            total += (n - 1) * metric[x][target] + abs(trans[x] - trans[target])
    return total


def connect_arm(edges, endpoint, first, length):
    for v in range(first, first + length):
        edges.append((endpoint, v))
        endpoint = v
    return endpoint


def poly_lower_bound_times_6(a, b, r):
    """Exact 6 * LB(a, b, r) proved in Lemma 3.2 for all a >= 2, 1 <= b <= a <= r."""
    d = a - b
    s = r - a
    return (12 * a * b * (a - 1) + b * (b - 1) * (b - 2)) * s + 2 * b * (
        6 * d**3
        + (15 * b - 6) * d**2
        + 2 * (b - 1) * (7 * b + 1) * d
        + (5 * b**3 - 7 * b**2 - 2 * b + 1)
    )


def verify_graft_bounds():
    checked_algebra = 0
    for a in range(2, 16):
        for b in range(1, a + 1):
            for r in range(a, a + 16):
                # Recompute 6 * LB directly from the family sums in Lemma 3.2
                m = a + b + r
                ac_bc_6 = 6 * a * b * (r + 1) * (2 * a - 1)
                ab_dist_6 = -6 * m * a * b
                bb_6 = -2 * a * b * (b * b - 1)
                ab_abs_6 = 0
                for i in range(1, a + 1):
                    for j in range(1, b + 1):
                        x_i = i * (r + b - a + i)
                        y_j = j * (r + a - b + j)
                        u = x_i - y_j
                        w = b * (r - a) + 2 * a * j
                        u2 = u + w
                        require(
                            u2 == (b + i - j) * (r + i + j - a) and u2 > 0,
                            ("u' identity failed", a, b, r, i, j),
                        )
                        if i < j:
                            require(u < 0, ("u < 0 failed for i < j", a, b, r, i, j))
                            lb = u2 + u
                        else:
                            lb = -2 * j * (a - b)
                        require(lb <= u2 - abs(u), ("pointwise LB failed", a, b, r, i, j))
                        ab_abs_6 += 6 * lb
                direct_6 = ac_bc_6 + ab_dist_6 + bb_6 + ab_abs_6
                closed_6 = poly_lower_bound_times_6(a, b, r)
                require(direct_6 == closed_6, ("polynomial identity mismatch", a, b, r))
                require(closed_6 > 0, ("nonpositive polynomial LB", a, b, r, closed_6))
                checked_algebra += 1

    checked_graphs = 0
    for a in range(1, 8):
        for b in range(1, a + 1):
            for r in range(a, a + 5):
                for star_core in (False, True):
                    core = [(0 if star_core else x - 1, x) for x in range(1, r + 1)]
                    tip = connect_arm(core, 0, r + 1, b)
                    before = core.copy()
                    after = core.copy()
                    connect_arm(before, 0, r + b + 1, a)
                    connect_arm(after, tip, r + b + 1, a)
                    n = a + b + r + 1
                    gain = hitting_time_index(n, after) - hitting_time_index(n, before)
                    if a == 1 and b == 1:
                        lb6 = 6 * r
                    else:
                        lb6 = poly_lower_bound_times_6(a, b, r)
                    require(6 * gain >= lb6 > 0, (a, b, r, star_core, gain, lb6))
                    checked_graphs += 1
    return checked_algebra, checked_graphs


def decode_prufer(n, code):
    deg = [1] * n
    for v in code:
        deg[v] += 1
    edges = []
    for v in code:
        leaf = deg.index(1)
        edges.append((leaf, v))
        deg[leaf] -= 1
        deg[v] -= 1
    edges.append(tuple(x for x in range(n) if deg[x] == 1))
    return edges


def selected_move(n, edges, neighbors):
    start = max(range(n), key=distances(neighbors, 0).__getitem__)
    from_start = distances(neighbors, start)
    end = max(range(n), key=from_start.__getitem__)
    from_end = distances(neighbors, end)
    diam = from_start[end]
    pivot = next(
        x for x in range(n)
        if len(neighbors[x]) >= 3 and from_start[x] + from_end[x] == diam
    )
    depth = max((from_start, from_end), key=lambda metric: metric[pivot])
    v = max((x for x in range(n) if len(neighbors[x]) >= 3), key=depth.__getitem__)
    arms = []
    for first in neighbors[v]:
        if depth[first] < depth[v]:
            continue
        tip = first
        while len(neighbors[tip]) == 2:
            tip = max(neighbors[tip], key=depth.__getitem__)
        arms.append((depth[tip] - depth[v], first, tip))
    (a, a_first, _), (b, _, b_tip) = sorted(arms, reverse=True)[:2]
    require(n - a - b - 1 >= a >= b >= 1, ("invalid arm lengths", edges))
    moved = [e for e in edges if set(e) != {v, a_first}]
    moved.append((b_tip, a_first))
    return moved


def verify_all_labeled_trees():
    expected_ht_path = {1: 0, 2: 1, 3: 10, 4: 38, 5: 102, 6: 223}
    count = 0
    for n in range(2, 7):
        path_ht = hitting_time_index(n, [(x, x + 1) for x in range(n - 1)])
        require(path_ht == expected_ht_path[n], (n, path_ht))
        for code in product(range(n), repeat=n - 2):
            edges = decode_prufer(n, code)
            neighbors = adjacency(n, edges)
            ht = hitting_time_index(n, edges)
            leaves = sum(len(row) == 1 for row in neighbors)
            if leaves == 2:
                require(ht == path_ht, ("path equality failed", edges))
            else:
                moved = selected_move(n, edges, neighbors)
                moved_leaves = sum(len(row) == 1 for row in adjacency(n, moved))
                require(moved_leaves == leaves - 1, ("leaf drop failed", edges))
                require(ht < hitting_time_index(n, moved) <= path_ht, edges)
            count += 1
    return count


def main():
    alg, graphs = verify_graft_bounds()
    trees = verify_all_labeled_trees()
    print(
        f"ALL CHECKS PASSED: {alg} algebraic (a,b,r) triples, "
        f"{graphs} explicit graft graphs, and all {trees} labeled trees of orders 2..6 verified."
    )


if __name__ == "__main__":
    main()
