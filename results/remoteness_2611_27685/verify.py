#!/usr/bin/env python3
"""
Standalone graph-level BFS verifier for the disproof of Conjecture 4.4 of
arXiv:2611.27685 (Allie, Du Preez, Hefty, Mafunda, Nov 2026).

Explicitly constructs each tree as an adjacency list, recovers its segment
sequence directly from the graph, and verifies:
  - exact sigma(v, T3) for EVERY vertex v (via O(n) rerooting + all-sources BFS for n=507);
  - exact leaf BFS for EVERY starlike and (Delta, 2)-D-tree (607 trees for k=13, 227 for k=8).
"""
import itertools
from collections import Counter, deque


class Tree:
    def __init__(self):
        self.adj = []

    def node(self):
        self.adj.append([])
        return len(self.adj) - 1

    def path(self, a, length, b=None):
        prev = a
        for i in range(length):
            x = b if (i == length - 1 and b is not None) else self.node()
            self.adj[prev].append(x)
            self.adj[x].append(prev)
            prev = x
        return prev


def sigma_bfs(adj, start):
    dist = [-1] * len(adj)
    dist[start] = 0
    q = deque([start])
    total = 0
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1
                total += dist[w]
                q.append(w)
    assert all(d >= 0 for d in dist), "Graph not connected"
    return total


def all_sigma_reroot(adj):
    n = len(adj)
    par = [-1] * n
    par[0] = 0
    order = [0]
    for u in order:
        for w in adj[u]:
            if par[w] < 0:
                par[w] = u
                order.append(w)
    size = [1] * n
    for u in reversed(order[1:]):
        size[par[u]] += size[u]
    sig = [0] * n
    sig[0] = sigma_bfs(adj, 0)
    for u in order[1:]:
        sig[u] = sig[par[u]] + n - 2 * size[u]
    return sig


def read_segments(adj):
    n = len(adj)
    assert sum(len(a) for a in adj) == 2 * (n - 1), "Not a tree"
    ends = [v for v in range(n) if len(adj[v]) != 2]
    seen_edges = set()
    segs = []
    for v in ends:
        for w in adj[v]:
            if (v, w) in seen_edges:
                continue
            prev, cur, length = v, w, 1
            seen_edges.add((v, w))
            while len(adj[cur]) == 2:
                nxt = adj[cur][0] if adj[cur][1] == prev else adj[cur][1]
                prev, cur, length = cur, nxt, length + 1
            seen_edges.add((cur, prev))
            segs.append(length)
    h = sum(1 for v in range(n) if len(adj[v]) >= 3)
    return sorted(segs, reverse=True), h, max(len(a) for a in adj)


def build_T3(j1, j2, p1, p2, p3):
    t = Tree()
    b1, b2, b3 = t.node(), t.node(), t.node()
    t.path(b1, j1, b2)
    t.path(b2, j2, b3)
    for b, p in ((b1, p1), (b2, p2), (b3, p3)):
        for length in p:
            t.path(b, length)
    return t.adj


def enum_h_le_2(D):
    t = Tree()
    c = t.node()
    for length in D:
        t.path(c, length)
    yield "starlike", t.adj

    cnt = Counter(D)
    for j in sorted(cnt):
        rest = cnt.copy()
        rest[j] -= 1
        vals = [v for v in sorted(rest) if rest[v] > 0]
        for split in itertools.product(*[range(rest[v] + 1) for v in vals]):
            a = [v for v, s in zip(vals, split) for _ in range(s)]
            b = [v for v, s in zip(vals, split) for _ in range(rest[v] - s)]
            if len(a) < 2 or len(b) < 2:
                continue
            t = Tree()
            u, v = t.node(), t.node()
            t.path(u, j, v)
            for length in a:
                t.path(u, length)
            for length in b:
                t.path(v, length)
            yield (j, tuple(a), tuple(b)), t.adj


CASES = [
    (315, 116, (21, 21), (25,), (1,) * 8),
    (5111, 3694, (15, 15), (79,), (1, 1, 1)),
]


def main():
    for j1, j2, p1, p2, p3 in CASES:
        D = sorted([j1, j2, *p1, *p2, *p3], reverse=True)
        n = 1 + sum(D)
        t3 = build_T3(j1, j2, p1, p2, p3)
        segs, h, delta = read_segments(t3)
        assert len(t3) == n and segs == D and h == 3
        sig = all_sigma_reroot(t3)
        if n < 2000:
            assert sig == [sigma_bfs(t3, v) for v in range(n)]
        for v in range(n):
            if len(t3[v]) == 1:
                assert sig[v] == sigma_bfs(t3, v)
        s3 = max(sig)

        best_le2 = None
        count = 0
        for tag, adj in enum_h_le_2(D):
            segs2, h2, _ = read_segments(adj)
            assert len(adj) == n and segs2 == D and h2 <= 2
            lb = max(sigma_bfs(adj, v) for v in range(n) if len(adj[v]) == 1)
            count += 1
            if best_le2 is None or lb < best_le2[0]:
                best_le2 = (lb, tag)

        assert best_le2[0] > s3
        print(f"[PASS] D={tuple(D)} (k={len(D)}, n={n}): ({delta},3)-tree sigma_max={s3} "
              f"< min(h<=2)={best_le2[0]} across all {count} trees (gap {best_le2[0] - s3}).")
    print("\nALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
