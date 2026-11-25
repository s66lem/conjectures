#!/usr/bin/env python3
"""Standalone Python 3 verifier for the disproof of Chen-Zwicker Conjecture 1
(arXiv:2402.05884 & arXiv:2608.29902).

Uses only the Python 3 standard library and is safe under `python3 -O`.
Checks:
1. H (K_{2,3} with sides {0,1} and {2,3,4} plus leaves 5-2, 6-3, 7-4) is connected.
2. Exact enumeration of all connected k-partitions of H for k = 2, 3, 4.
3. Under beta = 1_{2,3,4}, NO EF1_outer allocation exists at k = 2 and k = 4.
4. For ALL 256 common binary additive valuations on H, an EF1_outer 3-allocation exists.
5. All four minimal 8-vertex gap graphs (H plus 0, 1, 2, or 3 edges among {2,3,4})
   have exact common-binary spectrum Y N Y N Y Y Y Y.
"""


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


BASE_EDGES = [
    (0, 2), (0, 3), (0, 4),
    (1, 2), (1, 3), (1, 4),
    (2, 5), (3, 6), (4, 7),
]


def make_adj(edges: list[tuple[int, int]], n: int = 8) -> dict[int, set[int]]:
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def is_connected(adj: dict[int, set[int]], mask: int, n: int = 8) -> bool:
    verts = [v for v in range(n) if (mask >> v) & 1]
    if len(verts) <= 1:
        return True
    vset = set(verts)
    vis = {verts[0]}
    stack = [verts[0]]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w in vset and w not in vis:
                vis.add(w)
                stack.append(w)
    return len(vis) == len(verts)


def build_outer_rem(adj: dict[int, set[int]], n: int = 8) -> dict[int, list[int]]:
    outer_rem: dict[int, list[int]] = {}
    for mask in range(1 << n):
        if is_connected(adj, mask, n):
            verts = [v for v in range(n) if (mask >> v) & 1]
            outer_rem[mask] = [
                mask ^ (1 << v) for v in verts if is_connected(adj, mask ^ (1 << v), n)
            ]
    return outer_rem


def enum_unordered_connected_partitions(
    outer_rem: dict[int, list[int]], k: int, full_mask: int = 255
) -> list[tuple[int, ...]]:
    seen: set[tuple[int, ...]] = set()

    def bt(rem: int, prev: int, chosen: list[int]) -> None:
        if len(chosen) == k - 1:
            if rem >= prev and rem in outer_rem:
                seen.add(tuple(chosen + [rem]))
            return
        sub = rem
        while True:
            if sub >= prev and sub in outer_rem:
                bt(rem ^ sub, sub, chosen + [sub])
            if sub == 0:
                break
            sub = (sub - 1) & rem

    bt(full_mask, 0, [])
    return sorted(seen)


def has_ef1_outer_common_binary(
    val_bits: int,
    partitions: list[tuple[int, ...]],
    outer_rem: dict[int, list[int]],
) -> bool:
    for part in partitions:
        vals = [(m & val_bits).bit_count() for m in part]
        ok = True
        for i, vi in enumerate(vals):
            for j, mj in enumerate(part):
                if i == j or mj == 0:
                    continue
                if not any(vi >= (r & val_bits).bit_count() for r in outer_rem[mj]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


def main() -> None:
    beta = (1 << 2) | (1 << 3) | (1 << 4)  # hubs {a, b, c}
    variants = [
        ("H (0 hub edges)", BASE_EDGES),
        ("H + {a,b}", BASE_EDGES + [(2, 3)]),
        ("H + {a,b},{b,c}", BASE_EDGES + [(2, 3), (3, 4)]),
        ("H + K_3 on hubs", BASE_EDGES + [(2, 3), (3, 4), (2, 4)]),
    ]
    for name, edges in variants:
        adj = make_adj(edges)
        require(is_connected(adj, 255), f"{name} must be connected")
        outer_rem = build_outer_rem(adj)
        spec = []
        for k in range(1, 9):
            parts = enum_unordered_connected_partitions(outer_rem, k)
            if name.startswith("H ("):
                if k == 2:
                    require(len(parts) == 15, f"Expected 15 2-partitions, got {len(parts)}")
                elif k == 3:
                    require(len(parts) == 66, f"Expected 66 3-partitions, got {len(parts)}")
                elif k == 4:
                    require(len(parts) == 151, f"Expected 151 4-partitions, got {len(parts)}")
            if k in (2, 4):
                require(
                    not has_ef1_outer_common_binary(beta, parts, outer_rem),
                    f"{name} should fail at k={k} for beta",
                )
                spec.append("N")
            else:
                all_yes = all(
                    has_ef1_outer_common_binary(vb, parts, outer_rem) for vb in range(256)
                )
                require(all_yes, f"{name} should be YES at k={k} for all 256 binary valuations")
                spec.append("Y")
        require("".join(spec) == "YNYNYYYY", f"Unexpected spectrum for {name}: {''.join(spec)}")
    print(
        "PASS: verified H (8 vertices, connected) and all 3 hub-edge variants have exact "
        "common-binary EF1_outer spectrum Y N Y N Y Y Y Y (NO at k=2 and k=4 for beta=1_{a,b,c}; "
        "YES at k=3 for all 256 binary valuations across all 66 connected 3-partitions)."
    )


if __name__ == "__main__":
    main()
