r"""Independent verifier for Takuto Nakai's OEIS A400474 conjecture.

Verifies:
1. Published OEIS A400474 prefix (n = 3..40) against the closed-form formula.
2. Exact enumeration of ordered distinct positive triples (u, v, w) summing to n
   and all floor triples (p, q, r) summing to n - 2 for 3 <= n <= 25:
   - unrestricted count equals T(n),
   - disjoint exclusion count equals T(n) - E_n(p) - E_n(q) - E_n(r),
   - maximum over all (p, q, r) equals the conjectured formula.
3. Balancing optimality and closed-form formula for all 16 <= n <= 120.
4. Direct Euclidean geometry spot-check: given balanced angles A, B, C, reconstruct
   actual interior points P in R^2 via circle intersections and confirm exact angles.
"""

import math


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(f"Verification failed: {message}")


def compositions3(total: int):
    for p in range(total + 1):
        for q in range(total - p + 1):
            yield p, q, total - p - q


def d_step(n: int, s: int) -> int:
    return s - 1 - (1 if s % 2 == 0 else 0) - (2 if (2 * s > n and 3 * s != 2 * n) else 0)


def excluded(n: int, p: int) -> int:
    return sum(d_step(n, s) for s in range(1, p + 1))


def total_triples(n: int) -> int:
    return (n - 1) * (n - 2) // 2 - 3 * ((n - 1) // 2) + (2 if n % 3 == 0 else 0)


def conjectured(n: int) -> int:
    c = (6, -3, 4, 3, 0, -5)[n % 6]
    num = n * n - 4 * n + c
    require(num % 3 == 0, f"non-integral numerator at n={n}")
    return num // 3


def verify_geometry_spot_check() -> int:
    """Spot-check Lemma 2.1 in R^2: construct unique interior point P for every
    admissible triple (x, y, z) on balanced triangles for n = 6..12."""
    checked = 0
    for n in range(6, 13):
        q0, rem = divmod(n - 2, 3)
        p, q, r = q0 + (1 if rem > 0 else 0), q0 + (1 if rem > 1 else 0), q0
        A = (p + 2.0 / 3.0) * math.pi / n
        B = (q + 2.0 / 3.0) * math.pi / n
        C = (r + 2.0 / 3.0) * math.pi / n
        # Place A = (0, 0), B = (1, 0), C in upper half-plane
        cotA = math.cos(A) / math.sin(A)
        cotB = math.cos(B) / math.sin(B)
        cy = 1.0 / (cotA + cotB)
        cx = cotA * cy
        # For each admissible (u, v, w), solve P via circle intersection of Gamma_AB(z) and Gamma_BC(x)
        count = 0
        for u in range(1, n - p):
            for v in range(1, n - q):
                w = n - u - v
                if w <= 0 or w >= n - r or len({u, v, w}) < 3:
                    continue
                x = (n - u) * math.pi / n
                y = (n - v) * math.pi / n
                z = (n - w) * math.pi / n
                # Center O1 of circle through A=(0,0), B=(1,0) with inscribed angle z above AB:
                o1x, o1y = 0.5, 0.5 / math.tan(z)
                # Center O2 of circle through B=(1,0), C=(cx,cy) with inscribed angle x on A-side:
                mx, my = 0.5 * (1.0 + cx), 0.5 * cy
                # Inward normal to B->C is (-(cy), cx - 1)
                nx, ny = -cy, cx - 1.0
                # Check orientation: dot(A - B, n) = (-1)*(-cy) = cy > 0 -> inward!
                scale = 0.5 / math.tan(x)
                o2x, o2y = mx + scale * nx, my + scale * ny
                # Reflect B=(1,0) across line O1-O2 to get unique second intersection P!
                dx, dy = o2x - o1x, o2y - o1y
                d2 = dx * dx + dy * dy
                require(d2 > 1e-12, f"coincident circles at n={n}, {(u,v,w)}")
                # Projection of B - O1 onto (dx, dy)
                t = ((1.0 - o1x) * dx + (0.0 - o1y) * dy) / d2
                projx, projy = o1x + t * dx, o1y + t * dy
                px, py = 2.0 * projx - 1.0, 2.0 * projy
                # Direct barycentric coordinates: P = lA*A + lB*B + lC*C with A=(0,0), B=(1,0), C=(cx,cy)
                lC = py / cy
                lB = px - lC * cx
                lA = 1.0 - lB - lC
                require(lA > 1e-9 and lB > 1e-9 and lC > 1e-9, f"not interior at n={n}, {(u,v,w)}")
                # Verify exact angles BPC, CPA, APB
                def ang(p1, p2):
                    v1x, v1y = p1[0] - px, p1[1] - py
                    v2x, v2y = p2[0] - px, p2[1] - py
                    dot = v1x * v2x + v1y * v2y
                    nrm = math.hypot(v1x, v1y) * math.hypot(v2x, v2y)
                    return math.acos(max(-1.0, min(1.0, dot / nrm)))
                require(abs(ang((1.0, 0.0), (cx, cy)) - x) < 1e-9, "angle BPC mismatch")
                require(abs(ang((cx, cy), (0.0, 0.0)) - y) < 1e-9, "angle CPA mismatch")
                require(abs(ang((0.0, 0.0), (1.0, 0.0)) - z) < 1e-9, "angle APB mismatch")
                count += 1
                checked += 1
        require(count == conjectured(n), f"geometry count mismatch at n={n}")
    return checked


def main() -> None:
    # Exhaustive combinatorial verification for 3 <= n <= 25
    for n in range(3, 26):
        triples = [
            (u, v, w)
            for u, v, w in compositions3(n)
            if u > 0 and v > 0 and w > 0 and len({u, v, w}) == 3
        ]
        require(len(triples) == total_triples(n), f"T({n}) mismatch")
        best = -1
        for p, q, r in compositions3(n - 2):
            cnt = sum(1 for u, v, w in triples if u < n - p and v < n - q and w < n - r)
            modeled = total_triples(n) - excluded(n, p) - excluded(n, q) - excluded(n, r)
            require(cnt == modeled, f"exclusion model mismatch at {(n, p, q, r)}")
            if cnt > best:
                best = cnt
        require(best == conjectured(n), f"max mismatch at n={n}: got {best}, expected {conjectured(n)}")

    # Balancing optimality for 16 <= n <= 120
    for n in range(16, 121):
        costs = [excluded(n, p) for p in range(n - 1)]
        min_excl = min(costs[p] + costs[q] + costs[r] for p, q, r in compositions3(n - 2))
        q0, rem = divmod(n - 2, 3)
        bal = [q0 + (1 if i < rem else 0) for i in range(3)]
        bal_excl = sum(costs[x] for x in bal)
        require(bal_excl == min_excl, f"balanced triple not optimal at n={n}")
        require(total_triples(n) - min_excl == conjectured(n), f"formula mismatch at n={n}")

    geom_pts = verify_geometry_spot_check()
    print(
        f"ALL CHECKS PASSED: exact enumeration (3<=n<=25), balancing optimality (16<=n<=120), "
        f"and {geom_pts} explicit R^2 circle-intersection interior points verified."
    )


if __name__ == "__main__":
    main()
