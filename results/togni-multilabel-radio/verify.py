#!/usr/bin/env python3
"""Standalone exact verifier for Togni's multi-label radio labeling proofs (arXiv:2610.25863).

Verifies Definition 1.1 literally on all pairs of distinct vertex-label incidences
(including same-vertex pairs and cycle wraparound):
  1. Conjecture 1 upper bound (paths P_n, span <= m*S - 1) and S | n cycles.
  2. Conjecture 2 (cycles C_n, span <= m*S) for both general threshold
     n >= max(3, ceil(k*S*M/2)) and sharp residual threshold n >= max(3, k*M*dist(a*n, S*Z)),
     including half-integer tie choices of t.
  3. Non-vacuity check: confirms the checker detects invalid labelings below threshold.
"""

from itertools import combinations


def params(k: int):
    S = ((k + 1) ** 2 + 1) // 2
    a = k if k % 2 == 1 else k + 1
    return S, a


def dist_mod(x: int, mod: int) -> int:
    r = x % mod
    return min(r, mod - r)


def path_labeling(n: int, k: int, m: int):
    S, a = params(k)
    return [[(a * i) % S + j * S for j in range(m)] for i in range(n)]


def cycle_labeling(n: int, k: int, m: int, tie_high: bool = True):
    S, a = params(k)
    M = m * S + 1
    if tie_high:
        t = (2 * a * n + S) // (2 * S)
    else:
        t = (2 * a * n + S - 1) // (2 * S)
    return [[(M * (t * i + j * n) // (m * n)) % M for j in range(m)] for i in range(n)]


def check_literal_definition(rows, k: int, m: int, cycle: bool, max_span: int) -> int:
    """Verify Definition 1.1 over all relevant incidence pairs (all pairs when n <= 200;
    all same-vertex and distance <= k pairs when n > 200, as d > k holds trivially)."""
    n = len(rows)
    min_c = None
    max_c = None
    for row in rows:
        assert len(row) == m and len(set(row)) == m, "Duplicate labels at a vertex"
        for c in row:
            assert isinstance(c, int) and c >= 0, "Label must be a nonnegative integer"
            min_c = c if min_c is None else min(min_c, c)
            max_c = c if max_c is None else max(max_c, c)
    span = max_c - min_c
    assert span <= max_span, f"Span {span} exceeds {max_span}"
    D = k + 1
    if n <= 200:
        points = [(i, c) for i, row in enumerate(rows) for c in row]
        for (i, c1), (j, c2) in combinations(points, 2):
            d = min(j - i, n - (j - i)) if cycle else (j - i)
            if abs(c1 - c2) + d < D:
                raise AssertionError(
                    f"Constraint failed: k={k}, m={m}, n={n}, cycle={cycle}, "
                    f"({i},{c1}) vs ({j},{c2}), d={d}, |dc|={abs(c1-c2)}"
                )
        return len(points) * (len(points) - 1) // 2

    checked = 0
    for i in range(n):
        row_i = rows[i]
        # Same-vertex pairs
        for a_idx in range(m):
            for b_idx in range(a_idx + 1, m):
                if abs(row_i[a_idx] - row_i[b_idx]) < D:
                    raise AssertionError(f"Same-vertex failure at i={i}")
                checked += 1
        # Pairs at forward distance d = 1..k (covers every unordered pair with dist <= k)
        for d in range(1, min(k + 1, n)):
            j = i + d
            if j >= n:
                if not cycle:
                    break
                j -= n
            dist = min(d, n - d) if cycle else d
            row_j = rows[j]
            for c1 in row_i:
                for c2 in row_j:
                    if abs(c1 - c2) + dist < D:
                        raise AssertionError(
                            f"Constraint failed: k={k}, m={m}, n={n}, cycle={cycle}, "
                            f"({i},{c1}) vs ({j},{c2}), d={dist}"
                        )
                    checked += 1
    return checked


def main():
    total_pairs = 0
    total_cases = 0

    # 1. General threshold & boundary residual checks for 1 <= k <= 6, 1 <= m <= 3
    for k in range(1, 7):
        S, a = params(k)
        for m in range(1, 4):
            M = m * S + 1
            n0 = max(3, (k * S * M + 1) // 2)
            # Check n0 and n0 + 1 (at general threshold)
            for n in (n0, n0 + 1):
                for tie_high in (False, True):
                    rows = cycle_labeling(n, k, m, tie_high=tie_high)
                    total_pairs += check_literal_definition(rows, k, m, True, m * S)
                    total_cases += 1
            # Check sharp residual condition across residues -1, 0, +1 mod S
            for res in (-1, 0, 1):
                n = max(3, k * M * abs(res))
                while (a * n - res) % S != 0:
                    n += 1
                assert n >= max(3, k * M * dist_mod(a * n, S))
                rows_p = path_labeling(n, k, m)
                total_pairs += check_literal_definition(rows_p, k, m, False, m * S - 1)
                total_cases += 1
                rows_c = cycle_labeling(n, k, m, tie_high=True)
                total_pairs += check_literal_definition(rows_c, k, m, True, m * S)
                total_cases += 1
                if res == 0:
                    # S | n implies path labeling closes on C_n with span <= m*S - 1
                    total_pairs += check_literal_definition(rows_p, k, m, True, m * S - 1)
                    total_cases += 1

    # 2. Half-integer tie test (an/S = half-integer, e.g. k=3 => S=8, a=3, n=4*odd)
    for k in (1, 3, 5):
        S, a = params(k)
        for m in (1, 2):
            M = m * S + 1
            n = max(3, (k * S * M + 1) // 2)
            while (2 * a * n) % S != 0 or (a * n) % S == 0:
                n += 1
            for tie_high in (False, True):
                rows = cycle_labeling(n, k, m, tie_high=tie_high)
                total_pairs += check_literal_definition(rows, k, m, True, m * S)
                total_cases += 1

    # 3. Non-vacuity check: verify below-threshold cases genuinely fail
    failures_detected = 0
    for k in (2, 3):
        S, _ = params(k)
        for m in (1, 2):
            for n in range(3, 15):
                try:
                    check_literal_definition(cycle_labeling(n, k, m), k, m, True, m * S)
                except AssertionError:
                    failures_detected += 1
    assert failures_detected > 0, "Sanity check failed: expected below-threshold failures"

    print(
        f"PASS: {total_cases} labelings verified ({total_pairs:,} literal incidence pairs); "
        f"non-vacuity confirmed ({failures_detected} below-threshold failures caught)."
    )


if __name__ == "__main__":
    main()
