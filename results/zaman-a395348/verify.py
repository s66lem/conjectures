r"""Standalone verifier for Rahid Zaman's OEIS A395348 conjecture.

Checks:
1. Exact greedy two-color spiral queen simulation through 408 rounds (816 placements),
   matching the closed-form coordinates for both Black (A395348) and Red (A395349).
2. Exact line-set invariants (X, Y, X+Y, X-Y) at the start of every block h = 1..100.
3. Exact recurrence a(n + 4) = a(n) + 8*n + 34 for all 2 <= n <= 403.
4. Direct spiral label-to-coordinate bijection consistency.
"""

BASE = (
    ((0, 0), (2, -1)),
    ((1, 1), (-1, 2)),
    ((-2, 0), (-1, -2)),
    ((3, 1), (2, 3)),
)


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def spiral_xy(k: int) -> tuple[int, int]:
    """Return coordinates (x, y) for spiral label k >= 0."""
    if k == 0:
        return (0, 0)
    # Find ring r >= 1 with (2r - 1)^2 <= k < (2r + 1)^2
    s = int(k ** 0.5)
    while (s + 1) * (s + 1) <= k:
        s += 1
    while s * s > k:
        s -= 1
    r = (s + 1) // 2
    idx = k - (2 * r - 1) ** 2
    e, t = divmod(idx, 2 * r)
    if e == 0:
        return (r, 1 - r + t)
    if e == 1:
        return (r - 1 - t, r)
    if e == 2:
        return (-r, r - 1 - t)
    return (1 - r + t, -r)


def spiral_label(x: int, y: int) -> int:
    """Return spiral label k >= 0 for coordinates (x, y)."""
    r = max(abs(x), abs(y))
    if r == 0:
        return 0
    base = (2 * r - 1) ** 2
    if x == r and y > -r:
        return base + (y - (1 - r))
    if y == r and x < r:
        return base + 2 * r + ((r - 1) - x)
    if x == -r and y < r:
        return base + 4 * r + ((r - 1) - y)
    return base + 6 * r + (x - (1 - r))


def predicted_pair(n: int) -> tuple[tuple[int, int], tuple[int, int]]:
    if n < 4:
        return BASE[n]
    h, j = divmod(n - 4, 4)
    r = 2 * h + (3, 4, 4, 5)[j]
    return (
        ((-r, 1), (2, -r)),
        ((r, 0), (-1, r)),
        ((-r, 0), (-1, -r)),
        ((r, 1), (2, r)),
    )[j]


def predicted_black_label(n: int) -> int:
    if n < 4:
        return (0, 2, 18, 28)[n]
    h, j = divmod(n - 4, 4)
    r = 2 * h + (3, 4, 4, 5)[j]
    return (
        4 * r * r + r - 1,
        4 * r * r - 3 * r,
        4 * r * r + r,
        4 * r * r - 3 * r + 1,
    )[j]


def predicted_red_label(n: int) -> int:
    if n < 4:
        return (9, 15, 21, 31)[n]
    h, j = divmod(n - 4, 4)
    r = 2 * h + (3, 4, 4, 5)[j]
    return (
        4 * r * r + 3 * r + 2,
        4 * r * r - r + 1,
        4 * r * r + 3 * r - 1,
        4 * r * r - r - 2,
    )[j]


def lines_of(pt: tuple[int, int]) -> tuple[int, int, int, int]:
    x, y = pt
    return (x, y, x + y, x - y)


def main() -> None:
    # 1. Verify spiral_xy / spiral_label bijection for labels 0..10000
    for k in range(10001):
        pt = spiral_xy(k)
        require(spiral_label(*pt) == k, f"bijection failed at k={k}, pt={pt}")

    # 2. Simulate greedy game from scratch for 408 rounds (h = 0..100)
    num_rounds = 408
    occupied: set[tuple[int, int]] = set()
    opp_lines: list[list[set[int]]] = [[set() for _ in range(4)] for _ in range(2)]
    black_labels: list[int] = []
    red_labels: list[int] = []
    cursors = [0, 0]

    for n in range(num_rounds):
        exp_pair = predicted_pair(n)
        for color in (0, 1):
            k = cursors[color]
            while True:
                pt = spiral_xy(k)
                if pt not in occupied:
                    vals = lines_of(pt)
                    if not any(v in s for v, s in zip(vals, opp_lines[1 - color])):
                        break
                k += 1
            require(pt == exp_pair[color], f"round {n} color {color}: got {pt}, expected {exp_pair[color]}")
            occupied.add(pt)
            for v, s in zip(lines_of(pt), opp_lines[color]):
                s.add(v)
            cursors[color] = k + 1
            if color == 0:
                require(k == predicted_black_label(n), f"black label formula mismatch at n={n}: got {k}")
                black_labels.append(k)
            else:
                require(k == predicted_red_label(n), f"red label formula mismatch at n={n}: got {k}")
                red_labels.append(k)

        # Check exact Lemma 2.1 invariants at the end of round 4h + 3 (for h >= 1)
        if n >= 7 and (n - 3) % 4 == 0:
            h = (n - 3) // 4
            bx, by, bs, bd = opp_lines[0]
            rx, ry, rs, rd = opp_lines[1]
            require(bx == set(range(-(2 * h + 2), 2 * h + 4)) - {-1, 2}, f"bx invariant at h={h}")
            require(by == {0, 1}, f"by invariant at h={h}")
            require(bs == set(range(-(2 * h + 2), 2 * h + 5, 2)), f"bs invariant at h={h}")
            require(bd == set(range(-(2 * h + 2), 2 * h + 3, 2)), f"bd invariant at h={h}")
            require(rx == {-1, 2}, f"rx invariant at h={h}")
            require(ry == set(range(-(2 * h + 2), 2 * h + 4)) - {0, 1}, f"ry invariant at h={h}")
            require(rs == set(range(-(2 * h + 3), 2 * h + 6, 2)), f"rs invariant at h={h}")
            require(rd == set(range(-(2 * h + 3), 2 * h + 4, 2)), f"rd invariant at h={h}")

    # 3. Verify Zaman's recurrence for all 2 <= n <= num_rounds - 5
    for n in range(2, num_rounds - 4):
        require(
            black_labels[n + 4] == black_labels[n] + 8 * n + 34,
            f"recurrence failed at n={n}",
        )

    print(
        f"ALL CHECKS PASSED: {num_rounds} rounds (816 placements), "
        f"100 exact block invariants, final labels Black={black_labels[-1]} Red={red_labels[-1]}."
    )


if __name__ == "__main__":
    main()
