#!/usr/bin/env python3
"""Standalone verifier for Rofa's regular spider 0-rotatability theorem.

Directly implements the exact constructive proof formalized in
lean/Conjectures/SpiderRotatability.lean (zero search tables; Python 3 stdlib only).
Checks:
  1. Rosa's path alpha-labeling theorem for all 1 <= l <= 64, 0 <= d <= l, (l,d) != (4,2).
  2. Arbitrary-start graceful path theorem for all 1 <= l <= 64, 1 <= b <= l.
  3. Regular spider 0-rotatability for all 1 <= k <= 30, 1 <= l <= 30, 0 <= d <= l
     (14,850 triples), plus 333 larger stress-test triples up to k=256 and l=64.
"""

from functools import lru_cache
from itertools import pairwise


def flip_pair(x: int) -> int:
    return 2 * (x // 2) + (1 - (x % 2))


def walecki(n: int, x: int) -> int:
    return x // 2 if x % 2 == 0 else n - 1 - x // 2


def allowed(n: int, i: int) -> bool:
    return 0 <= i < n and (n % 2 == 0 or (i % 2 == 0 and (n != 2 * i + 1 or n == 1)))


def splice(f: tuple[int, ...], g: tuple[int, ...]) -> tuple[int, ...]:
    p = len(f)
    return f + tuple(p + x for x in g)


@lru_cache(maxsize=None)
def block_start(n: int, i: int) -> tuple[int, ...]:
    """Odd-sum permutation of 0..n-1 starting at i for every admissible (n, i)."""
    assert allowed(n, i), f"Not admissible: {(n, i)}"
    if n == 1:
        return (0,)
    if 2 * i >= n:
        f = block_start(n, n - 1 - i)
        return tuple(n - 1 - x for x in f)
    if i % 2 == 1:
        f = block_start(n, i - 1)
        return tuple(flip_pair(x) for x in f)
    if n % 2 == 0 and 2 * i + 2 < n:
        p = i + 2
        a = tuple(flip_pair(p - 1 - j) for j in range(p))
        return splice(a, block_start(n - p, i))
    p = i + 1
    a = tuple(p - 1 - j for j in range(p))
    return splice(a, block_start(n - p, i))


SEED_SIX = (3, 0, 1, 4, 5, 2)
SEED_NINE = (2, 5, 4, 1, 0, 3, 8, 7, 6)
SEED_THIRTEEN = (2, 5, 8, 7, 4, 1, 0, 3, 6, 11, 12, 9, 10)


def sum_extreme(n: int, d: int) -> tuple[int, ...]:
    """Odd-sum permutation of 0..n-1 with entry <= 1 at position d, (n,d) != (5,2)."""
    if 2 * d >= n:
        return sum_extreme(n, n - 1 - d)[::-1]
    if d <= 1:
        return tuple(range(n))
    if n == 9 and d in (3, 4):
        return SEED_NINE
    if n == 2 * d + 1 and d % 2 == 0:
        if d == 4:
            return SEED_NINE
        if d == 6:
            return SEED_THIRTEEN
        assert d >= 8
        p = d + 2
        a = splice(SEED_SIX, block_start(p - 6, 3))
        return splice(a[::-1], block_start(n - p, p - 4))
    for p in (d + 1, d + 2):
        if allowed(n - p, p - 1):
            a = tuple(p - 1 - j for j in range(p))
            return splice(a, block_start(n - p, p - 1))
        if p % 2 == 0 and allowed(n - p, p - 2):
            a = tuple(flip_pair(p - 1 - j) for j in range(p))
            return splice(a, block_start(n - p, p - 2))
    raise AssertionError(f"No construction for {(n, d)}")


def rosa_path_alpha(length: int, d: int) -> tuple[tuple[int, ...], int]:
    """Return (alpha-labeling of P_{length+1} with f[d] = 0, threshold a)."""
    n = length + 1
    g = sum_extreme(n, d)
    f = tuple(walecki(n, x) for x in g)
    a = length // 2
    if f[d] == 0:
        return f, a
    assert f[d] == length
    return tuple(length - x for x in f), length - 1 - a


def graceful_path_start(length: int, b: int) -> tuple[int, ...]:
    """Return 1-based graceful permutation of 1..length starting at b."""
    b0 = b - 1
    flip = 2 * b0 >= length
    target = length - 1 - b0 if flip else b0
    if allowed(length, 2 * target):
        g = block_start(length, 2 * target)
        f = tuple(walecki(length, x) for x in g)
    else:
        assert length == 4 * target + 1 and target > 0
        p = 2 * target + 1
        s = 2 * target
        u = block_start(s, 2 * (target - 1))
        tail = tuple(target + 1 + walecki(s, x) for x in u)
        prefix = tuple(walecki(length, p - 1 - i) for i in range(p))
        f = prefix + tail
    if flip:
        f = tuple(length - 1 - x for x in f)
    return tuple(x + 1 for x in f)


def spider_labeling(k: int, length: int, d: int) -> tuple[int, list[tuple[int, ...]]]:
    """Construct graceful labeling of T(k, length) with 0 at depth d on leg 0."""
    if length == 4 and d == 2:
        if k == 1:
            return 1, [(4, 0, 2, 3)]
        root, a = 2, 4
        legs = [(6, 0, 8, 1), (7, 4, 5, 3)]
        flip = False
    else:
        seed, a = rosa_path_alpha(length, d)
        flip = seed[0] > a
        if flip:
            seed = tuple(length - x for x in seed)
            a = length - 1 - a
        root = seed[0]
        legs = [seed[1:]]

    extra = k - len(legs)
    gap = extra * length
    legs = [tuple(x if x <= a else x + gap for x in leg) for leg in legs]
    if extra > 0:
        perm = graceful_path_start(length, length - a + root)
        for i in range(extra):
            legs.append(
                tuple(
                    a + b_val + length * (extra - 1 - i if j % 2 == 1 else i)
                    for j, b_val in enumerate(perm, start=1)
                )
            )
    if flip:
        q = k * length
        root = q - root
        legs = [tuple(q - x for x in leg) for leg in legs]
    return root, legs


def check_spider(k: int, length: int, d: int, root: int, legs: list[tuple[int, ...]]) -> None:
    q = k * length
    assert len(legs) == k and all(len(leg) == length for leg in legs)
    verts = [root]
    weights = []
    for leg in legs:
        verts.extend(leg)
        weights.extend(abs(u - v) for u, v in pairwise((root, *leg)))
    assert sorted(verts) == list(range(q + 1)), f"Bad vertex labels at {(k, length, d)}"
    assert sorted(weights) == list(range(1, q + 1)), f"Bad edge weights at {(k, length, d)}"
    target_val = root if d == 0 else legs[0][d - 1]
    assert target_val == 0, f"Zero misplaced at {(k, length, d)}: got {target_val}"


def main() -> None:
    # 1. Verify both path theorems through l = 64
    rosa_count = 0
    start_count = 0
    for length in range(1, 65):
        for d in range(length + 1):
            if (length, d) == (4, 2):
                continue
            f, a = rosa_path_alpha(length, d)
            assert sorted(f) == list(range(length + 1))
            assert sorted(abs(u - v) for u, v in pairwise(f)) == list(range(1, length + 1))
            assert all((u <= a < v) or (v <= a < u) for u, v in pairwise(f))
            assert f[d] == 0
            rosa_count += 1
        for b in range(1, length + 1):
            p = graceful_path_start(length, b)
            assert p[0] == b
            assert sorted(p) == list(range(1, length + 1))
            assert sorted(abs(u - v) for u, v in pairwise(p)) == list(range(1, length))
            start_count += 1

    # 2. Verify full 30x30 spider grid (14,850 triples)
    grid_count = 0
    for k in range(1, 31):
        for length in range(1, 31):
            for d in range(length + 1):
                root, legs = spider_labeling(k, length, d)
                check_spider(k, length, d, root, legs)
                grid_count += 1

    # 3. Larger stress tests (333 triples)
    larger_cases = [(1, 63), (2, 64), (31, 31), (64, 40), (101, 47), (73, 64), (256, 17)]
    larger_count = 0
    for k, length in larger_cases:
        for d in range(length + 1):
            root, legs = spider_labeling(k, length, d)
            check_spider(k, length, d, root, legs)
            larger_count += 1

    print(
        f"PASS: verified {rosa_count:,} Rosa alpha-paths, {start_count:,} arbitrary-start "
        f"graceful paths (l<=64), {grid_count:,} grid spiders (1<=k,l<=30), and "
        f"{larger_count:,} larger spider cases."
    )


if __name__ == "__main__":
    main()
