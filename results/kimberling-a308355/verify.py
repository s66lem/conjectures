r"""Standalone verifier for the OEIS A308355 and A025065 conjectures.

Checks:
  1. Explicit counterexamples at odd n = 1, 3, 5 (row 5 vs. A308355 limit prefix).
  2. Palindromic-partition count A025065(n) == sum_{r <= n // 2} p(r).
  3. Exact maximal common prefix length between row n of A128628 and A308355 equals
     A025065(n) for all 1 <= n <= 26, and equals A025065(n + 1) iff n is even.

Standard library only; safe under `python -O -W error verify.py`.
"""

from collections import Counter
from itertools import islice


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"Verification failed: {msg}")


def partitions(total: int, ceiling: int | None = None):
    """Yield weakly decreasing partitions in descending lexicographic order (A080577)."""
    if total == 0:
        yield ()
        return
    largest = total if ceiling is None else min(total, ceiling)
    for head in range(largest, 0, -1):
        for tail in partitions(total - head, head):
            yield (head,) + tail


def limit_entries():
    """Yield terms of OEIS A308355 = concatenation of unrestricted blocks B(0), B(1), ..."""
    remainder = 0
    while True:
        yield from (1 + len(tail) for tail in partitions(remainder))
        remainder += 1


def row_a128628(n: int) -> list[int]:
    return [len(parts) for parts in partitions(n)]


def is_palindromic_partition(parts: tuple[int, ...]) -> bool:
    return sum(cnt % 2 for cnt in Counter(parts).values()) <= 1


def a025065(n: int) -> int:
    return sum(1 for parts in partitions(n) if is_palindromic_partition(parts))


def common_prefix_length(entries: list[int]) -> int:
    for idx, (actual, limit) in enumerate(zip(entries, limit_entries())):
        if actual != limit:
            return idx
    return len(entries)


def main() -> None:
    # 1. Published OEIS prefixes of A025065 (n = 0..15) and A308355 (first 30 terms),
    #    plus explicit counterexamples at n = 1, 3, 5.
    oeis_a025065 = [1, 1, 2, 2, 4, 4, 7, 7, 12, 12, 19, 19, 30, 30, 45, 45]
    for n, expected in enumerate(oeis_a025065):
        require(a025065(n) == expected, f"published A025065({n}) mismatch")
    oeis_a308355 = [
        1, 2, 2, 3, 2, 3, 4, 2, 3, 3, 4, 5, 2, 3, 3, 4, 4, 5, 6, 2,
        3, 3, 4, 3, 4, 5, 4, 5, 6, 7, 2, 3, 3, 4, 3, 4, 5, 4, 4, 5,
        6, 5, 6, 7, 8, 2, 3, 3, 4, 3, 4, 5, 3, 4, 4, 5, 6, 4, 5, 5,
        6, 7, 5, 6, 7, 8, 9, 2,
    ]
    require(
        list(islice(limit_entries(), len(oeis_a308355))) == oeis_a308355,
        "wrong A308355 68-term prefix",
    )
    require(row_a128628(1) == [1], "wrong row 1")
    require(row_a128628(3) == [1, 2, 3], "wrong row 3")
    require(row_a128628(5) == [1, 2, 2, 3, 3, 4, 5], "wrong row 5")
    require(common_prefix_length(row_a128628(1)) == 1 and a025065(2) == 2, "n=1 mismatch")
    require(common_prefix_length(row_a128628(3)) == 2 and a025065(4) == 4, "n=3 mismatch")
    require(common_prefix_length(row_a128628(5)) == 4 and a025065(6) == 7, "n=5 mismatch")

    # 2. Check bijection A025065(n) == sum_{r=0}^{n//2} p(r) and agreement for 1 <= n <= 26.
    p_cache = [sum(1 for _ in partitions(r)) for r in range(15)]
    for n in range(1, 27):
        pal = a025065(n)
        sum_p = sum(p_cache[: n // 2 + 1])
        require(pal == sum_p, f"A025065({n}) != sum p(r): {pal} vs {sum_p}")

        pref = common_prefix_length(row_a128628(n))
        require(pref == pal, f"agreement({n}) != A025065({n}): {pref} vs {pal}")

        claimed = a025065(n + 1)
        require(
            (pref == claimed) == (n % 2 == 0),
            f"parity condition failed at n={n}: pref={pref}, claimed={claimed}",
        )

    print(
        "ALL CHECKS PASSED: counterexamples at n = 1, 3, 5 and exact agreement "
        "== A025065(n) == sum_{r<=n//2} p(r) verified for 1 <= n <= 26."
    )


if __name__ == "__main__":
    main()
