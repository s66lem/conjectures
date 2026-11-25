r"""Standalone stdlib-only verifier for Fonollosa Problem 4 (unique multiset sums in finite abelian groups).

Checks (-O safe via require()):
1. Elementary abelian 2-group affine-basis construction for n = 1..8 (exact multiset enumeration).
2. Exhaustive verification over all 19,523 anchored size-n families (2 <= n <= 5) across all
   finite abelian group shapes of order <= 16:
   - Distinct subset-sum lower bound |G| >= 2^(n - 1),
   - Disjointness of nonzero doubles from subset sums: |G| >= 2^(n - 1) + |{2a_i} \ {0}|,
   - Complete equality classification: |G| = 2^(n - 1) => 2g = 0 for all g in G (elementary abelian 2-group),
   - Cyclic lower bound N >= 2^(n - 1) + (n - 1) // gcd(2, N) whenever G = Z/NZ.
"""

import math
from itertools import combinations, combinations_with_replacement, product
from time import perf_counter


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def group_shapes(order: int, least: int = 2):
    if order == 1:
        yield ()
    for factor in range(least, order + 1):
        if order % factor == 0:
            for rest in group_shapes(order // factor, factor):
                yield (factor,) + rest


def group_table(shape: tuple[int, ...]) -> list[list[int]]:
    elements = list(product(*(range(m) for m in shape)))
    idx = {e: i for i, e in enumerate(elements)}
    return [
        [idx[tuple((a + b) % m for a, b, m in zip(x, y, shape))] for y in elements]
        for x in elements
    ]


def group_sum(table: list[list[int]], multiset: tuple[int, ...]) -> int:
    total = 0
    for elem in multiset:
        total = table[total][elem]
    return total


def is_valid(table: list[list[int]], entries: tuple[int, ...]) -> bool:
    target = group_sum(table, entries)
    return all(
        rival == entries or group_sum(table, rival) != target
        for rival in combinations_with_replacement(entries, len(entries))
    )


def subset_sums(table: list[list[int]], entries: tuple[int, ...]) -> list[int]:
    sums = [0]
    for elem in entries:
        sums.extend(table[x][elem] for x in tuple(sums))
    return sums


def verify_construction() -> None:
    for n in range(1, 9):
        entries = (0,) + tuple(1 << i for i in range(n - 1))
        target = (1 << (n - 1)) - 1
        for rival in combinations_with_replacement(entries, n):
            total = 0
            for entry in rival:
                total ^= entry
            require(total != target or rival == entries, f"Construction failed at n={n}, rival={rival}")


def verify_small_groups() -> tuple[int, int, int, int]:
    tested = valid_count = equality_count = cyclic_valid = 0
    for order in range(1, 17):
        for shape in group_shapes(order):
            table = group_table(shape)
            is_cyclic = len(shape) <= 1
            for n in range(2, min(order, 5) + 1):
                for other in combinations(range(1, order), n - 1):
                    tested += 1
                    if not is_valid(table, (0,) + other):
                        continue
                    valid_count += 1
                    sums = set(subset_sums(table, other))
                    doubled = {table[x][x] for x in other} - {0}
                    require(len(sums) == 2 ** (n - 1), f"Subset sums collision at {shape}, {other}")
                    require(doubled.isdisjoint(sums), f"Double hits subset sum at {shape}, {other}")
                    require(order >= len(sums) + len(doubled), f"Combined bound failed at {shape}")
                    if order == len(sums):
                        require(all(table[x][x] == 0 for x in range(order)), f"Non-2-group equality at {shape}")
                        equality_count += 1
                    if is_cyclic:
                        cyclic_valid += 1
                        g = math.gcd(2, order)
                        require(
                            order >= 2 ** (n - 1) + (n - 1) // g,
                            f"Cyclic bound failed at N={order}, n={n}",
                        )
    require(
        (tested, valid_count, equality_count) == (19523, 3550, 872),
        f"Unexpected census counts: {(tested, valid_count, equality_count)}",
    )
    return tested, valid_count, equality_count, cyclic_valid


def main() -> None:
    start = perf_counter()
    verify_construction()
    tested, valid_count, equality_count, cyclic_valid = verify_small_groups()
    elapsed = perf_counter() - start
    print("ALL CHECKS PASSED")
    print(f"Construction verified for n = 1..8 in (Z/2Z)^(n-1).")
    print(
        f"Exhaustive small-group census (|G| <= 16, n <= 5): {tested} anchored sets, "
        f"{valid_count} valid ({cyclic_valid} cyclic), {equality_count} hitting |G| = 2^(n-1) "
        f"(all elementary abelian 2-groups) in {elapsed:.3f} s."
    )


if __name__ == "__main__":
    main()
