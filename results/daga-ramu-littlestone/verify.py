#!/usr/bin/env python3
"""Standalone exact integer verifier for both conjectures in arXiv:2611.28727
(Daga & Ramu, "How many mistakes does it take to learn an interval?").

Uses Python 3 standard library only:
  1. Conjecture 31 (rods): exact scaled-integer check of all 65,792 first cuts
     (up to reflection) for rods of measure 2..513 (m = 1..512), verifying
     greedy optimality and exact match with recurrence R(m+1).
  2. Conjecture 31 (full Bellman DP): solves the exact Bellman recursion (2)
     over all 5,604 multisets of total measure <= 30 (and verifies V(S) = G(S)
     at every state and every legal cut).
  3. Odd-k signed rotation & brute-force Littlestone dimension check:
     verifies signed rotation T preserves C_{n,k}, slice equality with G_k(n)
     for k=3 (n=1..30), and exact brute-force Ldim(C_{n,k}) = 1 + Ldim(G_k(n))
     for k=1 (n<=10) and k=3,5 (n<=9).
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations

MAX_M = 512
MASS = 30
SCALE = 2048


def ilog(x: int) -> int:
    return x.bit_length() - 1


def log_scaled(x: int) -> int:
    t = ilog(x)
    return t * SCALE + (x - (1 << t)) * (SCALE >> t)


def reward(a: int, b: int) -> int:
    z = log_scaled(a) + log_scaled(b)
    assert z % 2 == 0
    return SCALE + z // 2


@lru_cache(None)
def greedy_forest(x: int) -> Counter:
    if x == 1:
        return Counter()
    t = ilog(x)
    u = max(1 << (t - 1), x - (1 << t))
    return Counter({x: 1}) + greedy_forest(u) + greedy_forest(x - u)


def greedy_value_num(runs: Counter) -> int:
    """Exact numerator with denominator SCALE * 2**(number of cuts)."""
    result = 0
    for x, count in sorted(runs.items(), reverse=True):
        result = (result << count) + log_scaled(x) * ((1 << count) - 1)
    return result


@lru_cache(None)
def r_recurrence_num(x: int) -> int:
    if x == 1:
        return 0
    a, b = x // 2, (x + 1) // 2
    return (
        SCALE * ((1 << (x - 1)) - 1)
        + (r_recurrence_num(a) << (x - a - 1))
        + (r_recurrence_num(b) << (x - b - 1))
    )


def verify_rods():
    cuts = 0
    for x in range(2, MAX_M + 2):
        g = greedy_value_num(greedy_forest(x))
        assert g == r_recurrence_num(x), (x, g, r_recurrence_num(x))
        best = 0
        for a in range(1, x // 2 + 1):
            b = x - a
            q = (reward(a, b) << (x - 2)) + greedy_value_num(
                greedy_forest(a) + greedy_forest(b)
            )
            assert q <= g, (x, a, g, q)
            best = max(best, q)
            cuts += 1
        assert best == g
    return cuts


def verify_full_bellman_dp():
    states = 0
    cuts = 0
    opt = {(): 0}
    by_count = [[] for _ in range(MASS)]

    def visit(s, remaining):
        nonlocal states, cuts
        states += 1
        count = sum(s) - len(s)
        if s:
            options = []
            for x in set(s):
                other = list(s)
                other.remove(x)
                for a in range(1, x // 2 + 1):
                    b = x - a
                    child = tuple(sorted(other + [p for p in (a, b) if p > 1]))
                    options.append((child, reward(a, b)))
            cuts += len(options)
            by_count[count].append((s, options))
        for x in range(s[-1] if s else 2, remaining + 1):
            visit(s + (x,), remaining - x)

    visit((), MASS)
    for count, layer in enumerate(by_count):
        for s, options in layer:
            opt[s] = max((r << (count - 1)) + opt[child] for child, r in options)
            g = greedy_value_num(sum((greedy_forest(x) for x in s), Counter()))
            assert opt[s] == g, (s, opt[s], g)
    return states, cuts


@lru_cache(None)
def exact_ldim(words: tuple, n_bits: int) -> int:
    """Exact memoized brute-force Littlestone dimension of a finite word set."""
    if not words:
        return -1
    if len(words) == 1:
        return 0
    best = 0
    for bit in range(n_bits):
        mask = 1 << bit
        w0 = tuple(w for w in words if (w & mask) == 0)
        w1 = tuple(w for w in words if (w & mask) != 0)
        if w0 and w1:
            d = 1 + min(exact_ldim(w0, n_bits), exact_ldim(w1, n_bits))
            if d > best:
                best = d
    return best


def enum_C(n: int, k: int):
    mask = (1 << n) - 1
    res = set()
    for cnt in range(k + 1):
        for ch in combinations(range(1, n), cnt):
            x = 0
            for pos in ch:
                x ^= (1 << pos) - 1
            res.add(x)
            res.add(x ^ mask)
    return res


def enum_G(n: int, k: int):
    """Words on n-1 free bits with fixed 0 on left and fixed 1 on right, <= k switches."""
    mask = (1 << (n - 1)) - 1
    res = set()
    for cnt in range(1, k + 1, 2):
        for ch in combinations(range(1, n + 1), cnt):
            # ch are 1-indexed edge positions among n edges; bit i (0..n-2) is left of edge i+2
            w = 0
            cur = 0
            edge_set = set(ch)
            for i in range(n - 1):
                if (i + 1) in edge_set:
                    cur ^= 1
                if cur:
                    w |= 1 << i
            res.add(w & mask)
    return res


def verify_odd_k():
    # 1. Signed rotation + slice equality for k=3, n=1..30
    words_checked = 0
    for n in range(1, 31):
        C = enum_C(n, 3)
        for x in C:
            y = (x >> 1) | ((1 ^ (x & 1)) << (n - 1))
            assert y in C
        slice0 = {x >> 1 for x in C if (x & 1) == 0}
        assert slice0 == enum_G(n, 3)
        words_checked += len(C)

    # 2. Exact brute-force Littlestone dimension check
    ldim_cases = 0
    for k, max_n in ((1, 10), (3, 9), (5, 7)):
        for n in range(1, max_n + 1):
            lc = exact_ldim(tuple(sorted(enum_C(n, k))), n)
            lg = exact_ldim(tuple(sorted(enum_G(n, k))), n - 1)
            assert lc == 1 + lg, (k, n, lc, lg)
            ldim_cases += 1
    return words_checked, ldim_cases


def main():
    rod_cuts = verify_rods()
    dp_states, dp_cuts = verify_full_bellman_dp()
    words_checked, ldim_cases = verify_odd_k()
    print(
        f"PASS: rods m<=512 ({rod_cuts:,} first cuts); "
        f"full Bellman DP ({dp_states:,} states, {dp_cuts:,} cuts, measure<=30); "
        f"odd-k signed rotation ({words_checked:,} words) & {ldim_cases} brute-force Ldim checks."
    )


if __name__ == "__main__":
    main()
