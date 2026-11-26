r"""Verify the disproof of Talmage's monotonicity conjecture (arXiv:2611.25115v1).

Stdlib only. Run: python -O -W error verify.py  (add --l4 to also recount length 4)
"""
import itertools
import sys
from collections import deque


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def moves(s, n):
    """All lists reachable from tuple s in one legal move with upper bound n."""
    st = set(s)
    out = set()
    for i in range(len(s) - 1):
        v = s[i] + s[i + 1]
        if v <= n and v not in st:
            out.add(s[:i] + (v,) + s[i + 2:])
    for i, x in enumerate(s):
        for a in range(1, x):
            b = x - a
            if a != b and a not in st and b not in st:
                out.add(s[:i] + (a, b) + s[i + 1:])
    return out


def legal_state(s, n):
    return len(set(s)) == len(s) and all(1 <= x <= n for x in s)


def component(L):
    n = max(L)
    seen = {L}
    dq = deque([L])
    while dq:
        s = dq.popleft()
        for t in moves(s, n):
            if t not in seen:
                seen.add(t)
                dq.append(t)
    return seen


def reversible(L):
    n, target = max(L), L[::-1]
    seen = {L}
    dq = deque([L])
    while dq:
        s = dq.popleft()
        if s == target:
            return True
        for t in moves(s, n):
            if t not in seen:
                seen.add(t)
                dq.append(t)
    return False


def check_closed(L, S):
    """Check S contains L, is closed under moves (bound max L), and omits reverse(L)."""
    n = max(L)
    require(L in S, f"{L} in its claimed component")
    for s in S:
        require(legal_state(s, n), f"{s} legal")
        require(sum(s) == sum(L), f"{s} preserves sum {sum(L)}")
        require(moves(s, n) <= S, f"moves of {s} stay in claimed closed set")
    require(L[::-1] not in S, f"reverse of {L} omitted from closed set")


def check_path(path):
    n = max(path[0])
    for a, b in zip(path, path[1:]):
        require(b in moves(a, n), f"{a} -> {b} is a legal move (bound {n})")
    require(path[-1] == path[0][::-1], "path ends at reverse")


def count_irreversible(length, nmax):
    tot = 0
    for n in range(length, nmax + 1):
        for rest in itertools.permutations(range(1, n), length - 1):
            for pos in range(length):
                L = rest[:pos] + (n,) + rest[pos:]
                if L[0] < L[-1] and not reversible(L):
                    tot += 1
    return tot


def main():
    # Paper's example reversal of (3, 5, 7)
    check_path([
        (3, 5, 7), (2, 1, 5, 7), (2, 1, 5, 4, 3), (2, 6, 4, 3),
        (2, 5, 1, 4, 3), (7, 1, 4, 3), (7, 5, 3),
    ])

    # Reproduce paper's Appendix A counts (11 for length 2, 51 for length 3)
    require(count_irreversible(2, 13) == 11, "11 irreversible length-2 lists (n <= 13)")
    require(count_irreversible(3, 9) == 51, "51 irreversible length-3 lists (n <= 9)")
    if "--l4" in sys.argv:
        require(count_irreversible(4, 10) == 307, "307 irreversible length-4 lists (n <= 10)")

    # Counterexample 1 (as stated): (2, 6) irreversible, (2, 7) reversible
    c26 = {(2, 6), (2, 1, 5), (2, 5, 1), (3, 5), (1, 2, 5), (3, 1, 4), (3, 4, 1)}
    check_closed((2, 6), c26)
    require(component((2, 6)) == c26, "reachable component of (2, 6) has exactly 7 states")
    check_path([(2, 7), (2, 1, 6), (3, 6), (3, 4, 2), (7, 2)])

    # Counterexample 2 (converse): (1, 3, 7, 4) reversible, (1, 3, 8, 4) irreversible
    c1384 = {(1, 3, 8, 4), (1, 3, 2, 6, 4), (1, 3, 6, 2, 4), (1, 5, 6, 4), (1, 2, 3, 6, 4)}
    check_closed((1, 3, 8, 4), c1384)
    require(component((1, 3, 8, 4)) == c1384, "reachable component of (1, 3, 8, 4) has exactly 5 states")
    check_path([
        (1, 3, 7, 4), (1, 3, 5, 2, 4), (1, 3, 5, 6), (4, 5, 6),
        (3, 1, 5, 6), (3, 1, 5, 2, 4), (3, 6, 2, 4), (3, 5, 1, 2, 4),
        (3, 5, 1, 6), (3, 5, 7), (1, 2, 5, 7), (1, 2, 5, 3, 4),
        (1, 7, 3, 4), (1, 5, 2, 3, 4), (6, 2, 3, 4), (6, 5, 4),
        (6, 5, 3, 1), (4, 2, 5, 3, 1), (4, 7, 3, 1),
    ])

    print("ALL CHECKS PASSED: (2,6) irreversible & (2,7) reversible; (1,3,7,4) reversible & (1,3,8,4) irreversible.")


if __name__ == "__main__":
    main()
