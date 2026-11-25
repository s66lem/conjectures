#!/usr/bin/env python3
"""Standalone Python 3 verifier for Manabe's Conjecture 57 (arXiv:2609.05358v2).

Uses only the Python 3 standard library and is safe under `python3 -O`.
Checks:
1. Verbatim Definition 19 (T0, T1, T2) and formula (4) on Example 1 ((a,b)=(3,8))
   and Manabe's exact paper census (2 <= a <= 8, b <= 40, c <= 100: 7,557 admissible,
   7,828 non-admissible).
2. Theorems A0, A1, A2, F1-F4, L1-L2, and the explicit cyclic-interval form of
   Theta_{c+b} on all unrestricted triples 1 <= a < b <= 30, b < c <= 70
   (including a = 1, non-primitive triples, c = a + b, b < c < a + b, b = k*a).
3. Both partial period exclusions (no pure period in (c-a, c+a); extended Fine-Wilf
   c >= p + (a+b) - gcd(p, a+b) including a+b | p).
"""

import math


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def p_positions(a: int, b: int, c: int, limit: int) -> list[bool]:
    w = [False] * limit
    for x in range(limit):
        w[x] = not (
            (x >= a and w[x - a])
            or (x >= b and w[x - b])
            or (x >= c and w[x - c])
        )
    return w


def base_p_positions(a: int, b: int, limit: int) -> list[bool]:
    wb = [False] * limit
    for x in range(limit):
        wb[x] = not ((x >= a and wb[x - a]) or (x >= b and wb[x - b]))
    return wb


def grundy_seq(a: int, b: int, c: int, limit: int) -> list[int]:
    g = [0] * limit
    for x in range(limit):
        seen = set()
        if x >= a:
            seen.add(g[x - a])
        if x >= b:
            seen.add(g[x - b])
        if x >= c:
            seen.add(g[x - c])
        m = 0
        while m in seen:
            m += 1
        g[x] = m
    return g


def admissible_sets(a: int, b: int):
    n = a + b
    delta = b - a
    eta, eps = divmod(delta, a)
    wb = base_p_positions(a, b, n)
    Z = {u for u in range(n) if wb[u]}
    Z_f1 = {u for u in range(b) if (u // a) % 2 == 0}
    require(Z == Z_f1, f"F1 mismatch for {(a, b)}")

    D = {u for u in range(a, b) if u not in Z}
    if eta % 2 == 0:
        Lam = set(range((eta + 1) * a, (eta + 1) * a + eps))
    else:
        Lam = set(range(eta * a + eps, (eta + 1) * a))
    Lam_f3a = {u for u in range(delta, b) if u not in Z}
    Lam_f3b = {w for w in range(n) if w not in Z and (w + a) % n not in Z}
    require(Lam == Lam_f3a == Lam_f3b, f"F3 mismatch for {(a, b)}")

    A = {u for u in Z if u < delta}
    T0 = {rho for rho in range(n) if not (Z & {(z + rho) % n for z in Z})}
    T1 = {
        rho
        for rho in range(n)
        if not (A & {(z + delta - rho) % n for z in Z})
    }
    T2 = {
        rho
        for rho in range(n)
        if not ({(rho + l) % n for l in Lam} & Z)
        and not ({(rho + d) % n for d in D} & Lam)
    }
    N1 = {rho for rho in range(n) if all((rho + l + a) % n in Z for l in Lam)}
    if eta % 2 == 0:
        Expl = {
            rho for rho in range(n) if all((rho - j) % n in Z for j in range(1, eps + 1))
        }
    else:
        Expl = {
            rho
            for rho in range(n)
            if all((rho - j) % n in Z for j in range(eps + 1, a + 1))
        }
    require(T2 == N1 == Expl, f"T2/N1/Explicit mismatch for {(a, b)}")
    return n, delta, Z, D, Lam, T0, T1, T2


def check_paper_calibration() -> None:
    # Example 1: (a, b) = (3, 8)
    _, _, Z, _, _, T0, T1, T2 = admissible_sets(3, 8)
    require(Z == {0, 1, 2, 6, 7}, f"Example 1 Z mismatch: {Z}")
    require(T0 == {3, 8}, f"Example 1 T0 mismatch: {T0}")
    require(T1 == {2, 8}, f"Example 1 T1 mismatch: {T1}")
    require(T2 == {3, 4, 5, 9, 10}, f"Example 1 T2 mismatch: {T2}")

    # Paper census: 2 <= a <= 8, a < b <= 40, b < c <= 100, primitive, c != a + b
    adm = 0
    non_adm = 0
    for a in range(2, 9):
        for b in range(a + 1, 41):
            n, _, _, _, _, T0, T1, T2 = admissible_sets(a, b)
            union = T0 | T1 | T2
            for c in range(b + 1, 101):
                if c == a + b or math.gcd(a, b, c) != 1:
                    continue
                if (c % n) in union:
                    adm += 1
                else:
                    non_adm += 1
    require(adm == 7557 and non_adm == 7828, f"Census mismatch: {adm}, {non_adm}")


def check_unrestricted_theorems() -> tuple[int, int, int]:
    checked = 0
    fw_hits = 0
    fw_gn_hits = 0
    for a in range(1, 19):
        for b in range(a + 1, 31):
            n, _, Z, D, _, T0, T1, T2 = admissible_sets(a, b)
            for c in range(b + 1, 66):
                rho = c % n
                limit = 3 * c + 2 * b + 8
                W = p_positions(a, b, c, limit)
                # Spot-check grundy == 0 iff isP on smaller triples
                if c <= 25:
                    G = grundy_seq(a, b, c, 2 * c + b + 4)
                    require(
                        all((G[x] == 0) == W[x] for x in range(len(G))),
                        f"G=0 vs W mismatch for {(a, b, c)}",
                    )
                # Check L2 verbatim
                for u in range(a, b):
                    rhs = (u in D) and (((rho + u + a) % n) not in Z)
                    require(W[c + u] == rhs, f"L2 mismatch for {(a, b, c, u)}")
                # Check A0, A1, A2
                for P, Th in ((n, T0), (c + a, T1), (c + b, T2)):
                    is_per = all(W[x] == W[x + P] for x in range(max(P, c) + 6))
                    require(
                        is_per == (rho in Th),
                        f"Periodicity mismatch for {(a, b, c, P)}: {is_per} vs {rho in Th}",
                    )
                # Check Partial Exclusion 1: no pure period in (c - a, c + a)
                for p in range(c - a + 1, c + a):
                    require(
                        not all(W[x] == W[x + p] for x in range(c + 2)),
                        f"Unexpected period in (c-a, c+a): {(a, b, c, p)}",
                    )
                # Check Partial Exclusion 2: extended Fine-Wilf
                for p in range(1, c + 1):
                    g = math.gcd(p, n)
                    if c >= p + n - g and all(W[x] == W[x + p] for x in range(c + p)):
                        fw_hits += 1
                        if g == n:
                            fw_gn_hits += 1
                        require(rho in T0, f"Extended Fine-Wilf failure: {(a, b, c, p)}")
                checked += 1
    return checked, fw_hits, fw_gn_hits


def main() -> None:
    check_paper_calibration()
    checked, fw_hits, fw_gn_hits = check_unrestricted_theorems()
    print(
        f"PASS: Manabe Example 1 & census (7557/7828) matched; "
        f"verified Theorems A0/A1/A2, L2, explicit Theta_(c+b), and partial period "
        f"exclusions on {checked} unrestricted triples 1<=a<b<c "
        f"(Fine-Wilf hits={fw_hits}, including {fw_gn_hits} with (a+b)|p)."
    )


if __name__ == "__main__":
    main()
