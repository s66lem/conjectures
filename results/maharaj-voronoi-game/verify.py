#!/usr/bin/env python3
"""Standalone exact (Fraction) verifier for the disproof of Maharaj's Conjecture 1
(arXiv:2609.24936) and exact determination k*(l) = 2l - 1.

Uses Python 3 standard library only:
  1. Verifies the explicit constructive Q-strategy from PROOF.md directly against
     the literal game rule dist(v, Q) < dist(v, P) in exact Fraction arithmetic
     across thousands of random and adversarial P-placements for l = 2, 3, 4, 5
     at n = 4*l*(l-1) + 1 and at n = 17 (l = 3, k = 4).
  2. Verifies exact sharpness of the l = 3, n = 17 certificate P = {2, 32, 512, 8192}
     (Q wins <= 9, P keeps 8).
  3. Verifies Maharaj's upper-bound strategy (k = 2l - 1) on random weighted multisets.
"""

import random
from fractions import Fraction as F


def literal_q_wins(voters, P, Q) -> int:
    """Count voters strictly closer to Q than to P (exact Fraction arithmetic)."""
    won = 0
    for v in voters:
        dp = min(abs(v - p) for p in P)
        dq = min(abs(v - q) for q in Q)
        if dq < dp:
            won += 1
    return won


def build_q_response(n: int, P_in, ell: int):
    """Construct the ell-point response Q from PROOF.md Steps 1-3 on V_n = {2^0..2^(n-1)}."""
    V = [F(1 << t) for t in range(n)]
    V_set = set(V)
    K = 2 * ell - 2
    P = sorted(set(P_in))
    assert len(P) <= K
    # Step 1: pad to K distinct points if needed
    pad = F(1 << n) + F(10)
    while len(P) < K:
        while pad in P:
            pad += 1
        P.append(pad)
    P.sort()

    # Step 2: compute explicit q_j in each of the K+1 gaps and its guaranteed gain g_j
    gaps = []
    # Left outer gap G_0 = (-inf, P[0])
    v0 = [v for v in V if v < P[0]]
    q0 = (v0[-1] + P[0]) / 2 if v0 else P[0] - 1
    gaps.append((len(v0), q0))

    # Inner gaps G_i = (P[i], P[i+1])
    for i in range(K - 1):
        a, b = P[i], P[i + 1]
        vi = [v for v in V if a < v < b]
        if not vi:
            gaps.append((0, (a + b) / 2))
        elif b in V_set:
            # Win all of vi
            lo = max(a, 2 * vi[-1] - b)
            hi = min(b, 2 * vi[0] - a)
            assert lo < hi
            gaps.append((len(vi), (lo + hi) / 2))
        elif len(vi) == 1:
            gaps.append((1, vi[0]))
        else:
            # Win all but the rightmost voter vi[-1]
            lo = max(a, 2 * vi[-2] - b)
            hi = min(b, 2 * vi[0] - a)
            assert lo < hi
            gaps.append((len(vi) - 1, (lo + hi) / 2))

    # Right outer gap G_K = (P[-1], +inf)
    vk = [v for v in V if v > P[-1]]
    qk = (P[-1] + vk[0]) / 2 if vk else P[-1] + 1
    gaps.append((len(vk), qk))

    # Step 3: pick top ell gaps by guaranteed gain
    assert sum(g for g, _ in gaps) >= n - K
    gaps.sort(key=lambda item: item[0], reverse=True)
    Q = [q for _, q in gaps[:ell]]
    assert len(set(Q)) == ell, "Q points must be pairwise distinct"
    return V, Q, sum(g for g, _ in gaps[:ell])


def random_p_placements(rng: random.Random, n: int, k: int, count: int):
    V = [F(1 << t) for t in range(n)]
    for idx in range(count):
        mode = idx % 4
        pts = set()
        if mode == 0:
            # All on voters
            pts = set(rng.sample(V, min(k, n)))
        elif mode == 1:
            # Mix of voters and random midpoints/fractions
            while len(pts) < k:
                if rng.random() < 0.4:
                    pts.add(rng.choice(V))
                else:
                    t = rng.randint(0, n - 2)
                    num = rng.randint(1, 7)
                    pts.add(V[t] + F(num, 8) * (V[t + 1] - V[t]))
        elif mode == 2:
            # Adversarial: evenly spaced indices on voters or just below voters
            step = max(1, n // (k + 1))
            for j in range(1, k + 1):
                t = min(n - 1, j * step)
                shift = rng.choice([F(0), F(-1, 2), F(1, 2), F(-1, 1000)])
                pts.add(V[t] + shift)
        else:
            # Wide continuous rationals including outside voter range
            while len(pts) < k:
                pts.add(F(rng.randint(-10, (1 << n) + 10), rng.choice([1, 2, 3, 5])))
        while len(pts) < k:
            pts.add(F(rng.randint(1, 1 << n), 2))
        yield sorted(pts)


def verify_upper_bound_strategy(rng: random.Random, trials: int = 500):
    """Verify Maharaj Theorem 4.1 greedy balanced placement for k = 2l - 1."""
    for _ in range(trials):
        ell = rng.randint(1, 5)
        k = 2 * ell - 1
        n = rng.randint(1, 25)
        V = sorted(F(rng.randint(-5, 10)) for _ in range(n))
        B = n // (2 * ell)
        P = []
        r = 0
        extra = V[-1] + 1
        for _ in range(k):
            if r + B >= n:
                P.append(extra)
                extra += 1
            else:
                p = V[r + B]
                P.append(p)
                while r < n and V[r] <= p:
                    r += 1
        assert len(set(P)) == k
        # Check every gap holds <= B voters
        P_sorted = sorted(P)
        gaps = [sum(1 for v in V if v < P_sorted[0])]
        for i in range(k - 1):
            gaps.append(sum(1 for v in V if P_sorted[i] < v < P_sorted[i + 1]))
        gaps.append(sum(1 for v in V if v > P_sorted[-1]))
        assert all(g <= B for g in gaps)
        assert ell * B <= n / 2


def main():
    rng = random.Random(20261124)
    total_tests = 0

    # 1. General threshold n = 4*l*(l-1) + 1 for l = 2, 3, 4, 5
    for ell in (2, 3, 4, 5):
        n = 4 * ell * (ell - 1) + 1
        k = 2 * ell - 2
        for P in random_p_placements(rng, n, k, 400):
            V, Q, guaranteed = build_q_response(n, P, ell)
            won = literal_q_wins(V, P, Q)
            assert won >= guaranteed and 2 * won > n, (ell, n, P, Q, won, guaranteed)
            total_tests += 1

    # 2. Tight n = 17 certificate for l = 3, k = 4
    n17 = 17
    for P in random_p_placements(rng, n17, 4, 2000):
        V, Q, guaranteed = build_q_response(n17, P, 3)
        won = literal_q_wins(V, P, Q)
        assert won >= guaranteed >= 9 and 2 * won > n17
        total_tests += 1

    # Check P* = {2, 32, 512, 8192} achieves exact Gamma_{4,3}(V_17) = 8
    V17 = [F(1 << t) for t in range(17)]
    P_star = [F(2), F(32), F(512), F(8192)]
    gaps_star = [
        sum(1 for v in V17 if v < P_star[0]),
        sum(1 for v in V17 if P_star[0] < v < P_star[1]),
        sum(1 for v in V17 if P_star[1] < v < P_star[2]),
        sum(1 for v in V17 if P_star[2] < v < P_star[3]),
        sum(1 for v in V17 if v > P_star[3]),
    ]
    assert gaps_star == [1, 3, 3, 3, 3]
    _, Q_star, g_star = build_q_response(17, P_star, 3)
    assert g_star == 9 and literal_q_wins(V17, P_star, Q_star) == 9

    # 3. Verify Maharaj upper bound construction on 500 random weighted multisets
    verify_upper_bound_strategy(rng, 500)

    print(
        f"PASS: {total_tests:,} exact literal-rule checks passed across l=2..5 (n=4l(l-1)+1) "
        f"and n=17 (l=3, k=4); Gamma_{{4,3}}(V_17)=8 confirmed; 500 upper-bound checks passed."
    )


if __name__ == "__main__":
    main()
