#!/usr/bin/env python3
"""Standalone exact (Fraction) verifier for the Rank Score Veto Core Distortion theorem
(arXiv:2610.26535, M. August Rossi).

Uses Python 3 standard library only:
  1. Verifies per-voter inequalities (4A) and (4B) over all m! rankings on 4,000
     random (s, rho) draws with m <= 6, including boundary/tied values.
  2. Verifies every intermediate inequality (Steps 1-5) and the main theorem
     SC(a) <= (1 + 2T) SC(b) on random L1 metric elections (exact blocking core).
  3. Verifies exhaustive two-site edge cases including SC(b) = 0 and d(a, b) = 0.
  4. Verifies exact sharpness on Rossi's Lemma 5 construction (rational s).
"""

import itertools
import random
from fractions import Fraction as F


def rand_scoring_vector(rng: random.Random, m: int):
    tail = sorted((F(rng.randint(0, 12), 12) for _ in range(m - 1)), reverse=True)
    return (F(1),) + tuple(tail)


def max_inversion_drop(pi, rho):
    return max(
        rho[pi[i]] - rho[pi[j]]
        for i in range(len(pi))
        for j in range(i, len(pi))
    )


def check_per_voter_lemmas(rng: random.Random, trials: int = 4000):
    checked = 0
    for _ in range(trials):
        m = rng.randint(2, 6)
        s = rand_scoring_vector(rng, m)
        S = sum(s)
        T = S - s[-1]
        a, b = 0, 1
        pool = [F(0), F(1), F(1, 2)] + [F(rng.randint(0, 24), 24) for _ in range(3)]
        rho = [rng.choice(pool) for _ in range(m)]
        rho[a] = F(1)
        rho[b] = F(0)
        for pi in itertools.permutations(range(m)):
            W = sum(s[pos] * rho[c] for pos, c in enumerate(pi))
            M = max_inversion_drop(pi, rho)
            pos_a = pi.index(a)
            pos_b = pi.index(b)
            if pos_a < pos_b:
                assert W <= T * M, ("Lemma (4A) failed", s, pi, rho)
            else:
                mu = min(rho[c] for c in pi[pos_a:])
                assert W - (S - 1) * mu <= T * M, ("Lemma (4B) failed", s, pi, rho)
            checked += 1
    return checked


def veto_core(profile, m: int, s):
    n = len(profile)
    S = sum(s)
    q = [sum(s[pi.index(c)] for pi in profile) / (n * S) for c in range(m)]
    core = []
    for a in range(m):
        blocked = False
        others = [c for c in range(m) if c != a]
        for k in range(1, len(others) + 1):
            for D in itertools.combinations(others, k):
                pS = F(
                    sum(1 for pi in profile if all(pi.index(d) < pi.index(a) for d in D)),
                    n,
                )
                if pS > 1 - sum(q[d] for d in D):
                    blocked = True
                    break
            if blocked:
                break
        if not blocked:
            core.append(a)
    return core


def verify_election_steps(profile, dv, dcc, m: int, s):
    n = len(profile)
    S = sum(s)
    T = S - s[-1]
    checked = 0
    zero_opt = 0
    worst_ratio = F(0)
    for a in veto_core(profile, m, s):
        SCa = sum(dv[i][a] for i in range(n))
        for b in range(m):
            SCb = sum(dv[i][b] for i in range(n))
            delta = dcc[a][b]
            if delta == 0:
                assert SCa == SCb
            else:
                rho = [min(dcc[b][c], delta) for c in range(m)]
                B = [i for i in range(n) if profile[i].index(b) < profile[i].index(a)]
                mu = {i: min(rho[c] for c in profile[i][profile[i].index(a):]) for i in range(n)}
                Mu = [max_inversion_drop(profile[i], rho) for i in range(n)]
                Wu = [sum(s[pos] * rho[c] for pos, c in enumerate(profile[i])) for i in range(n)]
                assert SCa <= SCb + sum(mu[i] for i in B)
                assert all(Mu[i] <= 2 * dv[i][b] for i in range(n))
                assert S * sum(mu[i] for i in B) <= sum(Wu)
                assert sum(mu[i] for i in B) <= T * sum(Mu)
            assert SCa <= (1 + 2 * T) * SCb
            if SCb == 0:
                assert SCa == 0
                zero_opt += 1
            else:
                worst_ratio = max(worst_ratio, (SCa / SCb) / (1 + 2 * T))
            checked += 1
    return checked, zero_opt, worst_ratio


def check_random_elections(rng: random.Random, trials: int = 3000):
    total_pairs = 0
    zero_opt_total = 0
    worst = F(0)
    for _ in range(trials):
        m = rng.randint(2, 5)
        n = rng.randint(1, 9)
        s = rand_scoring_vector(rng, m)
        R = rng.choice([2, 6, 20])
        cand = [(rng.randint(-R, R), rng.randint(-R, R)) for _ in range(m)]
        vote = [(rng.randint(-R, R), rng.randint(-R, R)) for _ in range(n)]
        l1 = lambda p, q: abs(p[0] - q[0]) + abs(p[1] - q[1])
        dv = [[F(l1(v, c)) for c in cand] for v in vote]
        dcc = [[F(l1(c1, c2)) for c2 in cand] for c1 in cand]
        profile = [
            tuple(sorted(range(m), key=lambda c: (dv[i][c], rng.random())))
            for i in range(n)
        ]
        c_cnt, z_cnt, w = verify_election_steps(profile, dv, dcc, m, s)
        total_pairs += c_cnt
        zero_opt_total += z_cnt
        worst = max(worst, w)
    return total_pairs, zero_opt_total, worst


def check_zero_cost_edge_cases():
    """Verify co-located / zero-optimum elections with arbitrary tie-breaking."""
    rng = random.Random(7)
    pairs = 0
    zero_opt = 0
    for m in (2, 3, 4):
        scoring_vecs = [
            (F(1),) + (F(0),) * (m - 1),
            (F(1),) * m,
            tuple(F(m - j, m) for j in range(m)),
            tuple(F(1, j + 1) for j in range(m)),
        ]
        for s in scoring_vecs:
            for _ in range(40):
                n = rng.randint(1, 6)
                cand_x = [rng.choice([0, 1]) for _ in range(m)]
                vote_x = [0] * n
                dv = [[F(abs(v - c)) for c in cand_x] for v in vote_x]
                dcc = [[F(abs(c1 - c2)) for c2 in cand_x] for c1 in cand_x]
                profile = [
                    tuple(sorted(range(m), key=lambda c: (dv[i][c], rng.random())))
                    for i in range(n)
                ]
                c_cnt, z_cnt, _ = verify_election_steps(profile, dv, dcc, m, s)
                pairs += c_cnt
                zero_opt += z_cnt
    return pairs, zero_opt


def check_lemma5_sharpness(s, n1: int):
    m = len(s)
    T = sum(s) - s[-1]
    n2_frac = T * n1
    assert n2_frac.denominator == 1
    n2 = int(n2_frac)
    profile = [tuple(range(1, m)) + (0,)] * n1 + [(0,) + tuple(range(1, m))] * n2
    assert 1 in veto_core(profile, m, s), "b_1 must lie in the veto core"
    SC_b1 = F(n1 + 2 * n2)
    SC_opt = F(n1)
    assert SC_b1 / SC_opt == 1 + 2 * T
    return SC_b1 / SC_opt


def main():
    rng = random.Random(20261124)
    voter_checks = check_per_voter_lemmas(rng, trials=4000)
    elec_pairs, z1, worst = check_random_elections(rng, trials=3000)
    edge_pairs, z2 = check_zero_cost_edge_cases()
    d_harm = check_lemma5_sharpness((F(1), F(1, 2), F(1, 3), F(1, 4)), 12)
    d_borda = check_lemma5_sharpness((F(1), F(3, 4), F(1, 2), F(1, 4)), 4)
    d_prop = check_lemma5_sharpness((F(1), F(1), F(1), F(1)), 1)
    assert d_harm == F(14, 3) and d_borda == F(11, 2) and d_prop == F(7)

    print(
        f"PASS: {voter_checks:,} per-voter lemma checks; "
        f"{elec_pairs + edge_pairs:,} exact election pairs ({z1 + z2:,} with SC(b)=0); "
        f"max random ratio/(1+2T)={float(worst):.4f}; "
        f"Lemma 5 sharpness verified (harmonic={d_harm}, Borda+={d_borda}, prop={d_prop})."
    )


if __name__ == "__main__":
    main()
