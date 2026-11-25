"""Standalone stdlib-only (-O-safe) verifier for the disproof of Conjecture 1
of Capozzoli, Couto, and Junchaya (arXiv:2609.22640v1) under ETH.

Verifies:
1. Structural Lemmas A, B, C, D, and E across 14 diverse tournament families.
2. Strong connectivity of Theorem 4.1 constructions.
3. Exact equivalence between the recursive band-splitting solver Solve(T, D, F, k)
   and an independent exact branch-and-bound solver on YES and NO instances
   (strong, non-strong, and constrained F != empty subproblems, with active
   recursive band-splitting splits >= 1 on both YES and NO runs).
"""

import itertools
import math
import random
import time
from collections import deque


def require(cond, msg=""):
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILED: {msg}")


def make_prop1_tournament(num_blocks):
    n = 4 * num_blocks
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            adj[i][j] = 1
    for b in range(num_blocks):
        u1, u4 = 4 * b, 4 * b + 3
        adj[u1][u4] = 0
        adj[u4][u1] = 1
    for b in range(num_blocks - 1):
        u4_prev, u1_next = 4 * b + 3, 4 * (b + 1)
        adj[u4_prev][u1_next] = 0
        adj[u1_next][u4_prev] = 1
    return adj


def make_random_tournament(n, rng):
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < 0.5:
                adj[i][j] = 1
            else:
                adj[j][i] = 1
    return adj


def make_perturbed_transitive(n, flip_prob, max_span, rng):
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if (j - i) <= max_span and rng.random() < flip_prob:
                adj[j][i] = 1
            else:
                adj[i][j] = 1
    return adj


def make_layered_chain(num_layers, layer_size, back_prob, rng):
    n = num_layers * layer_size
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        li = i // layer_size
        for j in range(i + 1, n):
            lj = j // layer_size
            if li == lj:
                if rng.random() < 0.5:
                    adj[i][j] = 1
                else:
                    adj[j][i] = 1
            elif lj == li + 1:
                if rng.random() < back_prob:
                    adj[j][i] = 1
                else:
                    adj[i][j] = 1
            else:
                adj[i][j] = 1
    return adj


def make_block_regular_chain(num_blocks, block_size):
    require(block_size % 2 == 1, "block_size must be odd")
    half = block_size // 2
    n = num_blocks * block_size
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        bi, oi = divmod(i, block_size)
        for j in range(i + 1, n):
            bj, oj = divmod(j, block_size)
            if bi == bj:
                if (oj - oi) % block_size <= half:
                    adj[i][j] = 1
                else:
                    adj[j][i] = 1
            else:
                adj[i][j] = 1
    return adj


def make_theorem41_tournament(base_adj):
    m = len(base_adj)
    n = 2 * m + 3
    adj = [[0] * n for _ in range(n)]
    x, y, z = 2 * m, 2 * m + 1, 2 * m + 2
    adj[x][y] = adj[y][z] = adj[z][x] = 1
    for u in range(m):
        for v in range(m):
            if base_adj[u][v]:
                adj[u][v] = 1
                adj[m + u][m + v] = 1
                adj[u][m + v] = 1
                adj[m + u][v] = 1
        adj[u][m + u] = 1
        adj[x][u] = 1
        adj[u][y] = 1
        adj[u][z] = 1
        adj[m + u][x] = 1
        adj[m + u][y] = 1
        adj[m + u][z] = 1
    return adj


def make_strong_short_span(n, rng, extra_span2_prob=0.0):
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            adj[i][j] = 1
    for i in range(n - 1):
        adj[i][i + 1] = 0
        adj[i + 1][i] = 1
    for i in range(n - 2):
        if extra_span2_prob > 0 and rng.random() < extra_span2_prob:
            adj[i][i + 2] = 0
            adj[i + 2][i] = 1
    return adj


def verify_tournament(adj):
    n = len(adj)
    for i in range(n):
        require(adj[i][i] == 0, f"self-loop at {i}")
        for j in range(i + 1, n):
            require(adj[i][j] + adj[j][i] == 1, f"invalid tournament pair ({i},{j})")


def is_strongly_connected(adj):
    n = len(adj)
    if n <= 1:
        return True
    for rev in (False, True):
        seen = {0}
        q = deque([0])
        while q:
            u = q.popleft()
            for v in range(n):
                if (adj[v][u] if rev else adj[u][v]) and v not in seen:
                    seen.add(v)
                    q.append(v)
        if len(seen) != n:
            return False
    return True


def precompute_masks(adj):
    n = len(adj)
    out_m = [0] * n
    in_m = [0] * n
    for u in range(n):
        om = 0
        im = 0
        for v in range(n):
            if adj[u][v]:
                om |= (1 << v)
            if adj[v][u]:
                im |= (1 << v)
        out_m[u] = om
        in_m[u] = im

    pair_cov = [[0] * n for _ in range(n)]
    covering_pairs = [[] for _ in range(n)]
    for u in range(n):
        for v in range(u + 1, n):
            cov = (out_m[v] & in_m[u]) if adj[u][v] else (out_m[u] & in_m[v])
            pair_cov[u][v] = cov
            pair_cov[v][u] = cov
            mm = cov
            while mm:
                lsb = mm & -mm
                w = lsb.bit_length() - 1
                covering_pairs[w].append((u, v))
                mm ^= lsb
    return out_m, in_m, pair_cov, covering_pairs


def interval_of_mask(S_mask, pair_cov):
    cov = S_mask
    verts = []
    mm = S_mask
    while mm:
        lsb = mm & -mm
        verts.append(lsb.bit_length() - 1)
        mm ^= lsb
    for i in range(len(verts)):
        u = verts[i]
        for j in range(i + 1, len(verts)):
            cov |= pair_cov[u][verts[j]]
    return cov


def greedy_and_bands(adj, out_m, in_m, pair_cov, D_mask, F_mask, r):
    n = len(adj)
    F_cov = interval_of_mask(F_mask, pair_cov)
    U_mask = D_mask & ~F_cov
    S_greedy = 0
    steps = 0

    while U_mask:
        u_size = U_mask.bit_count()
        best_cov = 0
        best_pair = None
        for w in range(n):
            for u in range(n):
                if adj[w][u]:
                    cov_u = (pair_cov[u][w] & U_mask).bit_count()
                    if cov_u > best_cov:
                        best_cov = cov_u
                        best_pair = (u, w)
        if best_cov * r < u_size:
            break
        u, w = best_pair
        S_greedy |= (1 << u) | (1 << w)
        U_mask &= ~((1 << u) | (1 << w) | pair_cov[u][w])
        steps += 1

    u_size = U_mask.bit_count()
    if u_size == 0:
        return S_greedy, U_mask, None, None, steps

    f_val = [(out_m[x] & U_mask).bit_count() for x in range(n)]
    band_of = [0] * n
    bands = [[] for _ in range(r + 1)]
    for x in range(n):
        fx = f_val[x]
        assigned = False
        for i in range(1, r):
            if (r - i) * u_size < fx * r <= (r - i + 1) * u_size:
                band_of[x] = i
                bands[i].append(x)
                assigned = True
                break
        if not assigned:
            require(fx * r <= u_size, "band assignment overflow")
            band_of[x] = r
            bands[r].append(x)

    return S_greedy, U_mask, f_val, (band_of, bands), steps


def test_lemmas_on_tournament(name, adj, r_list):
    verify_tournament(adj)
    n = len(adj)
    out_m, in_m, pair_cov, covering_pairs = precompute_masks(adj)
    full = (1 << n) - 1
    ell = n.bit_length()
    max_observed_gap = 0

    for r in r_list:
        S_g, U_m, f_val, band_info, steps = greedy_and_bands(adj, out_m, in_m, pair_cov, full, 0, r)
        u_size = U_m.bit_count()
        require(steps <= r * ell, f"Too many greedy steps {steps} > {r * ell}")
        if u_size == 0:
            continue

        band_of, bands = band_info

        # Lemma A
        for w in range(n):
            for u in range(n):
                if adj[w][u]:
                    require((f_val[u] - f_val[w]) * r < u_size, f"Lemma A failed on {name}")

        # Lemma B
        for x in range(n):
            for y in range(n):
                if band_of[y] >= band_of[x] + 2:
                    require(adj[x][y] == 1, f"Lemma B failed on {name}")

        # Lemma E
        for v in range(n):
            bv = band_of[v]
            for u, w in covering_pairs[v]:
                require(abs(band_of[u] - bv) <= 2 and abs(band_of[w] - bv) <= 2, f"Lemma E failed on {name}")

        # Lemma C
        if r >= 6:
            t = r // 2 - 1
            L_set = {x for x in range(n) if band_of[x] < t}
            B12 = {x for x in range(n) if band_of[x] in (t, t + 1)}
            B34 = {x for x in range(n) if band_of[x] in (t + 2, t + 3)}
            R_set = {x for x in range(n) if band_of[x] >= t + 4}
            for a in L_set | B12:
                for c in R_set:
                    require(adj[a][c] == 1 and (out_m[c] & in_m[a]) == 0, f"Lemma C(1) failed on {name}")
            for a in L_set:
                for c in B34 | R_set:
                    require(adj[a][c] == 1 and (out_m[c] & in_m[a]) == 0, f"Lemma C(2) failed on {name}")

        # Lemma D
        if 2 * u_size > r:
            non_empty = [i for i in range(1, r + 1) if any((U_m & (1 << x)) for x in bands[i])]
            require(len(non_empty) >= 1, f"empty U bands on {name}")
            left_gap = non_empty[0] - 1
            right_gap = r - non_empty[-1]
            max_mid_gap = max(
                (non_empty[idx + 1] - non_empty[idx] - 1 for idx in range(len(non_empty) - 1)),
                default=0,
            )
            max_observed_gap = max(max_observed_gap, max_mid_gap)
            require(left_gap <= 1, f"Left gap {left_gap} on {name}")
            require(right_gap <= 1, f"Right gap {right_gap} on {name}")
            require(max_mid_gap <= 3, f"Mid gap {max_mid_gap} on {name}")

    return max_observed_gap


def exact_bnb(n, pair_cov, covering_pairs, D_mask, F_mask, max_k):
    F_list = [v for v in range(n) if F_mask & (1 << v)]
    init_cov = interval_of_mask(F_mask, pair_cov)

    def add_verts(S_list, S_mask, cov_mask, to_add):
        nS = list(S_list)
        nSm = S_mask
        nCov = cov_mask
        for x in to_add:
            if not (nSm & (1 << x)):
                for prev in nS:
                    nCov |= pair_cov[prev][x]
                for fv in F_list:
                    nCov |= pair_cov[fv][x]
                nS.append(x)
                nSm |= (1 << x)
                nCov |= (1 << x)
        return nS, nSm, nCov

    def dfs(S_list, S_mask, cov_mask):
        uncov = D_mask & ~cov_mask
        if uncov == 0:
            return S_list
        rem = max_k - len(S_list)
        if rem <= 0:
            return None
        best_branches = None
        m = uncov
        while m:
            lsb = m & -m
            w = lsb.bit_length() - 1
            m ^= lsb
            branches = [(w,)]
            for u, v in covering_pairs[w]:
                need_u = 0 if ((S_mask | F_mask) & (1 << u)) else 1
                need_v = 0 if ((S_mask | F_mask) & (1 << v)) else 1
                if need_u + need_v <= rem:
                    to_add = tuple(x for x in (u, v) if not ((S_mask | F_mask) & (1 << x)))
                    if to_add:
                        branches.append(to_add)
            if best_branches is None or len(branches) < len(best_branches):
                best_branches = branches
                if len(best_branches) == 1:
                    break
        best_branches.sort(key=len)
        seen = set()
        for to_add in best_branches:
            if to_add in seen:
                continue
            seen.add(to_add)
            nS, nSm, nCov = add_verts(S_list, S_mask, cov_mask, to_add)
            res = dfs(nS, nSm, nCov)
            if res is not None:
                return res
        return None

    return dfs([], 0, init_cov)


def solve_band_split(adj, out_m, in_m, pair_cov, covering_pairs, D_mask, F_mask, k, stats, base_k=6, r_param=10):
    """Exact small-scale instantiation of the recursive band-splitting algorithm."""
    n = len(adj)
    if k >= n:
        return (1 << n) - 1
    F_cov = interval_of_mask(F_mask, pair_cov)
    if (D_mask & ~F_cov) == 0:
        return 0
    if k <= base_k:
        res = exact_bnb(n, pair_cov, covering_pairs, D_mask, F_mask, k)
        if res is None:
            return None
        mask = 0
        for x in res:
            mask |= (1 << x)
        return mask

    r = r_param
    S_g, U_m, f_val, band_info, _ = greedy_and_bands(adj, out_m, in_m, pair_cov, D_mask, F_mask, r)
    if (S_g | U_m).bit_count() <= k:
        cand = S_g | U_m
        require((D_mask & ~interval_of_mask(cand | F_mask, pair_cov)) == 0, "early YES invalid")
        stats["early_yes"] += 1
        return cand

    u_size = U_m.bit_count()
    if u_size <= r:
        res = exact_bnb(n, pair_cov, covering_pairs, D_mask, F_mask, k)
        if res is None:
            return None
        mask = 0
        for x in res:
            mask |= (1 << x)
        return mask

    stats["splits"] += 1
    band_of, _ = band_info
    windows = list(range(2, r - 3, 4))
    if not windows:
        windows = [2]
    s_max = k // len(windows)
    memo = stats.setdefault("memo", {})

    def rec(dm, fm, kk):
        key = (dm, fm, kk)
        if key in memo:
            return memo[key]
        ans = solve_band_split(adj, out_m, in_m, pair_cov, covering_pairs, dm, fm, kk, stats, base_k, r_param)
        memo[key] = ans
        return ans

    for t in windows:
        W_verts = [x for x in range(n) if band_of[x] in (t, t + 1, t + 2, t + 3)]
        D_L = 0
        D_R = 0
        for x in range(n):
            if D_mask & (1 << x):
                if band_of[x] <= t + 1:
                    D_L |= (1 << x)
                else:
                    D_R |= (1 << x)
        require((D_L | D_R) == D_mask and (D_L & D_R) == 0, "D_L/D_R partition failed")

        for sz in range(0, min(s_max, len(W_verts)) + 1):
            for comb in itertools.combinations(W_verts, sz):
                SW_mask = 0
                for x in comb:
                    SW_mask |= (1 << x)
                rem_k = k - sz
                for k_L in range(0, rem_k + 1):
                    k_R = rem_k - k_L
                    if k_L == k or k_R == k:
                        continue
                    res_L = rec(D_L, F_mask | SW_mask, k_L)
                    if res_L is None:
                        continue
                    res_R = rec(D_R, F_mask | SW_mask, k_R)
                    if res_R is not None:
                        sol = res_L | SW_mask | res_R
                        require(sol.bit_count() <= k, "solution exceeded k")
                        require((D_mask & ~interval_of_mask(sol | F_mask, pair_cov)) == 0, "solution incomplete")
                        return sol
    return None


def main():
    t0 = time.time()
    rng = random.Random(42)

    lemma_tests = [
        ("Prop1(k=8, n=32)", make_prop1_tournament(8), [4, 6, 8, 12]),
        ("Prop1(k=15, n=60)", make_prop1_tournament(15), [6, 10, 15, 20]),
        ("Random(n=40)", make_random_tournament(40, rng), [4, 8, 12]),
        ("Random(n=60)", make_random_tournament(60, rng), [4, 8, 16]),
        ("PerturbedTrans(n=50, p=0.3, span=5)", make_perturbed_transitive(50, 0.3, 5, rng), [6, 10, 15]),
        ("PerturbedTrans(n=60, p=0.2, span=8)", make_perturbed_transitive(60, 0.2, 8, rng), [6, 10, 14]),
        ("PerturbedTrans(n=60, p=0.05, span=60)", make_perturbed_transitive(60, 0.05, 60, rng), [6, 10]),
        ("StrongShortSpan(n=40, p2=0.2)", make_strong_short_span(40, rng, 0.2), [6, 10, 14]),
        ("LayeredChain(10x6, back=0.4)", make_layered_chain(10, 6, 0.4, rng), [6, 10, 14]),
        ("LayeredChain(12x5, back=0.2)", make_layered_chain(12, 5, 0.2, rng), [6, 10, 15]),
        ("BlockRegular(8x7, n=56)", make_block_regular_chain(8, 7), [6, 10, 16]),
        ("BlockRegular(10x5, n=50)", make_block_regular_chain(10, 5), [6, 10, 15]),
        ("Theorem41(Random n=20 -> 43)", make_theorem41_tournament(make_random_tournament(20, rng)), [4, 8]),
        ("Theorem41(Prop1(5) -> 43)", make_theorem41_tournament(make_prop1_tournament(5)), [6, 10]),
    ]
    for name, adj, r_list in lemma_tests:
        test_lemmas_on_tournament(name, adj, r_list)
        if name.startswith("Theorem41") or name.startswith("StrongShortSpan"):
            require(is_strongly_connected(adj), f"Expected strong tournament: {name}")

    solver_tests = [
        ("StrongShortSpan(n=21)", make_strong_short_span(21, random.Random(101), 0.0), 7, 10),
        ("StrongShortSpan(n=23)", make_strong_short_span(23, random.Random(202), 0.0), 8, 10),
        ("PerturbedTrans(n=21)", make_perturbed_transitive(21, 0.4, 1, random.Random(303)), 8, 10),
        ("PerturbedTrans(n=23)", make_perturbed_transitive(23, 0.6, 1, random.Random(404)), 8, 10),
    ]
    for name, adj, base_k, r_param in solver_tests:
        n = len(adj)
        out_m, in_m, pair_cov, covering_pairs = precompute_masks(adj)
        full = (1 << n) - 1
        exact_in = next(kk for kk in range(1, n + 1) if exact_bnb(n, pair_cov, covering_pairs, full, 0, kk) is not None)
        st_y = {"splits": 0, "early_yes": 0}
        st_n = {"splits": 0, "early_yes": 0}
        sol_y = solve_band_split(adj, out_m, in_m, pair_cov, covering_pairs, full, 0, exact_in, st_y, base_k=base_k, r_param=r_param)
        sol_n = solve_band_split(adj, out_m, in_m, pair_cov, covering_pairs, full, 0, exact_in - 1, st_n, base_k=base_k, r_param=r_param)
        require(sol_y is not None, f"YES missed on {name}")
        require(sol_n is None, f"false YES on {name}")
        require(st_y["splits"] >= 1 and st_n["splits"] >= 1, f"splits did not fire on {name}")

    # Constrained subproblem with F != empty (including vertices in right bands) AND active splits >= 1
    adj = make_strong_short_span(25, random.Random(606), 0.0)
    n = len(adj)
    out_m, in_m, pair_cov, covering_pairs = precompute_masks(adj)
    D_mask = ((1 << n) - 1) & ~(1 << 12)
    F_mask = (1 << 0) | (1 << 24)  # nonempty F with vertex in R_t
    exact_k = next(kk for kk in range(0, n + 1) if exact_bnb(n, pair_cov, covering_pairs, D_mask, F_mask, kk) is not None)
    st_y = {"splits": 0, "early_yes": 0}
    st_n = {"splits": 0, "early_yes": 0}
    sol_y = solve_band_split(adj, out_m, in_m, pair_cov, covering_pairs, D_mask, F_mask, exact_k, st_y, base_k=7, r_param=10)
    sol_n = solve_band_split(adj, out_m, in_m, pair_cov, covering_pairs, D_mask, F_mask, exact_k - 1, st_n, base_k=7, r_param=10)
    require(sol_y is not None and sol_n is None, "Constrained F!=empty solver mismatch")
    require(st_y["splits"] >= 1 and st_n["splits"] >= 1, f"Constrained F!=empty splits did not fire: {st_y}, {st_n}")

    print(
        f"PASS: verified Lemmas A-E across 14 families, Theorem 4.1 strong connectivity, "
        f"4 full-tournament exact BnB equivalence checks (splits >= 1), and F!=empty constrained split "
        f"(YES splits={st_y['splits']}, NO splits={st_n['splits']}) in {time.time() - t0:.2f}s."
    )


if __name__ == "__main__":
    main()
