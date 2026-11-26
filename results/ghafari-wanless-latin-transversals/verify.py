r"""
Standalone verifier for the proof of Conjecture 3 (Wormald's Question)
of Ghafari and Wanless (arXiv:2607.17547v1, July 2026).

Verifies:
1. All 4 base squares (n0 in {22, 26, 30, 32}): Latin square validity,
   exact Delta-sum bounds (no two disjoint transversals), and 3 unwrapped
   [n0/2, 3n0/2) transversals with empty triple intersection.
2. All 8 infinite mod-16 residue families (n mod 16 in {0, 2, 4, 6, 8, 10, 12, 14}):
   - Algebraic p-invariance of the finite leftover tables (proving validity
     for every p >= p_min to infinity).
   - Direct full-square end-to-end verification of Latin square validity,
     Delta-bounds, 3 transversals, and empty triple intersection for p = p_min..p_min+4
     (orders up to n = 206).
3. All 42 remaining small even orders n in {22, 26, 28, ..., 110}:
   full Latin square validity, exact Delta-bounds (no two disjoint transversals),
   and 3 explicit transversals with empty triple intersection (no pinned entry).

Run with:
    python -O -W error verify.py
"""

import sys


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"Verification failed: {msg}")


def base_shift(n0: int) -> int:
    return 2 * ((n0 // 2 - 4) // 2)


def dA(row: int, s: int, c: int) -> int:
    if s <= c <= s + 10:
        j = c - s
        if row == 0:
            return 3 if j in (1, 5, 8) else (1 if j == 4 else 0)
        if row == 1:
            return 2 if j in (4, 7, 9) else (1 if j in (1, 2, 3, 6) else 0)
        if row == 2:
            if j == 3:
                return 1
            if j in (2, 6, 9):
                return -1
            if j in (4, 8) or (j % 2 == 1 and j != 7):
                return -2
            return 0
        if j in (4, 5, 8, 9):
            return -1
        return -2 if j % 2 == 1 else 0
    if c % 2 == 1:
        return 2 if row < 2 else -2
    return 0


def dB(row: int, c_odd: int, c: int) -> int:
    if c == c_odd:
        return (1, 1, -2)[row]
    if c == c_odd + 1:
        return (1, -1, 0)[row]
    if c % 2 == 1:
        return (2, 0, -2)[row]
    return 0


def dP(is_top: bool, c: int) -> int:
    if c % 2 == 1:
        return 2 if is_top else -2
    return 0


def delta_mod(n0: int, r: int, c: int) -> int:
    sh = base_shift(n0)
    if n0 % 4 == 2:
        t0 = (n0 - 22) // 4
        if r < 4:
            return dA(r, sh, c)
        if r < 7:
            return dB(r - 4, sh + 11, c)
        if r < 10:
            return dB(r - 7, sh + 13, c)
        if r < 10 + 4 * t0:
            rem = (r - 10) % 4
            return dP(True, c) if rem == 0 else (dP(False, c) if rem == 2 else 0)
        if r < n0:
            return 0
        rem = (r - n0) % 4
        return dP(True, c) if rem == 0 else (dP(False, c) if rem == 2 else 0)
    t0 = (n0 - 28) // 4
    if r < 4:
        return dA(r, sh, c)
    if r < 8:
        return dA(r - 4, sh + 4, c)
    if r < 11:
        return dB(r - 8, sh + 13, c)
    if r < 11 + 4 * t0:
        rem = (r - 11) % 4
        return dP(True, c) if rem == 0 else (dP(False, c) if rem == 2 else 0)
    if r < n0:
        return 0
    rem = (r - n0) % 4
    return dP(True, c) if rem == 0 else (dP(False, c) if rem == 2 else 0)


def build_square(n: int, n0: int) -> list[list[int]]:
    return [[(r + c + delta_mod(n0, r, c)) % n for c in range(n)] for r in range(n)]


def check_latin_and_delta_bounds(n: int, n0: int) -> list[list[int]]:
    L = build_square(n, n0)
    for r in range(n):
        require(len(set(L[r])) == n, f"n={n}, n0={n0}: row {r} not a permutation")
    for c in range(n):
        require(len({L[r][c] for r in range(n)}) == n, f"n={n}, n0={n0}: col {c} not a permutation")
    m = n // 2
    max_sum = 0
    min_sum = 0
    umax = []
    for r in range(n):
        ds = [delta_mod(n0, r, c) for c in range(n)]
        mx = max(ds)
        mn = min(ds)
        max_sum += mx
        min_sum += mn
        if ds.count(mx) == 1:
            umax.append((r, ds.index(mx)))
    require(max_sum == m + 1, f"n={n}, n0={n0}: max_sum={max_sum} != {m + 1}")
    require(min_sum > -m, f"n={n}, n0={n0}: min_sum={min_sum} <= {-m}")
    sh = base_shift(n0)
    expected_u = (
        [(2, sh + 3), (5, sh + 11), (8, sh + 13)]
        if n0 % 4 == 2
        else [(2, sh + 3), (6, sh + 7), (9, sh + 13)]
    )
    require(umax == expected_u, f"n={n}, n0={n0}: umax={umax} != {expected_u}")
    return L


def check_three_transversals(L: list[list[int]], n: int, ts: list[list[int]], label: str) -> None:
    require(len(ts) == 3, f"{label}: expected 3 transversals")
    for idx, T in enumerate(ts):
        require(len(T) == n, f"{label} T{idx}: wrong length")
        require(len(set(T)) == n and min(T) == 0 and max(T) == n - 1, f"{label} T{idx}: cols not perm")
        syms = [L[r][T[r]] for r in range(n)]
        require(len(set(syms)) == n, f"{label} T{idx}: syms not perm")
    for r in range(n):
        require(not (ts[0][r] == ts[1][r] == ts[2][r]), f"{label}: common cell at row {r}")


def build_even_tail_params(h: int, R: int, d1: int, d2: int, p: int):
    d = h // 2
    t = 4 * p + R
    e1 = t - d
    e2 = 2 * t + d
    s1 = e1 + d1
    s2 = e2 + d2
    j0, U0 = 0, s1 - 1
    U1 = (s1 + 1) % 2
    j1 = (s1 + 1 - U1) // 2
    U3 = 2 * t - 2 * p - ((s2 - 1) % 2)
    j3 = (s2 - 1 - U3) // 2
    j2 = t - p
    U2 = s2 + 1 - 2 * j2
    require(e1 <= s1 and s1 + 4 * p <= e1 + t and e2 <= s2 and s2 + 4 * p <= e2 + t, "even s-bounds")
    require(0 <= j0 and j0 + p <= j3 and j3 + p <= j1 and j1 + p <= j2 and j2 + p <= t, "even j-bounds")
    require(0 <= U1 and U1 + 2 * p <= U2 and U2 + 2 * p <= U0 and U0 + 2 * p <= U3 and U3 + 2 * p <= 2 * t, "even u-bounds")
    rj = [(j, 1) for j in range(j0 + p, j3)] + [(j, 2) for j in range(j3 + p, j1)] + [(j, 3) for j in range(j1 + p, j2)]
    ru = (
        [(u, 0) for u in range(0, U1)]
        + [(u, 2) for u in range(U1 + 2 * p, U2)]
        + [(u, 4) for u in range(U2 + 2 * p, U0)]
        + [(u, 6) for u in range(U0 + 2 * p, U3)]
        + [(u, 8) for u in range(U3 + 2 * p, 2 * t)]
    )
    rs = (
        [(s, 4) for s in range(e1, s1)]
        + [(s, 8) for s in range(s1 + 4 * p, e1 + t)]
        + [(s, 8) for s in range(e2, s2)]
        + [(s, 12) for s in range(s2 + 4 * p, e2 + t)]
    )
    return t, (j0, U0, j1, U1, j2, U2, j3, U3), rj, ru, rs


def eval_even_tail(fam: dict, p: int, swapped: bool) -> list[int]:
    t, (j0, U0, j1, U1, j2, U2, j3, U3), rj, ru, _ = build_even_tail_params(
        fam["h"], fam["R"], fam["d1"], fam["d2"], p
    )
    col = [-1] * (4 * t)
    for js, Us in [(j0, U0), (j1, U1), (j2, U2), (j3, U3)]:
        for r in range(p):
            j = js + r
            ua, ub = (Us + 2 * r, Us + 2 * r + 1) if not swapped else (Us + 2 * r + 1, Us + 2 * r)
            col[4 * j + 0] = 2 * ua + 1
            col[4 * j + 1] = 2 * ub + 1
            col[4 * j + 2] = 2 * ua
            col[4 * j + 3] = 2 * ub
    for ji, (j, _) in enumerate(rj):
        ua_i, ub_i = fam["pairs"][ji]
        ua, ub = ru[ua_i][0], ru[ub_i][0]
        if swapped:
            ua, ub = ub, ua
        col[4 * j + 0] = 2 * ua + 1
        col[4 * j + 1] = 2 * ub + 1
        col[4 * j + 2] = 2 * ua
        col[4 * j + 3] = 2 * ub
    require(all(x >= 0 for x in col), "unfilled even tail row")
    return col


def build_odd_tail_params(h: int, R: int, d1: int, d2: int, p: int):
    d = h // 2
    t = 4 * p + R
    e1 = t - d
    e2 = 2 * t + d + 1
    o1 = e1 - 1
    o2 = e2 - 1
    s1 = e1 + d1
    s2 = e2 + d2
    j0, U0 = 0, s1 - 1
    U1 = s1 % 2
    j1 = (s1 - U1) // 2
    U3 = 2 * t - 2 * p - ((s2 - 1) % 2)
    j3 = (s2 - 1 - U3) // 2
    j2 = t - p
    U2 = s2 - 2 * j2
    require(e1 <= s1 and s1 + 4 * p <= e1 + t and e2 <= s2 and s2 + 4 * p <= e2 + t, "odd s-bounds")
    require(0 <= j0 and j0 + p <= j3 and j3 + p <= j1 and j1 + p <= j2 and j2 + p <= t, "odd j-bounds")
    require(0 <= U1 and U1 + 2 * p <= U2 and U2 + 2 * p <= U0 and U0 + 2 * p <= U3 and U3 + 2 * p <= 2 * t, "odd u-bounds")
    rj = [(j, 1) for j in range(j0 + p, j3)] + [(j, 2) for j in range(j3 + p, j1)] + [(j, 3) for j in range(j1 + p, j2)]
    ru = (
        [(u, 0) for u in range(0, U1)]
        + [(u, 2) for u in range(U1 + 2 * p, U2)]
        + [(u, 4) for u in range(U2 + 2 * p, U0)]
        + [(u, 6) for u in range(U0 + 2 * p, U3)]
        + [(u, 8) for u in range(U3 + 2 * p, 2 * t)]
    )
    rs1_ev = [(s, 4) for s in range(e1, s1)] + [(s, 8) for s in range(s1 + 4 * p, e1 + t)] + [(s, 8) for s in range(e2, s2)] + [(s, 12) for s in range(s2 + 4 * p, e2 + t)]
    ja1_ex = [(j0, 0), (j1, 2), (j2, 3), (j3, 1)]
    ua1_ex = [(U0 + 2 * (p - 1), 6), (U1 + 2 * (p - 1), 2), (U2 + 2 * (p - 1), 4), (U3 + 2 * (p - 1), 8)]
    rs1_od = [(s, 4) for s in range(o1, s1)] + [(s, 8) for s in range(s1 + 4 * p - 2, o1 + t)] + [(s, 8) for s in range(o2, s2)] + [(s, 12) for s in range(s2 + 4 * p - 2, o2 + t)]
    rs2_od = [(s, 4) for s in range(o1, s1 - 1)] + [(s, 8) for s in range(s1 + 4 * p - 1, o1 + t)] + [(s, 8) for s in range(o2, s2 - 1)] + [(s, 12) for s in range(s2 + 4 * p - 1, o2 + t)]
    jb2_ex = [(j0 + p - 1, 1), (j1 + p - 1, 3), (j2 + p - 1, 4), (j3 + p - 1, 2)]
    ub2_ex = [(U0, 4), (U1, 0), (U2, 2), (U3, 6)]
    rs2_ev = [(s, 4) for s in range(e1, s1 + 1)] + [(s, 8) for s in range(s1 + 4 * p - 1, e1 + t)] + [(s, 8) for s in range(e2, s2 + 1)] + [(s, 12) for s in range(s2 + 4 * p - 1, e2 + t)]
    return t, (j0, U0, j1, U1, j2, U2, j3, U3), rj, ru, (rs1_ev, ja1_ex, ua1_ex, rs1_od), (rs2_od, jb2_ex, ub2_ex, rs2_ev)


def eval_odd_tail(fam: dict, p: int, sol: int) -> list[int]:
    t, (j0, U0, j1, U1, j2, U2, j3, U3), rj, ru, (_, ja1_ex, ua1_ex, _), (_, jb2_ex, ub2_ex, _) = build_odd_tail_params(
        fam["h"], fam["R"], fam["d1"], fam["d2"], p
    )
    col = [-1] * (4 * t)
    if sol == 1:
        for js, Us in [(j0, U0), (j1, U1), (j2, U2), (j3, U3)]:
            for r in range(p):
                j = js + r
                col[4 * j + 2] = 2 * (Us + 2 * r)
                col[4 * j + 3] = 2 * (Us + 2 * r + 1) + 1
                col[4 * j + 1] = 2 * (Us + 2 * r + 1)
                if r >= 1:
                    col[4 * j + 0] = 2 * (Us + 2 * (r - 1)) + 1
        for ji, (j, _) in enumerate(rj):
            ua_i, ub_i = fam["s1_ev_pairs"][ji]
            col[4 * j + 2] = 2 * ru[ua_i][0]
            col[4 * j + 3] = 2 * ru[ub_i][0] + 1
        ua_rem = [ru[ua_i][0] for ua_i, _ in fam["s1_ev_pairs"]] + [u for u, _ in ua1_ex]
        ub_rem = [ru[ub_i][0] for _, ub_i in fam["s1_ev_pairs"]]
        ja_rem = [j for j, _ in rj] + [j for j, _ in ja1_ex]
        jb_rem = [j for j, _ in rj]
        for i, j in enumerate(ja_rem):
            col[4 * j + 0] = 2 * ua_rem[fam["s1_od_a"][i]] + 1
        for i, j in enumerate(jb_rem):
            col[4 * j + 1] = 2 * ub_rem[fam["s1_od_b"][i]]
    else:
        for js, Us in [(j0, U0), (j1, U1), (j2, U2), (j3, U3)]:
            for r in range(p):
                j = js + r
                col[4 * j + 0] = 2 * (Us + 2 * r + 1) + 1
                col[4 * j + 1] = 2 * (Us + 2 * r)
                col[4 * j + 2] = 2 * (Us + 2 * r + 1)
                if r < p - 1:
                    col[4 * j + 3] = 2 * (Us + 2 * (r + 1)) + 1
        for ji, (j, _) in enumerate(rj):
            ua_i, ub_i = fam["s2_od_pairs"][ji]
            col[4 * j + 0] = 2 * ru[ua_i][0] + 1
            col[4 * j + 1] = 2 * ru[ub_i][0]
        ua_rem = [ru[ua_i][0] for ua_i, _ in fam["s2_od_pairs"]]
        ub_rem = [ru[ub_i][0] for _, ub_i in fam["s2_od_pairs"]] + [u for u, _ in ub2_ex]
        ja_rem = [j for j, _ in rj]
        jb_rem = [j for j, _ in rj] + [j for j, _ in jb2_ex]
        for i, j in enumerate(ja_rem):
            col[4 * j + 2] = 2 * ua_rem[fam["s2_ev_a"][i]]
        for i, j in enumerate(jb_rem):
            col[4 * j + 3] = 2 * ub_rem[fam["s2_ev_b"][i]] + 1
    require(all(x >= 0 for x in col), "unfilled odd tail row")
    return col


def verify_all() -> None:
    # 1. Verify all 4 base squares (unwrapped [n0/2, 3n0/2) transversals)
    for n0_str, ts in BASE_TS.items():
        n0 = int(n0_str)
        m = n0 // 2
        L = check_latin_and_delta_bounds(n0, n0)
        check_three_transversals(L, n0, ts, f"base n0={n0}")
        for idx, T in enumerate(ts):
            unwrapped = [r + T[r] + delta_mod(n0, r, T[r]) for r in range(n0)]
            require(sorted(unwrapped) == list(range(m, 3 * m)), f"base n0={n0} T{idx}: not unwrapped [m, 3m)")
    print(f"[PASS] Verified all {len(BASE_TS)} base squares (n0 in {sorted(int(k) for k in BASE_TS)})")

    # 2. Verify all 4 even-h infinite mod-16 families (algebraic p-invariance + full-square checks)
    covered_thresholds = {}
    for mod_str, fam in sorted(EVEN_FAMILIES.items(), key=lambda kv: int(kv[0])):
        mod16 = int(mod_str)
        h, R, d1, d2 = fam["h"], fam["R"], fam["d1"], fam["d2"]
        n0 = 2 * h
        covered_thresholds[mod16] = n0 + 4 * R
        # Algebraic p-invariance check at p=0 and p=1
        _, _, rj0, ru0, rs0 = build_even_tail_params(h, R, d1, d2, 0)
        _, _, rj1, ru1, rs1 = build_even_tail_params(h, R, d1, d2, 1)
        require(all(a[0] + a[1] == b[0] for a, b in zip(rj0, rj1)), f"even mod16={mod16}: rj shift")
        require(all(a[0] + a[1] == b[0] for a, b in zip(ru0, ru1)), f"even mod16={mod16}: ru shift")
        require(all(a[0] + a[1] == b[0] for a, b in zip(rs0, rs1)), f"even mod16={mod16}: rs shift")
        s_map = {s: cs for s, cs in rs0}
        used_u = set()
        used_s = set()
        for ji, (j, cj) in enumerate(rj0):
            ua_i, ub_i = fam["pairs"][ji]
            require(ua_i != ub_i, f"even mod16={mod16}: ua_i == ub_i")
            for ui in (ua_i, ub_i):
                u, cu = ru0[ui]
                sv = 2 * j + u + 1
                require(sv in s_map and 2 * cj + cu == s_map[sv], f"even mod16={mod16}: shift mismatch")
                used_u.add(ui)
                used_s.add(sv)
        require(len(used_u) == len(ru0) and len(used_s) == len(rs0), f"even mod16={mod16}: incomplete matching")
        # Full-square end-to-end checks for p = 0..4 (plus p = 5)
        for p in (0, 1, 2, 3, 4, 5):
            t = 4 * p + R
            n = n0 + 4 * t
            require(n % 16 == mod16, f"even mod16={mod16}: wrong residue")
            L = check_latin_and_delta_bounds(n, n0)
            tail1 = eval_even_tail(fam, p, swapped=False)
            tail2 = eval_even_tail(fam, p, swapped=True)
            require(all(tail1[i] != tail2[i] for i in range(4 * t)), f"even mod16={mod16} p={p}: tail overlap")
            T0 = BASE_TS[str(n0)][0] + [n0 + c for c in tail1]
            T1 = BASE_TS[str(n0)][1] + [n0 + c for c in tail1]
            T2 = BASE_TS[str(n0)][2] + [n0 + c for c in tail2]
            check_three_transversals(L, n, [T0, T1, T2], f"even mod16={mod16} p={p} n={n}")
    print("[PASS] Verified all 4 even-h infinite families (mod 16 in {0, 4, 8, 12}) algebraically + full squares")

    # 3. Verify all 4 odd-h infinite mod-16 families
    for mod_str, fam in sorted(ODD_FAMILIES.items(), key=lambda kv: int(kv[0])):
        mod16 = int(mod_str)
        h, R, d1, d2 = fam["h"], fam["R"], fam["d1"], fam["d2"]
        n0 = 2 * h
        covered_thresholds[mod16] = n0 + 4 * (4 + R)
        _, _, rj1, ru1, p1_s1, p1_s2 = build_odd_tail_params(h, R, d1, d2, 1)
        _, _, rj2, ru2, p2_s1, p2_s2 = build_odd_tail_params(h, R, d1, d2, 2)
        for lst1, lst2 in [(rj1, rj2), (ru1, ru2), *zip(p1_s1, p2_s1), *zip(p1_s2, p2_s2)]:
            require(all(a[0] + a[1] == b[0] for a, b in zip(lst1, lst2)), f"odd mod16={mod16}: p-shift mismatch")
        # Check algebraic p-invariance of Sol 1 and Sol 2 and disjointness at p=1
        rs1_ev, ja1_ex, ua1_ex, rs1_od = p1_s1
        rs2_od, jb2_ex, ub2_ex, rs2_ev = p1_s2
        s1_ev_map = {s: cs for s, cs in rs1_ev}
        s1_od_map = {s: cs for s, cs in rs1_od}
        s2_od_map = {s: cs for s, cs in rs2_od}
        s2_ev_map = {s: cs for s, cs in rs2_ev}
        # Sol 1 EVEN
        uu = set(); ss = set()
        f2 = set(); f3 = set()
        for ji, (j, cj) in enumerate(rj1):
            ua_i, ub_i = fam["s1_ev_pairs"][ji]
            require(ua_i != ub_i, "odd s1 ua==ub")
            ua, cua = ru1[ua_i]; ub, cub = ru1[ub_i]
            sa = 2 * j + ua + 1; sb = 2 * j + ub + 2
            require(sa in s1_ev_map and 2 * cj + cua == s1_ev_map[sa], "odd s1 ev a")
            require(sb in s1_ev_map and 2 * cj + cub == s1_ev_map[sb], "odd s1 ev b")
            uu.update((ua_i, ub_i)); ss.update((sa, sb))
            f2.add((j, ua)); f3.add((j, ub))
        require(len(uu) == len(ru1) and len(ss) == len(rs1_ev), "odd s1 ev complete")
        # Sol 1 ODD
        ua1_rem = [ru1[ua_i] for ua_i, _ in fam["s1_ev_pairs"]] + ua1_ex
        ub1_rem = [ru1[ub_i] for _, ub_i in fam["s1_ev_pairs"]]
        ja1_rem = rj1 + ja1_ex
        jb1_rem = rj1
        ss_od = set(); f0 = set(); f1 = set()
        require(len(set(fam["s1_od_a"])) == len(ua1_rem), "odd s1 od a bij")
        require(len(set(fam["s1_od_b"])) == len(ub1_rem), "odd s1 od b bij")
        for i, (j, cj) in enumerate(ja1_rem):
            u, cu = ua1_rem[fam["s1_od_a"][i]]
            sv = 2 * j + u + 1
            require(sv in s1_od_map and 2 * cj + cu == s1_od_map[sv], "odd s1 od a shift")
            ss_od.add(sv); f0.add((j, u))
        for i, (j, cj) in enumerate(jb1_rem):
            u, cu = ub1_rem[fam["s1_od_b"][i]]
            sv = 2 * j + u
            require(sv in s1_od_map and 2 * cj + cu == s1_od_map[sv], "odd s1 od b shift")
            ss_od.add(sv); f1.add((j, u))
        require(len(ss_od) == len(rs1_od), "odd s1 od complete")
        # Sol 2 ODD
        uu2 = set(); ss2_od = set()
        for ji, (j, cj) in enumerate(rj1):
            ua_i, ub_i = fam["s2_od_pairs"][ji]
            require(ua_i != ub_i, "odd s2 ua==ub")
            ua, cua = ru1[ua_i]; ub, cub = ru1[ub_i]
            require((j, ua) not in f0 and (j, ub) not in f1, "odd s2 od overlaps s1")
            sa = 2 * j + ua + 1; sb = 2 * j + ub
            require(sa in s2_od_map and 2 * cj + cua == s2_od_map[sa], "odd s2 od a")
            require(sb in s2_od_map and 2 * cj + cub == s2_od_map[sb], "odd s2 od b")
            uu2.update((ua_i, ub_i)); ss2_od.add(sa); ss2_od.add(sb)
        require(len(uu2) == len(ru1) and len(ss2_od) == len(rs2_od), "odd s2 od complete")
        # Sol 2 EVEN
        ua2_rem = [ru1[ua_i] for ua_i, _ in fam["s2_od_pairs"]]
        ub2_rem = [ru1[ub_i] for _, ub_i in fam["s2_od_pairs"]] + ub2_ex
        ja2_rem = rj1
        jb2_rem = rj1 + jb2_ex
        ss2_ev = set()
        require(len(set(fam["s2_ev_a"])) == len(ua2_rem), "odd s2 ev a bij")
        require(len(set(fam["s2_ev_b"])) == len(ub2_rem), "odd s2 ev b bij")
        for i, (j, cj) in enumerate(ja2_rem):
            u, cu = ua2_rem[fam["s2_ev_a"][i]]
            require((j, u) not in f2, "odd s2 ev a overlaps s1")
            sv = 2 * j + u + 1
            require(sv in s2_ev_map and 2 * cj + cu == s2_ev_map[sv], "odd s2 ev a shift")
            ss2_ev.add(sv)
        for i, (j, cj) in enumerate(jb2_rem):
            u, cu = ub2_rem[fam["s2_ev_b"][i]]
            require((j, u) not in f3, "odd s2 ev b overlaps s1")
            sv = 2 * j + u + 2
            require(sv in s2_ev_map and 2 * cj + cu == s2_ev_map[sv], "odd s2 ev b shift")
            ss2_ev.add(sv)
        require(len(ss2_ev) == len(rs2_ev), "odd s2 ev complete")
        # Full-square end-to-end checks for p = 1..5
        for p in (1, 2, 3, 4, 5):
            t = 4 * p + R
            n = n0 + 4 * t
            require(n % 16 == mod16, f"odd mod16={mod16}: wrong residue")
            L = check_latin_and_delta_bounds(n, n0)
            tail1 = eval_odd_tail(fam, p, sol=1)
            tail2 = eval_odd_tail(fam, p, sol=2)
            require(all(tail1[i] != tail2[i] for i in range(4 * t)), f"odd mod16={mod16} p={p}: tail overlap")
            T0 = BASE_TS[str(n0)][0] + [n0 + c for c in tail1]
            T1 = BASE_TS[str(n0)][1] + [n0 + c for c in tail1]
            T2 = BASE_TS[str(n0)][2] + [n0 + c for c in tail2]
            check_three_transversals(L, n, [T0, T1, T2], f"odd mod16={mod16} p={p} n={n}")
    print("[PASS] Verified all 4 odd-h infinite families (mod 16 in {2, 6, 10, 14}) algebraically + full squares")

    # 4. Verify complete coverage of all even n >= 22, n != 24
    require(sorted(covered_thresholds.keys()) == [0, 2, 4, 6, 8, 10, 12, 14], "incomplete mod16 coverage")
    expected_small = [
        n for n in range(22, max(covered_thresholds.values()), 2)
        if n != 24 and n < covered_thresholds[n % 16]
    ]
    actual_small = sorted(int(k) for k in SMALL_WITNESSES.keys())
    require(actual_small == expected_small, f"small coverage mismatch: {actual_small} != {expected_small}")
    for n in actual_small:
        L = check_latin_and_delta_bounds(n, n)
        check_three_transversals(L, n, SMALL_WITNESSES[str(n)], f"small n={n}")
    print(f"[PASS] Verified all {len(actual_small)} small even orders (22 <= n <= {max(actual_small)}, n != 24)")
    print("[ALL PASS] Ghafari-Wanless Conjecture 3 holds for EVERY even n >= 22, n != 24 (including n = 30 and all n >= 28)!")


BASE_TS = {'22': [[14, 15, 13, 8, 21, 17, 10, 11, 19, 20, 4, 2, 0, 18, 16, 6, 3, 9, 7, 5, 12, 1], [11, 13, 9, 20, 5, 10, 14, 21, 19, 12, 17, 7, 1, 16, 18, 2, 15, 8, 4, 0, 6, 3], [14, 15, 9, 18, 19, 17, 8, 21, 7, 2, 6, 20, 16, 0, 13, 4, 10, 5, 11, 1, 12, 3]], '26': [[13, 17, 24, 20, 11, 19, 18, 5, 21, 4, 15, 25, 22, 2, 23, 3, 6, 14, 10, 0, 1, 8, 16, 12, 9, 7], [13, 23, 11, 10, 25, 15, 18, 19, 21, 6, 7, 24, 22, 20, 3, 14, 5, 8, 0, 4, 17, 1, 16, 9, 12, 2], [16, 25, 11, 18, 7, 19, 24, 23, 14, 22, 5, 4, 8, 13, 21, 1, 2, 10, 20, 17, 3, 12, 15, 6, 0, 9]], '30': [[15, 27, 22, 12, 29, 21, 16, 11, 23, 20, 13, 17, 28, 3, 1, 24, 26, 4, 25, 0, 6, 2, 14, 18, 7, 19, 8, 10, 5, 9], [18, 21, 13, 20, 25, 10, 22, 11, 23, 16, 27, 29, 24, 4, 3, 28, 26, 1, 8, 14, 15, 6, 0, 7, 17, 19, 12, 2, 9, 5], [18, 19, 13, 16, 27, 21, 28, 9, 7, 22, 5, 24, 26, 23, 25, 29, 4, 11, 12, 20, 6, 3, 10, 0, 1, 15, 17, 2, 14, 8]], '32': [[13, 16, 28, 24, 21, 11, 19, 30, 7, 25, 10, 27, 26, 12, 29, 31, 18, 14, 4, 2, 3, 23, 20, 1, 8, 22, 15, 6, 17, 0, 9, 5], [20, 29, 15, 30, 17, 9, 23, 12, 27, 25, 10, 21, 13, 18, 31, 6, 1, 24, 28, 7, 22, 26, 0, 4, 19, 14, 2, 3, 16, 11, 8, 5], [20, 29, 15, 22, 17, 13, 19, 26, 9, 31, 28, 3, 24, 4, 25, 6, 30, 12, 23, 8, 27, 1, 21, 14, 7, 10, 2, 18, 16, 5, 0, 11]]}

EVEN_FAMILIES = {'12': {'h': 16, 'n0': 32, 'R': 19, 'd1': 1, 'd2': 0, 'start_n': 108, 'pairs': [[12, 11], [13, 14], [23, 19], [22, 20], [37, 10], [9, 0], [2, 1], [8, 3], [5, 4], [7, 6], [36, 35], [30, 32], [26, 34], [21, 25], [18, 33], [27, 29], [31, 16], [15, 28], [17, 24]]}, '0': {'h': 16, 'n0': 32, 'R': 20, 'd1': 2, 'd2': 0, 'start_n': 112, 'pairs': [[14, 13], [27, 19], [21, 16], [22, 5], [10, 9], [12, 39], [0, 11], [1, 2], [3, 8], [32, 38], [7, 6], [37, 29], [33, 34], [4, 26], [35, 36], [30, 18], [23, 15], [20, 31], [17, 25], [24, 28]]}, '4': {'h': 16, 'n0': 32, 'R': 21, 'd1': 1, 'd2': 0, 'start_n': 116, 'pairs': [[13, 14], [15, 24], [23, 27], [26, 18], [12, 10], [9, 11], [41, 0], [2, 1], [40, 39], [4, 5], [8, 31], [3, 7], [6, 28], [36, 33], [32, 35], [34, 38], [37, 17], [20, 16], [30, 22], [29, 19], [25, 21]]}, '8': {'h': 16, 'n0': 32, 'R': 22, 'd1': 2, 'd2': 0, 'start_n': 120, 'pairs': [[16, 15], [19, 23], [27, 28], [7, 20], [10, 12], [14, 9], [43, 11], [0, 13], [6, 1], [39, 36], [33, 41], [30, 8], [4, 34], [3, 37], [42, 5], [21, 38], [40, 2], [22, 32], [26, 35], [29, 31], [24, 25], [18, 17]]}}

ODD_FAMILIES = {'6': {'h': 11, 'n0': 22, 'R': 16, 'd1': 2, 'd2': 3, 'start_n': 102, 's1_ev_pairs': [[12, 13], [14, 15], [19, 16], [5, 31], [9, 10], [0, 11], [1, 2], [30, 27], [24, 3], [6, 26], [29, 4], [25, 18], [28, 21], [17, 23], [20, 22], [7, 8]], 's1_od_a': [16, 0, 2, 3, 19, 5, 17, 6, 9, 10, 14, 12, 8, 11, 13, 1, 4, 18, 15, 7], 's1_od_b': [0, 13, 1, 3, 4, 5, 6, 8, 7, 10, 14, 11, 9, 12, 2, 15], 's2_od_pairs': [[13, 12], [22, 14], [6, 17], [31, 18], [10, 9], [11, 0], [2, 1], [3, 26], [28, 4], [27, 5], [21, 30], [29, 25], [16, 20], [24, 23], [19, 15], [8, 7]], 's2_ev_a': [0, 1, 10, 3, 4, 5, 6, 2, 7, 11, 8, 14, 9, 13, 12, 15], 's2_ev_b': [1, 12, 15, 19, 17, 5, 8, 10, 9, 13, 3, 7, 14, 11, 2, 18, 0, 6, 16, 4]}, '2': {'h': 13, 'n0': 26, 'R': 18, 'd1': 0, 'd2': 1, 'start_n': 114, 's1_ev_pairs': [[11, 12], [13, 24], [22, 16], [17, 21], [10, 8], [35, 9], [0, 1], [2, 4], [6, 26], [33, 30], [5, 3], [25, 32], [34, 27], [28, 29], [31, 19], [14, 15], [18, 20], [23, 7]], 's1_od_a': [18, 0, 1, 15, 20, 21, 19, 12, 11, 10, 2, 7, 14, 6, 16, 13, 3, 17, 4, 5, 8, 9], 's1_od_b': [0, 8, 2, 16, 4, 5, 6, 10, 17, 7, 11, 1, 9, 12, 13, 15, 14, 3], 's2_od_pairs': [[12, 11], [16, 13], [18, 17], [19, 21], [8, 10], [9, 35], [1, 0], [32, 2], [5, 34], [6, 28], [23, 4], [31, 26], [3, 29], [30, 33], [14, 27], [20, 22], [25, 24], [7, 15]], 's2_ev_a': [0, 3, 15, 1, 4, 5, 6, 12, 11, 8, 17, 9, 7, 10, 13, 16, 14, 2], 's2_ev_b': [1, 2, 3, 21, 5, 19, 7, 14, 13, 16, 10, 8, 12, 11, 15, 9, 17, 20, 0, 6, 4, 18]}, '10': {'h': 13, 'n0': 26, 'R': 20, 'd1': 0, 'd2': 1, 'start_n': 122, 's1_ev_pairs': [[13, 14], [16, 22], [25, 26], [21, 15], [8, 11], [9, 39], [12, 10], [0, 2], [37, 4], [33, 28], [29, 5], [34, 36], [38, 3], [6, 27], [35, 1], [31, 17], [32, 24], [18, 30], [19, 23], [20, 7]], 's1_od_a': [20, 3, 0, 2, 22, 23, 5, 21, 7, 9, 10, 11, 15, 12, 14, 16, 1, 18, 17, 19, 6, 4, 13, 8], 's1_od_b': [0, 9, 13, 1, 4, 6, 5, 7, 10, 19, 2, 8, 12, 11, 14, 17, 3, 16, 15, 18], 's2_od_pairs': [[14, 13], [22, 15], [16, 18], [24, 20], [11, 8], [39, 9], [10, 12], [37, 0], [1, 38], [34, 30], [6, 35], [26, 36], [32, 5], [3, 2], [33, 4], [25, 17], [31, 19], [28, 27], [23, 29], [7, 21]], 's2_ev_a': [0, 18, 3, 2, 6, 5, 4, 9, 8, 7, 19, 15, 10, 14, 13, 12, 11, 16, 17, 1], 's2_ev_b': [1, 18, 19, 23, 6, 5, 21, 10, 13, 12, 11, 8, 14, 16, 17, 3, 9, 2, 15, 22, 0, 7, 20, 4]}, '14': {'h': 15, 'n0': 30, 'R': 20, 'd1': 1, 'd2': 0, 'start_n': 126, 's1_ev_pairs': [[13, 14], [25, 16], [26, 23], [6, 19], [8, 9], [11, 12], [10, 39], [0, 34], [1, 31], [2, 37], [5, 3], [38, 35], [7, 4], [36, 27], [29, 21], [17, 32], [33, 22], [30, 18], [15, 24], [28, 20]], 's1_od_a': [20, 0, 18, 3, 22, 23, 4, 21, 9, 12, 13, 8, 10, 7, 17, 16, 19, 1, 14, 2, 5, 6, 15, 11], 's1_od_b': [0, 1, 3, 2, 4, 5, 6, 11, 9, 15, 13, 7, 12, 19, 10, 16, 8, 14, 17, 18], 's2_od_pairs': [[14, 13], [15, 26], [7, 27], [18, 20], [39, 8], [12, 9], [11, 10], [6, 0], [36, 1], [37, 2], [30, 35], [38, 5], [4, 25], [3, 31], [33, 24], [16, 34], [17, 22], [28, 32], [23, 29], [19, 21]], 's2_ev_a': [0, 1, 15, 16, 6, 4, 5, 12, 9, 17, 2, 7, 11, 13, 8, 14, 18, 3, 10, 19], 's2_ev_b': [14, 2, 19, 11, 20, 6, 21, 8, 23, 17, 18, 13, 10, 3, 9, 15, 12, 1, 16, 22, 0, 7, 5, 4]}}

SMALL_WITNESSES = {'22': [[7, 1, 13, 4, 5, 17, 10, 15, 19, 12, 2, 8, 6, 14, 11, 16, 20, 18, 21, 3, 0, 9], [11, 5, 9, 6, 7, 20, 10, 15, 19, 18, 16, 12, 8, 2, 3, 17, 13, 1, 4, 14, 21, 0], [14, 21, 9, 0, 3, 17, 12, 11, 2, 18, 20, 8, 4, 1, 7, 13, 6, 16, 19, 10, 15, 5]], '26': [[13, 25, 22, 4, 15, 19, 16, 23, 21, 0, 3, 7, 24, 1, 6, 8, 10, 2, 9, 18, 11, 17, 12, 20, 5, 14], [16, 25, 11, 24, 3, 18, 4, 7, 21, 6, 17, 9, 10, 5, 19, 22, 23, 15, 8, 12, 14, 0, 2, 20, 1, 13], [13, 17, 11, 20, 25, 19, 4, 23, 1, 12, 15, 8, 6, 24, 16, 18, 10, 0, 21, 22, 2, 3, 7, 5, 14, 9]], '28': [[11, 7, 24, 0, 15, 9, 17, 10, 5, 23, 20, 21, 27, 16, 6, 4, 25, 18, 22, 2, 8, 13, 3, 14, 12, 26, 1, 19], [15, 21, 13, 4, 22, 3, 26, 2, 9, 23, 18, 20, 10, 12, 7, 8, 24, 25, 27, 1, 19, 6, 14, 11, 17, 5, 0, 16], [15, 5, 13, 24, 19, 23, 17, 4, 27, 10, 18, 14, 2, 7, 8, 25, 16, 26, 20, 22, 11, 0, 1, 12, 21, 9, 3, 6]], '30': [[18, 17, 22, 20, 5, 21, 16, 27, 23, 0, 13, 2, 4, 1, 19, 11, 26, 28, 15, 29, 14, 7, 25, 8, 6, 24, 3, 10, 12, 9], [15, 27, 13, 6, 19, 17, 28, 3, 23, 24, 7, 25, 26, 8, 1, 11, 4, 12, 5, 16, 21, 10, 22, 20, 0, 2, 14, 18, 9, 29], [15, 9, 13, 22, 5, 21, 14, 25, 2, 10, 1, 12, 18, 20, 29, 23, 28, 4, 19, 17, 8, 26, 7, 16, 11, 6, 0, 27, 24, 3]], '32': [[20, 5, 4, 30, 24, 7, 19, 6, 15, 25, 8, 17, 9, 16, 29, 1, 28, 0, 18, 13, 21, 31, 12, 14, 3, 22, 2, 27, 23, 10, 26, 11], [13, 7, 15, 2, 21, 27, 14, 12, 17, 25, 16, 23, 9, 20, 3, 30, 24, 22, 28, 4, 5, 26, 8, 31, 19, 6, 18, 29, 10, 0, 11, 1], [13, 7, 15, 22, 21, 25, 19, 16, 5, 31, 28, 17, 2, 24, 30, 26, 11, 4, 6, 1, 14, 10, 23, 20, 27, 29, 9, 12, 8, 0, 3, 18]], '34': [[17, 11, 0, 32, 15, 23, 2, 1, 25, 28, 3, 7, 10, 12, 29, 18, 14, 21, 31, 4, 20, 22, 6, 8, 26, 33, 13, 5, 19, 24, 16, 30, 9, 27], [20, 21, 15, 8, 1, 0, 4, 23, 25, 10, 31, 22, 30, 3, 33, 16, 12, 29, 7, 17, 2, 26, 13, 6, 14, 5, 28, 32, 9, 11, 18, 24, 19, 27], [13, 25, 15, 30, 33, 23, 2, 31, 19, 26, 9, 32, 20, 6, 1, 10, 14, 29, 3, 12, 24, 27, 4, 22, 0, 16, 8, 11, 28, 18, 7, 5, 17, 21]], '36': [[15, 13, 0, 6, 26, 25, 21, 20, 29, 27, 12, 7, 24, 4, 34, 17, 30, 8, 5, 28, 9, 22, 33, 3, 16, 35, 31, 23, 14, 1, 11, 18, 19, 2, 10, 32], [22, 5, 17, 0, 19, 9, 30, 24, 35, 27, 8, 11, 18, 10, 26, 29, 6, 4, 33, 13, 15, 28, 31, 20, 23, 3, 12, 2, 14, 21, 25, 32, 16, 1, 7, 34], [22, 5, 17, 26, 19, 7, 21, 14, 29, 31, 32, 9, 25, 4, 1, 15, 27, 16, 23, 28, 34, 3, 30, 11, 6, 10, 33, 0, 18, 20, 8, 24, 35, 12, 2, 13]], '38': [[22, 37, 28, 20, 33, 25, 2, 15, 27, 10, 21, 6, 14, 16, 29, 0, 36, 34, 17, 35, 30, 7, 19, 9, 32, 24, 1, 8, 31, 13, 18, 3, 26, 11, 4, 12, 5, 23], [15, 29, 17, 14, 3, 35, 28, 1, 27, 32, 11, 26, 12, 37, 33, 23, 0, 13, 7, 16, 8, 24, 5, 10, 36, 19, 31, 25, 18, 2, 34, 20, 21, 30, 9, 4, 6, 22], [22, 29, 17, 20, 9, 25, 12, 15, 34, 30, 21, 36, 32, 23, 33, 37, 18, 4, 35, 31, 8, 19, 27, 6, 2, 5, 1, 14, 10, 16, 24, 26, 28, 13, 3, 0, 7, 11]], '40': [[24, 7, 10, 0, 21, 13, 23, 30, 31, 29, 32, 11, 5, 34, 22, 15, 3, 6, 16, 35, 26, 4, 18, 25, 37, 28, 9, 2, 27, 33, 36, 14, 1, 38, 17, 19, 8, 12, 20, 39], [24, 5, 19, 32, 21, 35, 6, 12, 31, 29, 16, 3, 8, 36, 10, 17, 14, 38, 27, 23, 13, 4, 28, 20, 39, 33, 11, 30, 26, 7, 2, 22, 15, 18, 37, 34, 25, 9, 0, 1], [21, 13, 19, 6, 28, 29, 23, 14, 35, 10, 30, 31, 11, 26, 0, 3, 16, 36, 15, 7, 18, 34, 24, 27, 5, 33, 25, 39, 37, 12, 22, 17, 2, 38, 8, 32, 1, 20, 9, 4]], '42': [[17, 9, 6, 12, 5, 27, 36, 21, 29, 26, 33, 25, 20, 13, 31, 34, 8, 14, 41, 37, 2, 23, 39, 0, 10, 18, 1, 40, 30, 22, 11, 24, 28, 15, 35, 4, 16, 3, 32, 7, 19, 38], [24, 41, 19, 8, 9, 32, 20, 11, 29, 22, 23, 21, 40, 26, 27, 35, 2, 28, 31, 36, 10, 37, 1, 13, 4, 34, 33, 39, 12, 0, 3, 16, 17, 30, 14, 6, 18, 5, 38, 7, 25, 15], [21, 5, 19, 10, 33, 27, 28, 35, 18, 14, 29, 25, 34, 2, 3, 41, 32, 15, 9, 16, 8, 22, 23, 7, 36, 37, 31, 0, 30, 38, 24, 20, 13, 4, 39, 17, 6, 26, 11, 1, 40, 12]], '44': [[19, 3, 12, 2, 23, 26, 25, 0, 11, 31, 8, 27, 13, 6, 9, 21, 15, 18, 28, 43, 41, 32, 37, 29, 10, 30, 17, 33, 20, 7, 38, 40, 24, 14, 36, 22, 16, 35, 4, 34, 5, 42, 39, 1], [23, 41, 21, 42, 30, 43, 16, 14, 7, 31, 28, 3, 15, 20, 29, 35, 40, 34, 22, 25, 9, 4, 36, 5, 33, 10, 6, 1, 39, 18, 12, 24, 32, 26, 2, 13, 27, 17, 37, 0, 38, 8, 11, 19], [23, 11, 21, 6, 27, 35, 25, 16, 7, 12, 30, 9, 33, 36, 34, 3, 28, 42, 18, 41, 13, 10, 32, 5, 39, 26, 24, 2, 15, 17, 22, 29, 37, 4, 38, 20, 43, 1, 19, 8, 31, 0, 14, 40]], '46': [[26, 25, 4, 20, 1, 29, 14, 37, 31, 10, 9, 36, 38, 21, 43, 39, 2, 34, 19, 23, 12, 41, 7, 18, 44, 5, 35, 17, 32, 8, 13, 24, 6, 40, 27, 22, 0, 42, 11, 33, 30, 15, 16, 28, 45, 3], [26, 29, 21, 28, 41, 22, 6, 9, 31, 10, 37, 15, 2, 17, 1, 0, 4, 33, 19, 35, 42, 36, 27, 45, 24, 13, 25, 8, 16, 30, 5, 12, 14, 38, 7, 20, 44, 32, 18, 40, 34, 11, 3, 39, 23, 43], [19, 17, 21, 4, 3, 29, 38, 43, 24, 20, 31, 25, 42, 0, 35, 30, 12, 22, 1, 11, 14, 5, 39, 34, 18, 13, 9, 37, 28, 36, 15, 40, 26, 27, 45, 6, 41, 32, 10, 23, 33, 8, 44, 7, 2, 16]], '48': [[21, 9, 16, 26, 32, 35, 27, 4, 17, 33, 46, 13, 45, 22, 5, 15, 25, 20, 3, 41, 8, 28, 36, 43, 14, 30, 24, 7, 18, 34, 40, 42, 39, 31, 44, 19, 29, 11, 23, 1, 12, 10, 37, 38, 0, 2, 47, 6], [25, 24, 23, 34, 29, 28, 40, 14, 41, 33, 44, 3, 26, 2, 30, 45, 4, 32, 15, 13, 20, 8, 10, 35, 7, 42, 47, 21, 38, 36, 18, 22, 39, 37, 27, 43, 9, 5, 1, 19, 16, 31, 17, 46, 11, 12, 6, 0], [25, 47, 23, 20, 32, 35, 27, 30, 3, 8, 4, 5, 41, 38, 34, 39, 17, 10, 6, 9, 40, 14, 21, 11, 31, 24, 44, 29, 36, 28, 43, 0, 37, 13, 46, 12, 16, 1, 7, 15, 19, 26, 2, 45, 33, 18, 22, 42]], '50': [[28, 41, 30, 48, 21, 31, 16, 1, 33, 32, 37, 24, 6, 44, 5, 13, 10, 46, 23, 40, 34, 4, 45, 25, 0, 36, 39, 2, 22, 35, 7, 9, 14, 47, 19, 12, 20, 8, 15, 49, 26, 29, 42, 43, 18, 38, 27, 11, 17, 3], [25, 27, 23, 32, 47, 42, 44, 43, 33, 34, 21, 2, 8, 48, 5, 12, 38, 15, 45, 37, 14, 30, 7, 1, 22, 0, 13, 46, 16, 20, 35, 17, 28, 4, 3, 29, 36, 31, 41, 6, 19, 49, 24, 26, 18, 10, 11, 39, 40, 9], [28, 19, 23, 48, 11, 31, 24, 35, 40, 44, 45, 10, 2, 20, 25, 27, 18, 26, 43, 6, 42, 34, 21, 4, 14, 29, 33, 46, 0, 36, 37, 5, 38, 49, 3, 15, 16, 22, 30, 7, 39, 8, 32, 47, 41, 13, 1, 9, 12, 17]], '52': [[30, 7, 40, 4, 34, 39, 29, 28, 15, 35, 50, 3, 5, 44, 37, 1, 8, 14, 21, 23, 18, 22, 42, 27, 43, 36, 47, 45, 6, 0, 49, 51, 16, 38, 41, 20, 17, 10, 11, 19, 25, 13, 24, 46, 48, 33, 26, 9, 2, 31, 32, 12], [30, 15, 25, 20, 34, 39, 2, 8, 49, 35, 44, 1, 13, 38, 12, 3, 6, 46, 31, 19, 7, 48, 14, 33, 29, 32, 24, 27, 4, 18, 5, 9, 41, 50, 21, 26, 40, 11, 43, 51, 28, 23, 10, 0, 47, 37, 16, 42, 17, 22, 36, 45], [23, 39, 25, 20, 31, 41, 29, 42, 17, 51, 22, 49, 21, 8, 45, 7, 1, 44, 37, 47, 30, 4, 13, 9, 5, 38, 32, 43, 36, 10, 16, 19, 34, 12, 40, 2, 15, 28, 18, 14, 3, 26, 50, 11, 27, 48, 24, 0, 35, 33, 46, 6]], '54': [[27, 1, 18, 0, 9, 33, 26, 19, 35, 24, 51, 53, 28, 16, 31, 37, 46, 6, 47, 29, 2, 20, 7, 15, 48, 25, 45, 22, 32, 52, 39, 23, 36, 10, 43, 40, 42, 14, 13, 50, 30, 5, 3, 12, 44, 21, 34, 49, 17, 41, 11, 8, 4, 38], [27, 17, 25, 24, 29, 16, 10, 47, 35, 14, 3, 8, 36, 33, 1, 53, 38, 19, 5, 41, 30, 28, 15, 22, 34, 12, 37, 51, 48, 26, 31, 0, 32, 39, 23, 52, 4, 43, 21, 49, 2, 11, 44, 40, 18, 6, 7, 20, 9, 46, 42, 50, 45, 13], [23, 5, 25, 24, 53, 33, 10, 29, 38, 20, 49, 34, 42, 9, 37, 18, 32, 48, 51, 11, 44, 46, 19, 28, 26, 17, 47, 31, 50, 40, 3, 16, 0, 1, 41, 22, 36, 12, 45, 2, 4, 27, 52, 30, 35, 15, 6, 8, 43, 7, 13, 39, 14, 21]], '56': [[32, 17, 16, 38, 33, 1, 31, 44, 49, 37, 24, 9, 7, 12, 10, 35, 29, 50, 30, 45, 22, 42, 8, 11, 48, 6, 13, 53, 15, 28, 26, 27, 36, 40, 3, 51, 47, 52, 39, 19, 25, 21, 43, 41, 2, 34, 4, 14, 23, 20, 5, 54, 18, 0, 46, 55], [32, 55, 27, 40, 29, 53, 6, 30, 15, 37, 0, 41, 9, 28, 10, 35, 23, 36, 2, 43, 3, 42, 39, 21, 5, 46, 48, 13, 44, 54, 8, 7, 25, 22, 17, 11, 51, 12, 52, 20, 38, 34, 47, 45, 26, 24, 4, 18, 14, 33, 50, 16, 49, 31, 19, 1], [29, 3, 27, 14, 33, 47, 31, 40, 11, 6, 54, 39, 22, 12, 43, 55, 53, 44, 13, 35, 15, 2, 21, 23, 50, 42, 0, 17, 38, 4, 20, 51, 28, 32, 46, 7, 5, 48, 30, 24, 18, 10, 34, 16, 1, 8, 9, 36, 45, 49, 25, 19, 26, 52, 41, 37]], '58': [[29, 51, 56, 10, 1, 35, 4, 11, 37, 28, 55, 20, 40, 31, 45, 21, 50, 16, 49, 19, 52, 18, 39, 7, 26, 48, 57, 13, 32, 14, 25, 44, 24, 43, 15, 47, 6, 12, 41, 54, 8, 42, 9, 27, 36, 0, 46, 17, 38, 30, 34, 23, 53, 2, 33, 22, 3, 5], [29, 55, 27, 38, 15, 6, 46, 11, 37, 16, 25, 20, 14, 43, 57, 30, 24, 53, 35, 47, 22, 56, 33, 12, 0, 26, 1, 7, 40, 9, 21, 49, 32, 39, 3, 41, 18, 54, 31, 23, 34, 44, 5, 17, 42, 36, 4, 28, 19, 45, 51, 10, 13, 52, 48, 8, 50, 2], [25, 51, 27, 30, 19, 35, 2, 29, 55, 46, 11, 32, 4, 34, 43, 24, 42, 33, 1, 54, 56, 6, 53, 17, 0, 45, 3, 38, 28, 22, 13, 26, 48, 15, 39, 36, 10, 7, 47, 14, 20, 49, 5, 52, 40, 16, 21, 31, 44, 23, 50, 18, 41, 57, 8, 9, 12, 37]], '60': [[27, 21, 20, 18, 31, 7, 33, 4, 47, 39, 10, 41, 25, 54, 38, 49, 15, 58, 30, 57, 8, 6, 46, 1, 12, 14, 43, 3, 35, 32, 26, 11, 28, 22, 36, 5, 37, 40, 51, 9, 19, 44, 23, 52, 50, 17, 55, 29, 16, 34, 56, 42, 59, 0, 53, 24, 2, 48, 45, 13], [27, 53, 29, 14, 35, 3, 46, 2, 31, 39, 4, 15, 11, 52, 20, 23, 56, 18, 48, 41, 59, 26, 54, 33, 37, 0, 7, 19, 25, 42, 30, 49, 5, 6, 55, 9, 44, 38, 40, 43, 17, 22, 1, 16, 10, 51, 21, 8, 50, 24, 36, 13, 58, 28, 57, 32, 12, 34, 47, 45], [34, 15, 29, 32, 35, 43, 33, 36, 1, 50, 58, 13, 27, 16, 0, 53, 57, 14, 18, 9, 24, 46, 42, 59, 31, 38, 30, 17, 37, 48, 55, 5, 47, 20, 41, 45, 40, 56, 11, 19, 54, 4, 10, 44, 22, 12, 23, 7, 3, 39, 51, 21, 6, 28, 8, 25, 52, 26, 49, 2]], '62': [[34, 11, 54, 18, 47, 37, 56, 1, 39, 0, 51, 46, 4, 5, 23, 52, 8, 53, 25, 31, 48, 13, 9, 7, 20, 21, 41, 50, 24, 6, 19, 10, 32, 16, 49, 59, 38, 3, 33, 26, 60, 40, 17, 55, 14, 2, 43, 12, 42, 44, 29, 15, 36, 22, 35, 27, 28, 30, 58, 45, 57, 61], [34, 57, 29, 40, 55, 48, 8, 7, 39, 4, 17, 43, 46, 60, 11, 36, 12, 9, 35, 1, 14, 42, 21, 58, 18, 10, 5, 41, 28, 23, 61, 15, 54, 51, 31, 37, 26, 22, 47, 59, 30, 24, 3, 49, 56, 38, 53, 32, 16, 25, 0, 20, 33, 27, 52, 2, 13, 45, 19, 44, 6, 50], [31, 49, 29, 32, 1, 37, 22, 59, 0, 56, 21, 60, 30, 35, 51, 3, 44, 28, 53, 8, 24, 5, 17, 14, 48, 11, 47, 23, 2, 34, 55, 50, 46, 25, 13, 19, 38, 10, 39, 20, 36, 52, 7, 41, 12, 40, 43, 54, 18, 15, 33, 57, 9, 4, 61, 27, 6, 45, 42, 58, 26, 16]], '64': [[36, 53, 26, 52, 37, 27, 35, 56, 61, 41, 2, 39, 62, 34, 10, 63, 17, 60, 7, 15, 44, 6, 57, 1, 46, 12, 31, 29, 33, 40, 13, 5, 30, 16, 48, 47, 45, 58, 3, 25, 20, 4, 23, 9, 24, 54, 32, 49, 38, 55, 43, 8, 42, 0, 19, 59, 11, 18, 14, 28, 50, 51, 21, 22], [33, 13, 31, 62, 40, 19, 6, 30, 11, 41, 8, 43, 1, 42, 32, 5, 29, 10, 39, 17, 50, 38, 7, 59, 47, 36, 37, 35, 44, 24, 58, 61, 0, 46, 55, 25, 22, 4, 49, 9, 26, 28, 57, 15, 48, 52, 2, 60, 20, 3, 56, 53, 51, 14, 21, 63, 27, 16, 23, 54, 18, 34, 12, 45], [29, 51, 31, 22, 37, 45, 35, 52, 39, 8, 2, 17, 23, 34, 24, 33, 0, 54, 61, 53, 9, 48, 6, 59, 3, 36, 41, 57, 50, 16, 25, 55, 21, 42, 43, 11, 15, 58, 62, 49, 32, 56, 1, 19, 12, 38, 27, 63, 18, 13, 20, 14, 5, 10, 28, 46, 4, 30, 47, 26, 44, 7, 60, 40]], '66': [[29, 19, 64, 20, 31, 39, 32, 33, 41, 40, 59, 65, 0, 49, 57, 62, 36, 38, 27, 21, 26, 5, 45, 10, 6, 50, 55, 7, 44, 52, 9, 28, 58, 24, 61, 4, 48, 30, 47, 63, 54, 12, 51, 11, 14, 34, 37, 23, 16, 25, 13, 42, 8, 15, 56, 1, 35, 60, 43, 2, 3, 53, 18, 46, 22, 17], [29, 37, 31, 58, 63, 6, 12, 55, 41, 18, 5, 43, 62, 0, 7, 47, 64, 4, 19, 44, 52, 26, 11, 45, 46, 17, 27, 1, 28, 24, 65, 42, 20, 57, 15, 53, 30, 59, 9, 32, 36, 2, 23, 3, 16, 13, 51, 60, 34, 54, 33, 8, 40, 49, 21, 10, 35, 38, 56, 22, 50, 25, 61, 48, 14, 39], [36, 57, 31, 48, 59, 39, 40, 29, 32, 58, 11, 50, 56, 0, 61, 26, 20, 65, 53, 6, 42, 23, 9, 64, 24, 33, 25, 54, 22, 51, 3, 41, 10, 14, 21, 62, 28, 34, 63, 35, 52, 2, 49, 12, 8, 43, 47, 38, 46, 37, 17, 5, 44, 45, 30, 60, 7, 13, 1, 16, 18, 15, 4, 27, 19, 55]], '68': [[38, 1, 46, 10, 39, 17, 37, 28, 57, 43, 22, 45, 4, 12, 31, 5, 47, 14, 34, 49, 42, 56, 11, 51, 62, 50, 48, 53, 40, 66, 8, 23, 32, 54, 3, 13, 7, 52, 59, 55, 25, 18, 19, 35, 63, 24, 9, 61, 60, 30, 65, 27, 67, 64, 6, 2, 15, 16, 33, 26, 44, 41, 36, 20, 58, 29, 0, 21], [31, 51, 33, 14, 42, 65, 52, 58, 57, 43, 4, 63, 0, 28, 7, 5, 32, 8, 17, 25, 19, 2, 39, 37, 62, 38, 49, 35, 40, 66, 67, 11, 23, 18, 9, 13, 6, 22, 45, 15, 44, 30, 27, 55, 29, 56, 41, 59, 46, 50, 20, 47, 53, 24, 61, 26, 36, 3, 48, 54, 60, 64, 34, 16, 10, 1, 12, 21], [38, 27, 33, 20, 35, 13, 37, 40, 51, 12, 66, 67, 50, 26, 23, 61, 36, 14, 8, 65, 4, 6, 29, 43, 39, 44, 53, 55, 31, 46, 34, 15, 0, 54, 32, 45, 24, 30, 2, 17, 16, 60, 48, 5, 28, 52, 57, 47, 9, 62, 3, 42, 18, 64, 59, 19, 25, 49, 56, 63, 11, 41, 21, 22, 1, 58, 7, 10]], '70': [[38, 65, 60, 52, 55, 41, 36, 9, 43, 66, 69, 13, 4, 57, 63, 33, 30, 34, 15, 10, 56, 17, 67, 26, 20, 6, 25, 53, 22, 27, 61, 35, 58, 49, 23, 62, 64, 59, 3, 48, 0, 44, 29, 21, 28, 12, 47, 37, 54, 14, 31, 18, 8, 5, 51, 19, 68, 32, 45, 39, 7, 16, 42, 46, 1, 50, 40, 11, 24, 2], [35, 37, 33, 16, 65, 22, 14, 39, 43, 46, 23, 64, 66, 30, 69, 19, 42, 15, 11, 53, 4, 8, 27, 3, 38, 58, 49, 59, 60, 50, 41, 51, 68, 20, 13, 29, 40, 26, 1, 52, 6, 28, 21, 55, 24, 48, 67, 7, 12, 54, 57, 10, 32, 34, 25, 2, 36, 17, 9, 61, 47, 56, 18, 63, 31, 5, 0, 62, 44, 45], [38, 59, 33, 60, 39, 41, 24, 11, 51, 20, 7, 64, 52, 58, 49, 62, 16, 66, 17, 3, 6, 28, 29, 61, 34, 31, 53, 0, 46, 4, 55, 8, 2, 22, 15, 35, 18, 56, 45, 5, 54, 47, 25, 23, 32, 27, 43, 69, 50, 37, 21, 10, 68, 26, 57, 63, 12, 65, 9, 1, 67, 40, 48, 19, 14, 30, 42, 13, 44, 36]], '72': [[37, 49, 66, 30, 44, 55, 39, 58, 21, 45, 12, 69, 7, 50, 61, 27, 16, 42, 0, 15, 4, 52, 48, 41, 62, 46, 32, 63, 70, 10, 51, 9, 29, 24, 26, 17, 2, 6, 47, 33, 67, 60, 57, 5, 25, 68, 43, 53, 1, 34, 59, 11, 36, 64, 22, 40, 23, 71, 14, 18, 65, 19, 31, 56, 3, 35, 54, 20, 38, 28, 8, 13], [33, 71, 35, 2, 41, 15, 70, 30, 57, 45, 18, 43, 31, 46, 38, 9, 0, 6, 53, 11, 24, 54, 65, 55, 25, 8, 5, 39, 63, 32, 12, 49, 58, 52, 62, 13, 56, 60, 69, 61, 17, 28, 20, 21, 29, 44, 47, 37, 10, 16, 1, 59, 67, 26, 27, 23, 14, 7, 68, 42, 3, 64, 22, 50, 19, 34, 66, 51, 4, 48, 36, 40], [40, 17, 35, 22, 37, 61, 39, 6, 31, 68, 48, 3, 44, 18, 70, 25, 55, 58, 19, 1, 42, 14, 65, 15, 30, 8, 67, 21, 52, 16, 0, 71, 50, 28, 38, 53, 34, 2, 36, 7, 29, 10, 11, 41, 56, 54, 13, 27, 60, 32, 45, 43, 46, 20, 47, 12, 23, 49, 33, 24, 4, 5, 59, 26, 63, 64, 69, 57, 51, 9, 62, 66]], '74': [[40, 67, 32, 18, 61, 43, 22, 37, 45, 66, 71, 51, 0, 11, 63, 59, 42, 25, 21, 69, 60, 29, 39, 54, 28, 35, 5, 12, 62, 68, 27, 50, 44, 14, 19, 64, 4, 73, 13, 55, 72, 15, 49, 53, 38, 23, 3, 58, 70, 20, 9, 41, 48, 56, 47, 30, 10, 16, 31, 6, 24, 26, 57, 1, 8, 46, 65, 34, 36, 2, 52, 7, 17, 33], [37, 53, 35, 66, 17, 55, 44, 7, 45, 22, 41, 14, 50, 51, 67, 30, 54, 69, 29, 72, 64, 42, 57, 5, 10, 68, 31, 49, 40, 23, 19, 65, 56, 33, 39, 4, 62, 48, 3, 16, 6, 1, 21, 58, 60, 28, 61, 47, 0, 25, 63, 70, 26, 18, 11, 52, 2, 32, 71, 59, 12, 34, 73, 24, 46, 38, 13, 15, 43, 8, 36, 9, 20, 27], [37, 3, 35, 30, 45, 43, 46, 13, 1, 14, 47, 20, 62, 53, 23, 2, 48, 39, 49, 25, 56, 6, 69, 19, 10, 57, 61, 5, 66, 41, 9, 50, 58, 24, 29, 38, 36, 16, 71, 65, 70, 51, 17, 12, 18, 34, 73, 55, 52, 68, 67, 44, 26, 33, 21, 32, 4, 27, 7, 40, 8, 63, 60, 22, 11, 72, 54, 42, 64, 59, 28, 0, 31, 15]], '76': [[42, 25, 16, 68, 43, 65, 41, 14, 75, 47, 60, 61, 67, 48, 3, 39, 0, 26, 36, 63, 44, 28, 22, 35, 29, 8, 10, 13, 54, 30, 69, 57, 37, 70, 64, 21, 71, 4, 62, 73, 33, 24, 9, 7, 19, 46, 55, 27, 74, 34, 66, 15, 53, 58, 52, 45, 31, 32, 38, 18, 50, 1, 51, 12, 2, 23, 49, 56, 40, 17, 11, 72, 59, 5, 6, 20], [35, 49, 37, 6, 39, 42, 20, 14, 45, 47, 50, 1, 57, 62, 63, 67, 58, 64, 61, 11, 10, 74, 3, 41, 15, 36, 33, 27, 68, 38, 17, 9, 19, 2, 28, 43, 5, 72, 12, 51, 31, 24, 71, 53, 34, 46, 66, 55, 59, 44, 70, 23, 69, 52, 29, 73, 7, 16, 30, 75, 8, 25, 48, 40, 60, 54, 21, 32, 4, 13, 0, 18, 22, 56, 26, 65], [39, 67, 37, 40, 43, 7, 41, 68, 29, 0, 54, 21, 18, 12, 2, 63, 75, 48, 5, 45, 11, 34, 71, 35, 73, 58, 1, 27, 17, 52, 38, 65, 62, 8, 28, 51, 60, 26, 16, 33, 19, 10, 4, 31, 42, 22, 15, 53, 24, 46, 70, 59, 56, 36, 69, 25, 55, 14, 47, 66, 49, 23, 72, 50, 13, 64, 3, 20, 32, 9, 44, 57, 61, 6, 30, 74]], '78': [[42, 11, 22, 28, 7, 45, 0, 51, 47, 16, 23, 4, 24, 63, 39, 56, 62, 58, 19, 3, 60, 67, 17, 73, 74, 21, 9, 77, 44, 68, 31, 37, 34, 57, 49, 76, 38, 32, 33, 20, 8, 75, 43, 6, 50, 25, 29, 36, 10, 18, 1, 59, 12, 52, 69, 26, 64, 55, 61, 40, 70, 46, 15, 2, 54, 41, 66, 72, 27, 71, 65, 30, 14, 35, 48, 53, 13, 5], [42, 7, 37, 52, 41, 12, 48, 57, 47, 56, 23, 64, 0, 13, 25, 69, 20, 53, 63, 55, 22, 36, 75, 6, 8, 76, 33, 50, 16, 34, 65, 67, 68, 70, 15, 4, 40, 30, 49, 43, 66, 27, 35, 9, 14, 5, 45, 24, 46, 31, 1, 73, 44, 58, 17, 54, 60, 2, 61, 3, 32, 26, 51, 18, 62, 21, 72, 11, 59, 39, 77, 71, 19, 29, 38, 10, 74, 28], [35, 77, 37, 18, 31, 45, 4, 33, 53, 46, 29, 56, 72, 1, 27, 43, 0, 2, 55, 52, 16, 70, 71, 3, 6, 68, 5, 7, 20, 28, 41, 25, 58, 48, 13, 54, 36, 66, 47, 57, 38, 12, 19, 21, 26, 64, 17, 39, 62, 30, 65, 8, 14, 49, 67, 50, 42, 75, 23, 15, 22, 40, 61, 59, 60, 73, 10, 63, 9, 44, 76, 69, 34, 74, 11, 32, 24, 51]], '80': [[37, 53, 24, 42, 48, 3, 43, 60, 73, 49, 18, 21, 4, 58, 10, 15, 63, 78, 76, 1, 55, 30, 22, 59, 62, 0, 28, 9, 19, 14, 39, 77, 26, 66, 46, 29, 5, 44, 79, 11, 36, 50, 35, 33, 54, 52, 17, 13, 20, 8, 51, 69, 64, 34, 7, 25, 72, 56, 57, 31, 40, 68, 23, 70, 47, 61, 27, 6, 41, 38, 2, 32, 16, 71, 45, 65, 74, 12, 67, 75], [41, 71, 39, 60, 45, 75, 26, 4, 13, 49, 2, 21, 19, 20, 57, 51, 62, 28, 8, 63, 68, 56, 32, 3, 43, 0, 36, 17, 7, 10, 77, 65, 61, 24, 47, 59, 22, 72, 37, 29, 64, 48, 30, 35, 5, 50, 14, 67, 73, 12, 6, 23, 76, 46, 66, 9, 54, 78, 69, 33, 25, 40, 38, 27, 15, 58, 31, 16, 34, 18, 79, 74, 1, 44, 70, 11, 42, 53, 55, 52], [44, 79, 39, 46, 45, 5, 43, 16, 9, 1, 12, 49, 56, 18, 30, 61, 14, 68, 35, 75, 51, 58, 54, 29, 2, 64, 10, 11, 77, 52, 3, 53, 27, 36, 41, 63, 37, 20, 28, 19, 78, 4, 22, 69, 47, 62, 17, 55, 8, 48, 67, 59, 25, 42, 34, 71, 65, 26, 40, 23, 66, 0, 76, 72, 6, 15, 57, 7, 33, 50, 24, 60, 21, 74, 13, 70, 32, 38, 31, 73]], '82': [[44, 15, 26, 64, 5, 47, 76, 65, 49, 52, 33, 41, 36, 16, 23, 19, 22, 39, 57, 79, 46, 48, 77, 81, 78, 25, 29, 17, 56, 59, 11, 2, 60, 50, 51, 73, 40, 70, 31, 55, 66, 37, 69, 75, 80, 6, 61, 38, 42, 32, 3, 45, 62, 9, 7, 10, 8, 13, 63, 20, 68, 12, 53, 28, 72, 54, 27, 30, 0, 34, 71, 18, 14, 58, 1, 67, 4, 35, 21, 43, 74, 24], [44, 33, 39, 10, 31, 9, 80, 15, 49, 78, 17, 58, 26, 65, 25, 18, 72, 3, 69, 53, 74, 13, 57, 52, 66, 51, 77, 38, 32, 64, 19, 42, 16, 34, 41, 0, 56, 45, 5, 20, 28, 67, 81, 11, 68, 76, 55, 8, 36, 22, 61, 29, 70, 4, 43, 7, 14, 50, 1, 73, 6, 37, 21, 47, 40, 35, 23, 12, 46, 62, 75, 63, 54, 24, 27, 71, 59, 79, 60, 30, 48, 2], [37, 57, 39, 30, 13, 47, 4, 53, 22, 32, 45, 33, 16, 21, 63, 2, 0, 52, 51, 74, 80, 55, 15, 35, 64, 1, 59, 68, 10, 41, 5, 25, 20, 48, 7, 76, 14, 18, 69, 66, 38, 31, 29, 23, 60, 61, 65, 43, 26, 36, 79, 40, 44, 77, 71, 9, 46, 8, 81, 27, 58, 42, 11, 70, 50, 19, 49, 62, 12, 28, 24, 72, 17, 34, 54, 75, 73, 6, 67, 3, 56, 78]], '84': [[39, 19, 60, 52, 43, 9, 45, 34, 25, 51, 44, 83, 12, 56, 77, 67, 50, 58, 75, 49, 72, 16, 3, 23, 62, 4, 69, 1, 17, 42, 81, 27, 57, 82, 68, 53, 13, 28, 61, 63, 54, 6, 59, 73, 37, 78, 30, 79, 35, 18, 22, 21, 33, 24, 2, 31, 71, 40, 5, 7, 64, 80, 20, 55, 14, 38, 76, 70, 11, 66, 46, 36, 8, 0, 74, 47, 41, 10, 65, 26, 32, 29, 48, 15], [43, 79, 41, 36, 50, 46, 34, 82, 67, 51, 12, 5, 16, 74, 9, 3, 59, 8, 52, 47, 14, 70, 15, 31, 75, 60, 1, 21, 20, 44, 54, 81, 13, 32, 2, 63, 7, 78, 24, 53, 40, 30, 77, 45, 37, 10, 42, 17, 38, 48, 66, 73, 49, 72, 4, 39, 23, 56, 6, 11, 18, 22, 55, 71, 58, 68, 26, 28, 25, 62, 65, 80, 33, 35, 29, 83, 0, 76, 69, 19, 64, 57, 61, 27], [39, 15, 41, 20, 43, 1, 45, 74, 81, 79, 72, 61, 33, 26, 0, 23, 77, 48, 54, 47, 66, 28, 44, 37, 13, 4, 32, 17, 29, 30, 49, 3, 69, 2, 53, 19, 31, 68, 51, 65, 7, 56, 58, 71, 60, 6, 8, 63, 70, 22, 25, 55, 42, 24, 78, 21, 40, 80, 67, 83, 9, 38, 52, 57, 46, 62, 10, 50, 12, 34, 75, 14, 82, 11, 16, 73, 35, 18, 5, 36, 59, 76, 27, 64]], '86': [[43, 19, 72, 76, 77, 49, 44, 53, 51, 18, 59, 54, 32, 35, 61, 81, 48, 15, 27, 20, 78, 42, 75, 14, 68, 13, 31, 16, 40, 58, 69, 84, 80, 3, 39, 82, 4, 67, 79, 2, 46, 28, 37, 73, 12, 66, 47, 33, 10, 5, 55, 25, 50, 85, 1, 38, 22, 57, 45, 62, 34, 30, 9, 65, 36, 23, 71, 64, 52, 41, 17, 11, 0, 83, 29, 60, 21, 8, 6, 74, 26, 56, 70, 7, 63, 24], [46, 49, 41, 0, 55, 20, 70, 33, 51, 50, 39, 9, 74, 40, 25, 56, 62, 80, 37, 21, 4, 22, 11, 52, 44, 48, 65, 61, 72, 58, 53, 59, 82, 66, 73, 42, 28, 2, 7, 64, 78, 13, 1, 26, 38, 5, 69, 18, 8, 6, 27, 54, 68, 63, 67, 60, 24, 45, 47, 75, 84, 71, 3, 35, 10, 29, 81, 57, 16, 14, 19, 77, 36, 85, 30, 17, 76, 79, 23, 43, 32, 15, 31, 12, 83, 34], [43, 42, 41, 36, 47, 49, 4, 67, 54, 8, 81, 20, 56, 34, 13, 65, 72, 24, 45, 51, 74, 14, 57, 26, 2, 76, 23, 63, 30, 46, 1, 68, 84, 78, 21, 83, 28, 17, 55, 71, 44, 32, 79, 39, 64, 27, 15, 75, 0, 3, 35, 62, 48, 33, 53, 5, 22, 50, 19, 77, 66, 59, 7, 11, 38, 82, 61, 37, 60, 29, 73, 18, 52, 80, 40, 31, 9, 6, 85, 12, 25, 16, 10, 69, 58, 70]], '88': [[41, 79, 30, 18, 49, 5, 47, 16, 57, 53, 50, 23, 52, 36, 58, 33, 1, 24, 71, 19, 28, 48, 13, 17, 74, 0, 60, 45, 73, 64, 32, 75, 15, 22, 81, 55, 76, 66, 68, 63, 77, 84, 31, 21, 44, 20, 12, 35, 37, 46, 2, 43, 7, 8, 67, 65, 51, 42, 87, 29, 59, 70, 14, 69, 62, 26, 61, 9, 3, 72, 11, 4, 25, 83, 40, 27, 34, 39, 80, 54, 38, 6, 85, 56, 10, 86, 82, 78], [41, 63, 43, 12, 45, 65, 64, 84, 39, 53, 82, 15, 57, 26, 18, 1, 81, 48, 58, 29, 17, 68, 77, 79, 87, 62, 32, 27, 47, 76, 51, 5, 42, 38, 6, 31, 72, 16, 21, 7, 22, 2, 46, 35, 70, 10, 55, 69, 73, 60, 36, 59, 83, 66, 23, 25, 86, 56, 37, 33, 85, 78, 67, 19, 3, 50, 30, 9, 49, 80, 52, 14, 61, 34, 74, 4, 54, 13, 24, 44, 20, 71, 28, 0, 40, 8, 75, 11], [48, 81, 43, 30, 49, 41, 47, 60, 29, 28, 68, 3, 78, 84, 9, 19, 59, 12, 1, 61, 73, 42, 27, 85, 26, 76, 32, 13, 70, 80, 2, 33, 6, 8, 25, 75, 4, 46, 15, 51, 55, 38, 72, 35, 52, 58, 56, 45, 7, 16, 24, 53, 71, 66, 34, 83, 31, 14, 18, 57, 17, 20, 10, 67, 36, 50, 69, 87, 23, 0, 63, 37, 44, 79, 39, 11, 74, 54, 21, 82, 65, 77, 40, 22, 5, 64, 62, 86]], '90': [[45, 5, 14, 24, 81, 51, 36, 1, 53, 70, 49, 22, 46, 18, 85, 77, 20, 78, 71, 48, 12, 76, 75, 23, 54, 28, 31, 11, 38, 47, 41, 33, 40, 4, 13, 8, 88, 82, 35, 63, 42, 55, 39, 66, 72, 43, 17, 73, 56, 2, 29, 84, 34, 52, 59, 87, 62, 50, 3, 10, 30, 64, 67, 7, 86, 15, 69, 27, 44, 60, 21, 74, 68, 57, 37, 83, 58, 0, 6, 32, 9, 65, 79, 61, 80, 25, 89, 16, 26, 19], [45, 55, 43, 20, 25, 84, 64, 41, 53, 32, 71, 11, 68, 15, 27, 51, 38, 56, 83, 13, 86, 70, 77, 17, 6, 40, 31, 37, 14, 34, 73, 59, 62, 75, 21, 46, 36, 79, 5, 0, 28, 35, 49, 8, 82, 4, 47, 76, 12, 88, 63, 66, 50, 61, 29, 72, 26, 39, 9, 2, 44, 58, 33, 48, 78, 42, 3, 57, 60, 18, 7, 54, 16, 19, 69, 89, 24, 22, 65, 67, 30, 87, 52, 74, 81, 1, 23, 80, 10, 85], [41, 73, 43, 12, 31, 51, 8, 71, 57, 0, 15, 60, 70, 72, 63, 27, 10, 26, 29, 28, 58, 82, 7, 68, 44, 56, 69, 47, 30, 6, 79, 42, 4, 80, 59, 67, 76, 3, 37, 61, 48, 25, 75, 18, 40, 14, 87, 13, 66, 20, 1, 36, 86, 55, 19, 38, 64, 53, 81, 83, 2, 33, 45, 9, 54, 24, 89, 78, 22, 85, 11, 35, 74, 49, 77, 23, 84, 52, 62, 65, 16, 50, 46, 32, 17, 39, 21, 5, 88, 34]], '92': [[43, 5, 4, 30, 54, 17, 49, 68, 39, 55, 74, 57, 64, 14, 69, 3, 46, 22, 25, 73, 62, 66, 47, 1, 42, 16, 37, 75, 67, 88, 12, 11, 6, 70, 56, 51, 28, 78, 48, 27, 18, 10, 82, 9, 36, 8, 86, 59, 53, 24, 79, 21, 76, 44, 60, 87, 65, 2, 13, 41, 89, 32, 80, 61, 35, 20, 23, 83, 72, 90, 50, 33, 38, 34, 63, 52, 71, 19, 45, 91, 31, 58, 40, 26, 29, 7, 85, 77, 81, 84, 15, 0], [50, 13, 45, 68, 51, 67, 8, 48, 89, 55, 32, 63, 71, 36, 23, 3, 53, 18, 91, 25, 10, 54, 83, 41, 78, 22, 81, 75, 73, 2, 34, 11, 28, 88, 38, 59, 57, 44, 35, 79, 60, 72, 82, 43, 19, 70, 16, 21, 42, 12, 47, 1, 46, 58, 30, 37, 26, 80, 85, 65, 56, 74, 17, 15, 87, 84, 66, 9, 62, 64, 49, 69, 76, 52, 86, 20, 27, 33, 14, 90, 7, 4, 77, 61, 5, 6, 0, 31, 29, 39, 24, 40], [43, 3, 45, 16, 54, 53, 49, 42, 29, 23, 12, 63, 39, 78, 33, 55, 70, 0, 15, 75, 81, 22, 65, 5, 60, 58, 28, 35, 71, 66, 27, 41, 85, 64, 19, 7, 30, 56, 82, 59, 1, 80, 88, 67, 50, 36, 17, 61, 57, 74, 18, 37, 90, 62, 4, 31, 72, 8, 68, 83, 2, 24, 11, 69, 14, 86, 9, 47, 51, 34, 77, 89, 20, 40, 32, 52, 6, 25, 91, 10, 38, 26, 79, 76, 87, 44, 46, 21, 84, 48, 73, 13]], '94': [[43, 63, 86, 52, 47, 53, 36, 59, 55, 18, 79, 45, 88, 26, 25, 8, 10, 89, 13, 9, 64, 81, 85, 6, 72, 38, 73, 33, 2, 32, 57, 1, 60, 39, 31, 14, 54, 66, 75, 65, 12, 24, 7, 40, 42, 3, 93, 61, 68, 20, 87, 74, 80, 34, 29, 50, 78, 62, 19, 70, 92, 16, 11, 48, 46, 17, 69, 30, 76, 44, 21, 28, 22, 58, 91, 37, 4, 41, 27, 51, 84, 0, 90, 15, 67, 71, 82, 83, 77, 49, 5, 23, 56, 35], [47, 75, 45, 64, 93, 92, 34, 83, 55, 36, 69, 5, 86, 23, 3, 60, 26, 66, 13, 84, 18, 16, 35, 81, 70, 29, 19, 30, 58, 73, 79, 38, 76, 87, 53, 31, 54, 6, 67, 48, 56, 41, 77, 85, 24, 50, 1, 27, 4, 44, 57, 49, 10, 2, 91, 15, 20, 8, 65, 59, 12, 74, 21, 14, 62, 68, 33, 78, 72, 88, 51, 9, 80, 0, 89, 42, 40, 28, 11, 43, 32, 7, 37, 46, 71, 39, 52, 63, 90, 17, 25, 82, 22, 61], [43, 69, 45, 58, 67, 53, 4, 27, 74, 28, 75, 56, 80, 41, 17, 50, 8, 68, 57, 77, 24, 72, 55, 9, 92, 86, 25, 87, 22, 11, 83, 63, 76, 35, 71, 20, 2, 51, 5, 18, 40, 82, 89, 48, 66, 91, 93, 54, 64, 13, 23, 47, 0, 60, 39, 3, 34, 42, 65, 46, 14, 59, 79, 21, 12, 6, 61, 19, 32, 88, 31, 10, 78, 85, 7, 70, 26, 1, 37, 30, 84, 16, 81, 38, 44, 52, 49, 73, 36, 33, 29, 15, 62, 90]], '96': [[52, 7, 60, 76, 53, 1, 51, 84, 41, 57, 18, 27, 25, 90, 21, 19, 47, 4, 13, 31, 56, 6, 26, 63, 69, 22, 35, 39, 94, 46, 42, 33, 54, 86, 67, 59, 2, 44, 49, 77, 72, 68, 73, 81, 9, 80, 83, 93, 65, 10, 87, 45, 78, 20, 40, 23, 43, 8, 62, 79, 24, 36, 15, 95, 89, 74, 16, 5, 37, 14, 71, 29, 66, 48, 34, 75, 38, 58, 50, 32, 30, 85, 92, 12, 61, 82, 64, 3, 28, 11, 17, 55, 0, 88, 91, 70], [52, 51, 47, 50, 53, 83, 40, 2, 59, 57, 68, 67, 65, 86, 10, 15, 19, 70, 39, 79, 3, 72, 82, 13, 6, 8, 11, 81, 69, 34, 1, 49, 74, 80, 42, 31, 56, 4, 32, 55, 92, 76, 20, 73, 17, 28, 35, 89, 16, 36, 93, 95, 64, 94, 30, 9, 84, 66, 21, 33, 14, 48, 60, 43, 61, 26, 78, 85, 77, 46, 18, 25, 29, 88, 38, 37, 91, 62, 5, 23, 44, 71, 54, 58, 87, 22, 0, 24, 7, 41, 45, 12, 63, 75, 27, 90], [49, 69, 47, 74, 56, 52, 51, 90, 11, 27, 16, 63, 57, 70, 85, 83, 50, 30, 23, 43, 40, 2, 46, 77, 91, 62, 5, 75, 88, 80, 25, 59, 78, 24, 17, 41, 20, 92, 53, 93, 13, 48, 0, 3, 79, 22, 8, 45, 87, 26, 21, 61, 81, 68, 36, 67, 89, 82, 35, 9, 38, 34, 66, 55, 10, 60, 15, 71, 28, 72, 42, 33, 58, 32, 6, 65, 37, 54, 1, 7, 31, 76, 19, 95, 4, 84, 94, 39, 73, 29, 18, 12, 44, 14, 64, 86]], '98': [[49, 27, 26, 60, 7, 55, 30, 23, 57, 64, 77, 93, 14, 63, 35, 31, 68, 89, 67, 72, 88, 32, 5, 11, 24, 19, 85, 8, 46, 90, 91, 37, 50, 84, 43, 21, 62, 53, 59, 39, 0, 74, 95, 38, 92, 40, 73, 54, 66, 1, 3, 52, 44, 87, 75, 2, 6, 10, 33, 61, 28, 9, 83, 17, 48, 42, 41, 58, 34, 94, 69, 12, 22, 56, 97, 82, 76, 18, 65, 13, 36, 86, 51, 79, 16, 20, 70, 71, 96, 29, 80, 78, 45, 4, 81, 15, 47, 25], [49, 73, 47, 8, 95, 51, 56, 25, 57, 32, 85, 38, 46, 82, 97, 11, 12, 27, 23, 2, 50, 90, 91, 45, 66, 4, 59, 21, 76, 62, 5, 87, 42, 28, 9, 29, 0, 83, 33, 67, 40, 61, 79, 10, 68, 14, 55, 63, 96, 16, 41, 30, 78, 54, 15, 39, 22, 31, 69, 93, 48, 75, 35, 58, 20, 52, 77, 71, 24, 13, 81, 60, 44, 92, 1, 74, 64, 19, 53, 26, 6, 17, 89, 94, 86, 37, 3, 80, 70, 72, 65, 34, 36, 7, 43, 88, 18, 84], [52, 81, 47, 72, 87, 55, 94, 59, 56, 80, 5, 15, 0, 49, 29, 73, 44, 24, 71, 89, 50, 13, 23, 58, 42, 8, 3, 77, 46, 57, 53, 12, 40, 93, 83, 86, 22, 34, 19, 97, 66, 51, 35, 70, 74, 18, 21, 43, 92, 33, 45, 84, 76, 25, 61, 91, 64, 85, 67, 78, 90, 48, 1, 4, 32, 65, 27, 10, 54, 69, 75, 9, 82, 26, 79, 96, 38, 30, 31, 95, 14, 20, 39, 68, 60, 2, 63, 16, 28, 36, 62, 7, 41, 88, 11, 17, 6, 37]], '100': [[47, 29, 44, 60, 51, 9, 53, 48, 99, 59, 98, 77, 33, 4, 96, 79, 62, 10, 3, 55, 80, 20, 45, 73, 5, 66, 97, 83, 16, 76, 92, 21, 17, 64, 70, 37, 71, 46, 49, 25, 61, 84, 86, 19, 91, 30, 72, 23, 34, 8, 87, 15, 81, 90, 32, 31, 36, 38, 13, 69, 1, 18, 27, 75, 88, 74, 7, 11, 35, 24, 56, 65, 52, 40, 68, 85, 94, 82, 41, 39, 14, 0, 95, 28, 67, 63, 50, 78, 26, 42, 57, 43, 93, 22, 12, 89, 6, 2, 58, 54], [47, 11, 49, 84, 58, 87, 32, 92, 35, 59, 46, 69, 64, 60, 10, 17, 0, 42, 9, 45, 66, 22, 62, 5, 71, 86, 65, 31, 52, 8, 77, 29, 96, 28, 56, 75, 19, 26, 37, 61, 91, 44, 79, 1, 53, 74, 57, 99, 30, 4, 94, 39, 20, 80, 78, 85, 73, 68, 23, 97, 38, 90, 95, 55, 41, 76, 2, 27, 50, 54, 70, 63, 67, 98, 36, 93, 88, 12, 15, 7, 3, 34, 72, 21, 33, 82, 40, 14, 89, 24, 16, 18, 43, 81, 6, 13, 83, 25, 51, 48], [54, 1, 49, 66, 55, 81, 53, 84, 93, 75, 96, 51, 16, 36, 37, 63, 32, 64, 91, 45, 97, 38, 5, 9, 62, 90, 76, 71, 47, 48, 82, 21, 0, 30, 10, 73, 43, 34, 17, 95, 18, 26, 31, 69, 41, 78, 7, 77, 89, 56, 72, 65, 13, 44, 92, 67, 60, 88, 80, 11, 23, 74, 6, 33, 83, 28, 4, 25, 40, 52, 50, 19, 68, 70, 87, 79, 57, 24, 98, 61, 15, 58, 8, 99, 29, 14, 3, 20, 42, 85, 39, 59, 86, 94, 2, 46, 35, 22, 27, 12]], '104': [[53, 69, 64, 78, 60, 83, 55, 58, 45, 61, 90, 21, 82, 48, 75, 59, 26, 0, 85, 97, 7, 14, 88, 63, 23, 12, 56, 1, 46, 96, 93, 95, 51, 36, 101, 89, 65, 80, 32, 11, 79, 86, 91, 99, 20, 28, 31, 67, 10, 50, 37, 39, 5, 94, 25, 49, 84, 2, 35, 41, 98, 54, 42, 77, 81, 72, 9, 103, 62, 44, 87, 13, 71, 24, 40, 19, 33, 18, 70, 3, 73, 74, 68, 27, 100, 6, 38, 102, 76, 16, 92, 17, 30, 43, 4, 34, 15, 57, 22, 8, 52, 66, 47, 29], [53, 55, 51, 40, 57, 101, 46, 18, 13, 61, 64, 17, 0, 68, 103, 85, 94, 28, 93, 21, 77, 98, 14, 9, 25, 2, 80, 39, 70, 6, 65, 81, 91, 60, 54, 1, 19, 88, 84, 89, 52, 12, 24, 5, 97, 34, 32, 47, 3, 20, 23, 83, 49, 36, 33, 29, 96, 26, 27, 43, 58, 4, 37, 35, 102, 56, 69, 59, 41, 22, 63, 75, 73, 42, 100, 67, 8, 30, 16, 45, 87, 62, 38, 99, 66, 78, 90, 50, 44, 76, 71, 95, 72, 31, 86, 10, 7, 74, 15, 82, 79, 11, 92, 48], [49, 47, 51, 92, 57, 7, 55, 38, 81, 65, 28, 93, 54, 14, 33, 17, 52, 62, 96, 1, 70, 98, 101, 99, 41, 88, 4, 91, 61, 80, 45, 13, 50, 6, 3, 39, 79, 20, 10, 19, 90, 2, 44, 35, 34, 26, 12, 21, 59, 56, 72, 63, 48, 84, 78, 83, 36, 82, 87, 27, 75, 16, 67, 37, 53, 102, 97, 29, 42, 32, 66, 11, 15, 60, 30, 69, 100, 76, 25, 31, 85, 18, 89, 23, 43, 8, 73, 68, 40, 71, 58, 94, 5, 64, 95, 103, 0, 24, 46, 74, 77, 86, 9, 22]], '106': [[53, 9, 36, 68, 69, 59, 20, 43, 61, 0, 49, 21, 94, 54, 67, 51, 64, 87, 89, 75, 80, 19, 13, 76, 60, 4, 31, 90, 22, 12, 81, 71, 78, 56, 55, 18, 100, 10, 101, 48, 24, 1, 29, 58, 42, 105, 45, 41, 72, 74, 11, 65, 70, 16, 99, 5, 6, 92, 79, 83, 52, 50, 93, 77, 88, 38, 95, 23, 86, 28, 47, 8, 102, 3, 85, 62, 32, 103, 25, 66, 84, 14, 37, 15, 40, 98, 63, 104, 46, 44, 39, 35, 96, 34, 2, 33, 91, 17, 27, 30, 7, 97, 82, 57, 26, 73], [53, 3, 51, 90, 55, 9, 34, 49, 61, 10, 57, 42, 18, 89, 91, 95, 58, 12, 79, 54, 0, 76, 47, 64, 14, 32, 17, 97, 104, 99, 71, 96, 68, 85, 77, 43, 26, 13, 1, 33, 28, 70, 93, 21, 72, 37, 31, 36, 94, 74, 25, 41, 78, 101, 73, 20, 30, 98, 45, 6, 44, 88, 69, 52, 86, 75, 27, 23, 80, 16, 29, 50, 62, 11, 15, 83, 38, 40, 63, 87, 8, 92, 103, 56, 102, 67, 81, 2, 84, 19, 39, 66, 4, 48, 59, 105, 65, 22, 24, 46, 82, 5, 7, 35, 100, 60], [49, 81, 51, 50, 35, 59, 0, 65, 8, 52, 9, 74, 14, 98, 57, 88, 46, 75, 97, 39, 80, 60, 99, 40, 96, 30, 85, 63, 90, 70, 55, 103, 36, 12, 61, 47, 24, 5, 95, 100, 54, 28, 7, 1, 58, 62, 27, 102, 92, 93, 37, 94, 56, 77, 23, 71, 22, 86, 17, 29, 16, 19, 69, 53, 64, 6, 87, 26, 76, 68, 91, 20, 34, 79, 89, 101, 78, 42, 73, 31, 82, 2, 45, 15, 72, 10, 21, 38, 104, 84, 13, 33, 4, 43, 44, 83, 25, 18, 48, 32, 41, 3, 105, 11, 66, 67]], '110': [[55, 75, 66, 34, 77, 61, 46, 1, 63, 52, 99, 104, 106, 86, 91, 78, 24, 37, 109, 29, 88, 45, 31, 23, 8, 18, 49, 108, 2, 50, 59, 53, 48, 27, 51, 22, 28, 68, 85, 80, 62, 95, 57, 87, 0, 41, 83, 74, 90, 4, 107, 25, 38, 98, 71, 97, 14, 60, 79, 73, 56, 105, 39, 47, 58, 9, 5, 81, 32, 92, 101, 72, 20, 16, 103, 19, 6, 69, 33, 93, 54, 64, 11, 43, 76, 96, 67, 82, 26, 102, 65, 7, 12, 3, 13, 17, 10, 36, 30, 42, 44, 84, 35, 21, 94, 70, 89, 100, 15, 40], [55, 23, 53, 66, 5, 52, 70, 51, 63, 62, 107, 84, 40, 19, 61, 87, 82, 57, 29, 85, 34, 68, 41, 94, 56, 83, 109, 98, 18, 93, 91, 108, 96, 78, 25, 16, 26, 30, 59, 36, 42, 102, 65, 69, 0, 81, 97, 88, 22, 80, 105, 89, 12, 20, 71, 4, 50, 74, 95, 106, 58, 92, 99, 21, 28, 86, 39, 47, 32, 46, 75, 73, 38, 43, 7, 101, 10, 2, 11, 14, 72, 24, 13, 67, 6, 35, 15, 104, 8, 49, 103, 3, 54, 48, 77, 37, 64, 100, 60, 31, 1, 33, 76, 45, 9, 44, 27, 17, 90, 79], [58, 89, 53, 98, 63, 61, 70, 107, 40, 86, 31, 33, 96, 76, 81, 9, 62, 46, 55, 13, 66, 82, 97, 56, 10, 4, 49, 32, 78, 23, 1, 109, 6, 57, 95, 88, 38, 67, 25, 29, 90, 42, 47, 41, 20, 87, 5, 79, 54, 64, 93, 21, 84, 35, 101, 94, 14, 102, 105, 108, 36, 103, 65, 48, 30, 73, 39, 83, 50, 51, 69, 75, 8, 27, 85, 34, 80, 106, 71, 91, 92, 12, 15, 2, 68, 43, 45, 60, 104, 28, 99, 7, 18, 44, 59, 24, 72, 100, 37, 16, 22, 26, 74, 11, 77, 0, 19, 17, 52, 3]]}

if __name__ == "__main__":
    verify_all()
