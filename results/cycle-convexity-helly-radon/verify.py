r"""Verification script for the disproof of Conjecture 1 in cycle convexity
(Nair, Anand, Chandran S. V., Nascimento, Anil, arXiv:2609.34236v1, Section 5).

Conjecture 1: for every connected graph G of order n >= 2, hl_cc(G) = rd_cc(G).

Counterexample graph G16 (n = 16, m = 36):
- Three cliques K^(i) = K_5 (i in {0, 1, 2}) on vertices
    s_i = 5i, t_i = 5i + 1, u_i = 5i + 2, p_i = 5i + 3, q_i = 5i + 4;
- One central hub x = 15 adjacent to u_0 = 2, u_1 = 7, u_2 = 12;
- Three cyclic port edges p_i - q_{(i+1) mod 3}: (3, 9), (8, 14), (13, 4).

We verify exhaustively over all 2^16 = 65,536 vertex subsets:
1. G16 is connected with n = 16 vertices and m = 36 edges.
2. The cycle-interval operator matches direct cycle search on all subsets of size <= 3.
3. For every A subseteq S = {0, 1, 5, 6, 10, 11}, Hull_cc(A) matches the closed formula W_A.
4. S is Radon independent (and convexly independent) with unique Helly point {x}.
5. hl_cc(G16) = 5 (exhaustive over all 65,536 sets, witnessed by {0, 1, 5, 6, 10}).
6. rd_cc(G16) = 6 (level-wise exhaustive + direct check of all C(16, 7) = 11,440 7-sets).
7. Every Helly-independent set on G16 is Radon independent (Levi inequality sanity check).

Standalone, stdlib-only, -O safe (uses require(), zero assert statements).
"""
import sys
from itertools import combinations


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


N_V = 16
X = 15
EDGES = []
for i in range(3):
    clique = list(range(5 * i, 5 * i + 5))
    EDGES += [(a, b) for a in clique for b in clique if a < b]
    EDGES.append((5 * i + 2, X))
for i in range(3):
    EDGES.append((5 * i + 3, 5 * ((i + 1) % 3) + 4))

ADJ = [0] * N_V
for a, b in EDGES:
    ADJ[a] |= 1 << b
    ADJ[b] |= 1 << a
FULL = (1 << N_V) - 1


def components(mask):
    comps = []
    rem = mask
    while rem:
        c = rem & -rem
        frontier = c
        while frontier:
            v = (frontier & -frontier).bit_length() - 1
            frontier &= frontier - 1
            nb = ADJ[v] & mask & ~c
            c |= nb
            frontier |= nb
        comps.append(c)
        rem &= ~c
    return comps


def cycle_interval(mask):
    comps = components(mask)
    add = 0
    for w in range(N_V):
        if not ((mask >> w) & 1):
            for c in comps:
                if (ADJ[w] & c).bit_count() >= 2:
                    add |= 1 << w
                    break
    return mask | add


def cycle_hull(mask):
    cur = mask
    while True:
        nxt = cycle_interval(cur)
        if nxt == cur:
            return cur
        cur = nxt


def bits(mask):
    return [i for i in range(N_V) if (mask >> i) & 1]


def on_cycle_with(w, mask):
    nbrs = bits(ADJ[w] & mask)
    for a, b in combinations(nbrs, 2):
        seen = 1 << a
        frontier = 1 << a
        while frontier:
            v = (frontier & -frontier).bit_length() - 1
            frontier &= frontier - 1
            nb = ADJ[v] & mask & ~seen
            seen |= nb
            frontier |= nb
        if (seen >> b) & 1:
            return True
    return False


def main():
    require(len(EDGES) == 36, "expected 36 edges")
    require(len(set(tuple(sorted(e)) for e in EDGES)) == 36, "duplicate edge")
    require(len(components(FULL)) == 1, "G16 must be connected")

    for k in range(1, 4):
        for subset in combinations(range(N_V), k):
            m = sum(1 << v for v in subset)
            alt = m | sum(1 << w for w in range(N_V) if not ((m >> w) & 1) and on_cycle_with(w, m))
            require(alt == cycle_interval(m), "cycle interval mismatch")
    print("check 0 ok: G16 connected (n=16, m=36); cycle-interval rule cross-checked")

    hulls = [cycle_hull(m) for m in range(1 << N_V)]
    print("computed hulls for all 65536 vertex subsets")

    s_list = [0, 1, 5, 6, 10, 11]
    s_mask = sum(1 << v for v in s_list)

    def is_radon_indep(mask):
        el = bits(mask)
        if len(el) <= 1:
            return True
        low = 1 << el[0]
        rest = mask & ~low
        t = rest
        while True:
            a = low | t
            b = mask & ~a
            if b and (hulls[a] & hulls[b]):
                return False
            if t == 0:
                break
            t = (t - 1) & rest
        return True

    def helly_intersection(mask):
        inter = FULL
        for a in bits(mask):
            inter &= hulls[mask & ~(1 << a)]
        return inter

    require(is_radon_indep(s_mask), "witness S must be Radon independent")
    require(helly_intersection(s_mask) == (1 << X), "S must have unique Helly point {x}")
    for a in s_list:
        require(not ((hulls[s_mask & ~(1 << a)] >> a) & 1), "S must be convexly independent")

    for sub in range(1 << 6):
        am = sum(1 << s_list[j] for j in range(6) if (sub >> j) & 1)
        full_cliques = [i for i in range(3) if ((am >> (5 * i)) & 1) and ((am >> (5 * i + 1)) & 1)]
        expected = am
        for i in full_cliques:
            expected |= 0b11111 << (5 * i)
        if len(full_cliques) >= 2:
            expected |= 1 << X
        require(hulls[am] == expected, "closed hull formula failed on subset of S")
    print("check 1 ok: witness S = {0,1,5,6,10,11} verified (Radon independent, closed hull formula exact)")

    hel = 0
    hel_witness = 0
    for m in range(1, 1 << N_V):
        c = m.bit_count()
        if c > hel and helly_intersection(m) == 0:
            hel = c
            hel_witness = m
    require(hel == 5, f"expected hl_cc(G16) = 5, got {hel}")
    h5_mask = sum(1 << v for v in [0, 1, 5, 6, 10])
    require(helly_intersection(h5_mask) == 0, "witnessH5 = {0,1,5,6,10} must be Helly independent")
    print(f"check 2 ok: hl_cc(G16) = 5 (exhaustive over 65536 sets), witness {bits(hel_witness)}")

    level = [1 << v for v in range(N_V)]
    rindep = set(level)
    rad = 1
    while level:
        nxt = set()
        for m in level:
            for v in range(N_V):
                if not ((m >> v) & 1):
                    u = m | (1 << v)
                    if u in nxt:
                        continue
                    if all((u & ~(1 << a)) in rindep for a in bits(u)) and is_radon_indep(u):
                        nxt.add(u)
        if nxt:
            rad += 1
            rindep |= nxt
        level = list(nxt)
    require(rad == 6, f"expected rd_cc(G16) = 6, got {rad}")
    require(s_mask in rindep, "S must be in Radon-independent sets")

    count7 = 0
    for subset in combinations(range(N_V), 7):
        m = sum(1 << v for v in subset)
        require(not is_radon_indep(m), "unexpected Radon-independent 7-set")
        count7 += 1
    require(count7 == 11440, "expected 11440 7-sets")
    print(f"check 3 ok: rd_cc(G16) = 6 (exhaustive; all {count7} 7-sets Radon dependent)")

    for m in range(1, 1 << N_V):
        if m.bit_count() <= 6 and helly_intersection(m) == 0:
            require(m in rindep, "Helly-independent set must be Radon independent")
    print("check 4 ok: Helly independent => Radon independent verified on G16")
    print(f"hl_cc(G16) = {hel} < {rad} = rd_cc(G16)")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
