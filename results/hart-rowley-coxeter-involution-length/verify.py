r"""Standalone verification script for the disproof of Hart-Rowley Conjecture 1.3
(S. B. Hart and P. J. Rowley, arXiv:2502.00777v1 / Archiv der Mathematik 2026).

Conjecture 1.3: assuming Conjecture 1.2 (the Ancestor Conjecture, proved for all Coxeter
groups by Gaetz and Gao, arXiv:2610.22857), every element w of a finite Coxeter group W
has involution length ilen(w) <= rank(W).

This script builds H3 (order 120, rank 3) over Q(sqrt(5)) and F4 (order 1152, rank 4)
and E6 (order 51840, rank 6) over Z, and verifies:
  1. |W| matches the classical group order and inversion count on positive roots equals
     BFS word length for every element of W.
  2. Conjecture 1.2 (unique longest involution prefix) holds for every w != 1 in H3, F4, E6.
  3. Direct definition-level prefix scans (u prefix of w <=> l(u) + l(u^{-1} w) = l(w))
     verify explicit witnesses violating Conjecture 1.3:
       - H3 (rank 3): w1 = r2 r3 r1 r2 r3 r2 r1 -> (r2 r3 r1 r2)(r3)(r2)(r1), ilen = 4 > 3;
                      w2 = r2 r3 r2 r3 r1 r2 r3 -> (r2 r3 r2)(r3 r1)(r2)(r3), ilen = 4 > 3;
       - F4 (rank 4): w = r3 r4 r1 r2 r3 r2 r1 -> (r3 r1)(r4 r2)(r3)(r2)(r1), ilen = 5 > 4;
       - E6 (rank 6): w = r3 r2 r4 r5 r6 r1 r3 r4 r5 r2 r4 r3 r1, ilen = 8 > 6.
  4. Exact maximum involution lengths: max ilen(H3) = 4, max ilen(F4) = 5, max ilen(E6) = 8.

Standalone, stdlib-only, -O safe (uses require(), zero assert statements).
"""
from fractions import Fraction as Fr
import sys


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def mul(x, y):
    return (x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def sign(x):
    a, b = x
    if a >= 0 and b >= 0:
        return 0 if (a == 0 and b == 0) else 1
    if a <= 0 and b <= 0:
        return -1
    d = a * a - 5 * b * b
    return (1 if a > 0 else -1) if d > 0 else (-1 if a > 0 else 1)


def num(a, b=0):
    return (Fr(a), Fr(b))


ZERO = num(0)


class CoxeterGroup:
    def __init__(self, name, cartan_mat, expected_order):
        n = len(cartan_mat)
        self.name = name
        self.n = n

        def refl(i, v):
            c = ZERO
            for j in range(n):
                c = add(c, mul(cartan_mat[i][j], v[j]))
            return tuple(add(v[k], mul(num(-1), c)) if k == i else v[k] for k in range(n))

        simple = [tuple(num(1) if j == i else ZERO for j in range(n)) for i in range(n)]
        pos = list(simple)
        seen = set(simple)
        frontier = list(simple)
        while frontier:
            nxt = []
            for v in frontier:
                for i in range(n):
                    w = refl(i, v)
                    if w not in seen and all(sign(x) >= 0 for x in w):
                        seen.add(w)
                        pos.append(w)
                        nxt.append(w)
            frontier = nxt
        for v in pos:
            require(any(sign(x) > 0 for x in v), "zero root encountered")
        all_roots = pos + [tuple(mul(num(-1), x) for x in v) for v in pos]
        idx = {v: k for k, v in enumerate(all_roots)}
        self.num_pos = len(pos)
        for v in all_roots:
            for i in range(n):
                require(refl(i, v) in idx, "root system not closed under reflections")
        self.gens = [tuple(idx[refl(i, v)] for v in all_roots) for i in range(n)]
        e = tuple(range(2 * self.num_pos))
        self.e = e

        self.elts = [e]
        self.eid = {e: 0}
        self.word_len = [0]
        frontier = [e]
        while frontier:
            nxt = []
            for w in frontier:
                wid = self.eid[w]
                for s in range(n):
                    u = self.compose(w, self.gens[s])
                    if u not in self.eid:
                        self.eid[u] = len(self.elts)
                        self.elts.append(u)
                        self.word_len.append(self.word_len[wid] + 1)
                        nxt.append(u)
            frontier = nxt
        require(len(self.elts) == expected_order, f"{name}: |W| = {len(self.elts)}, expected {expected_order}")
        self.lengths = [sum(1 for r in range(self.num_pos) if w[r] >= self.num_pos) for w in self.elts]
        require(self.lengths == self.word_len, f"{name}: inversion count != word length")
        self.inv = [self.eid[self.inverse_perm(w)] for w in self.elts]
        self.is_inv = [k != 0 and self.inv[k] == k for k in range(len(self.elts))]

    @staticmethod
    def compose(p, q):
        return tuple(p[x] for x in q)

    @staticmethod
    def inverse_perm(p):
        out = [0] * len(p)
        for i, x in enumerate(p):
            out[x] = i
        return tuple(out)

    def elt(self, word_1based):
        w = self.e
        for s in word_1based:
            w = self.compose(w, self.gens[s - 1])
        return self.eid[w]

    def times(self, a, b):
        return self.eid[self.compose(self.elts[a], self.elts[b])]

    def involution_prefixes(self, w):
        lw = self.lengths[w]
        return [
            u for u in range(len(self.elts))
            if self.is_inv[u] and self.lengths[u] + self.lengths[self.times(self.inv[u], w)] == lw
        ]

    def ancestor_decomposition(self, w):
        out = []
        while w != 0:
            ip = self.involution_prefixes(w)
            require(bool(ip), f"{self.name}: no involution prefix")
            m = max(self.lengths[u] for u in ip)
            top = [u for u in ip if self.lengths[u] == m]
            require(len(top) == 1, f"{self.name}: ancestor not unique")
            out.append(top[0])
            w = self.times(top[0], w)
        return out

    def check_all_and_max_ilen(self):
        order = sorted(range(len(self.elts)), key=lambda k: self.lengths[k])
        anc = [0] * len(self.elts)
        ilen = [0] * len(self.elts)
        for k in order[1:]:
            if self.is_inv[k]:
                anc[k] = k
                ilen[k] = 1
                continue
            w = self.elts[k]
            cands = set()
            for s in range(self.n):
                if w[s] >= self.num_pos:
                    cands.add(anc[self.eid[self.compose(w, self.gens[s])]])
            m = max(self.lengths[c] for c in cands)
            top = [c for c in cands if self.lengths[c] == m]
            require(len(top) == 1, f"{self.name}: Conjecture 1.2 failed")
            a = top[0]
            rem = self.times(a, k)
            require(self.lengths[rem] + self.lengths[a] == self.lengths[k], f"{self.name}: length not additive")
            anc[k] = a
            ilen[k] = ilen[rem] + 1
        return max(ilen)

    def reduced_word(self, k):
        out = []
        w = self.elts[k]
        while self.eid[w] != 0:
            for s in range(self.n):
                if w[s] >= self.num_pos:
                    out.append(s + 1)
                    w = self.compose(w, self.gens[s])
                    break
        return out[::-1]


def cartan(n, edges):
    mat = [[num(2) if i == j else ZERO for j in range(n)] for i in range(n)]
    for i, j, a, b in edges:
        mat[i][j] = num(a)
        mat[j][i] = num(b)
    return mat


def main():
    golden = (Fr(-1, 2), Fr(-1, 2))
    h3_mat = [[num(2), num(-1), ZERO], [num(-1), num(2), golden], [ZERO, golden, num(2)]]
    f4_mat = cartan(4, [(0, 1, -1, -1), (1, 2, -2, -1), (2, 3, -1, -1)])
    e6_mat = cartan(6, [(0, 2, -1, -1), (2, 3, -1, -1), (3, 4, -1, -1), (1, 3, -1, -1), (4, 5, -1, -1)])

    cases = [
        ("H3", h3_mat, 120, 3, [[2, 3, 1, 2, 3, 2, 1], [2, 3, 2, 3, 1, 2, 3]], 4),
        ("F4", f4_mat, 1152, 4, [[3, 4, 1, 2, 3, 2, 1], [4, 2, 3, 1, 2, 3, 4]], 5),
        ("E6", e6_mat, 51840, 6, [[3, 2, 4, 5, 6, 1, 3, 4, 5, 2, 4, 3, 1]], 8),
    ]

    for name, mat, expected_order, rank, witnesses, expected_max in cases:
        group = CoxeterGroup(name, mat, expected_order)
        for wd in witnesses:
            w = group.elt(wd)
            require(group.lengths[w] == len(wd), f"{name}: witness word not reduced")
            dec = group.ancestor_decomposition(w)
            words = [group.reduced_word(a) for a in dec]
            require(len(dec) > rank, f"{name}: witness does not violate Conjecture 1.3")
            prod = 0
            for a in dec:
                prod = group.times(prod, a)
            require(prod == w and sum(group.lengths[a] for a in dec) == group.lengths[w], "decomposition mismatch")
            fmt_w = "".join(f"r{s}" for s in wd)
            fmt_dec = " ".join("(" + "".join(f"r{s}" for s in x) + ")" for x in words)
            print(f"{name}: w = {fmt_w} (length {group.lengths[w]}): ancestors {fmt_dec} -> ilen {len(dec)} > rank {rank}")
        mx = group.check_all_and_max_ilen()
        require(mx == expected_max, f"{name}: max ilen = {mx}, expected {expected_max}")
        print(f"{name}: |W| = {expected_order}, Conjecture 1.2 holds for all w != 1, max ilen = {mx} > rank {rank}")

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
