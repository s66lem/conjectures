#!/usr/bin/env python3
"""Standalone exact Q verifier (Python 3 stdlib only, safe under `python -O`)
for the disproof of Sinclair's Conjecture C (arXiv:2608.18519).

Implements the definitions of Section 2 (Propositions 2.2-2.3) and Appendix B
literally in the flat basis using `fractions.Fraction`:
  - Reproduces Example 3.2 (K_5: H^0 = (1,10,20,10,1), H_beta = (1,11,25,10,1)).
  - Checks D_beta(v_j) = j * v_{j-1} on every layer.
  - Verifies exact H^0 and H_beta for M(K_{1,1,m} + e) for m = 4, 5, 6 (and
    confirms Conjecture C fails for every one) plus the 12-element binary example.
"""

from fractions import Fraction
from itertools import combinations
from math import factorial
import sys


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def gf2_rank(cols: list[int]) -> int:
    basis = []
    for c in cols:
        for b in basis:
            c = min(c, c ^ b)
        if c:
            basis.append(c)
    return len(basis)


def compute_hilbert(vecs: list[str]) -> tuple[list[int], list[int], list[int]]:
    col = [int(v, 2) for v in vecs]
    n = len(col)
    require(all(col) and len(set(col)) == n, "Matroid is not simple")

    def rk(S) -> int:
        return gf2_rank([col[i] for i in S])

    r = rk(range(n))

    def cl(S) -> frozenset[int]:
        k = rk(S)
        return frozenset(e for e in range(n) if rk(list(S) + [e]) == k)

    layers = [{frozenset()}]
    for j in range(r):
        layers.append({cl(set(x) | {a}) for x in layers[j] for a in range(n) if a not in x})
    layers = [sorted(L, key=sorted) for L in layers]
    W = [len(L) for L in layers]

    beta = {}
    for j, L in enumerate(layers):
        for x in L:
            nb = sum(1 for B in combinations(sorted(x), j) if rk(B) == j)
            beta[x] = factorial(j) * nb

    cov = {}
    for j in range(1, r + 1):
        for x in layers[j - 1]:
            for a in range(n):
                if a not in x:
                    cov.setdefault((cl(set(x) | {a}), a), []).append(x)

    def lower(vec: dict, a: int) -> dict:
        out = {}
        for y, c in vec.items():
            for x in cov.get((y, a), ()):
                out[x] = out.get(x, Fraction(0)) + c * Fraction(beta[x], beta[y])
        return out

    def D_op(vec: dict, j: int) -> dict:
        tot = {}
        for a in range(n):
            for x, c in lower(vec, a).items():
                tot[x] = tot.get(x, Fraction(0)) + c
        return {x: c * j / (n - len(x)) for x, c in tot.items() if n - len(x)}

    # Verify the defining radial identity D_beta(v_j) = j * v_{j-1}
    for j in range(1, r + 1):
        vj = {x: Fraction(beta[x]) for x in layers[j]}
        lhs = D_op(vj, j)
        rhs = {x: Fraction(j * beta[x]) for x in layers[j - 1]}
        require(lhs == rhs, f"Radial identity failed at rank {j}")

    def rowreduce(vs: list[dict], j: int) -> list[dict]:
        rows = [[v.get(x, Fraction(0)) for x in layers[j]] for v in vs]
        basis, piv = [], []
        for row in rows:
            row = row[:]
            for b, p in zip(basis, piv):
                if row[p]:
                    f = row[p]
                    row = [s - f * t for s, t in zip(row, b)]
            p = next((i for i, t in enumerate(row) if t), None)
            if p is None:
                continue
            inv = Fraction(1, 1) / row[p]
            row = [t * inv for t in row]
            for bi in range(len(basis)):
                if basis[bi][p]:
                    f = basis[bi][p]
                    basis[bi] = [s - f * t for s, t in zip(basis[bi], row)]
            basis.append(row)
            piv.append(p)
        return [{x: c for x, c in zip(layers[j], b) if c} for b in basis]

    res = {}
    for with_D in (False, True):
        top = layers[r][0]
        C = [{top: Fraction(beta[top])}]
        h = [1]
        for k in range(r):
            j = r - k
            gens = [lower(v, a) for v in C for a in range(n)]
            if with_D:
                gens += [D_op(v, j) for v in C]
            C = rowreduce(gens, j - 1)
            h.append(len(C))
        res[with_D] = h

    h_beta, h0 = res[True], res[False]
    for k in range(r + 1):
        require(h0[k] == h0[r - k], f"H^0 not symmetric at k={k}")
        require(h0[k] <= h_beta[k] <= W[r - k], f"Prop. 2.7 bound violated at k={k}")
    return h_beta, h0, W


def graph_vectors(edges: list[tuple[int, int]]) -> list[str]:
    nv = 1 + max(max(e) for e in edges)
    return ["".join("1" if v in e else "0" for v in range(nv)) for e in edges]


def book_plus_edge(m: int) -> list[tuple[int, int]]:
    return [(0, 1)] + [(i, j) for i in (0, 1) for j in range(2, 2 + m)] + [(2, 3)]


BINARY_12 = [
    "011010", "001101", "000100", "001000", "100000", "011111",
    "010010", "010000", "111111", "010111", "010011", "000111",
]


def main() -> None:
    # 1. Benchmark against Sinclair Example 3.2 (M(K_5))
    h_k5, h0_k5, _ = compute_hilbert(graph_vectors(list(combinations(range(5), 2))))
    require(h0_k5 == [1, 10, 20, 10, 1] and h_k5 == [1, 11, 25, 10, 1], "K_5 mismatch")

    # 2. Primary counterexample M(K_{1,1,4} + e) and family m = 5, 6
    expected = {
        4: ([1, 11, 31, 32, 10, 1], [1, 10, 27, 27, 10, 1]),
        5: ([1, 13, 48, 74, 49, 12, 1], [1, 12, 42, 62, 42, 12, 1]),
        6: ([1, 15, 68, 143, 149, 69, 14, 1], [1, 14, 60, 117, 117, 60, 14, 1]),
    }
    ms = [int(a) for a in sys.argv[1:]] or [4, 5, 6]
    for m in ms:
        hb, h0, _ = compute_hilbert(graph_vectors(book_plus_edge(m)))
        if m in expected:
            require((hb, h0) == expected[m], f"Unexpected H_beta for m={m}: {hb}, {h0}")
        r = len(hb) - 1
        fails = [(k, hb[k], hb[r - k]) for k in range(r // 2 + 1) if hb[k] < hb[r - k]]
        require(bool(fails), f"Expected Conjecture C failure for m={m}")

    # 3. Non-graphic 12-element rank-6 binary counterexample
    hb_bin, h0_bin, _ = compute_hilbert(BINARY_12)
    require(
        hb_bin == [1, 13, 50, 94, 51, 12, 1] and h0_bin == [1, 12, 44, 66, 44, 12, 1],
        f"Binary example mismatch: {hb_bin}",
    )

    print(
        "PASS: reproduced K_5 Example 3.2, verified radial identity D_beta(v_j)=j*v_{j-1}, "
        "and confirmed exact Q Conjecture C failures for M(K_{1,1,m}+e) (m=4,5,6; "
        "at m=4: h_2=31 < 32=h_3) and the 12-element rank-6 binary matroid (h_2=50 < 51=h_4)."
    )


if __name__ == "__main__":
    main()
