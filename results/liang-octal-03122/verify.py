r"""Standalone certificate for Liang, arXiv:2611.29198v1, Conjecture 4.1 (misere octal game 0.3122).

Rules of 0.3122: from one heap h you may remove the whole heap if h is 1 or 2,
or replace h by h - k with k in {1, 3, 4} if h > k. Heaps never split. Misere play:
the empty position is N, and a position is N iff some option is P.

Family F: multisets of at most four positive heaps, at most two of which exceed 2.
F is closed under moves. Write a position canonically as (h1, h2, h3, h4) with
h1 >= h2 >= h3 >= h4 >= 0 (zeros = absent heaps) and h3, h4 <= 2.

Claimed outcome function Phi: reduce (h1, h2) by
  rho1: (h1, h2) -> (h1 - 7, h2 - 7)  while h2 >= D + 7,
  rho2: (h1, h2) -> (h1 - 7, h2)      while h1 - h2 >= G + 7 and h1 >= C + 7,
then read the exact outcome from a finite table. The script checks:
  (1) the finite table is the true misere outcome (exact DP);
  (2) Phi satisfies the misere recursion on the finite window
      W = {h2 < D + 11 and (h1 - h2 < G + 11 or h1 < C + 11)}; positions outside W
      reduce to W by the translation lemma in PROOF.md, so Phi = o on all of F;
  (3) on the canonical domain, o(2, 2, x, y) for x, y >= 3 depends only on
      (x mod 7, y mod 7, [|x - y| <= 4]), and rho1/rho2 preserve that key;
  (4) the literal statement fails: o(2, 2, 7, 2) = N but o(2, 2, 14, 2) = P.

Run with: python -O -W error verify.py
"""
import sys

REM = (1, 2)
SUB = (1, 3, 4)
D, G, C = 13, 5, 8


def require(cond, msg):
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def canon(heaps):
    hs = sorted((h for h in heaps if h > 0), reverse=True)
    return tuple(hs + [0] * (4 - len(hs)))


def options(t):
    out = set()
    for i, h in enumerate(t):
        if h == 0 or (i and t[i - 1] == h):
            continue
        rest = t[:i] + t[i + 1:]
        if h in REM:
            out.add(canon(rest))
        for k in SUB:
            if h > k:
                out.add(canon(rest + (h - k,)))
    return out


def in_family(t):
    return len(t) == 4 and t[2] <= 2 and t[3] <= 2


def exact_table(hmax):
    r"""Exact misere outcomes (True = P) for every family position with h1 <= hmax."""
    pos = [canon((a, b, c, d))
           for a in range(hmax + 1) for b in range(a + 1)
           for c in range(3) for d in range(3)]
    pos = sorted(set(pos), key=sum)
    P = {}
    for t in pos:
        if t == (0, 0, 0, 0):
            P[t] = False
            continue
        P[t] = not any(P[o] for o in options(t))
    return P


def reduce_pair(h1, h2):
    if h2 >= D + 7:
        i = (h2 - D) // 7
        h1, h2 = h1 - 7 * i, h2 - 7 * i
    while h1 - h2 >= G + 7 and h1 >= C + 7:
        h1 -= 7
    return h1, h2


def main():
    require(3 <= D and 5 <= G and C <= D + G, "threshold side conditions")
    L = max(D + G + 26, C + 15)
    P = exact_table(L)

    def phi(t):
        h1, h2 = reduce_pair(t[0], t[1])
        r = (h1, h2, t[2], t[3])
        require(r in P, "reduced position outside table: %r" % (r,))
        return P[r]

    # Sanity: Liang's Theorem 3.7, o(2,2,h,h) = P and o(2,2,h+1,h) = N.
    for h in range(0, L - 1):
        require(P[canon((2, 2, h, h))], "Thm 3.7 diagonal fails at h=%d" % h)
        require(not P[canon((2, 2, h + 1, h))], "Thm 3.7 superdiagonal fails at h=%d" % h)

    # (1)+(2) Phi agrees with exact DP and satisfies the misere recursion on W.
    nW = 0
    for t in P:
        require(phi(t) == P[t], "Phi differs from exact outcome at %r" % (t,))
        h1, h2 = t[0], t[1]
        if h2 < D + 11 and (h1 - h2 < G + 11 or h1 < C + 11):
            nW += 1
            opts = options(t)
            require(all(in_family(o) for o in opts), "family not closed at %r" % (t,))
            want = (t != (0, 0, 0, 0)) and not any(phi(o) for o in opts)
            require(phi(t) == want, "recursion fails for Phi at %r" % (t,))
    require(max(D + G + 22, C + 11) <= L, "table does not cover W")

    # (3) Conjecture 4.1 for x, y >= 3 on the canonical domain.
    key_val = {}
    canon_pairs = 0
    for x in range(3, L + 1):
        for y in range(3, x + 1):
            if (x, y) != reduce_pair(x, y):
                continue
            canon_pairs += 1
            v = P[canon((2, 2, x, y))]
            for (a, b) in ((x, y), (y, x)):
                k = (a % 7, b % 7, abs(a - b) <= 4)
                require(key_val.setdefault(k, v) == v, "Conj 4.1 conflict at %r" % ((a, b),))
    require(len(key_val) == 98, "expected 98 keys, got %d" % len(key_val))

    base = {(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (1, 6), (6, 1), (2, 4), (4, 2), (3, 5), (5, 3)}
    for (r1, r2, band), v in key_val.items():
        extra = {(0, 0), (4, 4)} if band else {(0, 4), (4, 0)}
        require(v == ((r1, r2) in base | extra), "closed form wrong at %r" % ((r1, r2, band),))
    require(G >= 5, "rho2 could enter the band |x - y| <= 4")

    # (4) Literal statement fails for heaps of size 2.
    require(not P[canon((2, 2, 7, 2))], "o(2, 2, 7, 2) should be N")
    require(P[canon((2, 2, 14, 2))], "o(2, 2, 14, 2) should be P")

    # Extra check: Phi = exact DP on h1 <= 120.
    P2 = exact_table(120)
    for t, v in P2.items():
        require(phi(t) == v, "large-window mismatch at %r" % (t,))

    print("OK: D=%d G=%d C=%d, table h1<=%d (%d positions), |W|=%d, canonical (2,2,x,y) pairs=%d, keys=%d"
          % (D, G, C, L, len(P), nW, canon_pairs, len(key_val)))
    print("OK: o(2,2,7,2)=N, o(2,2,14,2)=P; Phi matches exact DP for h1<=120 (%d positions)" % len(P2))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
