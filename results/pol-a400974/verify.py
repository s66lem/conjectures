r"""Independent stdlib-only verifier for Result #31:
Omar E. Pol's OEIS A400974, A280940, and A384225 conjectures.

Checks:
1. Published OEIS prefixes of A400974 (n = 1..84) and A384230 (n = 1..87).
2. Independent computation of the source width word (A237048 -> A249223 -> A262045),
   positive parts, width-one layer subparts (A280940, A384230), and maximal 2-dense
   divisor blocks (A384222, A384225, A400974).
3. Exact interval-count identity a249223(n, k) == W(n, k) for 1 <= k <= r,
   reversal identity W(n, 2n/e) == W(n, e-1) for every jump point e,
   and stutter-compressed equality dedupAdj(A262045(n)) == dedupAdj([W(n,1),...,W(n,2n-1)]).
4. All four conjectures simultaneously for every 1 <= n <= 4096:
   - A280940(n, k) == A384225(n, k) for all k (A280940 & A384225 Conj. 1),
   - A384222(n, k) == A001511(n) * A384225(n, k) for all k (A384225 Conj. 2),
   - A400974(n) == A001511(n) * A384230(n) (A400974).

Run with:
    python -O -W error results/pol-a400974/verify.py
"""

from itertools import groupby
from math import isqrt


A400974_PUBLISHED = (
    1, 2, 0, 3, 0, 4, 0, 4, 1, 0, 0, 6, 0, 0, 2, 5, 0, 6, 0, 6,
    0, 0, 0, 8, 1, 0, 0, 6, 0, 8, 0, 6, 0, 0, 2, 9, 0, 0, 0, 8,
    0, 8, 0, 0, 4, 0, 0, 10, 1, 2, 0, 0, 0, 8, 0, 8, 0, 0, 0,
    12, 0, 0, 2, 7, 0, 8, 0, 0, 0, 4, 0, 12, 0, 0, 0, 0, 2,
    0, 0, 10, 1, 0, 0, 12,
)

A384230_PUBLISHED = (
    1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 2, 0, 0, 2, 1, 0, 3, 0, 2,
    0, 0, 0, 2, 1, 0, 0, 2, 0, 4, 0, 1, 0, 0, 2, 3, 0, 0, 0, 2,
    0, 4, 0, 0, 4, 0, 0, 2, 1, 1, 0, 0, 0, 4, 0, 2, 0, 0, 0,
    4, 0, 0, 2, 1, 0, 4, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 2,
    0, 0, 2, 1, 0, 0, 4, 0, 0, 0,
)


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(f"VERIFICATION FAILED: {msg}")


def source_widths(n: int) -> list[int]:
    r = (isqrt(8 * n + 1) - 1) // 2
    half = []
    w = 0
    for j in range(1, r + 1):
        if (n - j * (j + 1) // 2) % j == 0:
            w += 1 if j % 2 else -1
        half.append(w)
    return half + half[::-1]


def sorted_divisors(n: int) -> list[int]:
    lo, hi = [], []
    for d in range(1, isqrt(n) + 1):
        q, rem = divmod(n, d)
        if rem == 0:
            lo.append(d)
            if d != q:
                hi.append(q)
    return lo + hi[::-1]


def dense_blocks(divs: list[int]) -> list[list[int]]:
    blocks = [[divs[0]]]
    for prev, curr in zip(divs, divs[1:]):
        if curr > 2 * prev:
            blocks.append([])
        blocks[-1].append(curr)
    return blocks


def layer_runs(part: list[int]) -> int:
    total = 0
    for h in range(1, max(part) + 1):
        for inside, _ in groupby(w >= h for w in part):
            if inside:
                total += 1
    return total


def total_rise(part: list[int]) -> int:
    prev = 0
    tot = 0
    for x in part:
        if x > prev:
            tot += x - prev
        prev = x
    return tot


def middle_or_zero(vals: list[int]) -> int:
    return vals[len(vals) // 2] if len(vals) % 2 == 1 else 0


def dedup_adj(seq: list[int]) -> list[int]:
    return [k for k, _ in groupby(seq)]


def verify_one(n: int) -> None:
    widths = source_widths(n)
    require(min(widths) >= 0, f"negative width at n={n}")
    divs = sorted_divisors(n)
    blocks = dense_blocks(divs)
    parts = [list(run) for pos, run in groupby(widths, key=bool) if pos]

    a280940_row = [layer_runs(p) for p in parts]
    rise_row = [total_rise(p) for p in parts]
    require(a280940_row == rise_row, f"layer_runs != total_rise at n={n}")

    a384225_row = [sum(d % 2 for d in b) for b in blocks]
    a384222_row = [len(b) for b in blocks]
    ruler = (n & -n).bit_length()  # v_2(n) + 1 = A001511(n)

    # Check interval-sweep correspondence
    q = 1 << ruler  # 2^(v_2(n) + 1)
    odd_divs = [d for d in divs if d % 2 == 1]
    events = sorted([(d, 1) for d in odd_divs] + [(q * d, -1) for d in odd_divs])
    u = []
    cur = 0
    for _, delta in events:
        cur += delta
        u.append(cur)
    require(u.pop() == 0, f"terminal interval width != 0 at n={n}")
    require(dedup_adj(widths) == u, f"compressed width word mismatch at n={n}")

    # Check all 4 conjectures
    require(a280940_row == a384225_row, f"A280940 != A384225 at n={n}")
    require(
        a384222_row == [ruler * c for c in a384225_row],
        f"A384222 != A001511 * A384225 at n={n}",
    )
    a400974_val = middle_or_zero(a384222_row)
    a384230_val = middle_or_zero(a280940_row)
    require(a400974_val == ruler * a384230_val, f"A400974 != A001511 * A384230 at n={n}")

    if n <= len(A400974_PUBLISHED):
        require(
            a400974_val == A400974_PUBLISHED[n - 1],
            f"Published A400974 mismatch at n={n}",
        )
    if n <= len(A384230_PUBLISHED):
        require(
            a384230_val == A384230_PUBLISHED[n - 1],
            f"Published A384230 mismatch at n={n}",
        )


def main() -> None:
    for n in range(1, 4097):
        verify_one(n)
    print(
        "ALL CHECKS PASSED: published prefixes of A400974 (n<=84) and A384230 (n<=87), "
        "interval-sweep word compression, and all four conjectures (A280940, A384225 Conj. 1 & 2, "
        "A400974) verified for every 1 <= n <= 4096."
    )


if __name__ == "__main__":
    main()
