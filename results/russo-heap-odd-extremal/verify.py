r"""Verify the odd-n extremal Heap-type construction (arXiv:2611.22780v1, Sec. 10 item 2).

Conventions follow Russo: positions 1..n, a swap (i j) multiplies the state on the
left, the array equals the one-line form of the inverse state, and products act
right to left: (p*q)(x) = p(q(x)).

Construction for odd n >= 5:
  * levels 2..n-2 use the cyclic schedule of the paper;
  * level n-1 parks 1, n-2, 2, n-3, ..., (n-3)/2, (n+1)/2, (n-1)/2;
  * level n parks e_1..e_{n-1}, where (n e_1 ... e_{n-1}) = Z'^{-1} T and Z' is the
    level n-1 net. Closed forms for both orders are checked below.

Part A simulates the recursion directly for n = 3, 5, 7, 9 and does not use any
theorem from the paper. Part B checks the closed-form permutation identities of the
proof for all odd n up to N_ALGEBRA, using Theorem 18(b) of the paper.
"""
import sys
from itertools import permutations

N_SIM = (3, 5, 7, 9)
N_ALGEBRA = 1201


def require(cond, msg):
    if not cond:
        sys.stderr.write("FAIL: " + msg + "\n")
        sys.exit(1)


# ---------- permutations as tuples p[0..n], p[0] = 0 ----------
def ident(n):
    return tuple(range(n + 1))


def mul(p, q):
    return tuple(p[q[x]] for x in range(len(p)))


def inv(p):
    r = [0] * len(p)
    for x in range(len(p)):
        r[p[x]] = x
    return tuple(r)


def from_cycle(n, seq):
    p = list(range(n + 1))
    for i, a in enumerate(seq):
        p[a] = seq[(i + 1) % len(seq)]
    return tuple(p)


def orbit(p, s):
    out = [s]
    x = p[s]
    while x != s:
        out.append(x)
        x = p[x]
    return out


def power(p, k):
    r = ident(len(p) - 1)
    b = p
    while k:
        if k & 1:
            r = mul(r, b)
        b = mul(b, b)
        k >>= 1
    return r


def target_state(n):
    """T = inverse of the lexicographically largest odd arrangement a*_n."""
    t = [0] + [n + 1 - v for v in range(1, n + 1)]
    if n % 4 in (0, 1):
        t[1], t[2] = n - 1, n
    return tuple(t)


def target_array(n):
    if n % 4 in (2, 3):
        return tuple(range(n, 0, -1))
    return tuple(range(n, 2, -1)) + (1, 2)


def is_odd_perm(arr):
    seen, sign = set(), 0
    for s in range(len(arr)):
        if s in seen:
            continue
        L, x = 0, s
        while x not in seen:
            seen.add(x)
            x = arr[x] - 1
            L += 1
        sign ^= (L - 1) & 1
    return sign == 1


# ---------- closed forms used in the proof ----------
def penult_order(n):
    """Level n-1 parking order: 1, n-2, 2, n-3, ..., (n-3)/2, (n+1)/2, (n-1)/2."""
    h = (n - 3) // 2
    out = []
    for x in range(1, h + 1):
        out += [x, n - 1 - x]
    return out + [(n - 1) // 2]


def top_order(n):
    """Level n parking order: the orbit of n under Z, minus n."""
    hi = list(range(n - 1, (n + 1) // 2 - 1, -1))      # n-1 .. (n+1)/2
    a = (n + 1) // 2 - 2                                # continue by steps of -2
    run1 = list(range(a, 0, -2))
    run2 = list(range((n - 1) // 2, 0, -2))
    return hi + run1 + run2


def Zp_closed(n):
    p = list(range(n + 1))
    for x in range(1, (n - 3) // 2 + 1):
        p[x] = n - 1 - x
    for x in range((n + 1) // 2, n):
        p[x] = n - x
    p[(n - 1) // 2] = n - 1
    return tuple(p)


def Z_closed(n):
    z = [0] * (n + 1)
    for v in range(3, (n + 1) // 2 + 1):
        z[v] = v - 2
    for v in range((n + 3) // 2, n + 1):
        z[v] = v - 1
    if n % 4 == 3:
        z[1], z[2] = n, (n - 1) // 2
    else:
        z[1], z[2] = (n - 1) // 2, n
    return tuple(z)


# ---------- Part A: direct simulation of the recursion ----------
def cyclic_schedule(k):
    if k % 2 == 1:
        return [1] * (k - 1)
    if k == 2:
        return [1]
    return [k - 1] + list(range(2, k - 1)) + [1]


def run(arr, k, sched, out):
    """Russo's Heap(k) on the global list arr (0-based storage, 1-based positions)."""
    if k == 1:
        if out is not None:
            out.append(tuple(arr))
        return
    run(arr, k - 1, sched, out)
    for i in range(k - 1):
        j = sched[k][i]
        require(1 <= j <= k - 1, "schedule entry out of range")
        arr[j - 1], arr[k - 1] = arr[k - 1], arr[j - 1]
        run(arr, k - 1, sched, out)


def schedule_from_order(k, sched, order):
    """Level-k schedule realising a parking order, found by running one call on 1..k:
    before round m the partner is the current position of item order[m]."""
    arr = list(range(1, k + 1))
    run(arr, k - 1, sched, None)
    s = []
    for item in order:
        pos = arr.index(item) + 1
        require(pos != k, "parked item already at the last position")
        s.append(pos)
        arr[pos - 1], arr[k - 1] = arr[k - 1], arr[pos - 1]
        run(arr, k - 1, sched, None)
    return s


def simulate(n):
    sched = {k: cyclic_schedule(k) for k in range(2, n + 1)}
    if n >= 5:
        sched[n - 1] = schedule_from_order(n - 1, sched, penult_order(n))
        sched[n] = schedule_from_order(n, sched, top_order(n))
    out = []
    arr = list(range(1, n + 1))
    run(arr, n, sched, out)
    f = 1
    for i in range(2, n + 1):
        f *= i
    require(len(out) == f, "n=%d: %d outputs, expected %d" % (n, len(out), f))
    require(len(set(out)) == f, "n=%d: repeated arrangement" % n)
    for a, b in zip(out, out[1:]):
        require(sum(x != y for x, y in zip(a, b)) == 2, "n=%d: step is not one swap" % n)
    require(out[0] == tuple(range(1, n + 1)), "n=%d: wrong start" % n)
    require(out[-1] == target_array(n), "n=%d: final %r" % (n, out[-1]))
    # a*_n is the lexicographically largest odd permutation (Prop. 21 of the paper)
    if n <= 7:
        best = max(p for p in permutations(range(1, n + 1)) if is_odd_perm(p))
        require(best == target_array(n), "n=%d: a*_n is not the largest odd arrangement" % n)
    return sched


# ---------- Part B: algebraic identities for all odd n ----------
def check_algebra(n):
    T = target_state(n)
    # Net of the cyclic levels at odd level n-2 is (1 n-2); level n-1 net by Thm 18(b).
    C = from_cycle(n, [1, n - 2])
    e1 = penult_order(n)
    require(sorted(e1) == list(range(1, n - 1)), "n=%d: penult order not a permutation" % n)
    Zp = mul(power(C, n - 1), from_cycle(n, [n - 1] + e1))
    require(Zp == Zp_closed(n), "n=%d: closed form of Z' wrong" % n)
    require(len(orbit(Zp, 1)) == n - 1 and Zp[n] == n, "n=%d: Z' not an (n-1)-cycle" % n)
    for x in range(1, (n - 3) // 2 + 1):
        require(Zp[Zp[x]] == x + 1, "n=%d: Z'^2(x) != x+1" % n)
    Z = mul(power(inv(Zp), n), T)
    require(Z == mul(inv(Zp), T), "n=%d: Z'^n != Z'" % n)
    require(Z == Z_closed(n), "n=%d: closed form of Z wrong" % n)
    orb = orbit(Z, n)
    require(len(orb) == n, "n=%d: Z is not an n-cycle" % n)
    require(orb[1:] == top_order(n), "n=%d: top order mismatch" % n)
    # Thm 18(b): level-n net = Zp^n * Z must equal T
    require(mul(power(Zp, n), Z) == T, "n=%d: top net != T" % n)


def main():
    for n in N_SIM:
        simulate(n)
        print("simulated n=%d: %s" % (n, "".join(str(x) for x in target_array(n))))
    for n in range(5, N_ALGEBRA + 1, 2):
        check_algebra(n)
    print("closed-form identities checked for odd 5 <= n <= %d" % N_ALGEBRA)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
