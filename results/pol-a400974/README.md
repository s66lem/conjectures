# Proof of Omar E. Pol's OEIS A400974, A280940, and A384225 Conjectures

**Status:** All four conjectures proved for every integer $n \ge 1$ — **100% Lean 4 verified** (zero `sorry`, zero custom axioms, zero `native_decide`), cross-model audited (`claude-sonnet-5-5`).

**Preprint:** [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24556521.svg)](https://doi.org/10.5281/zenodo.24556521)

## Target Conjectures

1. **[OEIS A400974](https://oeis.org/A400974)** (Omar E. Pol, Oct 11 2026):
   > *Number of terms in the central 2-dense sublist of divisors of $n$, or $0$ if such a sublist does not exist.*
   > *Conjecture: $a(n) = \text{A001511}(n) \cdot \text{A384230}(n)$.*
2. **[OEIS A280940](https://oeis.org/A280940)** (Omar E. Pol, Jan 13 2026):
   > *Irregular triangle read by rows: $T(n,k)$ is the number of subparts in the $k$-th part of the symmetric representation of $\sigma(n)$.*
   > *Conjecture: $T(n,k)$ is the number of odd numbers in the $k$-th 2-dense sublist of divisors of $n$.*
3. **[OEIS A384225](https://oeis.org/A384225) Conjecture 1** (Omar E. Pol, Oct 13 2026):
   > *Conjecture 1: this is a duplicate of $\text{A280940}$.*
4. **[OEIS A384225](https://oeis.org/A384225) Conjecture 2** (Omar E. Pol, Oct 13 2026):
   > *Conjecture 2: $T(n,k) = \text{A384222}(n,k) / \text{A001511}(n)$.*

## Main Result

Let $n \ge 1$ be any positive integer, write $n = 2^v m$ with $m$ odd ($v = v_2(n)$, so $\text{A001511}(n) = v + 1$), and partition the sorted positive divisors of $n$ into maximal $2$-dense blocks $B_1, \dots, B_t$ (splitting whenever consecutive divisors satisfy $e' > 2e$). Let $P_1, \dots, P_s$ be the parts (maximal positive runs) of the width word $\text{A262045}(n)$ of the symmetric representation of $\sigma(n)$. Then for every $n \ge 1$:

1. $s = t$, and for every $1 \le k \le t$, the number of width-one layer subparts in $P_k$ equals the number of odd divisors in $B_k$:
   $$\text{A280940}(n, k) = \text{A384225}(n, k).$$
2. For every $1 \le k \le t$, every odd divisor $d \in B_k$ carries its full dyadic chain $\{d, 2d, \dots, 2^v d\}$ inside $B_k$, so
   $$\text{A384222}(n, k) = |B_k| = (v_2(n) + 1) \cdot \text{A384225}(n, k) = \text{A001511}(n) \cdot \text{A384225}(n, k).$$
3. Extracting the middle entry (or $0$ when the number of parts/blocks is even) gives
   $$\text{A400974}(n) = \text{A001511}(n) \cdot \text{A384230}(n).$$

## Proof Summary

Set $Q = 2^{v+1}$ so that $2n = Qm$, and define the interval-counting function
$$W_n(x) = \#\{d \mid m : d \le x < Q d\}.$$
- **Width-word identification:** For $1 \le k \le r = \lfloor(\sqrt{8n+1}-1)/2\rfloor$, the alternating partial sum $\text{A249223}(n, k)$ equals $W_n(k)$, because the indicator $\text{A237048}(n, j)$ equals $1$ on $[1, r]$ precisely when $j \mid m$ (odd, contributing $+1$) or $j = Qd$ with $d \mid m$ (even, contributing $-1$).
- **Reversal & stutter compression:** The involution $d \mapsto m/d$ proves $W_n(2n/e) = W_n(e - 1)$ for every divisor $e \mid 2n$. Pairing jump points $e \leftrightarrow 2n/e$ shows that the stutter-compressed full width word $\text{A262045}(n)$ coincides with the stutter-compressed sampling $[W_n(1), \dots, W_n(2n-1)]$.
- **Exact block correspondence:** Each half-open interval $[d, Qd)$ splits into the $v+1$ dyadic intervals $[2^i d, 2^{i+1} d)$, so $W_n(x) > 0$ if and only if $x \in [e, 2e)$ for some divisor $e \mid n$. Consequently, the maximal positive runs of $W_n$ on $[1, 2n-1]$ are precisely the intervals $[a_k, 2c_k)$ spanned by the maximal $2$-dense blocks $B_k$ (with minimum $a_k$ and maximum $c_k$), separated by nonempty zero gaps $[2c_k, a_{k+1})$.
- **Layer-run identity:** For any list $p$ of nonnegative integers, summing maximal runs of height $\ge h$ over $h \ge 1$ equals the total upward rise $\sum_i \max(0, p_i - p_{i-1})$ (with $p_{-1} = 0$), which is invariant under stutter compression. On $[a_k, 2c_k)$, $W_n$ rises by $+1$ precisely at odd divisors $d \mid m$ in $[a_k, 2c_k)$, which are exactly the odd divisors in $B_k$. Finally, since consecutive elements $2^i d, 2^{i+1} d$ satisfy ratio $2$, each odd divisor $d \in B_k$ contributes its entire dyadic chain $\{2^i d : 0 \le i \le v\}$ of size $v+1 = \text{A001511}(n)$ to $B_k$.

## Files

- [PROOF.md](PROOF.md) — complete self-contained mathematical proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/pol-a400974/verify.py`).
- [PolA400974.lean](../../lean/Conjectures/PolA400974.lean) — complete Lean 4 formalization (`lake build Conjectures.PolA400974`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
