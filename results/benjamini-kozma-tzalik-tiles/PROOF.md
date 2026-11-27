# Complete Proof: Tiles of $\mathbb{Z}$ Inside $\{1, 2, 4, \dots, 2^n\}$ (Benjamini–Kozma–Tzalik, EJC 33(3) #P3.28, Question 9)

## 1. Problem Statement

In *The number of tiles of $\mathbb{Z}^d$*, *Electron. J. Combin.* **33(3)** (2026), #P3.28 (`arXiv:2303.07956v2`, Section 3; Question 13 in v1, 2023), I. Benjamini, G. Kozma, and E. Tzalik define a subset $S \subset \mathbb{Z}$ to *tile $\mathbb{Z}$ by translations* if there exists $T \subset \mathbb{Z}$ such that $\mathbb{Z} = \bigsqcup_{t \in T} (S + t)$, and ask:

> **Question 9.** How many tiles are contained in the set $\{1, 2, 4, \dots, 2^n\}$? Are the only such tiles the sets of size $1$ and $2$?

## 2. Disproof of the Second Part (`bkt_q9_disproof`)

**Theorem 1.** The $3$-element set $S = \{1, 4, 16\} \subset \{1, 2, 4, 8, 16\}$ tiles $\mathbb{Z}$ with tiling complement $T = \{-1, 0, 1\} + 9\mathbb{Z}$. Consequently, $\{1, 2, \dots, 2^n\}$ contains a tile of size $3$ for every $n \ge 4$, answering the second part of Question 9 in the negative.

**Proof.** Reducing $S + \{-1, 0, 1\}$ modulo $9$ gives $\{0, 1, 2\} \cup \{3, 4, 5\} \cup \{6, 7, 8\} = \mathbb{Z}/9\mathbb{Z}$ with no repeats. Therefore every integer $z \in \mathbb{Z}$ admits a unique representation $z = s + t$ with $s \in \{1, 4, 16\}$ and $t \in \{-1, 0, 1\} + 9\mathbb{Z}$. $\blacksquare$

## 3. Complete Exact Size Spectrum (`power_of_two_tile_size_iff`)

**Theorem 2.** A finite subset $S \subset \{2^j : j \ge 0\}$ of cardinality $k$ tiles $\mathbb{Z}$ **if and only if** $k \in \{1, 2\}$ or $k$ is **odd**.

### 3.1. Existence for $k \in \{1, 2\}$ and Every Odd $k \ge 1$ (`odd_size_power_of_two_tile_exists`)

- $k = 1$: $\{1\} \oplus \mathbb{Z} = \mathbb{Z}$.
- $k = 2$: $\{1, 2\} \oplus 2\mathbb{Z} = \mathbb{Z}$.
- Odd $k \ge 3$: Let $r = \varphi(k) \ge 1$ (or more tightly $r = \mathrm{ord}_{\mathrm{rad}(k)}(2)$), $q = 2^r \ge 2$, and $g = q - 1 \ge 1$. Since $\gcd(2, k) = 1$, Euler's theorem gives $k \mid g$, so every odd prime $p \mid k$ satisfies $p \mid q - 1$.

Define $f(m) = \sum_{j=0}^{m-1} q^j = (q^m - 1)/g$. By lifting-the-exponent (for every odd prime $p \mid q - 1$):
- If $p \nmid m$, then $f(m) \equiv m \not\equiv 0 \pmod{p}$, so $v_p(f(m)) = 0 = v_p(m)$.
- Writing $q^a = 1 + pt$, we have $\sum_{i=0}^{p-1} (1 + pt)^i \equiv p + \binom{p}{2} pt \equiv p \pmod{p^2}$ since $p$ is odd, so $v_p(f(pa)) = v_p(f(a)) + v_p(f_{q^a}(p)) = v_p(f(a)) + 1$.

By strong induction, $v_p(f(m)) = v_p(m)$ for every prime $p \mid k$ and $m \ge 1$, hence $k \mid f(m) \iff k \mid m$. For $0 \le d_1 < d_2 < k$, $f(d_2) - f(d_1) = q^{d_1} f(d_2 - d_1)$; since $\gcd(q^{d_1}, k) = 1$ and $0 < d_2 - d_1 < k$, we have $f(d_1) \not\equiv f(d_2) \pmod{k}$. Thus $\{f(d) : 0 \le d < k\}$ is a complete residue system modulo $k$.

Setting $S_k = \{q^d : 0 \le d < k\} = \{1 + g f(d) : 0 \le d < k\}$ and $T = \{t \in \mathbb{Z} : (t + 1) \bmod (gk) < g\}$, every $z = gu + j$ ($0 \le j < g$) has a unique $d \in \{0, \dots, k-1\}$ with $f(d) \equiv u \pmod{k}$, giving the unique decomposition $z = q^d + (j - 1 + gkw)$ with $q^d \in S_k$ and $j - 1 + gkw \in T$. $\blacksquare$

### 3.2. Impossibility for Every Even $k \ge 4$ (`even_size_ge_four_no_power_of_two_tile`)

1. **Dilation normalization:** Dividing $S$ by its minimum element $2^e$ preserves tiling ($2^e S' \oplus T = \mathbb{Z} \implies S' \oplus \{t : 2^e t \in T\} = \mathbb{Z}$), so we may assume $1 \in S \subset \{2^c : c \ge 0\}$ with $|S| = k$.
2. **Newman periodicity (1977):** Let $D = \max S - \min S$. For every $y \in \mathbb{Z}$, $y \in T$ iff no $s \in S \setminus \{\min S\}$ has $y + \min S - s \in T$ (forward determinism from $T \cap [y - D, y)$), and symmetrically $y \in T$ iff no $s \in S \setminus \{\max S\}$ has $y + \max S - s \in T$ (backward determinism from $T \cap (y, y + D]$). By pigeonhole on the $2^D$ possible indicator windows of length $D$, $T$ is periodic with some period $M > 0$.
3. **Coven–Meyerowitz (T1) prime-power cyclotomic divisibility:** Setting $A = T \cap \{0, \dots, M-1\}$, every residue modulo $M$ occurs uniquely as $(s + a) \bmod M$, so $|S||A| = M$ and $(X^M - 1) \mid (S(X) A(X) - \sum_{r=0}^{M-1} X^r)$ in $\mathbb{Z}[X]$, where $S(X) = \sum_{s \in S} X^s$ and $A(X) = \sum_{a \in A} X^a$. For every prime power $q = p^a \mid M$ ($a \ge 1$), $\Phi_q(X)$ is irreducible over $\mathbb{Q}$, divides $(X^M - 1)/(X - 1)$, and is monic over $\mathbb{Z}$, so $\Phi_q \mid S$ or $\Phi_q \mid A$ in $\mathbb{Z}[X]$. Because $X^M - 1$ is separable over $\mathbb{Q}$, distinct $\Phi_q$ ($q \mid M$) are pairwise coprime over $\mathbb{Q}$, so the monic products $P_S = \prod_{q \in Q_S} \Phi_q$ and $P_A = \prod_{q \in Q_A} \Phi_q$ satisfy $P_S \mid S$ and $P_A \mid A$ in $\mathbb{Z}[X]$. Evaluating at $1$ gives $P_S(1) \mid |S|$, $P_A(1) \mid |A|$, and $M = \prod_{p^a \mid M} p \mid P_S(1) P_A(1) \mid |S||A| = M$, forcing $P_S(1) = |S| = k$. Since $2 \mid k$, some $\Phi_{2^j}(X)$ ($j \ge 1$) divides $S(X)$ in $\mathbb{Z}[X]$.
4. **Obstruction for $\Phi_{2^j}(X) = X^{2^{j-1}} + 1$:** Write $h = 2^{j-1}$ and $S(X) = (X^h + 1) Q(X)$. For any $r < h$ and large $N$, the alternating sum $\sum_{m=0}^{N-1} (-1)^m ((X^h + 1) Q)[mh + r]$ telescopes to $0$.
   - If $j = 1$ ($h = 1, r = 0$), this gives $\#\{s \in S \text{ even}\} - \#\{s \in S \text{ odd}\} = 0$. Since $1$ is the unique odd power of $2$, $|S| = 2$, contradicting $k \ge 4$.
   - If $j \ge 2$ ($h \ge 2$ even, $r = 1 < h$), every $s = 2^c \in S$ with $c \ge 1$ is even so $s \not\equiv 1 \pmod{h}$; only $s = 1$ ($m = 0$) contributes, giving $+1 = 0$, contradiction. $\blacksquare$

## 4. Prime-Size Classification and Exact Counts for $n \le 15$

By Newman's theorem (1977), a prime-size set $S$ with $|S| = p$ tiles $\mathbb{Z}$ iff all pairwise differences share a single $p$-adic valuation. For $S = \{2^c : c \in C\}$ and odd prime $p$ with $r_p = \mathrm{ord}_p(2)$, LTE gives $v_p(2^m - 1) = 0$ if $r_p \nmid m$ and $e_p + v_p(m / r_p)$ if $r_p \mid m$. Since $r_p \le p - 1 < p$, pigeonhole rules out all valuations being $0$, so $S$ tiles $\mathbb{Z}$ iff $C = c_0 + r_p p^t X$ where $X \ni 0$ is a complete residue system modulo $p$. The minimal span is $(p - 1)\,\mathrm{ord}_p(2)$ ($4, 16, 18, 100$ for $p = 3, 5, 7, 11$). More generally, for any odd $k$ divisible by a prime $p$, Coven–Meyerowitz (T1) gives some $\Phi_{p^a} \mid S(X)$ ($a \ge 2$ since $2^c \not\equiv 0 \pmod p$), forcing $p$ exponents in $C$ to be distinct and congruent modulo $\mathrm{ord}_{p^{a-1}}(2) \ge r_p$, so $\max C - \min C \ge (p - 1) r_p$; in particular, $k = 15$ (via $p = 5$) requires span $\ge 16$. Combined with Theorem 2 and exhaustive verification that $k = 9$ requires span $\ge 16$, every tile in $\{1, 2, \dots, 2^n\}$ for $n \le 15$ has size $1$, $2$, or $3$, yielding the exact counts
$$t(0), \dots, t(15) = 1, 3, 6, 10, 16, 23, 31, 40, 51, 63, 78, 94, 112, 131, 153, 176.$$
