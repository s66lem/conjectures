# Complete Proof of Conjecture 3 (Wormald's Question) of Ghafari and Wanless (`arXiv:2607.17547v1`)

**Target conjecture.** Conjecture 3 of Afsane Ghafari and Ian M. Wanless, *Latin Squares whose transversals intersect in unusual ways* ([arXiv:2607.17547v1](https://arxiv.org/abs/2607.17547), 20 July 2026), attributed to a question of Nick Wormald:

> Let $n \ge 28$ be an even integer. There is a latin square of order $n$ that has no two disjoint transversals, but also has no pinned entry.

Ghafari and Wanless verified existence computationally for $n = 28$ and $32 \le n \le 10\,000$, leaving $n = 30$ and all even $n > 10\,000$ open.

**Main Theorem.** For every even integer $n \ge 22$ with $n \ne 24$, there exists a Latin square $L$ of order $n$ such that:
1. $L$ has no two disjoint transversals; and
2. $L$ has no pinned entry (witnessed by three transversals $T_0, T_1, T_2$ whose triple intersection $T_0 \cap T_1 \cap T_2$ is empty).

In particular, Conjecture 3 holds for every even integer $n \ge 28$, including $n = 30$ and all even $n > 10\,000$, and our construction also yields the additional orders $n = 22$ and $n = 26$ below $28$ (only $n = 24$, which lies outside Conjecture 3, is excluded by the non-wrapping gadget bound $s_h + 14 < n_0$ below).

---

## 1. Definitions and Basic Lemmas

Let $n$ be an even positive integer, $n = 2m$, and index rows, columns, and symbols by $\mathbb{Z}/n\mathbb{Z} = \{0, 1, \dots, n - 1\}$. A *Latin square* of order $n$ is a function $L : \mathrm{Fin}\,n \times \mathrm{Fin}\,n \to \mathrm{Fin}\,n$ whose rows $c \mapsto L(r, c)$ and columns $r \mapsto L(r, c)$ are bijections. A *transversal* is a bijection $T : \mathrm{Fin}\,n \to \mathrm{Fin}\,n$ such that $r \mapsto L(r, T(r))$ is also a bijection. Two transversals $T_1, T_2$ are *disjoint* if $T_1(r) \ne T_2(r)$ for all $r$. An entry $(r, c)$ is *pinned* if $T(r) = c$ for every transversal $T$ of $L$ (and $L$ admits at least one transversal).

**Lemma 1 (Empty triple intersection rules out pinned entries).** If $L$ admits three transversals $T_0, T_1, T_2$ such that for every row $r$ we do not have $T_0(r) = T_1(r) = T_2(r)$, then $L$ has no pinned entry.

*Proof.* Given any cell $(r, c)$, at least one of $T_0(r), T_1(r), T_2(r)$ differs from $c$, so $(r, c)$ is not contained in every transversal. $\square$

**Lemma 2 ($\Delta$-Sum Lemma).** Let $L(r, c) = (r + c + \Delta(r, c)) \bmod n$ be a Latin square of even order $n = 2m$, where $\Delta : \mathrm{Fin}\,n \times \mathrm{Fin}\,n \to \mathbb{Z}$. For every transversal $T$ of $L$,
$$
  \sum_{r=0}^{n-1} \Delta(r, T(r)) \equiv m \pmod{n}.
$$

*Proof.* Since $r \mapsto T(r)$ and $r \mapsto L(r, T(r))$ are permutations of $\{0, \dots, n - 1\}$, summing $L(r, T(r)) \equiv r + T(r) + \Delta(r, T(r)) \pmod{n}$ over $r$ yields
$$
  \sum_{r=0}^{n-1} \Delta(r, T(r)) \equiv -\sum_{r=0}^{n-1} r = -\frac{n(n - 1)}{2} = -m(2m - 1) \equiv m \pmod{2m}. \quad \square
$$

**Lemma 3 (Three Unique Row-Maxima Imply No Two Disjoint Transversals).** Let $L(r, c) = (r + c + \Delta(r, c)) \bmod n$ be a Latin square of even order $n = 2m$. Suppose there exist integer bounds $\underline{\delta}_r \le \Delta(r, c) \le \overline{\delta}_r$ for all $r, c$ such that:
1. $\sum_{r=0}^{n-1} \overline{\delta}_r = m + 1$;
2. $\sum_{r=0}^{n-1} \underline{\delta}_r > -m$;
3. There exist three distinct rows $r_1, r_2, r_3$ and columns $c_1, c_2, c_3$ such that $\Delta(r_i, c) \le \overline{\delta}_{r_i} - 1$ for every $c \ne c_i$ ($i \in \{1, 2, 3\}$).

Then every transversal $T$ of $L$ hits at least two of the three cells $(r_1, c_1), (r_2, c_2), (r_3, c_3)$. By the pigeonhole principle, no two transversals of $L$ are disjoint.

*Proof.* For any transversal $T$, let $S = \sum_r \Delta(r, T(r))$. By (1) and (2), $-m < S \le m + 1$. By Lemma 2, $S \equiv m \pmod{2m}$, so the unique admissible value is $S = m$. If $T$ misses two distinct cells among $\{(r_1, c_1), (r_2, c_2), (r_3, c_3)\}$, then by (3) the sum drops by at least $2$ below $\sum_r \overline{\delta}_r = m + 1$, giving $S \le m - 1$, a contradiction. Therefore every transversal contains at least two of the three cells, and any two transversals share at least one of them. $\square$

---

## 2. The Modular Latin Square Family $L_{n, n_0}$

Fix an even base order $n_0 \ge 22$ with $n_0 \ne 24$, and an integer $t \ge 0$, and set $n = n_0 + 4t$. Define the even horizontal shift
$$
  s_h := 2 \left\lfloor \frac{n_0 / 2 - 4}{2} \right\rfloor.
$$
Because $n_0 \ge 22$ ($n_0 \ne 24$), we have $4 \le s_h$, $s_h + 14 < n_0$ whenever $n_0 \equiv 2 \pmod 4$, and $s_h + 14 < n_0$ whenever $n_0 \equiv 0 \pmod 4$ (as $n_0 \ge 28$ in the latter case). Consequently, all gadget windows stay strictly inside $[4, n_0 - 1]$ with zero modular wrap-around, and the offset function $\Delta_{n_0}(r, c)$ is independent of $n$.

We assemble $\Delta_{n_0}(r, c)$ from three row-band gadgets:

1. **4-row gadget $A(\mathrm{row}, s, c)$** ($0 \le \mathrm{row} < 4$, even anchor $s$): outside $[s, s + 10]$, $A(\mathrm{row}, s, c) = 2$ if $c$ is odd and $\mathrm{row} < 2$, $-2$ if $c$ is odd and $\mathrm{row} \ge 2$, and $0$ if $c$ is even. Inside $j = c - s \in \{0, \dots, 10\}$, $A(\mathrm{row}, s, s + j)$ is given by the table:

   | $\mathrm{row} \setminus j$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | $\min$ | $\max$ |
   |---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
   | 0 | 0 | 3 | 0 | 0 | 1 | 3 | 0 | 0 | 3 | 0 | 0 | 0 | 3 |
   | 1 | 0 | 1 | 1 | 1 | 2 | 0 | 1 | 2 | 0 | 2 | 0 | 0 | 2 |
   | 2 | 0 | $-2$ | $-1$ | **1** | $-2$ | $-2$ | $-1$ | 0 | $-2$ | $-1$ | 0 | $-2$ | 1 |
   | 3 | 0 | $-2$ | 0 | $-2$ | $-1$ | $-1$ | 0 | $-2$ | $-1$ | $-1$ | 0 | $-2$ | 0 |

   Row maxima sum to $3 + 2 + 1 + 0 = 6$; row minima sum to $-4$. Row 2 attains its maximum $+1$ uniquely at $c = s + 3$.

2. **3-row gadget $B(\mathrm{row}, c_{\mathrm{odd}}, c)$** ($0 \le \mathrm{row} < 3$, odd anchor $c_{\mathrm{odd}}$):
   - at $c = c_{\mathrm{odd}}$: $(1, \mathbf{1}, -2)$;
   - at $c = c_{\mathrm{odd}} + 1$: $(1, -1, 0)$;
   - at other odd $c$: $(2, 0, -2)$;
   - at other even $c$: $(0, 0, 0)$.

   Row maxima sum to $2 + 1 + 0 = 3$; row minima sum to $-3$. Row 1 attains its maximum $+1$ uniquely at $c = c_{\mathrm{odd}}$.

3. **4-row swap block $P$** (rows $0, 1, 2, 3$): rows $0$ and $2$ have $\Delta = +2$ and $-2$ on odd columns (and $0$ on even columns); rows $1$ and $3$ have $\Delta \equiv 0$. Row maxima sum to $2$; row minima sum to $-2$.

We stack these bands as follows:
- **Case $n_0 \equiv 2 \pmod 4$ ($n_0 \ge 22$):**
  - rows $0..3$: $A(\cdot, s_h)$;
  - rows $4..6$: $B(\cdot, s_h + 11)$;
  - rows $7..9$: $B(\cdot, s_h + 13)$;
  - rows $10..n_0 - 13$: $(n_0 - 22)/4$ copies of $P$;
  - rows $n_0 - 12..n_0 - 1$: $12$ untouched rows ($\Delta = 0$);
  - rows $n_0..n - 1$: $t$ tail copies of $P$.
  - Unique row-max cells: $(2, s_h + 3)$, $(5, s_h + 11)$, $(8, s_h + 13)$.
  - $\sum \overline{\delta}_r = 6 + 3 + 3 + 2\cdot\frac{n_0 - 22}{4} + 2t = \frac{n_0}{2} + 2t + 1 = \frac{n}{2} + 1$.
  - $\sum \underline{\delta}_r = -4 - 3 - 3 - 2\cdot\frac{n_0 - 22}{4} - 2t = -\frac{n}{2} + 1 > -\frac{n}{2}$.

- **Case $n_0 \equiv 0 \pmod 4$ ($n_0 \ge 28$):**
  - rows $0..3$: $A(\cdot, s_h)$;
  - rows $4..7$: $A(\cdot, s_h + 4)$;
  - rows $8..10$: $B(\cdot, s_h + 13)$;
  - rows $11..n_0 - 18$: $(n_0 - 28)/4$ copies of $P$;
  - rows $n_0 - 17..n_0 - 1$: $17$ untouched rows ($\Delta = 0$);
  - rows $n_0..n - 1$: $t$ tail copies of $P$.
  - Unique row-max cells: $(2, s_h + 3)$, $(6, s_h + 7)$, $(9, s_h + 13)$.
  - $\sum \overline{\delta}_r = 6 + 6 + 3 + 2\cdot\frac{n_0 - 28}{4} + 2t = \frac{n_0}{2} + 2t + 1 = \frac{n}{2} + 1$.
  - $\sum \underline{\delta}_r = -4 - 4 - 3 - 2\cdot\frac{n_0 - 28}{4} - 2t = -\frac{n}{2} + 3 > -\frac{n}{2}$.

**Proposition 1.** For every even $n_0 \ge 22$ ($n_0 \ne 24$) and $n = n_0 + 4t$ ($t \ge 0$), $L_{n, n_0}(r, c) = (r + c + \Delta_{n_0}(r, c)) \bmod n$ is a valid Latin square with no two disjoint transversals.

*Proof.* Row bijectivity follows from explicit local inverses of $c \mapsto c + \Delta_{n_0}(r, c)$ in each gadget ($A$, $B$, $P$, and untouched rows), verified directly on the finite windows and on odd/even parities outside. Column bijectivity follows because each band ($A$, $B$, $P$, untouched) preserves its own row-index interval under $r \mapsto r + \Delta_{n_0}(r, c)$ (within each band, $r + \Delta(r, c)$ is a permutation of the band's rows for every column $c$). Applying Lemma 3 to the exact row-min/max sums above shows $L_{n, n_0}$ has no two disjoint transversals. $\square$

---

## 3. Universal Gluing Theorem

Let $n_0 = 2h$ ($h \ge 11$, $h \ne 12$) and $t \ge h$, so $n = 2h + 4t$.

- A *valid base* for $h$ consists of three permutations $b_0, b_1, b_2$ of $\{0, \dots, 2h - 1\}$ with no common fixed cell ($b_0(r) = b_1(r) = b_2(r)$ never occurs) such that for each $\alpha \in \{0, 1, 2\}$, the *unwrapped* integer sums $r + b_\alpha(r) + \Delta_{2h}(r, b_\alpha(r))$ form a bijection from $\{0, \dots, 2h - 1\}$ onto the interval $[h, 3h)$.
- A *valid tail* for $(h, t)$ is a permutation $c : \{0, \dots, 4t - 1\} \to \{0, \dots, 4t - 1\}$ such that the unwrapped tail sums $s(i) := i + c(i) + \delta_{\mathrm{tail}}(i, c(i))$ are pairwise distinct and all lie in
  $$
    \mathcal{B}_{h, t} := [2t - h,\; 4t - h) \;\cup\; [4t + h,\; 6t + h),
  $$
  where $\delta_{\mathrm{tail}}(i, c) = +2$ if $i \equiv 0 \pmod 4$ and $c$ is odd, $-2$ if $i \equiv 2 \pmod 4$ and $c$ is odd, and $0$ otherwise.

**Theorem 1 (Universal Gluing).** Suppose $h \ge 11$ ($h \ne 12$) and $t \ge h$. If $h$ admits a valid base $(b_0, b_1, b_2)$ and $(h, t)$ admits two completely disjoint valid tails $V_1, V_2$ ($V_1(i) \ne V_2(i)$ for all $i < 4t$), then $L_{2h + 4t, 2h}$ has no pinned entry.

*Proof.* Define three maps $T_0, T_1, T_2$ on $\{0, \dots, n - 1\}$ by setting $T_\alpha(r) = b_\alpha(r)$ on base rows $r < 2h$, and on tail rows $2h + i$ ($i < 4t$) setting $T_0(2h + i) = T_1(2h + i) = 2h + V_1(i)$ and $T_2(2h + i) = 2h + V_2(i)$.

1. Each $T_\alpha$ is a bijection on columns because $b_\alpha$ permutes $[0, 2h)$ and $2h + V_\bullet$ permutes $[2h, 2h + 4t)$.
2. On base rows $r < 2h$, the unwrapped symbol lies in $[h, 3h) \subset [0, n)$ (since $t \ge h$ implies $3h < 2h + 4t = n$), so reduction mod $n$ is the identity and hits $[h, 3h)$ bijectively.
3. On tail rows $2h + i$, $\Delta_{2h}(2h + i, 2h + c) = \delta_{\mathrm{tail}}(i, c)$, so the unwrapped symbol is $4h + s(i)$ with $s(i) \in \mathcal{B}_{h, t}$.
   - For $s \in [2t - h, 4t - 2h)$, $4h + s \in [3h + 2t, 2h + 4t) = [3h + 2t, n)$, unchanged mod $n$.
   - For $s \in [4t - 2h, 4t - h)$, $4h + s - n \in [0, h)$.
   - For $s \in [4t + h, 6t + h)$, $4h + s - n \in [3h, 3h + 2t)$.
   These three intervals partition $[0, n) \setminus [h, 3h)$ disjointly, and distinct $s(i) \in \mathcal{B}_{h, t}$ reduce to distinct residues mod $n$. Hence every $T_\alpha$ is a transversal of $L_{n, 2h}$.
4. For $r < 2h$, $(T_0(r), T_1(r), T_2(r)) = (b_0(r), b_1(r), b_2(r))$ are not all equal; for $r = 2h + i$, $T_0(r) = 2h + V_1(i) \ne 2h + V_2(i) = T_2(r)$. Thus $T_0 \cap T_1 \cap T_2 = \emptyset$, and Lemma 1 applies. $\square$

Four valid base witnesses for $n_0 \in \{22, 26, 30, 32\}$ ($h \in \{11, 13, 15, 16\}$) are explicitly tabulated in `lean/Conjectures/GhafariWanlessData.lean` and `verify.py`.

---

## 4. Granularity-1 Parametric Tail Engine (All 8 Even Classes mod 16)

For $t = 4p + R$, write each tail row index as $i = 4j + k$ ($0 \le j < t$, $k \in \{0, 1, 2, 3\}$) and each column index as $2u$ or $2u + 1$ ($0 \le u < 2t$). Direct evaluation of $\delta_{\mathrm{tail}}$ gives the six exact symbol formulas:

| Row class $k$ | Column | Unwrapped tail sum $i + c + \delta_{\mathrm{tail}}(i, c)$ | Parity | Half-symbol $h_s$ |
|---:|---|---|---|---:|
| $0$ | $2u + 1$ | $2(2j + u + 1) + 1$ | odd | $2j + u + 1$ |
| $1$ | $2u + 1$ | $2(2j + u + 1)$ | even | $2j + u + 1$ |
| $1$ | $2u$ | $2(2j + u) + 1$ | odd | $2j + u$ |
| $2$ | $2u$ | $2(2j + u + 1)$ | even | $2j + u + 1$ |
| $3$ | $2u$ | $2(2j + u + 1) + 1$ | odd | $2j + u + 1$ |
| $3$ | $2u + 1$ | $2(2j + u + 2)$ | even | $2j + u + 2$ |

### 4.1 Even-$h$ Families ($n_0 = 32$, $h = 16$, $n \equiv 0, 4, 8, 12 \pmod{16}$)

Here $h = 2d$ with $d = 8$, so both even ($2h_s$) and odd ($2h_s + 1$) tail symbols lie in $\mathcal{B}_{h, t}$ if and only if $h_s \in [e_1, e_1 + t) \cup [e_2, e_2 + t)$, where $e_1 = t - d$ and $e_2 = 2t + d$.

For each $j \in [0, t)$, we assign an ordered pair $(u_a(j), u_b(j))$ of distinct elements of $[0, 2t)$ such that the $2t$ values $\{u_a(j), u_b(j)\}$ partition $[0, 2t)$ and the $2t$ half-symbols $\{2j + u_a(j) + 1, 2j + u_b(j) + 1\}$ partition $[e_1, e_1 + t) \cup [e_2, e_2 + t)$. Defining
$$
  V_1(4j + 0) = 2u_a(j) + 1,\quad V_1(4j + 1) = 2u_b(j) + 1,\quad V_1(4j + 2) = 2u_a(j),\quad V_1(4j + 3) = 2u_b(j)
$$
and $V_2$ by swapping $(u_a, u_b) \mapsto (u_b, u_a)$ automatically yields two **completely disjoint** valid tails (since $u_a(j) \ne u_b(j)$ for every $j$).

To construct $(u_a, u_b)$ uniformly for all $p \ge 0$, set $s_1 = e_1 + d_1$, $s_2 = e_2 + d_2$, and place four parametric blocks of length $p$ at starts $(j_b, U_b)$ ($b \in \{0, 1, 2, 3\}$):
- $j_0 = 0$, $U_0 = s_1 - 1$;
- $U_1 = (s_1 + 1) \bmod 2$, $j_1 = (s_1 + 1 - U_1)/2$;
- $U_3 = 2t - 2p - ((s_2 - 1) \bmod 2)$, $j_3 = (s_2 - 1 - U_3)/2$;
- $j_2 = t - p$, $U_2 = s_2 + 1 - 2j_2$.

For $r \in \{0, \dots, p - 1\}$ on block $b$, set $(u_a, u_b)(j_b + r) = (U_b + 2r, U_b + 2r + 1)$. Blocks $0, 1$ partition the half-symbol interval $[s_1, s_1 + 4p)$ bijectively, and blocks $3, 2$ partition $[s_2, s_2 + 4p)$ bijectively. The remaining $R$ row quadruples, $2R$ column indices, and $2R$ half-symbols sit in constant-size gaps whose elements shift linearly in $p$ with slopes:
- $j$-gaps: $1, 2, 3$;
- $u$-gaps: $0, 2, 4, 6, 8$;
- $h_s$-gaps: $4$ on $[e_1, s_1)$, $8$ on $[s_1 + 4p, e_1 + t) \cup [e_2, s_2)$, and $12$ on $[s_2 + 4p, e_2 + t)$.

Any finite $p$-invariant matching at $p = 0$ satisfying $2\cdot\mathrm{slope}(j) + \mathrm{slope}(u) = \mathrm{slope}(h_s)$ extends identically to every $p \ge 0$, because the four $h_s$-gap intervals remain strictly ordered and disjoint for all $p \ge 0$. The four verified families are:

| $n \bmod 16$ | $n_0$ | $h$ | $R$ | $(d_1, d_2)$ | Threshold $n_{\min}$ | Range covered |
|---:|---:|---:|---:|---:|---:|---|
| $12$ | $32$ | $16$ | $19$ | $(1, 0)$ | $108$ | $108, 124, 140, \dots$ ($p \ge 0$) |
| $0$ | $32$ | $16$ | $20$ | $(2, 0)$ | $112$ | $112, 128, 144, \dots$ ($p \ge 0$) |
| $4$ | $32$ | $16$ | $21$ | $(1, 0)$ | $116$ | $116, 132, 148, \dots$ ($p \ge 0$) |
| $8$ | $32$ | $16$ | $22$ | $(2, 0)$ | $120$ | $120, 136, 152, \dots$ ($p \ge 0$) |

### 4.2 Odd-$h$ Families ($n_0 \in \{22, 26, 30\}$, $h \in \{11, 13, 15\}$, $n \equiv 2, 6, 10, 14 \pmod{16}$)

Here $h = 2d + 1$ is odd, so the even half-symbol band $[e_1, e_1 + t) \cup [e_2, e_2 + t)$ (with $e_1 = t - d$, $e_2 = 2t + d + 1$) and the odd half-symbol band $[o_1, o_1 + t) \cup [o_2, o_2 + t)$ (with $o_1 = e_1 - 1$, $o_2 = e_2 - 1$) are shifted by $1$. We therefore use the asymmetric column parities $(k = 0 \to \mathrm{odd},\; k = 1 \to \mathrm{even},\; k = 2 \to \mathrm{even},\; k = 3 \to \mathrm{odd})$:
- Even symbols arise from $k = 2$ ($h_s = 2j + u + 1$) and $k = 3$ ($h_s = 2j + u + 2$).
- Odd symbols arise from $k = 0$ ($h_s = 2j + u + 1$) and $k = 1$ ($h_s = 2j + u$).

With $p = q + 1 \ge 1$ ($q \ge 0$), $s_1 = e_1 + d_1$, $s_2 = e_2 + d_2$, and block starts $j_0 = 0$, $U_0 = s_1 - 1$, $U_1 = s_1 \bmod 2$, $j_1 = (s_1 - U_1)/2$, $U_3 = 2t - 2p - ((s_2 - 1) \bmod 2)$, $j_3 = (s_2 - 1 - U_3)/2$, $j_2 = t - p$, $U_2 = s_2 - 2j_2$:
- **Tail $V_1$:** on block $b$ ($0 \le r < p$), $k = 2$ uses $U_b + 2r$, $k = 3$ uses $U_b + 2r + 1$, $k = 1$ uses $U_b + 2r + 1$, and $k = 0$ shifts by one step ($U_b + 2(r - 1)$ for $1 \le r < p$), leaving the four boundary rows $r = 0$ and four boundary columns $U_b + 2(p - 1)$ to be absorbed by the $q$-invariant leftover permutations `s1OdA` (size $R + 4$) and `s1OdB` (size $R$).
- **Tail $V_2$:** on block $b$ ($0 \le r < p$), $k = 0$ uses $U_b + 2r + 1$, $k = 1$ uses $U_b + 2r$, $k = 2$ uses $U_b + 2r + 1$, and $k = 3$ shifts by one step ($U_b + 2(r + 1)$ for $0 \le r < p - 1$), leaving the four boundary rows $r = p - 1$ and four boundary columns $U_b$ to be absorbed by `s2EvA` (size $R$) and `s2EvB` (size $R + 4$).

On every parametric block row, $V_1$ and $V_2$ land on opposite parities inside each $U$-block (or one lands in a $U$-block and the other in a $u$-gap), ensuring disjointness automatically; on the $R$ gap rows, disjointness is checked directly on the finite index tables. The four verified families are:

| $n \bmod 16$ | $n_0$ | $h$ | $R$ | $(d_1, d_2)$ | Threshold $n_{\min}$ ($p = 1$) | Range covered |
|---:|---:|---:|---:|---:|---:|---|
| $6$ | $22$ | $11$ | $16$ | $(2, 3)$ | $102$ | $102, 118, 134, \dots$ ($p \ge 1$) |
| $2$ | $26$ | $13$ | $18$ | $(0, 1)$ | $114$ | $114, 130, 146, \dots$ ($p \ge 1$) |
| $10$ | $26$ | $13$ | $20$ | $(0, 1)$ | $122$ | $122, 138, 154, \dots$ ($p \ge 1$) |
| $14$ | $30$ | $15$ | $20$ | $(1, 0)$ | $126$ | $126, 142, 158, \dots$ ($p \ge 1$) |

---

## 5. Remaining 42 Small Even Orders ($22 \le n \le 110$, $n \ne 24$)

Every even integer $n \ge 22$ ($n \ne 24$) strictly below the threshold $n_{\min}$ for its residue class mod $16$ belongs to the 42-element set
$$
  \{22, 26, 28, 30, 32, 34, \dots, 98, 100, 104, 106, 110\}.
$$
For each of these 42 orders, we exhibit three explicit transversals $T_0, T_1, T_2$ of $L_{n, n}$ with empty triple intersection, verified both by `verify.py` and inside the Lean 4 kernel (`small_22` through `small_110`).

Combining Proposition 1, Theorem 1, the 8 parametric mod-16 families, and the 42 small witnesses establishes the Main Theorem for every even $n \ge 22$ with $n \ne 24$, and hence proves Conjecture 3 of Ghafari and Wanless for every even integer $n \ge 28$. $\square$

---

## 6. Formal Lean 4 Verification

The entire proof is formally verified in Lean 4 (`v4.33.1` + Mathlib) with zero `sorry`, zero custom `axiom`, and zero `native_decide`, depending solely on `[propext, Classical.choice, Quot.sound]`:
- `lean/Conjectures/GhafariWanlessData.lean`: finite witness tables (4 base squares, 8 mod-16 families, 42 small orders).
- `lean/Conjectures/GhafariWanlessCore.lean`: Latin square definitions, $\Delta$-sum lemma (`delta_sum_modEq`), modular Latin square construction (`modLatinSquare`), and non-disjointness (`modLatinSquare_no_disjoint`).
- `lean/Conjectures/GhafariWanlessTailBase.lean`: shared tail primitives and interval-separation lemmas (`inSGaps_spec`, `inSGaps_inj`).
- `lean/Conjectures/GhafariWanlessEvenTail.lean`: soundness of the 4 even-$h$ infinite families (`evenTailValid`, `evenTail_disjoint`).
- `lean/Conjectures/GhafariWanlessOddTail.lean`: soundness of the 4 odd-$h$ infinite families (`oddTail1Valid`, `oddTail2Valid`, `oddTail_disjoint`).
- `lean/Conjectures/GhafariWanlessLatinTransversals.lean`: universal gluing (`glue_base_and_tail`), small/base kernel checks, `ghafari_wanless_all_even_ge_22_ne_24`, and `ghafari_wanless_conjecture3`.
