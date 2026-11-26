# Proof: Extremal Heap-Type Permutation Generation for Every Odd $n \ge 3$

**Target:** Open Question in Section 10, item 2 (and the Section 7 remark on odd $n$) of Luís M. S. Russo, *Heap-type permutation generation with a prescribed final arrangement*, [arXiv:2611.22780v1](https://arxiv.org/abs/2611.22780) (17 Nov 2026).

> **Verbatim (Section 10, item 2):** "We found no closed formula for the parking order at the top level and no variant for odd $n\ge7$ with the cyclic variant below it; whether other lower levels make the largest attainable arrangement reachable for odd $n$ is open."

> **Verbatim (Section 7, final remark, item 3):** "For odd $n$ the same construction (cyclic below) succeeds only for $n=3,5$ and fails for $7\le n\le 31$; we do not provide the variant for odd $n$. Whether other choices at lower levels make the largest attainable arrangement reachable for odd $n$ is not investigated here."

---

## Theorem

Let $n \ge 3$ be odd, and let $a^*_n \in S_n$ be the lexicographically largest odd permutation of $\{1,\dots,n\}$:
- $a^*_n = (n,\, n-1,\, \dots,\, 2,\, 1)$ when $n \equiv 3 \pmod 4$,
- $a^*_n = (n,\, n-1,\, \dots,\, 3,\, 1,\, 2)$ when $n \equiv 1 \pmod 4$.

Then there exists a valid Heap-type swap schedule on $\{1,\dots,n\}$ that starts from $(1, 2, \dots, n)$, lists every permutation in $S_n$ exactly once with a single transposition between consecutive arrangements, and terminates at $a^*_n$. Moreover, both the level-$(n-1)$ and top-level parking orders are given by explicit closed formulas.

*(Note: Combined with Russo's construction for $n \equiv 0 \pmod 4$ and the independent $n \equiv 2 \pmod 4$ construction, this settles the attainability of $a^*_n$ for every $n \ge 2$.)*

---

## 1. Conventions and Level-Lifting Formula

We follow Russo's conventions (1-based positions $1,\dots,n$, products acting right to left):
- Swapping positions $i$ and $j$ of the current array $a$ replaces $a$ by $a \circ (i\;j)$ and multiplies the inverse state $g = a^{-1}$ on the left by $(i\;j)$.
- Suppose levels $1,\dots,k-1$ define a valid Heap-type enumeration of $S_{k-1}$ with net state transformation $C \in S_{k-1}$ (fixing positions $\ge k$).
- Fix any parking order $e_0 = k, e_1, \dots, e_{k-1}$ of $\{1,\dots,k\}$. Define block-start states inductively by $g_0 = \mathrm{id}$ and, for $0 \le m < k-1$:
  - after block $m$, the state is $h_m = C g_m$;
  - choose the swap partner $s(m) = h_m(e_{m+1})$ and set $g_{m+1} = (s(m)\;k)\,h_m$.

By induction on $m$, $g_m(e_m) = k$, so $h_m(e_m) = C(k) = k$. Since $e_{m+1} \neq e_m$ and $h_m \in S_k$, we always have $s(m) = h_m(e_{m+1}) \in \{1,\dots,k-1\}$. Conjugation gives
$$g_{m+1} = (h_m(e_{m+1})\; h_m(e_m))\, h_m = h_m (e_{m+1}\;e_m) = C g_m (e_{m+1}\;e_m),$$
so by induction
$$g_m = C^m (e_1\;e_0)(e_2\;e_1)\cdots(e_m\;e_{m-1}).$$
Across the $k$ blocks, every state $p g_m$ in block $m$ has item $(p g_m)^{-1}(k) = g_m^{-1}(k) = e_m$ in position $k$; because $e_0,\dots,e_{k-1}$ are distinct, the $k$ blocks are pairwise disjoint cosets of $S_{k-1}$, so level $k$ lists all $k!$ permutations of $S_k$ without repetition. Its net state transformation is
$$\pi_k = C g_{k-1} = C^k (e_1\;e_0)(e_2\;e_1)\cdots(e_{k-1}\;e_{k-2}) = C^k (k\; e_1\; e_2\; \cdots\; e_{k-1}).$$

---

## 2. Construction for Odd $n \ge 3$

**Case $n = 3$.** Russo's classic/cyclic schedule already produces net $(1\;3)$, whose inverse is $321 = a^*_3$.

**Case $n \ge 5$ odd.** Set $h = (n - 3)/2 \ge 1$.
1. **Levels $2,\dots,n-2$ (cyclic):** Use Russo's cyclic schedule. By induction on $k \ge 2$:
   - at even $k$, the net is the $k$-cycle $(k\;1\;2\;\cdots\;k-1)$ (order $k$);
   - at odd $k \ge 3$, parking in descending order $(k-1,k-2,\dots,1)$ yields net
     $$(k-1\;1\;2\;\cdots\;k-2)^k (k\;k-1\;\cdots\;1) = (k-1\;1\;2\;\cdots\;k-2)(k\;k-1\;\cdots\;1) = (1\;k).$$
   In particular, at the odd level $n - 2$, the net is $C = (1\;n-2)$.

2. **Level $n - 1$ (zigzag):** Since $C = (1\;n-2)$ has order $2$ and $n - 1$ is even, $C^{n-1} = \mathrm{id}$. Park the elements of $\{1,\dots,n-2\}$ in the zigzag order
   $$E' = \bigl(1,\; n-2,\; 2,\; n-3,\; \dots,\; h,\; h+2,\; h+1\bigr)$$
   (note $h + 1 = (n - 1)/2$ and $h + 2 = (n + 1)/2$). By Section 1, the level-$(n-1)$ net is the $(n-1)$-cycle $Z' = (n-1\; e'_1\;\cdots\; e'_{n-2})$, explicitly:
   $$Z'(x) = \begin{cases} n - 1 - x & 1 \le x \le h, \\ n - 1 & x = h + 1, \\ n - x & h + 2 \le x \le n - 1, \\ n & x = n. \end{cases}$$
   Its inverse is
   $$(Z')^{-1}(y) = \begin{cases} n - y & 1 \le y \le h + 1, \\ n - 1 - y & h + 2 \le y \le n - 2, \\ h + 1 & y = n - 1, \\ n & y = n. \end{cases}$$
   Because $Z'$ is an $(n - 1)$-cycle, $(Z')^{n-1} = \mathrm{id}$, hence $(Z')^n = Z'$.

3. **Level $n$ (three-phase top order):** The target state is $T = (a^*_n)^{-1}$, given by $T(v) = n + 1 - v$ for $3 \le v \le n$ and
   $$(T(1), T(2)) = \begin{cases} (n,\, n - 1) & n \equiv 3 \pmod 4, \\ (n - 1,\, n) & n \equiv 1 \pmod 4. \end{cases}$$
   To achieve net $\pi_n = (Z')^n Z = Z' Z = T$, we require $Z = (Z')^{-1} T$ to be a single $n$-cycle. Evaluating $(Z')^{-1}(T(v))$ directly gives:
   - For $3 \le v \le h + 2$: $T(v) = n + 1 - v \in [h + 2,\, n - 2]$, so $Z(v) = n - 1 - (n + 1 - v) = v - 2$.
   - For $h + 3 \le v \le n$: $T(v) = n + 1 - v \in [1,\, h + 1]$, so $Z(v) = n - (n + 1 - v) = v - 1$.
   - For $v \in \{1, 2\}$:
     $$(Z(1), Z(2)) = \begin{cases} (n,\, h + 1) & n \equiv 3 \pmod 4, \\ (h + 1,\, n) & n \equiv 1 \pmod 4. \end{cases}$$

---

## 3. Proof That $Z$ Is an $n$-Cycle

Trace the orbit of $n$ under $Z$:
1. **Phase 1 (step $-1$):** Starting at $n$, repeated application of $Z(v) = v - 1$ descends through $n, n - 1, \dots, h + 2$.
2. **Phase 2 (step $-2$):** From $h + 2 = (n + 1)/2$, repeated application of $Z(v) = v - 2$ descends through all integers in $[1, h + 2]$ having the same parity as $h + 2$, terminating at $r \in \{1, 2\}$ where $r \equiv h + 2 \pmod 2$:
   - If $n \equiv 3 \pmod 4$, then $h + 2 = (n + 1)/2$ is even, so $r = 2$, and $Z(2) = h + 1$.
   - If $n \equiv 1 \pmod 4$, then $h + 2 = (n + 1)/2$ is odd, so $r = 1$, and $Z(1) = h + 1$.
3. **Phase 3 (step $-2$):** From $h + 1 = (n - 1)/2$, which has the *opposite* parity from $h + 2$, repeated application of $Z(v) = v - 2$ descends through all integers in $[1, h + 1]$ having the parity of $h + 1$, terminating at $r' = 3 - r \in \{1, 2\}$:
   - If $n \equiv 3 \pmod 4$, $r' = 1$ and $Z(1) = n$.
   - If $n \equiv 1 \pmod 4$, $r' = 2$ and $Z(2) = n$.

The three phases visit $[h + 2, n]$ and both parity classes of $[1, h + 1]$ without overlap before returning to $n$. Thus $Z$ is a single $n$-cycle, and the explicit top-level parking order is
$$E = \bigl(n-1,\, n-2,\, \dots,\, h+2,\; h,\, h-2,\, \dots,\, r,\; h+1,\, h-1,\, \dots,\, 3-r\bigr).$$
Applying Section 1 at level $n$ yields a valid Heap-type enumeration of all $n!$ permutations with net $\pi_n = (Z')^n Z = Z' (Z')^{-1} T = T$, hence final array $T^{-1} = a^*_n$. $\square$

---

## 4. Machine Verification

- **Lean 4:** [RussoHeapOddExtremal.lean](../../lean/Conjectures/RussoHeapOddExtremal.lean) proves the entire result end-to-end from the recursive definition of Heap-type schedules (including level lifting, cyclic lower levels, lexicographic maximality of $a^*_n$ among odd permutations, and the main theorem `russo_open_question_item2`), with zero `sorry` and standard axioms only.
- **Python:** `python -O -W error results/russo-heap-odd-extremal/verify.py` directly simulates the Heap recursion for $n \in \{3, 5, 7, 9\}$ (confirming all $n!$ distinct permutations, single-swap adjacency, and final array $a^*_n$) and verifies the closed-form algebraic identities for all odd $5 \le n \le 1201$.
