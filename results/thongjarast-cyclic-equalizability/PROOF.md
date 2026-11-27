# Disproof of Thongjarast's Discard-Letter Conjecture on Cyclic Equalizability (`arXiv:2607.18452v1`, Problem 2)

## Problem Statement

Let $\Sigma$ be a finite alphabet and $\sigma \subseteq \Sigma$. A *$\sigma$-simultaneous insertion* applied to two length-$n$ words $u = a_0 \dots a_{n-1}$ and $v = b_0 \dots b_{n-1}$ over $\Sigma$ chooses $n + 1$ words $w_0, \dots, w_n \in \sigma^*$ and produces
$$u' = w_0 a_0 w_1 a_1 \dots w_{n-1} a_{n-1} w_n, \qquad v' = w_0 b_0 w_1 b_1 \dots w_{n-1} b_{n-1} w_n.$$
Two words $u', v'$ of common length $L$ are *cyclically equivalent* if there exists an integer $d$ such that $u'[t] = v'[(t + d) \bmod L]$ for all $0 \le t < L$. The pair $(u, v)$ is *$\sigma$-cyclically equalizable* if some $\sigma$-simultaneous insertion produces cyclically equivalent words $u'$ and $v'$.

In *0-Cyclic Equalizability of Binary Words Characterized by Hamming Weight* (`arXiv:2607.18452v1`, July 2026), S. Thongjarast posed Problem 2 (`prob:discard`):

> Let $\Sigma$ be an alphabet of size at least $3$. Let $u$ and $v$ be words over $\Sigma$ that are permutations of each other. Must there exist a letter $c \in \Sigma$ such that $u$ and $v$ are $(\Sigma \setminus \{c\})$-equalizable?

---

## Main Theorem

**Theorem.** *For every alphabet $\Sigma = \{x_0, \dots, x_{m-1}\}$ of size $m \ge 3$ (indices taken modulo $m$), define the length-$3m$ words*
$$u_m = \prod_{i=0}^{m-1} x_i x_i x_{i+1}, \qquad v_m = \prod_{i=0}^{m-1} x_{i+1} x_i x_{i+1}.$$
*Then:*
1. *$u_m$ and $v_m$ are permutations of each other (every letter of $\Sigma$ occurs exactly $3$ times in each), and $u_m \ne v_m$.*
2. *For every letter $c \in \Sigma$, $(u_m, v_m)$ is **not** $(\Sigma \setminus \{c\})$-cyclically equalizable.*
3. *For the smallest instance $m = 3$ ($\Sigma = \{a, b, c\}$, $u_3 = \texttt{aabbbccca}$, $v_3 = \texttt{babcbcaca}$), $(u_3, v_3)$ **is** $\Sigma$-cyclically equalizable (e.g. via the length-$15$ simultaneous insertion $\texttt{aabcababcacabca}$ vs $\texttt{babcacabcaaabca}$ with shift $d = 10$).*

---

## Complete Proof

Number positions $0, 1, \dots, 3m - 1$. Block $k \in \{0, \dots, m - 1\}$ occupies indices $3k, 3k + 1, 3k + 2$ with letter pairs $(u_m[j], v_m[j])$ given by:
- $3k$: $(x_k, x_{k+1})$ (a mismatch, since $x_k \ne x_{k+1}$);
- $3k + 1$: $(x_k, x_k)$;
- $3k + 2$: $(x_{k+1}, x_{k+1})$.

Each letter $x_i$ appears three times in $u_m$ (at $3(i - 1) + 2 \bmod 3m$, $3i$, and $3i + 1$) and three times in $v_m$ (at $3(i - 1) \bmod 3m$, $3(i - 1) + 2 \bmod 3m$, and $3i + 1$), so $u_m$ and $v_m$ are permutations of each other. They differ at position $0$, where $u_m[0] = x_0 \ne x_1 = v_m[0]$.

Now fix an arbitrary discarded letter $c = x_i \in \Sigma$, set $\sigma := \Sigma \setminus \{c\}$, and suppose toward a contradiction that a $\sigma$-simultaneous insertion $w_0, \dots, w_{3m} \in \sigma^*$ yields cyclically equivalent words $u', v'$ of length $L$ with shift $d$:
$$u'[t] = v'[(t + d) \bmod L] \qquad (0 \le t < L).$$
Let $0 \le P(0) < P(1) < \dots < P(3m - 1) < L$ denote the indices of the original letters in $u'$ (and identically in $v'$). For every $j$, $u'[P(j)] = u_m[j]$ and $v'[P(j)] = v_m[j]$; for every non-original index $t \notin \mathrm{range}(P)$, $u'[t] = v'[t] \in \sigma$.

Set $e := d \bmod L \in \{0, \dots, L - 1\}$.

### Step 1: Nonzero Shift ($0 < e < L$)

If $e = 0$, then $(t + d) \bmod L = t$ for all $t < L$, so $u' = v'$. Evaluating at $t = P(j)$ gives $u_m[j] = v_m[j]$ for all $j$, contradicting $u_m \ne v_m$. Thus $0 < e < L$.

### Step 2: Rigidity of the Discarded Letter $c$

Let $U_c := \{j : u_m[j] = c\}$ and $V_c := \{j : v_m[j] = c\}$. For any $j \in U_c$, put $t' := (P(j) + e) \bmod L$. Then
$$v'[t'] = u'[P(j)] = u_m[j] = c \notin \sigma.$$
Since every inserted index $t \notin \mathrm{range}(P)$ carries a letter in $\sigma$, $t'$ must be an original index: $t' = P(j')$ for a unique $j' \in \{0, \dots, 3m - 1\}$ (uniqueness by strict monotonicity of $P$). Then $v_m[j'] = v'[P(j')] = c$, so $j' \in V_c$. Writing $\varphi(j) := j'$ defines a map $\varphi : U_c \to V_c$ satisfying:
1. $P(\varphi(j)) = (P(j) + e) \bmod L$ for all $j \in U_c$;
2. $\varphi$ is injective (if $P(\varphi(j_1)) = P(\varphi(j_2))$, then $P(j_1) \equiv P(j_2) \pmod{L}$, so $P(j_1) = P(j_2)$ and $j_1 = j_2$);
3. $\varphi$ has no fixed points (if $\varphi(j) = j$, then $P(j) = (P(j) + e) \bmod L$, contradicting $0 < e < L$).

Since $|U_c| = |V_c| = 3$, $\varphi : U_c \to V_c$ is a fixed-point-free bijection.

### Step 3: Forcing a Half-Turn Shift ($2e = L$)

Let $i' := (i - 1) \bmod m$ and define the four distinct indices in $\{0, \dots, 3m - 1\}$:
$$\alpha := 3i' + 2, \qquad \beta := 3i, \qquad \gamma := 3i + 1, \qquad \delta := 3i'.$$
Then $U_c = \{\alpha, \beta, \gamma\}$ and $V_c = \{\alpha, \gamma, \delta\}$. Define the cyclic offset from $P(\beta)$:
$$x(j) := (P(j) + L - P(\beta)) \bmod L \in \{0, \dots, L - 1\}.$$
Then $x(\beta) = 0$, and $x(\varphi(j)) = (x(j) + e) \bmod L$ for all $j \in U_c$.

We claim that
$$0 = x(\beta) < x(\gamma) < x(\delta) < x(\alpha) < L.$$
Indeed:
- If $i = 0$, then $i' = m - 1$, so $0 = \beta < \gamma = 1 < \delta = 3m - 3 < \alpha = 3m - 1$ (since $m \ge 3$). Strict monotonicity of $P$ gives $P(\beta) < P(\gamma) < P(\delta) < P(\alpha) < L$, hence $x(j) = P(j) - P(\beta)$ for $j \in \{\gamma, \delta, \alpha\}$, preserving the strict ordering.
- If $i \ge 1$, then $i' = i - 1$, so $\delta = 3i - 3 < \alpha = 3i - 1 < \beta = 3i < \gamma = 3i + 1$. Strict monotonicity of $P$ gives $P(\delta) < P(\alpha) < P(\beta) < P(\gamma) < L$, hence
  $$x(\gamma) = P(\gamma) - P(\beta) < L - P(\beta) \le L + P(\delta) - P(\beta) = x(\delta) < L + P(\alpha) - P(\beta) = x(\alpha) < L.$$

Now split on $\varphi(\beta) \in \{\alpha, \gamma, \delta\}$:
- **Case 2 ($\varphi(\beta) = \alpha$):** Since $\varphi(\gamma) \ne \gamma$ and $\varphi$ is bijective, we must have $\varphi(\alpha) = \gamma$ and $\varphi(\gamma) = \delta$. Thus
  $$x(\alpha) = e, \qquad x(\gamma) = (2e) \bmod L, \qquad x(\delta) = (3e) \bmod L,$$
  so $0 < (2e) \bmod L < (3e) \bmod L < e$. From $(2e) \bmod L < e$ we must have $2e \ge L$, so $(2e) \bmod L = 2e - L$.
  - If $3e < 2L$, then $(3e) \bmod L = 3e - L < e$ gives $2e < L$, contradiction.
  - If $3e \ge 2L$, then $(3e) \bmod L = 3e - 2L > 2e - L$ gives $e > L$, contradiction.
- **Case 3 ($\varphi(\beta) = \gamma$):** Since $\varphi(\alpha) \ne \alpha$ and $\varphi$ is bijective, we must have $\varphi(\gamma) = \alpha$ and $\varphi(\alpha) = \delta$. Thus
  $$x(\gamma) = e, \qquad x(\alpha) = (2e) \bmod L, \qquad x(\delta) = (3e) \bmod L,$$
  so $0 < e < (3e) \bmod L < (2e) \bmod L$. From $(2e) \bmod L > e$ we must have $2e < L$, so $(2e) \bmod L = 2e$.
  - If $3e < L$, then $(3e) \bmod L = 3e > 2e$, contradicting $(3e) \bmod L < (2e) \bmod L$.
  - If $3e \ge L$, then $(3e) \bmod L = 3e - L > e$ gives $2e > L$, contradiction.
- **Case 1 ($\varphi(\beta) = \delta$):** Since $\varphi(\alpha) \ne \alpha$ and $\varphi(\gamma) \ne \gamma$, we must have $\varphi(\alpha) = \gamma$ and $\varphi(\gamma) = \alpha$. Thus $x(\alpha) = (x(\alpha) + 2e) \bmod L$, which forces $(2e) \bmod L = 0$. Since $0 < e < L$, this forces $2e = L$.

### Step 4: Antipodal-Swap Contradiction

Since $2e = L$, shifting twice by $d$ returns to the starting index: $((t + d) \bmod L + d) \bmod L = t$ for every $t < L$.

Consider the mismatch position $0$, where $u_m[0] = x_0$ and $v_m[0] = x_1$. Set $t_0 := P(0)$ and $t_1 := (t_0 + d) \bmod L$. Then
$$v'[t_1] = u'[t_0] = u_m[0] = x_0, \qquad u'[t_1] = v'[(t_1 + d) \bmod L] = v'[t_0] = v_m[0] = x_1.$$
If $t_1 \notin \mathrm{range}(P)$, then $u'[t_1] = v'[t_1]$, forcing $x_1 = x_0$, a contradiction. Therefore $t_1 = P(j_1)$ for some $j_1 \in \{0, \dots, 3m - 1\}$ with $(u_m[j_1], v_m[j_1]) = (x_1, x_0)$.

Write $j_1 = 3q + r$ with $0 \le q < m$ and $r \in \{0, 1, 2\}$. For $r \in \{1, 2\}$ we have $u_m[j_1] = v_m[j_1]$, impossible since $x_1 \ne x_0$. For $r = 0$ we have $u_m[j_1] = x_q = x_1$ (hence $q = 1$) and $v_m[j_1] = x_{(q + 1) \bmod m} = x_0$, hence $(1 + 1) \bmod m = 0$, impossible for $m \ge 3$. $\square$

---

## Remark on Minimality

Exhaustive certificate search in `verify.py` verifies that every pair of distinct permutations over $\{a, b, c\}$ of length $n \le 6$ using all three letters is $(\Sigma \setminus \{c\})$-cyclically equalizable for at least one $c \in \{a, b, c\}$ (with explicit insertions of length $\le n + 6$). Hence the smallest counterexample length over a ternary alphabet lies in $\{7, 8, 9\}$.

## Lean 4 Formalization

The complete proof is formally verified in [ThongjarastCyclicEqualizability.lean](../../lean/Conjectures/ThongjarastCyclicEqualizability.lean) (`0` errors, `0` warnings, standard axioms `[propext, Classical.choice, Quot.sound]` only):
- `step3_arithmetic`: elementary arithmetic impossibility of Cases 2 and 3 and half-turn forcing $2e = L$;
- `wordU_perm_wordV`, `wordU_ne_wordV`, `wordU_surjective`: permutation equivalence, distinctness, and surjectivity of $(u_m, v_m)$;
- `family_not_equalizable`: full proof for `Fin m` ($m \ge 3$);
- `thongjarast_prob_discard_disproof`: general disproof for every finite alphabet `α` with `3 ≤ Fintype.card α`;
- `smallest_counterexample_full_alphabet_equalizable`: explicit length-$15$ full-alphabet equalization of $(u_3, v_3)$ with shift $d = 10$.
