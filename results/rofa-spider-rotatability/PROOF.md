# Every Regular Spider Tree Is 0-Rotatable

**Theorem.** *For every $k, \ell \ge 1$, the regular spider tree $T(k, \ell)$ formed by identifying one endpoint of each of $k$ paths of length $\ell$ is $0$-rotatable: for every vertex $v \in V(T(k, \ell))$, there exists a graceful labeling $f : V(T(k, \ell)) \to \{0, 1, \dots, k\ell\}$ with $f(v) = 0$.*

This settles the regular (symmetric) spider 0-rotatability conjecture of R. I. Rofa (`arXiv:2312.16235`, §1 item 2 & Summary), whose cases $\ell \le 3$ were proved by Rofa (2023) and $\ell = 4$ by `arXiv:2611.29448` (Nov 2026).

---

## 1. Preliminaries

A **graceful labeling** of a graph $G = (V, E)$ with $|E| = q$ edges and $|V| = q + 1$ vertices is a bijection $f : V \to \{0, 1, \dots, q\}$ whose induced edge weights $w_f(uv) = |f(u) - f(v)|$ form a bijection onto $\{1, 2, \dots, q\}$. An **$\alpha$-labeling** is a graceful labeling together with a threshold $a \in \{0, \dots, q - 1\}$ such that every edge $uv \in E$ crosses $a$: one endpoint has label $\le a$ and the other has label $> a$. The **complementary labeling** $\bar{f}(v) = q - f(v)$ preserves gracefulness and maps an $\alpha$-labeling with threshold $a$ to an $\alpha$-labeling with threshold $q - 1 - a$.

---

## 2. Two Path Theorems via Odd-Sum Permutations

Both path results used in our main proof follow from a single elementary device. Call a permutation $\pi = (\pi_0, \dots, \pi_{n-1})$ of $\{0, \dots, n - 1\}$ an **odd-sum path** of length $n$ if the adjacent sums $\{\pi_i + \pi_{i+1} : 0 \le i \le n - 2\}$ equal $\{1, 3, \dots, 2n - 3\}$.

- **Walecki map:** Define $W_n(2u) = u$ and $W_n(2u + 1) = n - 1 - u$. Then $W_n$ is a bijection on $\{0, \dots, n - 1\}$; whenever $x + y = 2r + 1$, one of $x, y$ is even and the other odd, so $|W_n(x) - W_n(y)| = n - 1 - r$ and the pair crosses $a = \lfloor (n - 1)/2 \rfloor$. Hence $W_n \circ \pi$ is an $\alpha$-labeling of the path $P_n$ ($n - 1$ edges) with threshold $\lfloor (n - 1)/2 \rfloor$, sending $0 \mapsto 0$ and $1 \mapsto n - 1$.
- **Operations on odd-sum paths:**
  1. *Identity:* $(0, 1, \dots, n - 1)$ is an odd-sum path.
  2. *Reversal:* $(\pi_{n-1}, \dots, \pi_0)$ is an odd-sum path.
  3. *Mirror:* $(n - 1 - \pi_0, \dots, n - 1 - \pi_{n-1})$ is an odd-sum path.
  4. *Pair-flip (for even $n$):* applying $x \mapsto 2\lfloor x/2 \rfloor + (1 - x \bmod 2)$ preserves every odd adjacent sum.
  5. *Block splice:* if $\pi$ (length $p \ge 1$) and $\sigma$ (length $s \ge 1$) are odd-sum paths with $\pi_{p-1} + \sigma_0 = p - 1$, then concatenating $\pi$ with $p + \sigma$ gives an odd-sum path of length $p + s$ (the bridge sum is $2p - 1$, separating $\{1, \dots, 2p - 3\}$ from $\{2p + 1, \dots, 2(p+s) - 3\}$).

Call a pair $(n, i)$ **admissible** if $0 \le i < n$ and either $n$ is even, or $i$ is even with $(n \ne 2i + 1 \text{ or } n = 1)$.

**Lemma 2.1 (Block-start recursion).** *For every admissible $(n, i)$, there exists an odd-sum path of length $n$ starting at $\pi_0 = i$.*

*Proof.* By strong induction on $(n, i)$ lexicographically. For $n = 1$, take $(0)$. If $2i \ge n$, apply mirror to $(n, n - 1 - i)$ (which has $n - 1 - i < i$). If $i$ is odd (so $n$ is even), apply pair-flip to $(n, i - 1)$. Otherwise $i$ is even and $2i < n$:
- If $n$ is even and $2i + 2 < n$, put $p = i + 2$ and splice the pair-flipped reversed identity of length $p$ (which starts at $i$ and ends at $1$) with an odd-sum path of length $n - p$ starting at $i$ (bridge sum $1 + i = p - 1$).
- Otherwise put $p = i + 1$ and splice the reversed identity of length $p$ (starting at $i$ and ending at $0$) with an odd-sum path of length $n - p$ starting at $i$ (bridge sum $0 + i = p - 1$).
In both cases $(n - p, i)$ is admissible with $n - p < n$. $\square$

**Theorem 2.2 (Rosa, 1977).** *For every $\ell \ge 1$ and $0 \le d \le \ell$ with $(\ell, d) \ne (4, 2)$, the path $P_{\ell+1}$ ($\ell$ edges) admits an $\alpha$-labeling $f$ with $f(d) = 0$.*

*Proof.* Put $n = \ell + 1 \ge 2$. It suffices to construct an odd-sum path $\pi$ of length $n$ with $\pi_d \in \{0, 1\}$, since $W_n \circ \pi$ (or its complement if $\pi_d = 1$) then puts $0$ at $d$. By reversal, assume $2d < n$.
- If $d \le 1$, take the identity path.
- If $n = 9$ and $d \in \{3, 4\}$, take $(2,5,4,1,0,3,8,7,6)$ (which has $\pi_3 = 1, \pi_4 = 0$).
- If $n = 2d + 1$ and $d$ is even: for $d = 4$ use the $n = 9$ seed above; for $d = 6$ use $(2,5,8,7,4,1,0,3,6,11,12,9,10)$ ($\pi_6 = 0$); for $d \ge 8$, put $p = d + 2$, splice the $6$-entry seed $(3,0,1,4,5,2)$ with a block of length $p - 6$ starting at $3$ (bridge $2 + 3 = 5$), reverse the resulting length-$p$ path (putting entry $0$ at index $p - 2 = d$ and entry $3$ at index $p - 1$), and splice with a block of length $n - p = d - 1$ starting at $p - 4 = d - 2$ (bridge $3 + (p - 4) = p - 1$).
- In every remaining case with $2d < n$, $d \ge 2$, and $(n, d) \ne (5, 2)$, direct arithmetic shows that for at least one $p \in \{d + 1, d + 2\}$ either $(n - p, p - 1)$ is admissible (splice the reversed identity of length $p$ with a length-$(n-p)$ path starting at $p - 1$) or $p$ is even and $(n - p, p - 2)$ is admissible (splice the pair-flipped reversed identity of length $p$ with a length-$(n-p)$ path starting at $p - 2$). In all cases $\pi_d \in \{0, 1\}$. $\square$

**Theorem 2.3 (Flandrin–Fournier–Germa, 1983; Cattell, 2007).** *For every $\ell \ge 1$ and $1 \le b \le \ell$, there exists a permutation $(b_1, \dots, b_\ell)$ of $\{1, \dots, \ell\}$ with $b_1 = b$ whose consecutive absolute differences $\{|b_{j+1} - b_j| : 1 \le j \le \ell - 1\}$ equal $\{1, \dots, \ell - 1\}$.*

*Proof.* Shift by $-1$ to work on $\{0, \dots, \ell - 1\}$ with target start $b_0 = b - 1$; by complementation $x \mapsto \ell - 1 - x$, assume $2b_0 < \ell$.
- If $(\ell, 2b_0)$ is admissible, Lemma 2.1 yields an odd-sum path $\pi$ starting at $2b_0$, and $W_\ell \circ \pi$ is a graceful path starting at $W_\ell(2b_0) = b_0$.
- The only non-admissible case with $2b_0 < \ell$ is $\ell = 4b_0 + 1$ with $b_0 \ge 1$. Put $p = 2b_0 + 1$ and $s = 2b_0$. Take the reversed prefix $(W_\ell(2b_0), W_\ell(2b_0 - 1), \dots, W_\ell(0))$ — which starts at $b_0$, ends at $0$, uses $\{0, \dots, b_0\} \cup \{3b_0 + 1, \dots, 4b_0\}$, and produces edge weights $\{2b_0 + 1, \dots, 4b_0\}$ — and append $b_0 + 1 + g$, where $g$ is the graceful path of length $s = 2b_0$ starting at $b_0 - 1$ (from the admissible case $(2b_0, 2(b_0 - 1))$). The appended block uses $\{b_0 + 1, \dots, 3b_0\}$ and weights $\{1, \dots, 2b_0 - 1\}$, and the bridge from $0$ to $b_0 + 1 + (b_0 - 1) = 2b_0$ supplies the exact missing weight $2b_0$. Adding $1$ to every entry gives the desired permutation of $\{1, \dots, \ell\}$. $\square$

---

## 3. General Leg-Attachment Lemma

**Lemma 3.1 (Attaching equal legs).** *Let $H$ be an $\alpha$-labeled finite graph on $s \ge 1$ edges and $s + 1$ vertices with threshold $a \in \{0, \dots, s - 1\}$. Let $v_0 \in V(H)$ have label $c \le a$, and suppose $\ell \ge 1$ satisfies $0 \le a - c \le \ell - 1$. Then for any $m \ge 0$, attaching $m$ pairwise internally disjoint paths of length $\ell$ at $v_0$ produces a graph admitting a graceful labeling $g$ such that $g(v) = f(v)$ whenever $f(v) \le a$ and $g(v) = f(v) + m\ell$ whenever $f(v) > a$. In particular, the vertex labeled $0$ keeps $0$, and the vertex labeled $s$ (which satisfies $s > a$) receives $s + m\ell$.*

*Proof.* Put $M = m\ell$. The case $m = 0$ is immediate. For $m \ge 1$, define $g(v) = f(v)$ if $f(v) \le a$ and $g(v) = f(v) + M$ if $f(v) > a$. Since $H$ is $\alpha$-labeled with threshold $a$, every edge of $H$ has one endpoint $\le a$ and one $> a$, so its weight increases by $+M$; thus old edges realize $\{M + 1, \dots, M + s\}$, and the unused vertex labels are precisely $\{a + 1, \dots, a + M\}$.

Since $0 \le a - c \le \ell - 1$, the integer $b_1 := \ell - a + c$ satisfies $1 \le b_1 \le \ell$. Choose a permutation $(b_1, \dots, b_\ell)$ of $\{1, \dots, \ell\}$ from Theorem 2.3 starting at $b_1$. Indexing the new legs by $i = 0, \dots, m - 1$ and depths by $j = 1, \dots, \ell$, label the vertex $v_{i,j}$ by
$$g(v_{i,j}) = a + b_j + \ell \cdot \begin{cases} m - 1 - i & \text{if } j \text{ is odd}, \\ i & \text{if } j \text{ is even}. \end{cases}$$

1. **Vertex bijectivity:** For each fixed $j$, as $i$ runs over $\{0, \dots, m - 1\}$ the multiplier runs bijectively over $\{0, \dots, m - 1\}$. Since $b_j$ runs bijectively over $\{1, \dots, \ell\}$, the new labels cover $\{a + 1, \dots, a + m\ell\} = \{a + 1, \dots, a + M\}$ bijectively.
2. **Root-incident edges:** Since $j = 1$ is odd and $g(v_0) = c$, the edge $v_0 v_{i,1}$ has weight
   $$g(v_{i,1}) - c = a + (\ell - a + c) + \ell(m - 1 - i) - c = (m - i)\ell,$$
   which runs over $\{\ell, 2\ell, \dots, m\ell\}$ — all multiples of $\ell$ in $[1, M]$.
3. **Internal new edges:** For each $j \in \{1, \dots, \ell - 1\}$, one of $j, j + 1$ is odd and the other even. Let $\delta_j$ be the $b$-value at the odd depth minus the $b$-value at the even depth, so $r_j := |\delta_j| = |b_{j+1} - b_j|$ runs bijectively over $\{1, \dots, \ell - 1\}$. Across the $m$ legs, the edge between depths $j$ and $j + 1$ receives weights
   $$|(m - 1 - 2i)\ell + \delta_j| = |t\ell + \delta_j|, \qquad t \in S := \{m - 1, m - 3, \dots, -(m - 1)\}.$$
   Since $S = -S$, the multiset $\{|t\ell + \delta_j| : t \in S\}$ equals $\{|t\ell + r_j| : t \in S\}$.
   - For $t \in S$ with $t \ge 0$, as $r_j$ runs over $\{1, \dots, \ell - 1\}$, $|t\ell + r_j| = t\ell + r_j$ covers $\{t\ell + 1, \dots, (t + 1)\ell - 1\}$. Here $t$ ranges over all integers in $\{0, \dots, m - 1\}$ with the same parity as $m - 1$.
   - For $t \in S$ with $t < 0$, put $u = -t - 1 \ge 0$; then $|t\ell + r_j| = (-t)\ell - r_j = u\ell + (\ell - r_j)$, which covers $\{u\ell + 1, \dots, (u + 1)\ell - 1\}$. Here $u$ ranges over all integers in $\{0, \dots, m - 1\}$ of the opposite parity to $m - 1$.

   Together, $u$ covers every integer in $\{0, \dots, m - 1\}$ exactly once, so the internal edges cover every non-multiple of $\ell$ in $[1, M]$ bijectively (for $\ell = 1$, both sets are empty).

Hence $g$ is a graceful labeling of the extended graph, fixing $0$ (since $0 \le a$) and sending $s \mapsto s + M$ (since $a < s$). $\square$

---

## 4. Proof of the Main Theorem

Fix $k, \ell \ge 1$ and a vertex $v \in V(T(k, \ell))$. By leg symmetry, $v$ lies at depth $d \in \{0, 1, \dots, \ell\}$ along leg $L_1$ (with $d = 0$ being the root $v_0$).

**Case 1: $(\ell, d) \ne (4, 2)$.**
Take $H$ to be the single path $L_1$ including $v_0$ ($s = \ell$ edges). By Theorem 2.2, $H$ admits an $\alpha$-labeling $f$ with threshold $a$ such that $f(v) = 0$. If $f(v_0) > a$, replace $f$ by its complement $\ell - f$ (and $a$ by $\ell - 1 - a$), so that $f(v_0) \le a$ and $f(v) \in \{0, \ell\}$. (When $d = 0$, $f(v_0) = 0 \le a$ already holds.)

Since $H$ is connected and bipartite and every edge crosses $a$, the low class $\{u : f(u) \le a\}$ must consist precisely of the even-depth vertices $\{0, 2, \dots, 2\lfloor \ell/2 \rfloor\}$, which has cardinality $\lfloor \ell/2 \rfloor + 1$. Because the low labels are $\{0, 1, \dots, a\}$, we obtain $a = \lfloor \ell/2 \rfloor$. Therefore $c := f(v_0)$ satisfies
$$0 \le a - c \le \lfloor \ell/2 \rfloor \le \ell - 1.$$
Applying Lemma 3.1 with $m = k - 1$ yields a graceful labeling $g$ of $T(k, \ell)$ with $g(v) \in \{0, k\ell\}$. If $g(v) = k\ell$, replace $g$ by its complement $k\ell - g$, obtaining a graceful labeling with $g(v) = 0$.

**Case 2: $(\ell, d) = (4, 2)$.**
- For $k = 1$, $T(1, 4) = P_5$; the path labeling $(1, 4, 0, 2, 3)$ from $v_0$ is graceful (edge weights $3, 4, 2, 1$) with $0$ at depth $2$.
- For $k \ge 2$, let $H = T(2, 4)$ be the two-leg tree on $s = 8$ edges labeled along its two legs from the common root $v_0$ by
  $$(2, 6, 0, 8, 1), \qquad (2, 7, 4, 5, 3).$$
  The vertex labels are $\{0, 1, \dots, 8\}$ (counting $v_0$ once), the edge weights are $\{4, 6, 8, 7\} \cup \{5, 3, 1, 2\} = \{1, \dots, 8\}$, every edge crosses $a = 4$, the root has label $c = 2 \le 4$ with $a - c = 2 \le 3 = \ell - 1$, and depth $2$ on leg $1$ has label $0$. Applying Lemma 3.1 with $m = k - 2$ yields a graceful labeling of $T(k, 4)$ retaining $0$ at depth $2$ on leg $1$.

Every $k \ge 1$, $\ell \ge 1$, and $v \in V(T(k, \ell))$ is covered. $\square$
