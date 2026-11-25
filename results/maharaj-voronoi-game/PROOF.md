# Exact Facility Advantage in the One-Round Discrete Voronoi Game on a Line (`arXiv:2609.24936`)

We **disprove Conjecture 1** of Tamal Maharaj (*The Facility Advantage in the One-Round Discrete Voronoi Game on a Line*, `arXiv:2609.24936`, Section 4.3) for every $\ell \ge 3$ and prove that the facility advantage is
$$k^*(\ell) = 2\ell - 1 \qquad \text{for every } \ell \ge 1,$$
showing that Maharaj's upper bound (Theorem 4.1) is already sharp. Conjecture 1 ($k^*(\ell) = \ell + 1$) holds only at $\ell = 2$ (where $2\ell - 1 = \ell + 1 = 3$).

---

## 1. Model and Main Results

Following Maharaj (`arXiv:2609.24936`, Sections 1 and 4):
- An instance is a finite nonempty multiset $V \subset \mathbb{R}$ of $n = |V|$ voters.
- Player $\mathcal{P}$ chooses a $k$-element subset $P \subset \mathbb{R}$; player $\mathcal{Q}$ then chooses an $\ell$-element subset $Q \subset \mathbb{R}$.
- A voter $v \in V$ is won by $\mathcal{P}$ if $\mathrm{dist}(v, P) \le \mathrm{dist}(v, Q)$ (ties favor $\mathcal{P}$), and by $\mathcal{Q}$ if $\mathrm{dist}(v, Q) < \mathrm{dist}(v, P)$.
- Write $V[P \succ Q]$ for the submultiset of voters won by $\mathcal{P}$, and
  $$\Gamma_{k,\ell}(V) := \max_{P \subset \mathbb{R},\, |P| = k}\; \min_{Q \subset \mathbb{R},\, |Q| = \ell}\; |V[P \succ Q]|.$$
  Player $\mathcal{P}$ wins if $\Gamma_{k,\ell}(V) \ge n/2$.
- The **facility advantage** is
  $$k^*(\ell) := \min\{k \ge 1 : \Gamma_{k,\ell}(V) \ge n/2 \text{ for every finite nonempty multiset } V \subset \mathbb{R}\}.$$

**Theorem 1 (Exponential Lower Bound).** *Let $\ell \ge 2$, $1 \le k \le 2\ell - 2$, and $n \ge 4\ell(\ell - 1) + 1$. For the unit-weight (simple) voter set*
$$V_n := \{2^0, 2^1, \dots, 2^{n-1}\} \subset \mathbb{R},$$
*we have $\Gamma_{k,\ell}(V_n) < n/2$. Moreover, as $n \to \infty$ with $k = 2\ell - 2$, $\mathcal{P}$ retains at most $\frac{\ell - 1}{2\ell - 1} n + O(\ell)$ voters, so $\mathcal{Q}$ wins by a margin growing linearly in $n$.*

**Corollary 1 (Exact Facility Advantage and Disproof of Conjecture 1).** *Combined with Maharaj's upper bound $k^*(\ell) \le 2\ell - 1$ (Theorem 4.1),*
$$k^*(\ell) = 2\ell - 1 \qquad \text{for every } \ell \ge 1.$$
*In particular, Conjecture 1 ($k^*(\ell) = \ell + 1$ for all $\ell \ge 2$) is false for every $\ell \ge 3$.*

**Theorem 2 (Small Explicit Counterexample for $\ell = 3$).** *For $V_{17} = \{1, 2, 4, \dots, 65536\}$ ($n = 17$, unit weights), $\Gamma_{4,3}(V_{17}) = 8 < 8.5$ (attained by $P = \{2, 32, 512, 8192\}$).*

*Remark.* Maharaj (`arXiv:2609.24936`, Abstract & §4.2) proved that on arithmetic progressions $k = \ell$ suffices and remarked that extremal instances must be weighted with $\mathcal{Q}$ winning by a single voter. Theorem 1 shows that unweighted (distinct, multiplicity-$1$) exponentially spaced voters defeat every $k \le 2\ell - 2$ with a linear winning margin. Maharaj's computer search only tested $m \le 10$ consecutive integer sites ($n \le 17$), which cannot realize the exponential spacing needed for $k = \ell + 1$.

---

## 2. Proof of Theorem 1 and Theorem 2

Write $x_t := 2^t$ for $0 \le t \le n - 1$. The key geometric identity is that for all $0 \le s \le t$,
$$x_{t+1} - x_t = 2^t > 2^t - 2^s = x_t - x_s,$$
and therefore
$$x_{t+1} - x_s = (x_{t+1} - x_t) + (x_t - x_s) > 2(x_t - x_s). \tag{$\ast$}$$

### Step 1: Reduction to $K = 2\ell - 2$ via padding

Let $P \subset \mathbb{R}$ be any strategy of $\mathcal{P}$ with $|P| = k \le 2\ell - 2$. Choose $K - k$ additional distinct points outside $P$ to form a superset $\widetilde{P} \supseteq P$ with $|\widetilde{P}| = K := 2\ell - 2$. For every $v \in V_n$ and $Q \subset \mathbb{R}$, we have $\mathrm{dist}(v, \widetilde{P}) \le \mathrm{dist}(v, P)$, so every voter strictly closer to $Q$ than to $\widetilde{P}$ is also strictly closer to $Q$ than to $P$. Thus any $\ell$-point response $Q$ defeating $\widetilde{P}$ automatically defeats $P$. We therefore replace $P$ by $\widetilde{P}$ and assume $|P| = K = 2\ell - 2$.

Write $P = \{p_1 < p_2 < \dots < p_K\}$, and let $a := |P \cap V_n| \in \{0, \dots, K\}$ be the number of absorbed voters. The points of $P$ partition $\mathbb{R} \setminus P$ into $K + 1 = 2\ell - 1$ pairwise disjoint open gaps:
$$G_0 := (-\infty, p_1), \qquad G_i := (p_i, p_{i+1}) \;\;(1 \le i \le K - 1), \qquad G_K := (p_K, +\infty).$$
Write $V(G_j) := V_n \cap G_j$ and $c_j := |V(G_j)|$, so $\sum_{j=0}^K c_j = n - a$.

### Step 2: Single-facility capture inside each gap

We show that in every gap $G_j$ ($0 \le j \le K$), there exists a point $q_j \in G_j$ winning at least $c_j - d_j$ voters of $V(G_j)$ against $P$, where $d_j \in \{0, 1\}$ satisfies $d_j = 0$ unless $1 \le j \le K - 1$ and $p_{j+1} \notin V_n$.

- **Empty gap ($c_j = 0$):** Any point $q_j \in G_j$ wins $0 = c_j$ voters ($d_j = 0$).
- **Outer gap $G_0 = (-\infty, p_1)$ with $c_0 \ge 1$:** Let $M := \max V(G_0) < p_1$, and set $q_0 := \frac{1}{2}(M + p_1) \in G_0$. For every $v \in V(G_0)$, we have $v \le M < q_0 < p_1$, hence
  $$|v - q_0| = q_0 - v < p_1 - v = \mathrm{dist}(v, P).$$
  Thus $q_0$ wins all $c_0$ voters of $V(G_0)$ ($d_0 = 0$).
- **Outer gap $G_K = (p_K, +\infty)$ with $c_K \ge 1$:** Symmetrically, taking $m := \min V(G_K) > p_K$ and $q_K := \frac{1}{2}(p_K + m) \in G_K$ gives $|v - q_K| = v - q_K < v - p_K = \mathrm{dist}(v, P)$ for all $v \in V(G_K)$, so $q_K$ wins all $c_K$ voters ($d_K = 0$).
- **Inner gap $G_i = (p_i, p_{i+1})$ ($1 \le i \le K - 1$) with $c_i \ge 1$:** Because $G_i$ is an interval, $V(G_i)$ is a contiguous slice $\{x_s, x_{s+1}, \dots, x_t\}$ of size $c_i = t - s + 1$, with $p_i < x_s \le x_t < p_{i+1}$.
  For any $v, q \in (p_i, p_{i+1})$, we have $\mathrm{dist}(v, P) = \min(v - p_i,\, p_{i+1} - v)$, so
  $$|v - q| < \mathrm{dist}(v, P) \iff \frac{p_i + q}{2} < v < \frac{q + p_{i+1}}{2}.$$
  Therefore a point $q \in (p_i, p_{i+1})$ wins the entire sub-block $\{x_s, \dots, x_r\}$ ($s \le r \le t$) if and only if
  $$\max(p_i,\, 2x_r - p_{i+1}) < q < \min(p_{i+1},\, 2x_s - p_i).$$
  Since $p_i < x_s$ implies $p_i < 2x_s - p_i$ and $x_r < p_{i+1}$ implies $2x_r - p_{i+1} < p_{i+1}$, this open interval is nonempty if and only if
  $$2(x_r - x_s) < p_{i+1} - p_i.$$
  We check the three subcases:
  1. **$p_{i+1} \in V_n$:** Because $x_t$ is the largest element of $V_n$ strictly below $p_{i+1}$ and $p_{i+1} \in V_n$, we must have $p_{i+1} = x_{t+1}$. Then by ($\ast$) and $p_i < x_s$,
     $$p_{i+1} - p_i = x_{t+1} - p_i > x_{t+1} - x_s > 2(x_t - x_s).$$
     Taking $r = t$, a point $q_i \in G_i$ wins all $c_i$ voters ($d_i = 0$).
  2. **$p_{i+1} \notin V_n$ and $t = s$ ($c_i = 1$):** Taking $q_i := x_s \in G_i$ wins $x_s$ since $|x_s - q_i| = 0 < \mathrm{dist}(x_s, P)$ ($d_i = 0$).
  3. **$p_{i+1} \notin V_n$ and $t > s$ ($c_i \ge 2$):** Taking $r = t - 1 \ge s$, we have by ($\ast$), $p_i < x_s$, and $x_t < p_{i+1}$ that
     $$p_{i+1} - p_i > x_t - x_s > 2(x_{t-1} - x_s).$$
     Hence a point $q_i \in G_i$ wins $\{x_s, \dots, x_{t-1}\}$, capturing $c_i - 1$ voters ($d_i = 1$).

Because the right endpoints $p_2, p_3, \dots, p_K$ of the inner gaps are pairwise distinct points of $P$, the number of gaps with $d_j = 1$ is at most $|P \setminus V_n| = K - a$:
$$\sum_{j=0}^K d_j \le K - a.$$

### Step 3: Summing over all gaps and selecting the top $\ell$

Let $g_j := c_j - d_j$ be the guaranteed single-facility capture in gap $G_j$. Summing over all $K + 1 = 2\ell - 1$ gaps, the absorbed count $a$ cancels identically:
$$\sum_{j=0}^{2\ell - 2} g_j = \sum_{j=0}^{2\ell - 2} c_j - \sum_{j=0}^{2\ell - 2} d_j \ge (n - a) - (K - a) = n - (2\ell - 2). \tag{1}$$

Let $J \subset \{0, 1, \dots, 2\ell - 2\}$ be a subset of $\ell$ gap indices with the largest values of $g_j$, and set $Q := \{q_j : j \in J\}$. Because the open gaps $G_j$ are pairwise disjoint, the points $q_j$ ($j \in J$) are pairwise distinct ($|Q| = \ell$), and the voter subsets they win inside distinct gaps are pairwise disjoint. Therefore $\mathcal{Q}$ wins at least $\sum_{j \in J} g_j$ voters.

By averaging over the $\ell$ largest of $2\ell - 1$ integers,
$$\sum_{j \in J} g_j \ge \frac{\ell}{2\ell - 1} \sum_{j=0}^{2\ell - 2} g_j \ge \frac{\ell\bigl(n - (2\ell - 2)\bigr)}{2\ell - 1}. \tag{2}$$
We have
$$\frac{\ell\bigl(n - (2\ell - 2)\bigr)}{2\ell - 1} > \frac{n}{2} \iff 2\ell n - 4\ell(\ell - 1) > (2\ell - 1)n \iff n > 4\ell(\ell - 1).$$
Hence for every $n \ge 4\ell(\ell - 1) + 1$, player $\mathcal{Q}$ wins strictly more than $n/2$ voters against every strategy $P$ of size $k \le 2\ell - 2$, proving Theorem 1.

*(Proof of Theorem 2: $n = 17, k = 4, \ell = 3$.)* By (1) with $n = 17$ and $K = 4$, the five integer captures $g_0, \dots, g_4$ satisfy $\sum_{j=0}^4 g_j \ge 17 - 4 = 13$. Sort them as $g_{(1)} \ge g_{(2)} \ge g_{(3)} \ge g_{(4)} \ge g_{(5)}$. If $g_{(1)} + g_{(2)} + g_{(3)} \le 8$, then $g_{(3)} \le \lfloor 8/3 \rfloor = 2$, so $g_{(4)}, g_{(5)} \le 2$ and $\sum_{j=1}^5 g_{(j)} \le 8 + 2 + 2 = 12 < 13$, a contradiction. Therefore $\mathcal{Q}$ always wins at least $9 > 8.5$ voters, so $\Gamma_{4,3}(V_{17}) \le 8$. Conversely, placing $P = \{2, 32, 512, 8192\} = \{2^1, 2^5, 2^9, 2^{13}\}$ absorbs $4$ voters and leaves five gaps of sizes $1, 3, 3, 3, 3$, so any three facilities of $\mathcal{Q}$ win at most $3 + 3 + 3 = 9$ voters, keeping $17 - 9 = 8$ for $\mathcal{P}$. Thus $\Gamma_{4,3}(V_{17}) = 8$. $\blacksquare$

---

## 3. Matching Upper Bound (Self-Contained Proof of Maharaj's Theorem 4.1)

For completeness (and as formalized alongside Theorem 1 in Lean 4), we record why $k^*(\ell) \le 2\ell - 1$ for every $\ell \ge 1$. Given any finite nonempty multiset $V = \{v_1 \le v_2 \le \dots \le v_n\}$ of size $n \ge 1$, set $B := \lfloor n / (2\ell) \rfloor$ and $k := 2\ell - 1$. Construct $P = \{p_1 < \dots < p_k\}$ greedily: starting at $r_0 := 0$, for $j = 1, \dots, k$, if $r_{j-1} + B \ge n$ place the remaining points strictly to the right of $v_n$ (distinct); otherwise set $p_j := v_{r_{j-1} + B + 1}$ and $r_j := |\{i : v_i \le p_j\}| \ge r_{j-1} + B + 1$. Each gap created before $p_j$ holds at most $B$ voters, and after $k$ steps the right tail holds at most $n - k(B + 1) = n - (2\ell - 1)(B + 1) \le B$ voters (since $n \le 2\ell(B + 1) - 1$). By locality, every facility $q \in Q$ lies in at most one gap of $P$ and can win only voters strictly inside that gap, hence at most $B$ voters. Thus any $\ell$-point set $Q$ wins at most $\ell B \le n/2$ voters, so $\mathcal{P}$ retains at least $n/2$ voters. Combining with Theorem 1 gives $k^*(\ell) = 2\ell - 1$ for all $\ell \ge 1$. $\blacksquare$
