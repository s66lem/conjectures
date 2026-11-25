# Exact Littlestone Dimensions of Intervals and Unions of Intervals (`arXiv:2611.28727`)

We prove **both open conjectures** posed by Miit Daga and Swarna Priya Ramu (*How many mistakes does it take to learn an interval? Exact Littlestone dimensions of intervals and their unions*, `arXiv:2611.28727`, November 2026):

1. **Odd-$k$ union-of-intervals conjecture:** For every odd switch budget $k \ge 1$ and every $n \ge 1$,
   $$\mathrm{Ldim}(C_{n,k}) = 1 + \mathrm{Ldim}(G_k(n)) = 1 + v_k(n).$$
2. **Conjecture 31 (Randomized Littlestone dimension of intervals):** In the discounted cutting game of Equation (2), the greedy schedule value $G(S)$ satisfies the Bellman supersolution inequality for every finite multiset position $S$ and every legal cut $p = u + v$, and therefore equals the exact Bellman optimum:
   $$V(S) = G(S) \quad \text{for every } S, \qquad \mathrm{RL}(\mathrm{Int}_m) = R(m + 1) \quad \text{for every } m \ge 0.$$

---

## 1. Proof of the Odd-$k$ Conjecture

Let $k \ge 1$ be odd and $n \ge 1$. Recall from `arXiv:2611.28727` that:
- $C_{n,k} \subseteq \{0, 1\}^n$ is the class of binary words $f = (f_1, \dots, f_n)$ with at most $k$ switches $t(f) := |\{i \in \{1, \dots, n-1\} : f_i \neq f_{i+1}\}| \le k$.
- $G_k(n)$ is the gap family of words $(0, g_2, \dots, g_n, 1)$ with fixed endpoints $0, 1$, $n - 1$ free coordinates, and $n$ edges having at most $k$ switches, viewed as a concept class on the $n - 1$ free points. By Theorem 4 of `arXiv:2611.28727`, $\mathrm{Ldim}(G_k(n)) = v_k(n) := \max\{d \ge 0 : Q_k(d) \le n\}$.
- For any finite concept class $\mathcal{H} \subseteq \{0, 1\}^X$ with $|\mathcal{H}| \ge 2$, the Littlestone dimension satisfies the standard first-query recursion
  $$\mathrm{Ldim}(\mathcal{H}) = \max_{\substack{x \in X \\ \mathcal{H}_x^0 \neq \emptyset,\; \mathcal{H}_x^1 \neq \emptyset}} \Bigl(1 + \min\bigl(\mathrm{Ldim}(\mathcal{H}_x^0),\, \mathrm{Ldim}(\mathcal{H}_x^1)\bigr)\Bigr),$$
  where $\mathcal{H}_x^b := \{f \in \mathcal{H} : f(x) = b\}$.

**Theorem 1.** *For every odd integer $k \ge 1$ and every $n \ge 1$, $\mathrm{Ldim}(C_{n,k}) = 1 + \mathrm{Ldim}(G_k(n)) = 1 + v_k(n)$.*

*Proof.* For any word $f = (f_1, \dots, f_n) \in \{0, 1\}^n$, append the bit $f_{n+1} := 1 - f_1$. The resulting $n$ consecutive pairs $(f_1, f_2), \dots, (f_{n-1}, f_n), (f_n, 1 - f_1)$ have switch count
$$a(f) := t(f) + \mathbf{1}_{f_n = f_1} = t(f) + \mathbf{1}_{t(f) \text{ is even}},$$
since $f_n = f_1$ if and only if $t(f)$ is even. Thus $a(f)$ is the least odd integer at least $t(f)$. Because $k$ is odd,
$$a(f) \le k \iff t(f) \le k.$$

Define the **signed rotation** $T : \{0, 1\}^n \to \{0, 1\}^n$ by
$$T(f_1, f_2, \dots, f_n) := (f_2, \dots, f_n, 1 - f_1).$$
Clearly $T$ is a bijection. Its appended sequence is $(f_2, \dots, f_n, 1 - f_1, 1 - f_2)$. For $n \ge 2$, the $n$ edge-switch indicators of $T(f)$ are the $n$ edge-switch indicators of $f$ cyclically shifted by one position, because the final edge $(1 - f_1, 1 - f_2)$ switches if and only if $(f_1, f_2)$ switches. For $n = 1$, $a(f) = 1 = a(T(f))$. Hence $a(T(f)) = a(f)$ for all $f \in \{0, 1\}^n$, so $T(C_{n,k}) = C_{n,k}$.

A coordinate permutation combined with fixed coordinatewise bit-flips is an automorphism of the hypercube $\{0, 1\}^n$ that preserves shattered binary tree depth (relabel every internal node's query coordinate and swap its $0$- and $1$-subtrees whenever that coordinate is flipped). For any coordinate $p \in \{1, \dots, n\}$, iterating $T^{p-1}$ carries the slice $\{f \in C_{n,k} : f_p = 0\}$ isomorphically onto $\{f \in C_{n,k} : f_1 = 0\}$, while global complementation $f \mapsto \mathbf{1} - f$ preserves $C_{n,k}$ and carries $\{f \in C_{n,k} : f_p = 1\}$ isomorphically onto $\{f \in C_{n,k} : f_p = 0\}$. Note that both slices are nonempty (the all-$0$ and all-$1$ words lie in $C_{n,k}$).

Finally, in the slice $\{f \in C_{n,k} : f_1 = 0\}$, the appended bit is the constant $1 - f_1 = 1$, so by $a(f) \le k \iff t(f) \le k$, deleting the fixed first coordinate $f_1 = 0$ identifies $\{f \in C_{n,k} : f_1 = 0\}$ with the exact gap family $G_k(n)$ on the $n - 1$ free coordinates $(f_2, \dots, f_n)$. Deleting a constant coordinate does not change shattered-tree depth. Therefore every first-query slice at every coordinate $p \in \{1, \dots, n\}$ has Littlestone dimension $\mathrm{Ldim}(G_k(n))$. By the first-query recursion (and Theorem 4 of `arXiv:2611.28727`),
$$\mathrm{Ldim}(C_{n,k}) = 1 + \mathrm{Ldim}(G_k(n)) = 1 + v_k(n). \qquad \blacksquare$$

*(Check $n = 1$: $C_{1,k} = \{0, 1\}$ has $\mathrm{Ldim}(C_{1,k}) = 1$, while $G_k(1)$ consists of the single empty word with $\mathrm{Ldim}(G_k(1)) = 0 = v_k(1)$ since $Q_k(1) = 2$.)*

---

## 2. Proof of Conjecture 31 (Bellman Optimality of the Greedy Cutting Schedule)

Write $L(z) := \widetilde{\lambda}(z) = t + (z / 2^t - 1)$ for $z \in \mathbb{Z}_{\ge 1}$, where $t := \lfloor \log_2 z \rfloor$. A position is a finite multiset $S$ of positive integer piece measures (unit pieces of measure $1$ are inert). A legal cut replaces a piece $p \in S$ ($p \ge 2$) by $u, v \in \mathbb{Z}_{\ge 1}$ with $u + v = p$, yielding $S' = (S \setminus \{p\}) \cup \{u, v\}$ and undiscounted step reward
$$r(p; u, v) := 1 + \frac{L(u) + L(v)}{2}.$$
The Bellman recursion (Equation (2) of `arXiv:2611.28727`) is
$$V(S) = \max\left(0,\; \max_{\substack{p \in S,\; p = u + v \\ u, v \ge 1}} \frac{r(p; u, v) + V(S')}{2}\right),$$
with $V(S) = 0$ when every piece in $S$ has measure $1$. Let $G(S) \ge 0$ denote the value of the greedy schedule (which repeatedly cuts the largest piece $p \ge 2$ via the greedy split $u = \max(2^{t-1}, p - 2^t)$, $v = p - u$, earning reward $L(p)$ per Theorem 30, Step 1 of `arXiv:2611.28727`).

**Theorem 2 (Conjecture 31).** *For every finite multiset $S$ of positive integers and every legal cut $p = u + v$ ($u, v \ge 1$) producing $S'$,*
$$2 G(S) - G(S') \ge 1 + \frac{L(u) + L(v)}{2}.$$
*Consequently $V(S) = G(S)$ for every finite multiset $S$, and in particular $\mathrm{RL}(\mathrm{Int}_m) = R(m + 1)$ for every $m \ge 0$.*

### Step 1: Dyadic-scale decomposition

All sums over $h$ below range over dyadic scales $h \in \{1, 2, 4, 8, \dots\}$ (with finite support for any fixed finite multiset). For each scale $h$ and $z \in \mathbb{Z}_{\ge 1}$, define
$$X_h(z) := \max\left(0,\; \frac{z}{h} - 1\right), \qquad b_h(z) := \min\bigl(1,\, X_h(z)\bigr).$$

**Lemma 2.1.** *For every integer $z \ge 1$,*
$$\sum_h b_h(z) = L(z), \qquad \sum_h X_h(z) = 2z - 2 - L(z). \tag{1}$$

*Proof.* Write $t = \lfloor \log_2 z \rfloor$, so $2^t \le z < 2^{t+1}$. For $h = 2^j$ with $0 \le j < t$, $z/h \ge 2$ so $b_h(z) = 1$; for $h = 2^t$, $b_{2^t}(z) = X_{2^t}(z) = z/2^t - 1 \in [0, 1)$; for $h \ge 2^{t+1}$, $X_h(z) = b_h(z) = 0$. Hence $\sum_h b_h(z) = t + (z/2^t - 1) = L(z)$, and
$$\sum_h X_h(z) = \sum_{j=0}^t \left(\frac{z}{2^j} - 1\right) = z\left(2 - \frac{1}{2^t}\right) - (t + 1) = 2z - 2 - \left(t + \frac{z}{2^t} - 1\right) = 2z - 2 - L(z). \qquad \blacksquare$$

For any real $x \ge 0$, define the **packed multiset** $P(x)$ consisting of $\lfloor x \rfloor$ copies of $1$ together with one copy of the fractional part $x - \lfloor x \rfloor$ (if positive). For a finite multiset $D$ of nonnegative reals, write $D_1^\downarrow \ge D_2^\downarrow \ge \dots$ for its elements in non-increasing order (padded with trailing zeros) and define
$$F(D) := \sum_{i \ge 1} 2^{-i} D_i^\downarrow.$$
Write $D + E$ for multiset union.

**Lemma 2.2 (Single-scale greedy credits).** *At every dyadic scale $h$ and for every rod $p \ge 1$, the multiset of nonzero values $b_h(z)$ over all nodes $z \ge 2$ cut in the greedy tree of $p$ equals $P(X_h(p))$. Consequently, for every finite multiset $S$,*
$$G(S) = \sum_h G_h(S), \qquad G_h(S) := F\!\left(\sum_{p \in S} P(X_h(p))\right). \tag{2}$$

*Proof.* Induct on $p \ge 1$. For $p = 1$ there are no cuts and $X_h(1) = 0$. Suppose $p \ge 2$ has greedy children $a, b$ ($a + b = p$, $a = \max(2^{t-1}, p - 2^t)$ where $t = \lfloor \log_2 p \rfloor$).
- If $p < 2h$: when $p \le h$, $X_h(p) = 0$ and $a, b < h$, so nothing contributes. When $h < p < 2h$, $2^t = h$, so $a = \max(h/2, p - h) < h$ and $b = p - a \le h$. Thus $X_h(a) = X_h(b) = 0$, neither child contributes, and only the root contributes $b_h(p) = X_h(p) \in (0, 1)$, matching $P(X_h(p))$.
- If $p \ge 2h$: then $2^{t-1} \ge h$ and $2^t \ge 2h$. If $p - 2^t \ge 2^{t-1}$, then $a = p - 2^t \ge h$ and $b = 2^t \ge 2h$; otherwise $a = 2^{t-1} \ge h$ and $b = p - 2^{t-1} \ge h$. In both cases $a \ge h$, $b \ge h$, and at least one of $a, b$ is a dyadic power divisible by $h$. Therefore
  $$X_h(a) + X_h(b) = \left(\frac{a}{h} - 1\right) + \left(\frac{b}{h} - 1\right) = X_h(p) - 1,$$
  and at least one of $X_h(a), X_h(b)$ is an integer. Adding the root contribution $b_h(p) = 1$ to $P(X_h(a)) + P(X_h(b))$ yields $P(X_h(p))$.

Since the greedy schedule orders all cuts in non-increasing order of piece measure $z$, and each function $z \mapsto b_h(z)$ is non-decreasing, the greedy cut order sorts the values $b_h(z)$ in non-increasing order at every scale $h$ simultaneously. Since each greedy cut of $z$ earns reward $L(z) = \sum_h b_h(z)$, summing over $h$ gives (2). $\blacksquare$

### Step 2: Three finite-list lemmas

**Lemma 2.3.** *For any finite multisets $A, E$ of nonnegative reals:*
1. *(Rearrangement)* $F(D) = \max_\pi \sum_{i \ge 1} 2^{-i} D_{\pi(i)}$ over all orderings $\pi$ of $D$ (including inserting any number of zeros).
2. *(Packing)* If every entry of $E$ lies in $[0, 1]$ and $\sum_{e \in E} e = x$, then $F(A + E) \le F(A + P(x))$.
3. *($1/2$-Lipschitzness)* For $0 \le y \le z$, $F(A + P(z)) - F(A + P(y)) \le (z - y)/2$.

*Proof.* (1) Swapping any inversion $(i < j, D_i < D_j)$ strictly increases $\sum 2^{-k} D_k$.
(2) Let $s_j(D) := \sum_{i=1}^j D_i^\downarrow$ be the sum of the $j$ largest entries of $D$. Since $2^{-i} = \sum_{j \ge i} 2^{-(j+1)}$, summation by parts gives $F(D) = \sum_{j \ge 1} 2^{-(j+1)} s_j(D)$. For $E$ with entries in $[0, 1]$ summing to $x$, $s_j(E) \le \min(j, x) = s_j(P(x))$ for every $j \ge 1$. Because $s_j(A + D) = \max_{a + b = j} (s_a(A) + s_b(D))$, we obtain $s_j(A + E) \le s_j(A + P(x))$ for all $j$, hence $F(A + E) \le F(A + P(x))$.
(3) Pad $P(y)$ and $P(z)$ with zeros to equal length; in descending order, $P(y)_k^\downarrow \le P(z)_k^\downarrow$ for every $k$, with total drop $\sum_k (P(z)_k^\downarrow - P(y)_k^\downarrow) = z - y$. Take an optimal ordering of $A + P(z)$ and replace each $P(z)_k^\downarrow$ in place by $P(y)_k^\downarrow$. Every slot weight satisfies $2^{-i} \le 1/2$, so the discounted sum drops by at most $(z - y)/2$. Re-sorting into descending order can only increase the value (by (1)), giving $F(A + P(y)) \ge F(A + P(z)) - (z - y)/2$. $\blacksquare$

### Step 3: Proof of the Bellman supersolution inequality

Fix a finite multiset $S$ of positive integers and any legal cut $p = u + v$ ($p \in S$, $u, v \ge 1$) yielding $S' = (S \setminus \{p\}) \cup \{u, v\}$.

At a fixed dyadic scale $h$, set $X := X_h(p)$, $b := b_h(p) = \min(1, X)$, and
$$\delta_h := X_h(p) - X_h(u) - X_h(v).$$
We claim $0 \le \delta_h \le b$:
- If $p \le h$, then $u, v < h$ as well, so $X = X_h(u) = X_h(v) = 0$ and $\delta_h = 0 = b$.
- If $p > h$, then $X = p/h - 1 = u/h + v/h - 1$. Since $z/h - X_h(z) = \min(z/h, 1)$ for all $z \ge 1$,
  $$\delta_h = \min\left(\frac{u}{h}, 1\right) + \min\left(\frac{v}{h}, 1\right) - 1.$$
  Clearly $\delta_h \le 1 + 1 - 1 = 1$, and $\delta_h \ge 0$ (if either $u \ge h$ or $v \ge h$ one minimum is $1$; otherwise $u/h + v/h - 1 = p/h - 1 > 0$). Also $\delta_h = X - X_h(u) - X_h(v) \le X$ since $X_h(u), X_h(v) \ge 0$. Thus $0 \le \delta_h \le \min(1, X) = b$.

Let $A := \sum_{q \in S \setminus \{p\}} P(X_h(q))$. The two children contribute $P(X_h(u)) + P(X_h(v))$, whose entries lie in $[0, 1]$ and sum to $X - \delta_h$. Since $0 \le X - b \le X - \delta_h$, Lemma 2.3(2)–(3) give
$$G_h(S') = F\bigl(A + P(X_h(u)) + P(X_h(v))\bigr) \le F\bigl(A + P(X - \delta_h)\bigr) \le F\bigl(A + P(X - b)\bigr) + \frac{b - \delta_h}{2}. \tag{3}$$
On the other hand, $P(X)$ equals $\{b\} + P(X - b)$ (up to a harmless zero when $X = 0$). Placing $b$ in the first slot (weight $1/2$) followed by $A + P(X - b)$ in descending order (weights $2^{-(i+1)} = \frac{1}{2} \cdot 2^{-i}$) is a valid ordering of $A + P(X)$, so Lemma 2.3(1) gives
$$2 G_h(S) \ge b + F\bigl(A + P(X - b)\bigr). \tag{4}$$
Subtracting (3) from (4) yields
$$2 G_h(S) - G_h(S') \ge \frac{b + \delta_h}{2}. \tag{5}$$

Summing (5) over all dyadic scales $h$ and applying Lemma 2.1 together with $p = u + v$:
$$\sum_h \delta_h = (2p - 2 - L(p)) - (2u - 2 - L(u)) - (2v - 2 - L(v)) = 2 + L(u) + L(v) - L(p),$$
and $\sum_h b_h(p) = L(p)$. The $L(p)$ terms cancel identically:
$$2 G(S) - G(S') \ge \sum_h \frac{b_h(p) + \delta_h}{2} = \frac{L(p) + \bigl(2 + L(u) + L(v) - L(p)\bigr)}{2} = 1 + \frac{L(u) + L(v)}{2} = r(p; u, v).$$
Since $G(S) \ge 0$ for all $S$ and $G(S) = 0$ at terminal positions (where $\sum_{p \in S} (p - 1) = 0$), induction on $\sum_{p \in S} (p - 1)$ shows $V(S) \le G(S)$ (including the $\max(0, \cdot)$ branch of Equation (2)). Because greedy play is an admissible strategy attaining $G(S)$, we conclude $V(S) = G(S)$ for all finite multisets $S$, and Theorem 30 of `arXiv:2611.28727` gives $\mathrm{RL}(\mathrm{Int}_m) = R(m + 1)$ for every $m \ge 0$. $\blacksquare$
