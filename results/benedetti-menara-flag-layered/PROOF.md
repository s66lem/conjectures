# Proof of Conjecture 7.1 of Benedetti–Menara (`arXiv:2611.08071`) for $r = 2$

**Theorem 1.** *Every flag $1$-layered family of $2$-subsets of an $m$-element set ($m \ge 2$) has at most $m - 1$ layers. This bound is sharp, attained by the path on $m$ vertices with one edge per layer.*

This resolves the $r = 2$ (triangle-free graph) case of **Conjecture 7.1** of Bruno Benedetti and Giuliamaria Menara, *Diameter bounds for complexes that are close to flag or close to normal* (`arXiv:2611.08071`, §7), where the Larman–Barnette bound (Theorem 2.1) gave only $2m - 3$ layers.

---

## 1. Exact Formulation at $r = 2$

Following Sections 2 and 7 of `arXiv:2611.08071`, a **$1$-layered family of $r$-sets** on an $m$-set $X$ is a set $\mathcal{F}$ of $r$-subsets of $X$, partitioned into nonempty disjoint layers $L_0, L_1, \dots, L_N$, such that for every nonempty $S \subseteq X$ the set $\{t \in \{0, \dots, N\} : \exists F \in L_t,\, S \subseteq F\}$ is a (possibly empty) interval of consecutive integers. The family is **flag** if no $(r + 1)$-clique in its graph of co-occurring pairs exists (equivalently, every clique in the $1$-skeleton is contained in a member of $\mathcal{F}$, which for $r = 2$ means no $3$ vertices have all $3$ pairs in $\mathcal{F}$).

At $r = 2$:
- $\mathcal{F}$ is the edge set $E$ of a simple **triangle-free** graph $G = (V, E)$ on the set $V \subseteq X$ of used vertices ($|V| \le m$).
- The partition into nonempty disjoint layers $L_0, \dots, L_N$ is a surjective edge labeling $\lambda : E \to \{0, \dots, N\}$ with $L_t = \lambda^{-1}(t)$.
- For $|S| = 2$, $S$ belongs to at most one layer; for $|S| \ge 3$, no layer contains $S$. Thus the $1$-layered condition holds if and only if for every vertex $v \in V$, the incident label set $I_v := \{\lambda(e) : v \in e\}$ is an interval of consecutive integers.
- Neither connectivity nor properness of $\lambda$ is assumed: several edges incident to the same vertex may carry the same label.

It suffices to prove $N + 1 \le |V| - 1$ (equivalently $|V| \ge N + 2$), since $|V| \le m$.

---

## 2. Monotone Path Counting Lemma

The following lemma adapts Theorem 1 of Asratian and Kamalian (`arXiv:1401.8079`) to edge labelings that need not be proper.

**Lemma 2.1.** *Let $G = (V, E)$ be a finite triangle-free simple graph with an interval edge labeling $\lambda : E \to \mathbb{Z}$. Suppose $G$ contains a simple path $x_0 x_1 \dots x_k$ ($k \ge 1$) whose edge labels $\lambda_i := \lambda(x_{i-1} x_i)$ satisfy $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_k$. Then $|V| \ge \lambda_1 - \lambda_k + 2$.*

*Proof.* Put $p = \lambda_1$ and $q = \lambda_k$. Among all simple paths in $G$ with non-increasing edge labels, first label $p$, and last label $q$, choose one, $P = x_0 x_1 \dots x_k$, of minimum length $k$; among those of length $k$, choose $P$ with lexicographically maximal label sequence $(\lambda_1, \dots, \lambda_k)$.

For each $i \in \{1, \dots, k - 1\}$, define
$$A(i) := \{y \in N_G(x_i) : \lambda_{i+1} < \lambda(x_i y) < \lambda_i\}.$$
Because $I_{x_i}$ is an interval containing $\lambda_i$ and $\lambda_{i+1}$, every integer $t$ strictly between $\lambda_{i+1}$ and $\lambda_i$ occurs as $\lambda(x_i y)$ for some edge $x_i y$. Distinct integers require distinct edges incident to $x_i$, hence distinct neighbors of $x_i$ because $G$ is simple. Therefore
$$|A(i)| \ge \lambda_i - \lambda_{i+1} - 1,$$
which also holds trivially when $\lambda_i = \lambda_{i+1}$ (as $0 \ge -1$).

**Claim 1:** $A(i) \cap V(P) = \emptyset$ for every $1 \le i \le k - 1$.

*Proof of Claim 1.* Clearly $x_i \notin A(i)$ (loopless) and $x_{i-1}, x_{i+1} \notin A(i)$ since their edge labels to $x_i$ are $\lambda_i$ and $\lambda_{i+1}$. Suppose $x_j \in A(i)$ for some other $j$, and put $g = \lambda(x_i x_j)$, so $\lambda_{i+1} < g < \lambda_i$:
- If $i + 2 \le j \le k - 1$, then $x_0 \dots x_i x_j \dots x_k$ is a shorter simple path with labels $\lambda_1, \dots, \lambda_i, g, \lambda_{j+1}, \dots, \lambda_k$, non-increasing since $\lambda_i > g > \lambda_{i+1} \ge \lambda_{j+1}$, preserving first label $p$ and last label $q$.
- If $j = k$, triangle-freeness rules out $i = k - 2$, so $i \le k - 3$. Then $x_0 \dots x_i x_k x_{k-1}$ has length $i + 2 < k$, labels $\lambda_1, \dots, \lambda_i, g, \lambda_k$ (non-increasing since $\lambda_i > g > \lambda_{i+1} \ge \lambda_k$), and end labels $p, q$.
- If $1 \le j \le i - 2$, then $x_0 \dots x_j x_i \dots x_k$ is a shorter simple path with labels $\lambda_1, \dots, \lambda_j, g, \lambda_{i+1}, \dots, \lambda_k$ (non-increasing since $\lambda_j \ge \lambda_i > g > \lambda_{i+1}$) and end labels $p, q$.
- If $j = 0$, triangle-freeness rules out $i = 2$, so $i \ge 3$. Then $x_1 x_0 x_i \dots x_k$ has length $k - i + 2 < k$, labels $\lambda_1, g, \lambda_{i+1}, \dots, \lambda_k$ (non-increasing since $\lambda_1 \ge \lambda_i > g > \lambda_{i+1}$), and end labels $p, q$.

Every case contradicts the minimality of $k$.

**Claim 2:** $A(i) \cap A(j) = \emptyset$ for all $1 \le i < j \le k - 1$.

*Proof of Claim 2.* Suppose $v \in A(i) \cap A(j)$. By Claim 1, $v \notin V(P)$; by triangle-freeness, $j \ne i + 1$, so $j \ge i + 2$. Consider the simple path $P' = x_0 \dots x_i v x_j \dots x_k$. Its labels satisfy
$$\lambda_i > \lambda(x_i v) > \lambda_{i+1} \ge \lambda_j > \lambda(v x_j) > \lambda_{j+1},$$
so $P'$ is non-increasing and preserves both end labels $p$ and $q$. Its length is $k - (j - i - 2)$:
- If $j - i \ge 3$, then $P'$ is strictly shorter than $P$, contradicting minimality of $k$.
- If $j - i = 2$, then $P'$ has the same length $k$, agrees with $P$ on its first $i$ labels, and has $(i + 1)$-st label $\lambda(x_i v) > \lambda_{i+1}$, contradicting lexicographic maximality of $P$.

By Claims 1 and 2, the sets $V(P), A(1), \dots, A(k - 1)$ are pairwise disjoint subsets of $V$, so
$$|V| \ge (k + 1) + \sum_{i=1}^{k-1} |A(i)| \ge (k + 1) + \sum_{i=1}^{k-1} (\lambda_i - \lambda_{i+1} - 1) = \lambda_1 - \lambda_k + 2. \qquad \square$$

---

## 3. Proof of Theorem 1

We induct on $N \ge 0$. For $N = 0$, layer $L_0$ is nonempty and contains at least one edge, so $|V| \ge 2 = N + 2$.

Now assume $N \ge 1$ and the result holds for all smaller top labels. Consider the time-expanded node set $\{(v, t) : v \in V,\, t \in I_v\}$, and let $D$ be the smallest subset of nodes that:
1. contains every top-level node $(v, N)$ with $N \in I_v$;
2. is closed under **horizontal moves**: if $(u, t) \in D$ and $uv \in E$ with $\lambda(uv) = t$, then $(v, t) \in D$;
3. is closed under **downward moves**: if $(v, t) \in D$ and $t - 1 \in I_v$, then $(v, t - 1) \in D$.

Let $c := \min\{t : \exists v,\, (v, t) \in D\}$, and let $W := \{w \in V : \exists t,\, (w, t) \in D\}$. By downward closure, for every $w \in W$ the slice $\{t : (w, t) \in D\}$ is the interval $[\min I_w, h_w]$ where $h_w = \max\{t : (w, t) \in D\}$; in particular, $\min I_w \ge c$ for every $w \in W$.

Define $F_D := \{e = uv \in E : (u, \lambda(e)) \in D\}$. By horizontal closure in both directions, $(u, \lambda(e)) \in D \iff (v, \lambda(e)) \in D$. For every $w \in W$ and every $t \in [\min I_w, h_w] \subseteq I_w$, there is an edge $wu \in E$ of label $t$, and $(w, t) \in D$ puts $wu \in F_D$. Hence the $F_D$-labels at each $w \in W$ form the interval $[\min I_w, h_w]$. Moreover, $F_D$ is triangle-free and uses vertex set $W$.

Choose a node $(z, c) \in D$, reached from some $(v_0, N) \in D$ by a sequence of horizontal and downward moves. Each move decreases the level by $0$ or $1$, so every level in $[c, N]$ is visited; in particular every label in $[c, N]$ appears in $F_D$. Prepending an $F_D$-edge of label $N$ incident to $v_0$, reading off the horizontal edges of the sequence, and appending an $F_D$-edge of label $c$ incident to $z$ yields a non-increasing walk in $F_D$ with first edge label $N$ and last edge label $c$.

Let $w_0 w_1 \dots w_s$ ($s \ge 1$) be a **shortest** non-increasing walk in $F_D$ with $\lambda(w_0 w_1) = N$ and $\lambda(w_{s-1} w_s) = c$. We claim it is a simple path. Suppose $w_a = w_b$ with $0 \le a < b \le s$:
- If $a \ge 1$ and $b \le s - 1$, deleting $w_{a+1} \dots w_b$ gives the shorter non-increasing walk $w_0 \dots w_a w_{b+1} \dots w_s$ keeping both end labels.
- If $a = 0$ and $b \le s - 1$, then $b \ge 2$ (as $w_0 w_1$ is an edge), and $w_1 w_0 w_{b+1} \dots w_s$ has length $s - b + 1 < s$ and keeps both end labels.
- If $a \ge 1$ and $b = s$, then $a \le s - 2$, and $w_0 \dots w_a w_{s-1}$ has length $a + 1 < s$ and keeps both end labels.
- If $a = 0$ and $b = s$ with $s = 2$, then $w_0 w_1 w_0$ traverses a single edge twice, so $N = c$ and $w_0 w_1$ has length $1 < 2$.
- If $a = 0$ and $b = s$ with $s \ge 3$, then $w_1 w_0 w_{s-1}$ (using $w_0 = w_s$) has length $2 < s$ and edge labels $N, c$.

Every case contradicts minimality of $s$. Applying Lemma 2.1 to the simple path $w_0 \dots w_s$ in $F_D$ yields
$$|W| \ge N - c + 2.$$

- **Case $c = 0$:** $|V| \ge |W| \ge N + 2$.
- **Case $c \ge 1$:** Let $F_{\mathrm{low}} := \{e \in E : \lambda(e) < c\}$ and $V_{\mathrm{low}} \subseteq V$ its set of incident vertices. Since every layer $0, \dots, c - 1$ is nonempty, $F_{\mathrm{low}}$ is a flag $1$-layered family with $c \le N$ layers (top label $c - 1 < N$). By the induction hypothesis, $|V_{\mathrm{low}}| \ge c + 1$. Because every $w \in W$ has $\min I_w \ge c$, we have $W \cap V_{\mathrm{low}} = \emptyset$. Therefore
  $$|V| \ge |V_{\mathrm{low}}| + |W| \ge (c + 1) + (N - c + 2) = N + 3 > N + 2.$$

In both cases $N + 1 \le |V| - 1 \le m - 1$. Sharpness is attained by the path on $m$ vertices with edges $\{i, i + 1\}$ in layer $i$ ($0 \le i \le m - 2$). $\square$

---

## 4. Consequences for Higher Rank $r \ge 2$

Because links of flag $1$-layered families and contiguous layer ranges remain flag $1$-layered (Section 7 of `arXiv:2611.08071`), Theorem 1 yields two immediate improvements:

1. **Halved Larman–Barnette bound for flag $1$-layered families:** For every $m \ge r \ge 2$, every flag $1$-layered family of $r$-subsets of an $m$-set has at most $2^{r-2}(m - r) + 1$ layers (half the general bound $2^{r-1}(m - r) + 1$ of Theorem 2.1). Indeed, starting the block-decomposition induction of Theorem 2.1 at $r = 2$ with $\lambda'_2(m) = m - 1$, for $r \ge 3$ and $A = 2^{r-3}$ we have $\sum_{i=1}^k n_i \le 2m - r$, giving
   $$N + 1 \le \sum_{i=1}^k \bigl(A(n_i - r) + 1\bigr) \le A(2m - r - kr) + k = 2A(m - r) + 1 - (k - 1)(Ar - 1) \le 2^{r-2}(m - r) + 1.$$
2. **Unconditional Lemma 7.2 and Main Theorem E(a) at $p = r - 2$ / $p = d - 2$:** Carrying the upper bound $p = r - 2$ through the link recursion of Lemma 7.2 (an outer range keeps $(r, p)$ with smaller $m$, while a middle vertex-link reduces $(r, p)$ to $(r - 1, p - 1)$), the only flag base case invoked is $r = 2$ (where $p = 0$), now proved unconditionally by Theorem 1. Hence every $1$-layered family of $r$-sets on $m \ge r \ge 2$ vertices with flag deficiency $\mathrm{fd}(\mathcal{F}) \le r - 2$ has at most $(m - r + 1)\binom{\lfloor \log_2(m - r + 1) \rfloor + r - 2}{r - 2}$ layers, and Main Theorem E(a) of `arXiv:2611.08071` holds unconditionally for every pure normal $(d - 1)$-complex ($d \ge 2$) with $\mathrm{fd}(\Delta) \le d - 2$ at parameter $p = d - 2$.
