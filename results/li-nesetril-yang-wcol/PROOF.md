# Disproof of Li–Nešetřil–Yang Problem 3.6 and the Weak Inequality of Problem 3.5 (`arXiv:2611.33681v1`)

## 1. Definitions and Problem Statements

In §3.2 of *Generalized oriented chromatic numbers and directed generalized coloring numbers of graphs* ([arXiv:2611.33681v1](https://arxiv.org/abs/2611.33681v1), November 25, 2026), Wenwen Li, Jaroslav Nešetřil, and Daqing Yang define the directed generalized coloring numbers for an oriented graph $D$, a linear ordering $\sigma$ of $V(D)$, and an integer $k \ge 1$:

- A vertex $x$ is **weakly $(k, +)$-reachable** from $y$ under $\sigma$ if $x \le_\sigma y$ and there exists a directed path from $y$ to $x$ of length at most $k$ whose vertices $z$ all satisfy $x \le_\sigma z$.
- A vertex $x$ is **strongly $(k, +)$-reachable** from $y$ under $\sigma$ if, in addition, every internal vertex $z$ of the path satisfies $y <_\sigma z$.
- The **$(k, -)$-reachability** notions are defined identically using directed paths from $x$ to $y$ (equivalently, $(k, +)$-reachability in the reversed orientation $D^{\mathrm{rev}}$).
- Write $W^{k, \pm}_{D, \sigma}(y)$ and $S^{k, \pm}_{D, \sigma}(y)$ for the respective sets of reachable vertices (each containing $y$ via the length-$0$ path).

The parameters of an oriented graph $D$ are
$$\overrightarrow{\mathrm{wcol}}^+_k(D) = \min_\sigma \max_{y \in V(D)} \bigl|W^{k, +}_{D, \sigma}(y)\bigr|, \qquad \overrightarrow{\mathrm{wcol}}_k(D) = \min_\sigma \max_{y \in V(D)} \bigl|W^{k, +}_{D, \sigma}(y) \cup W^{k, -}_{D, \sigma}(y)\bigr|,$$
and $\overrightarrow{\mathrm{col}}^+_k(D)$, $\overrightarrow{\mathrm{col}}_k(D)$ are defined identically with $S$ in place of $W$. For an undirected graph $G$, each parameter is defined as the maximum over all orientations $D$ of $G$.

In §3.2, the authors ask:

- **Problem 3.5:** Are there linear functions $f, g$ such that for any graph $G$ and any $k \ge 1$, $\overrightarrow{\mathrm{col}}_k(G) \le f(\overrightarrow{\mathrm{col}}^+_k(G))$ and $\overrightarrow{\mathrm{wcol}}_k(G) \le g(\overrightarrow{\mathrm{wcol}}^+_k(G))$? In particular, do $\overrightarrow{\mathrm{col}}_k(G) \le 2\,\overrightarrow{\mathrm{col}}^+_k(G)$ and $\overrightarrow{\mathrm{wcol}}_k(G) \le 2\,\overrightarrow{\mathrm{wcol}}^+_k(G)$ hold?
- **Problem 3.6:** For any graph $G$ and any $k \ge 1$, is there an orientation $\vec{G}$ of $G$ such that $\overrightarrow{\mathrm{col}}^+_k(\vec{G}) = \lceil \overrightarrow{\mathrm{col}}_k(G)/2 \rceil$ and $\overrightarrow{\mathrm{wcol}}^+_k(\vec{G}) = \lceil \overrightarrow{\mathrm{wcol}}_k(G)/2 \rceil$?

## 2. Main Theorem

**Theorem 1.**
1. *(Forest Lemma)* For every finite forest $F$, every orientation $D$ of $F$, and every $k \ge 1$,
   $$\overrightarrow{\mathrm{col}}^+_k(D) = \overrightarrow{\mathrm{wcol}}^+_k(D) = 1,$$
   and hence $\overrightarrow{\mathrm{col}}^+_k(F) = \overrightarrow{\mathrm{wcol}}^+_k(F) = 1$.
2. *(Counterexample to Problem 3.6 and the factor-$2$ weak bound)* For the $4$-vertex path $P_4 = abcd$ and every $k \ge 2$,
   $$\overrightarrow{\mathrm{wcol}}_k(P_4) = 3, \qquad \overrightarrow{\mathrm{wcol}}^+_k(D) = 1 \quad \text{for every orientation } D \text{ of } P_4.$$
   Consequently, $\overrightarrow{\mathrm{wcol}}_k(P_4) = 3 > 2 = 2\,\overrightarrow{\mathrm{wcol}}^+_k(P_4)$, and no orientation $D$ of $P_4$ satisfies $\overrightarrow{\mathrm{wcol}}^+_k(D) = \lceil \overrightarrow{\mathrm{wcol}}_k(P_4)/2 \rceil = 2$. More generally, by subgraph monotonicity, every forest containing a $3$-edge path fails Problem 3.6 for all $k \ge 2$.
3. *(Unbounded separation)* For every integer $t \ge 1$, $N = 2^t - 1$, and $k \ge N - 1$,
   $$\overrightarrow{\mathrm{wcol}}_k(P_N) \ge t \qquad \text{while} \qquad \overrightarrow{\mathrm{wcol}}^+_k(P_N) = 1.$$
   Hence no function $g : \mathbb{N} \to \mathbb{N}$ satisfies $\overrightarrow{\mathrm{wcol}}_k(G) \le g(\overrightarrow{\mathrm{wcol}}^+_k(G))$ uniformly over all graphs $G$ and all $k \ge 1$.

## 3. Proofs

### 3.1 Proof of Part 1 (Forest Lemma)

Let $D$ be any orientation of a finite forest $F$. Any directed cycle in $D$ would project to a cycle in the underlying undirected graph $F$, so $D$ is a finite directed acyclic graph. Every finite nonempty DAG has a source (a vertex of in-degree $0$): otherwise, following incoming arcs backward indefinitely would repeat a vertex and form a directed cycle. Inducting on $|V(F)|$ by placing a source first produces a topological linear ordering $\sigma$ of $V(D)$ such that $u <_\sigma v$ for every arc $u \to v$ of $D$.

Along any directed path $y = w_0 \to w_1 \to \dots \to w_\ell = x$ with $\ell \ge 1$, we have $y = w_0 <_\sigma w_1 <_\sigma \dots <_\sigma w_\ell = x$, contradicting $x \le_\sigma y$. Hence no $x \ne y$ is weakly (or strongly) $(k, +)$-reachable from $y$, so $W^{k, +}_{D, \sigma}(y) = S^{k, +}_{D, \sigma}(y) = \{y\}$ for every $y \in V(D)$. Thus $\overrightarrow{\mathrm{wcol}}^+_k(D) \le 1$ and $\overrightarrow{\mathrm{col}}^+_k(D) \le 1$; since $y$ always lies in its own reachability set, both equal $1$. $\square$

### 3.2 Proof of Part 2 ($P_4$ for all $k \ge 2$ and Subgraph Monotonicity)

Since $W^{k, \pm}_{D, \sigma}(y)$ is nondecreasing in $k$, it suffices to show $\overrightarrow{\mathrm{wcol}}_2(\vec{P}_4) \ge 3$ for the directed path $\vec{P}_4 : a \to b \to c \to d$ (and $\overrightarrow{\mathrm{wcol}}_k(D) \le 3$ for every orientation $D$ of $P_4$).

**Lower bound ($\overrightarrow{\mathrm{wcol}}_2(\vec{P}_4) \ge 3$).** In $\vec{P}_4$, every pair of vertices at distance at most $2$ is joined by a directed path in one direction or the other. Hence $x \in W^{2, +}(y) \cup W^{2, -}(y)$ whenever $x \le_\sigma y$, $\mathrm{dist}(x, y) \le 2$, and every vertex on the $x$–$y$ subpath is $\ge_\sigma x$. Fix an arbitrary linear ordering $\sigma$ of $\{a, b, c, d\}$, and let $f$ be its minimum vertex:
- **$f = b$:** Every vertex is $\ge_\sigma b$, and $\mathrm{dist}(b, d) = 2$.
  - If $c <_\sigma d$, then $d$ reaches $\{d, c, b\}$ ($c$ via $c \to d$, $b$ via $b \to c \to d$ with $b \le_\sigma c, d$).
  - If $d <_\sigma c$, then $c$ reaches $\{c, b, d\}$ ($b$ via $b \to c$, $d$ via $c \to d$).
- **$f = c$:** Symmetric to $f = b$ (reversing the path $a \leftrightarrow d, b \leftrightarrow c$, which swaps $(k, +)$ and $(k, -)$).
- **$f = a$:** Let $g$ be the minimum of $\{b, c, d\}$ under $\sigma$.
  - If $g = b$, then $c$ reaches $\{c, b, a\}$ ($b$ via $b \to c$, $a$ via $a \to b \to c$ with $a \le_\sigma b, c$).
  - If $g = c$, then $b$ reaches $\{b, a, c\}$ ($a$ via $a \to b$, $c$ via $b \to c$).
  - If $g = d$, then $c$ reaches $\{c, d, a\}$ ($d$ via $c \to d$, $a$ via $a \to b \to c$ with $a \le_\sigma b, c$).
- **$f = d$:** Symmetric to $f = a$.

In all cases, $\max_y |W^{2, +}(y) \cup W^{2, -}(y)| \ge 3$, so $\overrightarrow{\mathrm{wcol}}_k(P_4) \ge \overrightarrow{\mathrm{wcol}}_2(\vec{P}_4) \ge 3$.

**Upper bound ($\overrightarrow{\mathrm{wcol}}_k(P_4) \le 3$).** For any orientation $D$ of $P_4$, take the ordering $\sigma : b < c < a < d$. For $b$ and $c$, at most $1$ and $2$ vertices are $\le_\sigma$-earlier respectively. For $a$, $d$ is $>_\sigma a$, so $|W(a)| \le 3$. For $d$, any $d$–$a$ path passes through $b$, and $a \not\le_\sigma b$ since $b <_\sigma a$; thus $a$ is NOT weakly reachable from $d$, leaving at most $\{d, c, b\}$, so $|W(d)| \le 3$. Hence $\overrightarrow{\mathrm{wcol}}_k(P_4) = 3$ for every $k \ge 2$.

**Subgraph Monotonicity (Lemma M).** If $H \subseteq G$, let $D_H$ be an orientation of $H$ attaining $\overrightarrow{\mathrm{wcol}}_k(H)$, and extend $D_H$ arbitrarily to an orientation $D$ of $G$. For any ordering $\sigma$ of $V(G)$ with restriction $\sigma_H$ to $V(H)$ and any $y \in V(H)$, every path in $D_H$ witnessing $x \in W^{k, \pm}_{D_H, \sigma_H}(y)$ is also a valid path in $D$ under $\sigma$, so $W^{k, \pm}_{D_H, \sigma_H}(y) \subseteq W^{k, \pm}_{D, \sigma}(y)$. Taking $\max_y$ and $\min_\sigma$ yields $\overrightarrow{\mathrm{wcol}}_k(G) \ge \overrightarrow{\mathrm{wcol}}_k(H)$. In particular, every forest $F$ containing a $3$-edge path has $\overrightarrow{\mathrm{wcol}}_k(F) \ge 3$ and $\lceil \overrightarrow{\mathrm{wcol}}_k(F)/2 \rceil \ge 2$, while every orientation of $F$ has $\overrightarrow{\mathrm{wcol}}^+_k = 1$. $\square$

### 3.3 Proof of Part 3 (Unbounded Separation on $P_{2^t - 1}$)

Fix $t \ge 1$, $N = 2^t - 1$, and $k \ge N - 1$. Orient $P_N$ as the directed path $0 \to 1 \to \dots \to N - 1$, and fix an arbitrary linear ordering $\sigma$ of $\{0, \dots, N - 1\}$.

We construct by recursion a nested sequence of nonempty contiguous intervals $Q_0 \supset Q_1 \supset \dots \supset Q_{t - 1}$ with $|Q_i| \ge 2^{t - i} - 1$ and vertices $m_i = \min_\sigma Q_i \in Q_i$:
- Start with $Q_0 = [0, N - 1]$, which has $|Q_0| = 2^t - 1$.
- Given $Q_i = [\ell, r]$ with $|Q_i| = r - \ell + 1 \ge 2^{t - i} - 1$ and $i + 1 < t$, let $m_i = \min_\sigma Q_i$. Deleting $m_i$ splits $Q_i \setminus \{m_i\}$ into two disjoint intervals $[\ell, m_i - 1]$ and $[m_i + 1, r]$ whose sizes sum to $|Q_i| - 1 \ge 2^{t - i} - 2$. By pigeonhole, the larger interval $Q_{i + 1}$ has cardinality at least $(2^{t - i} - 2)/2 = 2^{t - (i + 1)} - 1 \ge 1$.

Let $y = m_{t - 1} \in Q_{t - 1}$. Because the intervals are strictly nested ($m_i \notin Q_{i + 1} \supseteq Q_j$ for all $j > i$), the $t$ vertices $m_0, m_1, \dots, m_{t - 1}$ are pairwise distinct. Moreover, for each $i < t - 1$:
- $y \in Q_{i + 1} \subset Q_i$ and $m_i = \min_\sigma Q_i$, so $m_i <_\sigma y$;
- the contiguous subpath between $y$ and $m_i$ lies entirely inside the interval $Q_i$, so every vertex $z$ on this subpath satisfies $m_i \le_\sigma z$;
- this subpath is a directed path (from $m_i$ to $y$ if $m_i < y$, or from $y$ to $m_i$ if $y < m_i$) of length $|y - m_i| \le N - 1 \le k$.

Hence $m_i \in W^{k, +}_{\vec{P}_N, \sigma}(y) \cup W^{k, -}_{\vec{P}_N, \sigma}(y)$ for every $0 \le i \le t - 1$, giving $\bigl|W^{k, +}(y) \cup W^{k, -}(y)\bigr| \ge t$. Since $\sigma$ was arbitrary, $\overrightarrow{\mathrm{wcol}}_k(P_N) \ge t$, while Part 1 gives $\overrightarrow{\mathrm{wcol}}^+_k(P_N) = 1$. If any single function $g : \mathbb{N} \to \mathbb{N}$ satisfied $\overrightarrow{\mathrm{wcol}}_k(G) \le g(\overrightarrow{\mathrm{wcol}}^+_k(G))$ for all $G$ and $k \ge 1$, then $t \le g(1)$ for every $t \ge 1$, a contradiction. $\square$

## 4. Sharp Boundary at $k = 1$

For $k = 1$, Problem 3.6 has a **positive** answer for every finite graph $G$:
1. By standard degeneracy duality, for every orientation $D$, $\overrightarrow{\mathrm{col}}^+_1(D) = \overrightarrow{\mathrm{wcol}}^+_1(D) = 1 + \max_{S \subseteq V(D)} \delta^+(D[S])$, where $\delta^+$ denotes minimum out-degree.
2. Reversing a single arc changes $\max_S \delta^+(D[S])$ by at most $1$, and every acyclic orientation achieves value $1$.
3. Letting $d = \mathrm{col}(G) - 1 = \overrightarrow{\mathrm{col}}_1(G) - 1 = \overrightarrow{\mathrm{wcol}}_1(G) - 1$, choose a subgraph $H \subseteq G$ with minimum degree $\delta(H) = d$. An Euler-tour orientation of $H$ (pairing odd-degree vertices via an auxiliary vertex) orients every vertex with out-degree at least $\lfloor d/2 \rfloor$, so extending it to $G$ gives $\overrightarrow{\mathrm{col}}^+_1(D^*) \ge 1 + \lfloor d/2 \rfloor = \lceil \mathrm{col}(G)/2 \rceil$.
4. Connecting an acyclic orientation to $D^*$ by single-arc flips and applying discrete intermediate values yields an orientation $D$ with $\overrightarrow{\mathrm{col}}^+_1(D) = \overrightarrow{\mathrm{wcol}}^+_1(D) = \lceil \mathrm{col}(G)/2 \rceil$. $\square$

*(Remark: The strong inequality $\overrightarrow{\mathrm{col}}_k(G) \le 2\,\overrightarrow{\mathrm{col}}^+_k(G)$ of Problem 3.5 remains open.)*

## 5. Machine Verification

- **Lean 4 (`lean/Conjectures/LiNesetrilYangWcol.lean`):** Formally proves the Forest Lemma (arbitrary finite acyclic simple graphs via topological ordering), the exact $P_4$ disproof of Problem 3.6 and the weak factor-$2$ inequality for all $k \ge 2$, subgraph monotonicity, and the binary-halving lower bound $\overrightarrow{\mathrm{wcol}}_k(P_{2^t - 1}) \ge t$ ruling out any uniform function $g$, using only standard Lean axioms `[propext, Classical.choice, Quot.sound]`.
- **Python (`results/li-nesetril-yang-wcol/verify.py`):** Exhaustively checks all $65{,}988$ oriented forests on $\le 6$ vertices for $k \in \{1, 2, 3, 4\}$, exact $P_4$ parameters for $k \in \{2, 3, 4\}$, all $24$ orderings in the hand case analysis, and the halving chain exhaustively for $N \in \{3, 7\}$ and constructively for $N \in \{15, 31, 63\}$.
