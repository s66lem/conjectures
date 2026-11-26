# Disproof of Zai–Lv–Sabir / Tian–Dong Conjecture 1.14 for All $r \ge 5$

## Problem Statement

In *Spanning cyclability of split graphs* (`arXiv:2611.32794v1`, 24 November 2026), Jingfan Zai, Wenjing Lv, and Eminjan Sabir state the following conjecture (originally Conjecture 6.1 of Tian and Dong, `arXiv:2603.12770v1`; the case $r = 3$ is Theorem 1.13):

> **Conjecture 1.14 (Tian et al. / Zai–Lv–Sabir).** Let $r \ge 3$ be an integer. Every $r$-connected $\{K_{1,r+1}, K_{1,r+1}+e\}$-free split graph with at least $2r + 7$ vertices is Hamilton-connected.

Here $K_{1,r+1}+e$ denotes the graph obtained from the star $K_{1,r+1}$ by adding one edge between two leaves, and forbidden subgraphs are induced.

## Main Result

**Theorem.** Conjecture 1.14 is **false for every integer $r \ge 5$**. Specifically:
1. For **$r = 5$**, the $22$-vertex Paley $(11, 5, 2)$ biplane split graph ($22 \ge 17 = 2 \cdot 5 + 7$) is a $5$-connected $\{K_{1,6}, K_{1,6}+e\}$-free split graph that is not Hamilton-connected.
2. For **every $r \ge 6$**, the $(2r + 8)$-vertex circulant split graph $G(r+4, \{0, 1, \dots, r-1\})$ ($2r + 8 \ge 2r + 7$) is an $r$-connected $\{K_{1,r+1}, K_{1,r+1}+e\}$-free split graph that is not Hamilton-connected.

(In addition, a simple double-counting argument shows that any balanced $r$-regular $\{K_{1,r+1}, K_{1,r+1}+e\}$-free split graph satisfies $m \le \binom{r}{2} + 1$, so no balanced $r$-regular counterexample has order $\ge 15 = 2 \cdot 4 + 7$ at $r = 4$; the case $r = 4$ of Conjecture 1.14 remains open.)

## Unified Construction and Proof

Let $m \ge 2$ and $S \subseteq \mathbb{Z}/m\mathbb{Z}$. Define the **split circulant graph** $G(m, S)$ on vertex set $V = C \sqcup I$ with $C = \{c_a : a \in \mathbb{Z}/m\mathbb{Z}\}$ and $I = \{i_b : b \in \mathbb{Z}/m\mathbb{Z}\}$ by:
- $C$ is a clique of size $m$,
- $I$ is an independent set of size $m$, and
- $c_a$ is adjacent to $i_b$ if and only if $b - a \in S$.

**Proposition.** *Suppose $|S| = r < m$ and for every nonzero shift $d \in (\mathbb{Z}/m\mathbb{Z}) \setminus \{0\}$,*
$$|S \cap (S + d)| \ge 2.$$
*Then $G(m, S)$ is a split graph on $2m$ vertices that is:*
1. *$r$-connected,*
2. *$\{K_{1,r+1}, K_{1,r+1}+e\}$-free, and*
3. *not Hamilton-connected.*

*Proof.*
- **Split partition:** Immediate from the definition ($C$ is a clique, $I$ is an independent set).
- **$r$-connectivity:** We have $|V| = 2m > r$. Delete any set $D \subseteq V$ of size $|D| < r$. Since $|C| = m > r > |D|$, $C \setminus D$ is nonempty (and forms a clique, hence is connected). Every surviving vertex $i_b \in I \setminus D$ has $|S| = r > |D|$ neighbors $\{c_{b-s} : s \in S\}$ in $C$, so at least one lies in $C \setminus D$. Thus every two vertices in $V \setminus D$ are joined by a path of length at most $3$ inside $V \setminus D$.
- **$\{K_{1,r+1}, K_{1,r+1}+e\}$-freeness:** Let $c \in V$ be any center and let $L \subseteq N(c)$ be any subset of $|L| = r + 1$ neighbors. We show that the induced subgraph $G[L]$ contains at least $2$ edges.
  - $c$ cannot lie in $I$, because every vertex of $I$ has degree $|S| = r < r + 1$.
  - Hence $c = c_a \in C$. Write $L_C = L \cap C$ and $L_I = L \cap I$. Since $L_I \subseteq N_I(c_a) = \{i_{s+a} : s \in S\}$ has $|L_I| \le r$, we have $|L_C| \ge 1$. Moreover, for every $c_{a'} \in L_C$ (so $a' \ne a$), the shift $d = a' - a \ne 0$ satisfies
    $$|N_I(c_a) \cap N_I(c_{a'})| = |S \cap (S + (a' - a))| \ge 2.$$
  - If $|L_C| = 1$, say $L_C = \{c_{a'}\}$, then $|L_I| = r$, so $L_I = N_I(c_a)$. Thus $c_{a'}$ has at least $2$ neighbors in $L_I$, giving at least $2$ edges in $G[L]$.
  - If $|L_C| = 2$, say $L_C = \{c_{a_1}, c_{a_2}\}$, then $|L_I| = r - 1$, so $L_I$ omits only one vertex of $N_I(c_a)$. Since $|N_I(c_a) \cap N_I(c_{a_1})| \ge 2$, the vertex $c_{a_1}$ still has at least one neighbor in $L_I$. Together with the clique edge $c_{a_1}c_{a_2}$, $G[L]$ has at least $2$ edges.
  - If $|L_C| \ge 3$, then the clique $L_C$ alone spans at least $\binom{3}{2} = 3 \ge 2$ edges in $G[L]$.
- **Not Hamilton-connected:** Suppose for contradiction that $G(m, S)$ admits a Hamilton path $p(0), p(1), \dots, p(2m-1)$ from $c_0$ to $c_1$. Let $T = \{t \in \{0, \dots, 2m-1\} : p(t) \in I\}$, so $|T| = |I| = m$. Since $p(2m-1) = c_1 \notin I$, every $t \in T$ satisfies $t + 1 \le 2m - 1$. Because $I$ is an independent set, $p(t + 1) \in C$ for every $t \in T$, and $p(t + 1) \ne p(0) = c_0$ (as $t + 1 \ge 1$). Thus $t \mapsto p(t + 1)$ injects the $m$-element set $T$ into the $(m - 1)$-element set $C \setminus \{c_0\}$, a contradiction. $\square$

### Instantiations

1. **$r = 5$:** Take $m = 11$ and the Paley quadratic-residue difference set $S = \{1, 3, 4, 5, 9\} \subseteq \mathbb{Z}/11\mathbb{Z}$. Then $|S| = 5$, $2m = 22 \ge 17 = 2 \cdot 5 + 7$, and every nonzero shift $d \in (\mathbb{Z}/11\mathbb{Z}) \setminus \{0\}$ satisfies $|S \cap (S + d)| = 2$.
2. **$r \ge 6$:** Take $m = r + 4$ and $S = \{0, 1, \dots, r - 1\} \subseteq \mathbb{Z}/(r+4)\mathbb{Z}$. Then $|S| = r$, $2m = 2r + 8 \ge 2r + 7$, and for every shift $d \in \mathbb{Z}/(r+4)\mathbb{Z}$, inclusion–exclusion gives
   $$|S \cap (S + d)| = |S| + |S + d| - |S \cup (S + d)| \ge r + r - (r + 4) = r - 4 \ge 2.$$

## Formal Verification

The complete proof above — including both the $r = 5$ Paley $(11, 5, 2)$ counterexample and the infinite family for all $r \ge 6$ — is formally verified in Lean 4 with zero `sorry`, zero custom axioms, and zero `native_decide` in `lean/Conjectures/ZaiLvSabirSplitHamilton.lean`:
- `ZaiLvSabirSplitHamilton.paley22_counterexample`
- `ZaiLvSabirSplitHamilton.circulant_counterexample_all_ge_6`
- `ZaiLvSabirSplitHamilton.zai_lv_sabir_conjecture_1_14_false_all_ge_5`
