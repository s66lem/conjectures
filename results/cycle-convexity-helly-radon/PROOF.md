# Disproof of the Cycle Convexity Helly–Radon Conjecture (`arXiv:2609.34236v1`)

## 1. Conjecture

In Section 5 ("Conclusion") of *Computing the Helly Number, Radon Number and Rank in Cycle Convexity* (`arXiv:2609.34236v1`, 28 Sep 2026), R. S. Nair, B. S. Anand, Ullas Chandran S. V., J. R. Nascimento, and A. Anil pose:

> **Conjecture 1.** For every connected graph $G$ of order $n \ge 2$, we have $\mathrm{hl}_{cc}(G) = \mathrm{rd}_{cc}(G)$.

Here, for a simple undirected graph $G = (V, E)$ and $S \subseteq V$:
- The **cycle interval** $I_{cc}(S)$ consists of $S$ together with every vertex $w \in V$ lying on a cycle of $G$ whose other vertices all lie in $S$ (equivalently, $w \notin S$ has at least two distinct neighbors in a single connected component of $G[S]$).
- A set $W \subseteq V$ is **cycle convex** if $I_{cc}(W) = W$, and the **cycle convex hull** $\mathrm{Hull}_{cc}(S)$ is the smallest cycle convex set containing $S$.
- $S$ is **Helly independent** if $\bigcap_{a \in S} \mathrm{Hull}_{cc}(S \setminus \{a\}) = \emptyset$; $\mathrm{hl}_{cc}(G)$ is the maximum size of a Helly-independent set.
- $S$ is **Radon independent** if no bipartition $\{A, B\}$ of $S$ ($A, B \neq \emptyset$, $A \cap B = \emptyset$, $A \cup B = S$) satisfies $\mathrm{Hull}_{cc}(A) \cap \mathrm{Hull}_{cc}(B) \neq \emptyset$; $\mathrm{rd}_{cc}(G)$ is the maximum size of a Radon-independent set.

## 2. General Inequality (Levi Direction)

**Proposition 1.** For every finite graph $G$, every Helly-independent set is Radon independent, so $\mathrm{hl}_{cc}(G) \le \mathrm{rd}_{cc}(G)$.

*Proof.* Suppose $S$ has a Radon partition $\{A, B\}$ with $v \in \mathrm{Hull}_{cc}(A) \cap \mathrm{Hull}_{cc}(B)$. For any $a \in S$:
- if $a \in A$, then $B \subseteq S \setminus \{a\}$, so $v \in \mathrm{Hull}_{cc}(B) \subseteq \mathrm{Hull}_{cc}(S \setminus \{a\})$;
- if $a \in B$, then $A \subseteq S \setminus \{a\}$, so $v \in \mathrm{Hull}_{cc}(A) \subseteq \mathrm{Hull}_{cc}(S \setminus \{a\})$.

Hence $v \in \bigcap_{a \in S} \mathrm{Hull}_{cc}(S \setminus \{a\})$, so $S$ is Helly dependent. $\square$

## 3. Counterexample Graph $G_{16}$

Define the simple graph $G_{16} = (V, E)$ on $n = 16$ vertices and $m = 36$ edges as follows:
- For each $i \in \mathbb{Z}_3 = \{0, 1, 2\}$, take a clique $K^{(i)} \cong K_5$ on five vertices
  $$s_i = 5i,\quad t_i = 5i + 1,\quad u_i = 5i + 2,\quad p_i = 5i + 3,\quad q_i = 5i + 4.$$
- Add one central hub vertex $x = 15$ adjacent to $u_0, u_1, u_2$.
- Add three cyclic "port" edges $p_i q_{i+1}$ for $i \in \mathbb{Z}_3$: $(3, 9)$, $(8, 14)$, $(13, 4)$.

The graph $G_{16}$ is connected (every vertex in $K^{(i)}$ is equal or adjacent to $u_i$, which is adjacent to $x$) and has $3 \binom{5}{2} + 3 + 3 = 36$ edges (graph6 string: `O~{?GKFDw??@?BAB_DxAC`).

**Theorem 2 (Refutation of Conjecture 1).** The connected $16$-vertex graph $G_{16}$ satisfies
$$\mathrm{hl}_{cc}(G_{16}) = 5 < 6 = \mathrm{rd}_{cc}(G_{16}).$$

## 4. Complete Proof

**Lemma 1 (No triangles in independent sets).** If $T \subseteq V$ contains three pairwise adjacent vertices $a, b, c$, then $T$ is Radon dependent (and hence also Helly dependent).

*Proof.* Partition $T$ as $A = \{a\}$ and $B = T \setminus \{a\}$. Both $b, c \in B$ are adjacent to each other and to $a$, forming the triangle $a - b - c - a$, so $a \in \mathrm{Hull}_{cc}(B) \cap \mathrm{Hull}_{cc}(A)$. $\square$

In particular, every Radon-independent (or Helly-independent) subset $T \subseteq V(G_{16})$ satisfies $|T \cap K^{(i)}| \le 2$ for every $i \in \mathbb{Z}_3$.

**Lemma 2 (Clique and hub generation).**
1. If $A \subseteq V(G_{16})$ contains two distinct vertices $a, b \in K^{(i)}$, then $K^{(i)} \subseteq \mathrm{Hull}_{cc}(A)$.
2. If $\mathrm{Hull}_{cc}(A)$ contains two distinct full cliques $K^{(i)}$ and $K^{(j)}$ ($i \neq j$), then $x \in \mathrm{Hull}_{cc}(A)$.

*Proof.*
1. Every $w \in K^{(i)} \setminus \{a, b\}$ forms the triangle $w - a - b - w$ with $a, b \in A$.
2. Since $i \neq j$ in $\mathbb{Z}_3$, either $j \equiv i + 1$ or $i \equiv j + 1 \pmod 3$. Without loss of generality $j \equiv i + 1$. Then $x - u_i - p_i - q_{i+1} - u_{i+1} - x$ is a $5$-cycle whose four vertices other than $x$ all lie in $K^{(i)} \cup K^{(i+1)} \subseteq \mathrm{Hull}_{cc}(A)$, so $x \in \mathrm{Hull}_{cc}(A)$. $\square$

**Lemma 3 (Exact hulls of subsets of $S$).** Let $S = \{s_0, t_0, s_1, t_1, s_2, t_2\} = \{0, 1, 5, 6, 10, 11\}$. For any $A \subseteq S$, let $J(A) = \{i \in \mathbb{Z}_3 : s_i, t_i \in A\}$. Then
$$\mathrm{Hull}_{cc}(A) = W_A := A \cup \bigcup_{i \in J(A)} K^{(i)} \cup \begin{cases}\{x\} & \text{if } |J(A)| \ge 2, \\ \emptyset & \text{if } |J(A)| \le 1.\end{cases}$$

*Proof.* By Lemma 2, $W_A \subseteq \mathrm{Hull}_{cc}(A)$. Conversely, it suffices to show that $W_A$ is cycle convex, i.e. no $w \notin W_A$ has two distinct neighbors $u, v \in W_A$ connected by a walk in $G_{16}[W_A]$.
- **Case $w = x$.** Since $x \notin W_A$, we have $|J(A)| \le 1$. The neighbors of $x$ in $G_{16}$ are $u_0, u_1, u_2$. Because $u_k \notin S$, we have $u_k \in W_A \iff k \in J(A)$. Hence $x$ has at most $|J(A)| \le 1$ neighbor in $W_A$.
- **Case $w \in K^{(k)}$ for some $k \notin J(A)$.** Since $k \notin J(A)$, $W_A \cap K^{(k)} = A \cap K^{(k)}$ has cardinality at most $1$ and consists only of a vertex in $\{s_k, t_k\}$. Because $s_k$ and $t_k$ have no neighbors outside $K^{(k)}$, any vertex $z \in W_A \cap K^{(k)}$ is **isolated** in $G_{16}[W_A]$. On the other hand, every vertex $w \in K^{(k)}$ has at most one neighbor outside $K^{(k)}$ ($s_k, t_k$ have $0$; $u_k$ has only $x$; $p_k$ has only $q_{k+1}$; $q_k$ has only $p_{k-1}$). Therefore $w$ cannot have two distinct neighbors in $W_A$ outside $K^{(k)}$, and any neighbor of $w$ in $W_A \cap K^{(k)}$ is isolated in $G_{16}[W_A]$ and cannot reach any other vertex of $W_A$.

Thus $W_A$ is cycle convex, so $\mathrm{Hull}_{cc}(A) = W_A$. $\square$

**Proof of $\mathrm{rd}_{cc}(G_{16}) = 6$.**
- *Lower bound ($\ge 6$):* Let $\{A, B\}$ be any bipartition of $S$. Then $J(A) \cap J(B) = \emptyset$, so $|J(A)| + |J(B)| \le 3$, and therefore at most one of $J(A), J(B)$ has size $\ge 2$; hence $x \notin W_A \cap W_B$. The full cliques $\bigcup_{i \in J(A)} K^{(i)}$ and $\bigcup_{j \in J(B)} K^{(j)}$ are disjoint. Finally, a vertex $v \in A \cap K^{(k)}$ cannot belong to $K^{(k)}$ in $W_B$ (that requires $k \in J(B)$, hence $s_k, t_k \in B$, contradicting $A \cap B = \emptyset$), and symmetrically for $B$. Thus $W_A \cap W_B = \emptyset$, so $S$ is Radon independent and $\mathrm{rd}_{cc}(G_{16}) \ge |S| = 6$.
- *Upper bound ($\le 6$):* Suppose $T \subseteq V(G_{16})$ is Radon independent with $|T| \ge 7$. By Lemma 1, $|T \cap K^{(i)}| \le 2$ for each $i \in \mathbb{Z}_3$. Since $V(G_{16}) = K^{(0)} \sqcup K^{(1)} \sqcup K^{(2)} \sqcup \{x\}$, we must have $x \in T$ and $|T \cap K^{(i)}| = 2$ for all $i \in \mathbb{Z}_3$. Partition $T$ as $A = \{x\}$ and $B = T \setminus \{x\}$. By Lemma 2, $x \in \mathrm{Hull}_{cc}(B)$ (since $B$ has $2$ vertices in $K^{(0)}$ and $2$ vertices in $K^{(1)}$), so $x \in \mathrm{Hull}_{cc}(A) \cap \mathrm{Hull}_{cc}(B)$, contradicting Radon independence.

**Proof of $\mathrm{hl}_{cc}(G_{16}) = 5$.**
- *Lower bound ($\ge 5$):* Let $H_5 = \{s_0, t_0, s_1, t_1, s_2\} = \{0, 1, 5, 6, 10\} \subset S$. By Lemma 3:
  - $\mathrm{Hull}_{cc}(H_5 \setminus \{s_0\}) = \{t_0, s_2\} \cup K^{(1)}$ (missing $K^{(0)} \setminus \{t_0\}$, $K^{(2)} \setminus \{s_2\}$, and $x$, and in particular missing $s_0$ and $x$),
  - $\mathrm{Hull}_{cc}(H_5 \setminus \{t_0\}) = \{s_0, s_2\} \cup K^{(1)}$ (missing $t_0$),
  - $\mathrm{Hull}_{cc}(H_5 \setminus \{s_1\}) = \{t_1, s_2\} \cup K^{(0)}$ (missing $K^{(1)} \setminus \{t_1\}$),
  - $\mathrm{Hull}_{cc}(H_5 \setminus \{t_1\}) = \{s_1, s_2\} \cup K^{(0)}$ (missing $t_1$),
  - $\mathrm{Hull}_{cc}(H_5 \setminus \{s_2\}) = K^{(0)} \cup K^{(1)} \cup \{x\}$ (missing $s_2$).
  Every vertex of $G_{16}$ is missed by at least one of these five hulls, so $\bigcap_{a \in H_5} \mathrm{Hull}_{cc}(H_5 \setminus \{a\}) = \emptyset$. Thus $\mathrm{hl}_{cc}(G_{16}) \ge 5$.
- *Upper bound ($\le 5$):* Let $T \subseteq V(G_{16})$ be Helly independent with $|T| \ge 6$. By Proposition 1 and Lemma 1, $|T \cap K^{(i)}| \le 2$ for each $i \in \mathbb{Z}_3$. We show $x \in \mathrm{Hull}_{cc}(T \setminus \{a\})$ for every $a \in T$:
  - If $a = x$, then $|T \setminus \{x\}| \ge 5$, so at least two cliques $K^{(i)}, K^{(j)}$ contain $2$ vertices of $T \setminus \{x\}$, and Lemma 2 gives $x \in \mathrm{Hull}_{cc}(T \setminus \{x\})$.
  - If $a \neq x$ and $x \in T$, then $x \in T \setminus \{a\} \subseteq \mathrm{Hull}_{cc}(T \setminus \{a\})$.
  - If $a \neq x$ and $x \notin T$, then $|T| \ge 6$ forces $|T \cap K^{(i)}| = 2$ for all three cliques $i \in \mathbb{Z}_3$. Removing $a \in K^{(k)}$ leaves two full pairs in the other two cliques $K^{(i)}, K^{(j)}$ ($i, j \neq k$), so Lemma 2 gives $x \in \mathrm{Hull}_{cc}(T \setminus \{a\})$.
  Hence $x \in \bigcap_{a \in T} \mathrm{Hull}_{cc}(T \setminus \{a\})$, contradicting Helly independence. $\square$
