# Laplacian Spectral Radius of Token Graphs: Proof of the Connected Conjecture and Complete Equality Characterization

## Problem Statement

For a finite simple graph $G = (V, E)$ of order $n$ and $1 \le k \le n - 1$, the *$k$-token graph* $F_k(G)$ has vertex set $\binom{V}{k}$ (the $k$-element subsets of $V$), with two $k$-subsets $S, T$ adjacent if and only if their symmetric difference $S \triangle T$ is an edge of $G$. Let $L(H)$ denote the combinatorial Laplacian of a graph $H$, with quadratic form
$$f^\top L(H) f = \sum_{uv \in E(H)} (f_u - f_v)^2,$$
and let $\rho(H) := \max_{f \ne 0} \frac{f^\top L(H) f}{f^\top f}$ denote the Laplacian spectral radius of $H$.

In *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs* (`arXiv:2610.00500v1`, September 2026), X. Song, C. Dalfó, M. À. Fiol, and S. Zhang posed the following conjecture:

> **Conjecture.** Let $G$ be a graph of order $n (\ge 4)$, the equality $\rho(F_k(G)) = \rho(G)$ holds for all $k$ with $2 \le k \le \lfloor n/2 \rfloor$ if and only if $G \cong S_n$.

Here $S_n = K_{1, n-1}$ is the star on $n$ vertices. While the literal all-graphs statement fails for disconnected graphs such as $K_2 \cup 2K_1$ (previously noted in `trureturing`), we prove that the intended connected version holds — in fact strictly at $k = 2$ — and classify all equality cases among arbitrary graphs of order $n \ge 4$.

## Main Theorems

**Theorem 1 (Connected Graphs).** Let $G$ be a connected graph of order $n \ge 4$ that is not isomorphic to the star $S_n$. Then
$$\rho(F_2(G)) > \rho(G).$$
Consequently, for connected graphs of order $n \ge 4$, $\rho(F_k(G)) = \rho(G)$ for all $2 \le k \le \lfloor n/2 \rfloor$ if and only if $G \cong S_n$.

**Theorem 2 (Complete Classification for All Graphs).** Let $G$ be any graph of order $n \ge 4$. Then $\rho(F_k(G)) = \rho(G)$ for all $2 \le k \le \lfloor n/2 \rfloor$ if and only if $G$ is one of:
1. the edgeless graph $\overline{K_n}$,
2. $S_m \cup (n - m)K_1$ for some $2 \le m \le n$, or
3. $K_3 \cup (n - 3)K_1$.

## Lemmas

**Lemma 0 (Subgraph Monotonicity).** If $H'$ is a subgraph of $H$ and $f$ is supported on $V(H')$, then $f^\top L(H) f \ge f^\top L(H') f$. Hence $\rho(H) \ge \rho(H')$.

*Proof.* Every edge of $H'$ is an edge of $H$, and each edge contributes a nonnegative square $(f_u - f_v)^2 \ge 0$. $\square$

**Lemma 1 (Grone–Merris Star Test Vector).** Let $S \in V(H)$ have degree $D := \deg_H(S) \ge 1$. Define $f_S = D$, $f_T = -1$ for $T \in N_H(S)$, and $f_T = 0$ otherwise. Then
$$f^\top L(H) f = D(D + 1)^2 + e_H\bigl(N_H(S),\, V(H) \setminus N_H[S]\bigr), \qquad f^\top f = D(D + 1).$$
Hence $\rho(H) \ge D + 1$, with strict inequality whenever there is an edge between $N_H(S)$ and $V(H) \setminus N_H[S]$.

*Proof.* The $D$ edges incident to $S$ each contribute $(D - (-1))^2 = (D + 1)^2$, edges within $N_H(S)$ contribute $(-1 - (-1))^2 = 0$, edges between $N_H(S)$ and $V(H) \setminus N_H[S]$ each contribute $(-1 - 0)^2 = 1$, and all remaining edges contribute $0$. Dividing by $f^\top f = D^2 + D = D(D + 1)$ gives the claim. $\square$

**Lemma 2 (Edge-Difference Bound).** Let $G$ be a connected graph with at least one edge, let $\lambda = \rho(G)$, and let $x \ne 0$ satisfy $L(G) x = \lambda x$. Choose an edge $uv \in E(G)$ maximizing $|x_u - x_v| =: M$, oriented so that $x_u - x_v = M$. Then $M > 0$ and
$$\lambda \le |N_G(u) \cup N_G(v)| = d_u + d_v - |N_G(u) \cap N_G(v)|.$$

*Proof.* If $M = 0$, then $x$ is constant on every edge, hence constant on the connected graph $G$, so $L(G) x = 0$, contradicting $\lambda \ge 1 > 0$ (since $G$ has an edge). Subtracting $(L(G)x)_v = \lambda x_v$ from $(L(G)x)_u = \lambda x_u$ yields
$$\lambda M = \lambda(x_u - x_v) = \sum_{w \in N(u)} (x_u - x_w) + \sum_{w \in N(v)} (x_w - x_v).$$
Partition the terms according to $N(u) \cup N(v) = \{v\} \sqcup \{u\} \sqcup (N(u) \cap N(v)) \sqcup (N(u) \setminus N[v]) \sqcup (N(v) \setminus N[u])$:
- $w = v$ in the first sum contributes $x_u - x_v = M$;
- $w = u$ in the second sum contributes $x_u - x_v = M$;
- each $c \in N(u) \cap N(v)$ appears in both sums and contributes $(x_u - x_c) + (x_c - x_v) = x_u - x_v = M$;
- each $w \in N(u) \setminus N[v]$ satisfies $x_u - x_w \le |x_u - x_w| \le M$;
- each $w \in N(v) \setminus N[u]$ satisfies $x_w - x_v \le |x_w - x_v| \le M$.

Summing gives $\lambda M \le M |N(u) \cup N(v)|$. Dividing by $M > 0$ finishes the proof. $\square$

**Lemma 3 (Cartesian Product of Stars).** In $K_{1, a} \square K_{1, b}$ ($a, b \ge 1$) with star centres $u, v$ and leaf sets $X, Y$ ($|X| = a$, $|Y| = b$), define $P_u = a$, $P_x = -1$ ($x \in X$), $Q_v = b$, $Q_y = -1$ ($y \in Y$), and $y(s, t) = P_s Q_t$. Then $y \ne 0$ and
$$L(K_{1, a} \square K_{1, b})\, y = (a + b + 2)\, y.$$

*Proof.* In $K_{1, a}$, $(L P)_u = a(a - (-1)) = a(a + 1) = (a + 1) P_u$ and $(L P)_x = -1 - a = (a + 1) P_x$ for $x \in X$. Similarly $L(K_{1, b}) Q = (b + 1) Q$. For $H_1 \square H_2$, $(L(H_1 \square H_2)(P \otimes Q))_{(s, t)} = (L_1 P)_s Q_t + P_s (L_2 Q)_t = (a + b + 2) P_s Q_t$. $\square$

**Lemma 4 (Star-Product Embedding in $F_2(G)$).** Let $uv \in E(G)$, $X = N(u) \setminus \{v\}$, $A_0 = N(u) \setminus N[v]$, and $Y = B_0 = N(v) \setminus N[u]$. Then $\{u\} \cup X$ and $\{v\} \cup Y$ are disjoint, and $\varphi(s, t) := \{s, t\}$ is an injective graph homomorphism from $K_{1, |X|} \square K_{1, |Y|}$ into $F_2(G)$.

*Proof.* Since $uv \in E(G)$, $u \ne v$ and $u \in N[u]$, so $u \notin \{v\} \cup Y$. For $x \in X$, $x \in N(u) \setminus \{v\}$, so $x \ne v$ and $x \in N[u]$, whence $x \notin Y$. Thus $(\{u\} \cup X) \cap (\{v\} \cup Y) = \emptyset$, making $\varphi$ injective. For every edge $(u, t)(s, t)$ ($s \in X, t \in \{v\} \cup Y$), $\varphi(u, t) \triangle \varphi(s, t) = \{u, s\} \in E(G)$; for every edge $(s, v)(s, t)$ ($s \in \{u\} \cup X, t \in Y$), $\varphi(s, v) \triangle \varphi(s, t) = \{v, t\} \in E(G)$. $\square$

**Lemma 5 (Strict Perturbation Witness).** In the setting of Lemma 4, assume $a := |X| \ge 1$, $b := |Y| \ge 1$, and $A_0 \ne \emptyset$. Set $\rho_0 := a + b + 2 = |N(u) \cup N(v)|$. Then $\rho(F_2(G)) > \rho_0$.

*Proof.* Let $W = \varphi((\{u\} \cup X) \times (\{v\} \cup Y))$ and let $\tilde{y} \in \mathbb{R}^{V(F_2(G))}$ be the vector $y$ of Lemma 3 transported to $W$ via $\varphi$ and extended by $0$ outside $W$. By Lemmas 0, 3, and 4, $\tilde{y}^\top L(F_2(G)) \tilde{y} \ge \rho_0 \tilde{y}^\top \tilde{y}$.

Pick $x_0 \in A_0$ and set $S := \{u, x_0\}$. Since both $u, x_0 \in \{u\} \cup X$ and $(\{u\} \cup X) \cap (\{v\} \cup Y) = \emptyset$, we have $S \notin W$ and $\tilde{y}_S = 0$. Every neighbor $T$ of $S$ in $F_2(G)$ that belongs to $W$ arises either by moving $u$ to a vertex $w \in N(u) \cap (\{v\} \cup Y)$ (forcing $w = v$ since $Y \cap N(u) = \emptyset$, giving $T = \{v, x_0\} = \varphi(x_0, v)$ with $\tilde{y}_T = -b$) or by moving $x_0$ to a vertex $w \in N(x_0) \cap (\{v\} \cup Y)$ (forcing $w \in Y \cap N(x_0)$ since $x_0 \in A_0 \implies x_0 \not\sim v$, giving $T = \{u, w\} = \varphi(u, w)$ with $\tilde{y}_T = -a$). Therefore
$$g := (L(F_2(G))\tilde{y})_S = -\sum_{T \in N_{F_2}(S) \cap W} \tilde{y}_T = b + a |Y \cap N(x_0)| \ge b \ge 1 > 0.$$
For $z := \tilde{y} + \varepsilon e_S$ ($\varepsilon > 0$), since $\tilde{y}_S = 0$ and $L(F_2(G))$ is symmetric,
$$z^\top L(F_2(G)) z - \rho_0 z^\top z = (\tilde{y}^\top L \tilde{y} - \rho_0 \tilde{y}^\top \tilde{y}) + 2\varepsilon g + \varepsilon^2 (\deg_{F_2}(S) - \rho_0) \ge 2\varepsilon g + \varepsilon^2 (\deg_{F_2}(S) - \rho_0).$$
Choosing $\varepsilon := \frac{g}{|\deg_{F_2}(S) - \rho_0| + 1} > 0$ gives $z^\top L(F_2(G)) z > \rho_0 z^\top z$ (and $z \ne 0$ since $z_S = \varepsilon > 0$), hence $\rho(F_2(G)) > \rho_0$. $\square$

**Lemma 6 (Stars and Triangles).** For every $m \ge 2$ and $1 \le j \le m - 1$, $\rho(F_j(S_m)) = m$. Moreover, $F_1(K_3) \cong F_2(K_3) \cong K_3$, so $\rho(F_j(K_3)) = 3$ for $j \in \{1, 2\}$.

*Proof.* Let $c$ be the centre of $S_m$. Partition $V(F_j(S_m))$ into $\mathcal{A} = \{S : c \in S\}$ (each of degree $s := m - j$) and $\mathcal{B} = \{S : c \notin S\}$ (each of degree $t := j$). Every edge of $F_j(S_m)$ joins $\mathcal{A}$ to $\mathcal{B}$, so $F_j(S_m)$ is bipartite (and connected since $1 \le j \le m - 1$).
- For every edge $ST$ ($S \in \mathcal{A}, T \in \mathcal{B}$), $|N(S) \cup N(T)| \le \deg(S) + \deg(T) = s + t = m$, so Lemma 2 gives $\rho(F_j(S_m)) \le m$.
- Setting $f_S = s$ for $S \in \mathcal{A}$ and $f_T = -t$ for $T \in \mathcal{B}$ gives $(L f)_S = s(s + t) = m f_S$ for $S \in \mathcal{A}$ and $(L f)_T = t(-t - s) = m f_T$ for $T \in \mathcal{B}$, so $\rho(F_j(S_m)) \ge m$.

For $K_3$, complementing subsets gives an isomorphism $F_2(K_3) \cong F_1(K_3) \cong K_3$, with $\rho(K_3) = 3$. $\square$

## Proof of Theorem 1

Let $G$ be connected of order $n \ge 4$ and not isomorphic to $S_n$.

- **Case 1: Some vertex $c \in V(G)$ has degree $n - 1$.** Since $G \not\cong S_n$, there is an edge $pq \in E(G)$ with $p, q \ne c$, so $H := S_n + pq$ (centred at $c$) is a spanning subgraph of $G$. In $F_2(H)$, the vertex $S := \{c, p\}$ has degree $D = n - 1$ (moving $c$ to any of the $n - 2$ vertices outside $\{c, p\}$, or moving $p$ to $q$). Since $n \ge 4$, pick $\ell \in V(G) \setminus \{c, p, q\}$. Then $T := \{\ell, p\} \in N_{F_2(H)}(S)$ is adjacent to $U := \{\ell, c\}$, whereas $U \notin N_{F_2(H)}[S]$ because $S \triangle U = \{p, \ell\} \notin E(H)$. By Lemmas 0 and 1, $\rho(F_2(G)) \ge \rho(F_2(H)) > (n - 1) + 1 = n$. Meanwhile Lemma 2 gives $\rho(G) \le |N(u) \cup N(v)| \le n$. Thus $\rho(F_2(G)) > \rho(G)$.

- **Case 2: Every vertex of $G$ has degree $< n - 1$.** Choose an edge $uv \in E(G)$ as in Lemma 2, so $\rho(G) \le |N(u) \cup N(v)| =: \rho_0$. Let $A_0 = N(u) \setminus N[v]$ and $B_0 = N(v) \setminus N[u]$.
  - If $A_0 = \emptyset$, then $N(u) \subseteq N[v]$, so $\rho_0 = d_v + 1$. Since $d_v < n - 1$, pick $z \notin N[v]$; connectivity gives $d_z \ge 1$. Because $z \notin N[v]$, the $d_v$ moves of $v$ and the $d_z$ moves of $z$ from $\{v, z\}$ yield $d_v + d_z$ distinct neighbors in $F_2(G)$, so $\deg_{F_2(G)}(\{v, z\}) = d_v + d_z \ge d_v + 1$. By Lemma 1, $\rho(F_2(G)) \ge d_v + 2 > \rho_0 \ge \rho(G)$.
  - If $B_0 = \emptyset$, the same argument applies with $u$ and $v$ swapped.
  - If $A_0 \ne \emptyset$ and $B_0 \ne \emptyset$, then $a = |N(u) \setminus \{v\}| \ge |A_0| \ge 1$ and $b = |B_0| \ge 1$, so Lemma 5 gives $\rho(F_2(G)) > \rho_0 \ge \rho(G)$.

Since $n \ge 4 \implies 2 \le \lfloor n/2 \rfloor$, equality fails at $k = 2$ for every connected non-star graph, while Lemma 6 gives $\rho(F_k(S_n)) = n = \rho(S_n)$ for all $1 \le k \le n - 1$. $\square$

## Proof of Theorem 2

Let $G$ have order $n \ge 4$. For any graph $G = G_1 \sqcup G_2$, $F_k(G)$ is the disjoint union over $k_1 + k_2 = k$ ($0 \le k_i \le |V(G_i)|$) of $F_{k_1}(G_1) \square F_{k_2}(G_2)$ (taking $F_0(H) \cong K_1$). For any Cartesian product $H_1 \square H_2$, taking tensor products of top eigenvectors shows $\rho(H_1 \square H_2) \ge \rho(H_1) + \rho(H_2)$ (in fact equality holds).

1. **At least two nontrivial components:** Suppose $G$ has two distinct connected components $G_1, G_2$ each containing an edge. Then $\rho(G_1) > 0$, $\rho(G_2) > 0$, and $F_2(G)$ contains $F_1(G_1) \square F_1(G_2) \cong G_1 \square G_2$ as a subgraph. Choosing $G_1$ to achieve $\rho(G_1) = \rho(G)$ and $G_2$ any other nontrivial component gives $\rho(F_2(G)) \ge \rho(G_1) + \rho(G_2) > \rho(G)$.

2. **Exactly one nontrivial component $H$:** Write $G = H \sqcup I$ where $I$ consists of $n - |H|$ isolated vertices and $m := |H| \ge 2$. Then $\rho(G) = \rho(H)$, and for every $k$, $F_k(G)$ is the disjoint union of $\binom{n - m}{k - j}$ copies of $F_j(H)$ over all $j$ with $\max(0, k - (n - m)) \le j \le \min(m, k)$.
   - For $k = 2$, $j = 2$ is feasible whenever $m \ge 2$, so $F_2(H)$ is a component of $F_2(G)$ and $\rho(F_2(G)) \ge \rho(F_2(H))$. If $m \ge 4$ and $H \not\cong S_m$, Theorem 1 gives $\rho(F_2(G)) \ge \rho(F_2(H)) > \rho(H) = \rho(G)$.
   - If $m \le 3$, the connected graphs on $2$ or $3$ vertices are $K_2 = S_2$, $P_3 = S_3$, and $K_3$.
   - Conversely, if $H \cong S_m$ ($2 \le m \le n$) or $H \cong K_3$, then for every $2 \le k \le \lfloor n/2 \rfloor$ we have $1 \le k \le n - 1$, so there is at least one feasible $j \in \{1, \dots, m - 1\}$ (namely $j = \min(k, m - 1)$ satisfies $j \ge 1$ and $k - j \le n - m$ because $k \le n - 1$ when $j = m - 1$). Every feasible $j \in \{0, m\}$ contributes isolated vertices ($\rho = 0$), and every feasible $j \in \{1, \dots, m - 1\}$ satisfies $\rho(F_j(H)) = \rho(H)$ by Lemma 6. Hence $\rho(F_k(G)) = \rho(H) = \rho(G)$.

3. **No edges ($G \cong \overline{K_n}$):** Every $F_k(\overline{K_n})$ is edgeless, so $\rho(F_k(\overline{K_n})) = 0 = \rho(\overline{K_n})$. $\square$
