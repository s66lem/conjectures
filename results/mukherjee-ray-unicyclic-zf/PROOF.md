# Disproof of Log-Concavity for Unicyclic Connected Zero Forcing Polynomials (Mukherjee–Ray Problem 6.2)

**Target:** Problem 6.2 (and minimum order for Problem 6.4) of S. Mukherjee and P. Ray, *On the connected zero forcing polynomial of finite trees*, [arXiv:2611.10985v2](https://arxiv.org/abs/2611.10985) (v2 posted 25 Nov 2026).

> **Problem 6.2 (verbatim from v2):** "Determine the connected zero forcing polynomial of a unicyclic graph. Is this polynomial always log-concave? Furthermore, for fixed positive integers $n$ and $p$, do there exist unicyclic graphs $U_{\min}$ and $U_{\max}$, each having $n$ vertices and $p$ pendant vertices, such that $U_{\min} \le U \le U_{\max}$ for every unicyclic graph $U$ with $n$ vertices and $p$ pendant vertices?"

---

## Theorem

For integers $m \ge 3$ and $\ell \ge 0$, let $T_{m,\ell}$ denote the **tadpole graph** consisting of an $m$-cycle $C = (c_0, c_1, \dots, c_{m-1})$ together with a pendant path $c_0 - t_1 - \dots - t_\ell$ of length $\ell$ attached at $c_0$. Then $T_{m,\ell}$ is a connected unicyclic graph on $n = m + \ell$ vertices (with $n$ edges), and:

1. **Connected zero forcing characterization:** A subset $S \subseteq V(T_{m,\ell})$ is a connected zero forcing set of $T_{m,\ell}$ if and only if $T_{m,\ell}[S]$ is connected and $S$ contains two adjacent vertices of the cycle $C$.
2. **Closed-form connected zero forcing polynomial:** Setting
   $$A_m(b) := \begin{cases} b & 2 \le b \le m - 1, \\ 1 & b = m, \\ 0 & \text{otherwise,} \end{cases} \qquad N_m(b) := \begin{cases} m - b & 2 \le b \le m - 1, \\ 0 & \text{otherwise,} \end{cases}$$
   the number $Z_C(T_{m,\ell}, k)$ of connected zero forcing sets of size $k$ is
   $$Z_C(T_{m,\ell}, k) = N_m(k) + \sum_{a=0}^{\ell} A_m(k - a).$$
3. **Exact log-concavity criterion:** $Z_C(T_{m,\ell}; x) = \sum_{k=0}^{m+\ell} Z_C(T_{m,\ell}, k) x^k$ is log-concave **if and only if $m \le 4$ or $\ell \le 1$**.
4. **Counterexamples of every order $n \ge 7$ and sharp minimality:** For every $n \ge 7$, the unicyclic graph $T_{5, n-5}$ has non-log-concave $Z_C(T_{5, n-5}; x)$. The smallest counterexample is $T_{5,2}$ ($n = 7$), with
   $$Z_C(T_{5,2}; x) = 5x^2 + 7x^3 + 10x^4 + 8x^5 + 5x^6 + x^7, \qquad 7^2 = 49 < 50 = 5 \cdot 10.$$
   Exhaustively, every connected graph on $\le 6$ vertices has a log-concave connected zero forcing polynomial, and $T_{5,2}$ is the unique non-log-concave unicyclic graph on $7$ vertices.

---

## 1. Zero Forcing Sets and the Fort Lemma

Recall the standard zero forcing color-change rule on a graph $G = (V, E)$: if a colored vertex $v \in B$ has a unique uncolored neighbor $w \in N_G(v) \setminus B$, then $v$ forces $w$ to become colored ($B \mapsto B \cup \{w\}$). A subset $S \subseteq V$ is a **zero forcing set** if finitely many forcing steps color all of $V$; it is a **connected zero forcing set** if in addition the induced subgraph $G[S]$ is connected.

A nonempty subset $F \subseteq V$ is a **fort** of $G$ if every vertex $v \notin F$ that has a neighbor in $F$ has at least two neighbors in $F$.

**Lemma 1 (Fort Lemma).** Every zero forcing set $S$ of $G$ intersects every fort $F$ of $G$.

*Proof.* If $B \cap F = \emptyset$ and $v \in B$ forces $w$, then $v \notin F$. If $w \in F$, the fort condition gives a second neighbor $w' \in F \setminus \{w\}$ of $v$, which also satisfies $w' \notin B$, contradicting that $w$ is the unique uncolored neighbor of $v$. By induction on the number of forcing steps, $F$ remains uncolored forever, contradicting $B = V$ since $F \neq \emptyset$. $\square$

---

## 2. Proof of (1): Characterization on $T_{m,\ell}$

- **($\Rightarrow$):** Suppose $S$ is a connected zero forcing set of $T_{m,\ell}$.
  First, $F_1 := \{c_1, \dots, c_{m-1}\}$ is a nonempty fort: outside $F_1$, the vertex $c_0$ has two neighbors $c_1, c_{m-1} \in F_1$ (as $m \ge 3$), and no tail vertex $t_j$ is adjacent to any vertex of $F_1$. By Lemma 1, $S$ contains some cycle vertex $c_i$ with $1 \le i \le m - 1$.
  Second, $F_2 := V(T_{m,\ell}) \setminus \{c_i\}$ is a nonempty fort: $c_i$ is the unique vertex outside $F_2$, and its two cycle neighbors $c_{i-1}, c_{(i+1) \bmod m}$ are distinct and lie in $F_2$. By Lemma 1, $S$ contains some vertex $u \neq c_i$.
  Since $T_{m,\ell}[S]$ is connected, there is a path in $S$ from $c_i$ to $u$; its first step moves from $c_i$ to a neighbor $v \in S$. Because $1 \le i \le m - 1$, every neighbor of $c_i$ in $T_{m,\ell}$ is an adjacent cycle vertex, so $\{c_i, v\} \subseteq S$ is an adjacent cycle pair.

- **($\Leftarrow$):** Suppose $T_{m,\ell}[S]$ is connected and $S$ contains two adjacent cycle vertices $c_i, c_{(i+1) \bmod m}$.
  Every vertex $c_j$ with $1 \le j \le m - 1$ has degree $2$ in $T_{m,\ell}$ (neighbors $c_{j-1}$ and $c_{(j+1) \bmod m}$). Thus whenever $c_j$ and one of its cycle neighbors are colored, $c_j$ can force its other cycle neighbor (if not already colored).
  - If $i = 0$, starting from $\{c_0, c_1\}$, vertices $c_1, c_2, \dots, c_{m-2}$ sequentially force $c_2, c_3, \dots, c_{m-1}$, coloring the whole cycle $C$.
  - If $i = m - 1$, starting from $\{c_{m-1}, c_0\}$, vertices $c_{m-1}, c_{m-2}, \dots, c_2$ sequentially force $c_{m-2}, \dots, c_1$, coloring $C$.
  - If $1 \le i \le m - 2$, starting from $\{c_i, c_{i+1}\}$, forward forcing colors $c_{i+2}, \dots, c_{m-1}, c_0$ and backward forcing colors $c_{i-1}, \dots, c_1$, coloring $C$.
  Once all of $C$ is colored, $c_0$ has at most one uncolored neighbor ($t_1$, if $\ell \ge 1$), so $c_0, t_1, \dots, t_{\ell-1}$ force $t_1, \dots, t_\ell$ in turn, coloring all of $V(T_{m,\ell})$. $\square$

---

## 3. Proof of (2): Exact Enumeration

Let $S \subseteq V(T_{m,\ell})$ satisfy (1), and let $B = S \cap C$ ($|B| = b \ge 2$) and $T = S \cap \{t_1, \dots, t_\ell\}$ ($|T| = a$). Because deleting $c_0$ disconnects the tail from $C \setminus \{c_0\}$ and $T_{m,\ell}[S]$ is connected:
- **Case $c_0 \notin S$:** Then $T = \emptyset$ ($a = 0$), so $S = B$ is a contiguous arc of $b = k$ vertices inside the path $c_1 - c_2 - \dots - c_{m-1}$. There are $m - k$ such arcs for $2 \le k \le m - 1$, and $0$ otherwise — precisely $N_m(k)$.
- **Case $c_0 \in S$:** Then $T$ is a prefix $\{t_1, \dots, t_a\}$ for a unique $a \in \{0, 1, \dots, \ell\}$, and $B$ is a connected subset of $C$ containing $c_0$ of size $b = k - a \ge 2$. If $2 \le b \le m - 1$, $B$ is uniquely determined by how many vertices $r \in \{0, \dots, b - 1\}$ precede $c_0$ clockwise (namely $\{c_{m-r}, \dots, c_{m-1}, c_0, c_1, \dots, c_{b-1-r}\}$), giving $b = A_m(b)$ arcs. If $b = m$, $B = C$ ($1 = A_m(m)$ choice).

Summing over both disjoint cases gives $Z_C(T_{m,\ell}, k) = N_m(k) + \sum_{a=0}^{\ell} A_m(k - a)$. $\square$

---

## 4. Proof of (3) and (4): Log-Concavity Criterion

Let $z_k = Z_C(T_{m,\ell}, k)$. Note $z_0 = z_1 = 0$ and $z_k > 0$ for all $2 \le k \le m + \ell$ (no internal zeros).

- **Necessity ($m \ge 5$ and $\ell \ge 2 \implies$ not log-concave):**
  Since $m \ge 5$ and $\ell \ge 2$, the formula gives:
  $$z_2 = N_m(2) + A_m(2) = (m - 2) + 2 = m,$$
  $$z_3 = N_m(3) + A_m(3) + A_m(2) = (m - 3) + 3 + 2 = m + 2,$$
  $$z_4 = N_m(4) + A_m(4) + A_m(3) + A_m(2) = (m - 4) + 4 + 3 + 2 = m + 5.$$
  Therefore $z_3^2 - z_2 z_4 = (m + 2)^2 - m(m + 5) = 4 - m < 0$.
  For $m = 5, \ell = 2$: $(z_0, \dots, z_7) = (0, 0, 5, 7, 10, 8, 5, 1)$ with $7^2 = 49 < 50 = 5 \cdot 10$.

- **Sufficiency ($m \le 4$ or $\ell \le 1 \implies$ log-concave):**
  - If $\ell = 0$: $(z_2, \dots, z_m) = (m, m, \dots, m, 1)$, clearly log-concave.
  - If $\ell = 1$: for $m = 3$, $(z_2, z_3, z_4) = (3, 3, 1)$; for $m \ge 4$, $z_2 = m$, $z_k = m + k - 1$ for $3 \le k \le m - 1$, $z_m = m$, $z_{m+1} = 1$. Every triple satisfies $z_k^2 \ge z_{k-1} z_{k+1}$:
    - $k = 2$: $m^2 \ge 0$;
    - $k = 3$ ($m \ge 4$): $(m + 2)^2 \ge m(m + 3)$ ($m \ge 4$ for $m \ge 5$, or $36 \ge 32$ at $m = 4$);
    - $4 \le k \le m - 2$: $(m + k - 1)^2 = (m + k - 2)(m + k) + 1$;
    - $k = m - 1$ ($m \ge 5$): $(2m - 2)^2 - (2m - 3)m = 2m^2 - 5m + 4 > 0$;
    - $k = m$: $m^2 \ge (2m - 2) \cdot 1$ for $m \ge 3$.
  - If $m = 3$ ($\ell \ge 2$): $(z_2, \dots, z_{\ell+3}) = (3, 3, \dots, 3, 1)$, log-concave.
  - If $m = 4$ ($\ell \ge 2$): $(z_2, z_3, \dots, z_{\ell+2}, z_{\ell+3}, z_{\ell+4}) = (4, 6, 6, \dots, 6, 4, 1)$, log-concave since $4^2 \ge 0$, $6^2 \ge 4 \cdot 6$, $6^2 \ge 6 \cdot 6$, $4^2 \ge 6 \cdot 1$. $\square$
