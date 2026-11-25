# Resolution of Conjecture 5.6 and Disproof of Literal Hypothesis 3.2 (`arXiv:2610.09650`)

**Paper:** Tamás Csernák and Dániel T. Soukup, *The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem*, `arXiv:2610.09650` (October 7, 2026).

We establish two results on the exact definitions of `arXiv:2610.09650` (Definitions 2.1, 3.1, 5.1):
1. **Disproof of literal Hypothesis 3.2 (Almost Stacked Hypothesis, both parts):**
   - **Part (1) (Stacking):** On $P_4 = (0\text{-}1\text{-}2\text{-}3)$, all $32$ almost stacked configurations of size $12$ are stackable (while sizes $2 \le t \le 11$ each admit a non-stackable almost stacked configuration), so the least almost-stacked threshold is $12$. Yet $(9,0,0,3)$ of size $12$ is not stackable, bad almost stacked configurations reappear at sizes $13$ and $14$ (e.g. $(13,0,0,1)$), and $\mathrm{stack}(P_4) = 15 \ne 12$.
   - **Part (2) (Clearing):** On $G_5$ (triangle $0\text{-}1\text{-}2$ with path tail $2\text{-}3\text{-}4$), all $80$ almost stacked configurations of size $16$ are clearable (while sizes $2 \le t \le 15$ each admit a non-clearable almost stacked configuration), so the least almost-stacked threshold is $16$. Yet $(0,0,0,2,14)$ of size $16$ is not clearable, bad almost stacked configurations reappear at sizes $17$ and $21$ (e.g. $(0,0,0,0,21)$), and $\mathrm{clear}(G_5) = 22 \ne 16$.
2. **Unconditional Proof of Conjecture 5.6:** For every finite connected tree $T$,
   $$\mathrm{stack}(T) = \mathrm{estim}(T)$$
   holds without assuming the Almost Stacked Hypothesis. The proof also yields an explicit $O(n^2)$ stacking algorithm.

Both claims are independently verified by [verify.py](verify.py).

---

## 1. Disproof of Literal Hypothesis 3.2

Under Definitions 2.1 and 3.1 of `arXiv:2610.09650`:
- A configuration $c : V(G) \to \mathbb{N}$ is *stacked* if $|\mathrm{supp}(c)| = 1$ and *cleared* if $\|c\| = 1$.
- A configuration $c$ is *almost stacked* if there exists $v_0 \in V(G)$ such that $c(u) \le 1$ for all $u \in V(G) \setminus \{v_0\}$.
- Hypothesis 3.2 asserts that $\mathrm{stack}(G)$ (resp. $\mathrm{clear}(G)$ for non-bipartite $G$) equals the *least* integer $t \ge 2$ such that every almost stacked configuration in $\mathrm{Conf}_t(G)$ is stackable (resp. clearable).

Unlike unrestricted stackability/clearability—which is monotone for $t > |V(G)|$ by Lemma 4.7—almost-stacked stackability and clearability are **not monotone** in $t$:
- **On $P_4$:** Every $t \in \{2,\dots,11\}$ has a non-stackable almost stacked configuration; at $t = 12$, all $32$ almost stacked configurations stack, but $(9,0,0,3)$, $(3,0,0,9)$, $(6,0,0,6)$, and $(0,3,9,0)$ do not stack; non-stackable almost stacked configurations reappear at $t = 13$ ($(11,1,0,1)$, $(1,0,1,11)$) and $t = 14$ ($(13,0,0,1)$, $(1,0,0,13)$); and $\mathrm{stack}(P_4) = 15$.
- **On $G_5$ (edges $01, 12, 02, 23, 34$):** Every $t \in \{2,\dots,15\}$ has a non-clearable almost stacked configuration; at $t = 16$, all $80$ almost stacked configurations clear, but $(0,0,0,2,14)$, $(0,0,0,5,11)$, and $(0,0,1,2,13)$ do not clear; non-clearable almost stacked configurations reappear at $t = 17$ ($(0,0,0,1,16)$, $(0,0,1,1,15)$) and $t = 21$ ($(0,0,0,0,21)$); and $\mathrm{clear}(G_5) = 22$.

Across all $12{,}112$ connected graphs on $n \le 8$ vertices, literal Hypothesis 3.2 fails on $2{,}580$ `(graph, parameter)` pairs ($1{,}268$ stacking, $1{,}312$ clearing). By contrast, the monotone repair $1 + \max\{t : \text{some AS config of size } t \text{ is bad}\}$ holds for all $23{,}971$ checked pairs on $n \le 8$ (and for trees in stacking, follows from Theorem 2 below).

---

## 2. Unconditional Proof of Conjecture 5.6

**Theorem.** *For every finite connected tree $T$, $\mathrm{stack}(T) = \mathrm{estim}(T)$.*

*Proof.* For $|V(T)| = 1$, Definitions 2.1 and 5.1 give $\mathrm{stack}(K_1) = 2 = \mathrm{estim}(K_1)$. Assume now that $n = |V(T)| \ge 2$. The lower bound $\mathrm{stack}(T) \ge \mathrm{estim}(T)$ is Theorem 5.2 of `arXiv:2610.09650` (unconditional). It suffices to prove that every configuration $c$ on $T$ with $\|c\| \ge \mathrm{estim}(T)$ is stackable.

Let $L = \{v \in V(T) : \deg(v) = 1\}$ be the leaf set of $T$. For any $r \in V(T)$, write $R_r(y) = 2^{\mathrm{dist}_T(r, y)}$ and $E_r = \rho_T(r) + \mathrm{leaf}_T(r)$, so that $\mathrm{estim}(T) = 1 + \max_{r \in V(T)} E_r$ (since $n \ge 2$ implies $\rho_T(r) \ge 1$ and $\mathrm{leaf}_T(r) \ge 1$, hence $1 + E_r \ge 3 > 2$).

### Lemma A (Edge form of $E_r$)
For every $r \in V(T)$,
$$E_r = \sum_{y \in V(T) \setminus \{r\}} e_y, \qquad e_y := \begin{cases} \frac{3}{2} R_r(y) & \text{if } y \notin L, \\ \frac{1}{2} R_r(y) + 1 & \text{if } y \in L. \end{cases}$$

*Proof.* Root $T$ at $r$. Every $v \in V(T)$ has $\deg(v) = \#\mathrm{children}(v) + \mathbf{1}[v \ne r]$. For $v \ne r$ with $v \notin L$ (i.e., $\deg(v) > 1$), $\deg(v)$ contributes to $\rho_T(r)$; for $v = r$, $\deg(r) = \#\mathrm{children}(r)$ contributes; for $v \in L \setminus \{r\}$, $v$ does not enter $\rho_T(r)$ and contributes $1$ to $\mathrm{leaf}_T(r)$. Since each child $y \ne r$ has parent $p$ with $R_r(p) = \frac{1}{2} R_r(y)$,
$$\rho_T(r) + \mathrm{leaf}_T(r) = \sum_{y \ne r} \frac{1}{2} R_r(y) + \sum_{y \ne r,\, y \notin L} R_r(y) + \sum_{y \ne r,\, y \in L} 1 = \sum_{y \ne r} e_y. \quad\square$$

### Bottom-up greedy potential
Fix a root $w \in V(T)$ and denote by $B(y)$ the rooted subtree at $y$. Call $y \ne w$ **live** if $\sum_{u \in B(y)} c(u) > 0$. Define $\tau : \mathbb{Z} \to \mathbb{Z}$ by
$$\tau(V) := \begin{cases} 2V - 3 & \text{if } V \le 1, \\ V/2 & \text{if } V \ge 2 \text{ is even}, \\ (V - 3)/2 & \text{if } V \ge 3 \text{ is odd}. \end{cases}$$
Compute $V(y)$ bottom-up by
$$V(y) := c(y) + \sum_{z \text{ live child of } y} \tau(V(z)),$$
and set $v_w(c) := V(w)$.

### Lemma B (Soundness of the greedy strategy)
If $v_w(c) \ge 1$, then $c$ is stackable at $w$ (ending with $v_w(c)$ pebbles at $w$).

*Proof.* Define the recursive procedure $\mathrm{Run}(y)$, called when $B(y) \setminus \{y\}$ is untouched from $c$ and $y$ currently holds $c(y) + \delta(y)$ pebbles (where $\delta(y) \ge 0$ pebbles were delivered to $y$ prior to the call):
1. For each live child $z$ of $y$ with $V(z) \ge 1$: execute $\mathrm{Run}(z)$ (with $\delta(z) = 0$), then perform $\lfloor V(z)/2 \rfloor$ moves $z \Rightarrow y$.
2. For each live child $z$ of $y$ with $V(z) \le 0$: perform $1 - V(z)$ moves $y \Rightarrow z$ (so $\delta(z) = 1 - V(z)$), then execute $\mathrm{Run}(z)$.
3. For each live child $z$ of $y$ with $V(z) \le 0$ or ($V(z) \ge 1$ odd): perform one round $y \Rightarrow z$ followed by $z \Rightarrow y$.

We prove by bottom-up induction on $y$ that if $h(y) := V(y) + \delta(y) \ge 1$, then $\mathrm{Run}(y)$ performs only legal moves inside $B(y)$, empties $B(y) \setminus \{y\}$, and leaves $h(y)$ pebbles on $y$.

- If $y$ has no live children, $B(y) \setminus \{y\}$ is already empty, no moves are made, and $y$ holds $c(y) + \delta(y) = h(y)$ pebbles.
- In general, sibling subtrees are disjoint and each recursive call touches only its own subtree. In Step 1, each live child $z$ with $V(z) \ge 1$ satisfies $h(z) = V(z) \ge 1$, so by induction $\mathrm{Run}(z)$ empties $B(z) \setminus \{z\}$ and leaves $V(z)$ pebbles on $z$; the $\lfloor V(z)/2 \rfloor$ moves $z \Rightarrow y$ are legal and leave $V(z) \bmod 2 \in \{0,1\}$ pebbles on $z$.
- After Step 1, $y$ holds $P = c(y) + \delta(y) + \sum_{V(z) \ge 1} \lfloor V(z)/2 \rfloor$ pebbles. Let $D = \sum_{V(z) \le 0} (1 - V(z))$ be the number of payment moves in Step 2, and let $o$ be the number of live children with $V(z) \le 0$ or $V(z)$ odd (the number of rounds in Step 3). Since $\tau(V) = \lfloor V/2 \rfloor - \mathbf{1}[V \text{ odd}]$ for $V \ge 1$ and $\tau(V) = -2(1 - V) - 1$ for $V \le 0$, we have
  $$P - 2D - o = c(y) + \delta(y) + \sum_{z \text{ live}} \tau(V(z)) = V(y) + \delta(y) = h(y).$$
- In Step 2, before every payment move $y \Rightarrow z$, vertex $y$ holds at least $P - 2(D - 1) = h(y) + o + 2 \ge 3$ pebbles, so every payment is legal. Delivering $1 - V(z)$ pebbles to $z$ gives $h(z) = V(z) + (1 - V(z)) = 1 \ge 1$, so by induction $\mathrm{Run}(z)$ empties $B(z) \setminus \{z\}$ and leaves $1$ pebble on $z$.
- Entering Step 3, every child scheduled for a round holds exactly $1$ pebble with its proper subtree empty, and $y$ holds $P - 2D = h(y) + o$ pebbles. Before each round, $y$ holds at least $h(y) + 1 \ge 2$ pebbles, so $y \Rightarrow z$ is legal (raising $z$ from $1$ to $2$) and $z \Rightarrow y$ is legal (emptying $z$ and costing $y$ one net pebble).
- At the end of Step 3, $B(y) \setminus \{y\}$ is empty and $y$ holds $P - 2D - o = h(y)$ pebbles.

Applying the claim at $y = w$ with $\delta(w) = 0$ and $h(w) = v_w(c) \ge 1$ stacks $c$ at $w$. $\square$

### Lemma C (Fractional relaxation)
Define $\tau_f(V) := \min\bigl(2V - 3,\, (V - 3)/2\bigr)$. Then $\tau_f$ is nondecreasing, $\tau_f(V) \le \tau(V)$ for all $V \in \mathbb{Z}$, and defining $v_w^f(c)$ by the same bottom-up recursion with $\tau_f$ (using the same live set) yields $v_w(c) \ge v_w^f(c)$.

*Proof.* For $V \le 1$, $2V - 3 \le (V - 3)/2$, so $\tau_f(V) = 2V - 3 = \tau(V)$. For $V \ge 2$, $(V - 3)/2 < 2V - 3$, so $\tau_f(V) = (V - 3)/2 \le \tau(V)$ (equal for odd $V \ge 3$, strictly smaller for even $V \ge 2$). Both branches are increasing, so $\tau_f$ is nondecreasing and bottom-up induction gives $V(y) \ge V^f(y)$ for all $y$. $\square$

### Lemma D (Affine representation)
A *choice* $s$ assigns $s_y \in \{2, 1/2\}$ to each live vertex $y$. Since $B(z) \supseteq B(y)$ for every ancestor $z$ of $y$, every vertex on the path $[y, w)$ from a live vertex $y$ to $w$ (excluding $w$) is live. Set $\alpha_w := 1$ and, for each live $y$,
$$\alpha_y := \prod_{z \in [y, w)} s_z, \qquad \kappa_y := \begin{cases} 3/2 & \text{if } s_y = 2, \\ 3 & \text{if } s_y = 1/2. \end{cases}$$
Writing $S = \mathrm{supp}(c)$ (note every $u \in S \setminus \{w\}$ is live, so $\alpha_u$ is well-defined on $S$; non-live vertices have $c(u) = 0$), we have
$$v_w^f(c) = \min_s \left(\sum_{u \in S} \alpha_u c(u) - \beta_s\right), \qquad \beta_s := \sum_{y \text{ live}} \kappa_y \alpha_y.$$

*Proof.* Write $\tau_f(V) = \min_{s_y \in \{2, 1/2\}} (s_y V - \gamma(s_y))$ with $\gamma(2) = 3$ and $\gamma(1/2) = 3/2$. Because $s_y > 0$, minima commute with the recursion. Unrolling from $w$ down, each $u \in S$ contributes $\alpha_u c(u)$, and each live $y$ contributes $-\gamma(s_y) \prod_{z \in (y, w)} s_z = -(\gamma(s_y)/s_y)\alpha_y = -\kappa_y \alpha_y$. $\square$

### Lemma E (Comparison with $E_r$)
Fix a choice $s$ and nonempty $S = \mathrm{supp}(c)$, and assume that $w \in L \implies w \in S$. Let $r \in S$ minimize $\alpha_u$ over $u \in S$, and set $\rho_y := \alpha_y / \alpha_r$ for live $y$ and for $y = w$. Then
$$\sum_{y \text{ live}} \kappa_y \rho_y - \sum_{u \in S} (\rho_u - 1) \le E_r.$$

*Proof.* Note that $\rho_u \ge 1$ for every $u \in S$, with $\rho_r = 1$. Let $P = (r = p_0, p_1, \dots, p_k = w)$ be the unique $r$–$w$ path ($k = \mathrm{dist}_T(r, w) \ge 0$).

1. **Weight bounds.** For $0 \le j \le k$, we have $\alpha_r = \alpha_{p_j} \prod_{i=0}^{j-1} s_{p_i}$, so $\rho_{p_j} = \prod_{i=0}^{j-1} s_{p_i}^{-1} \le 2^j = R_r(p_j)$. For any live vertex $y \notin P$, let $m = p_j$ be the first vertex of $P$ on the $y$–$w$ path; then $\mathrm{dist}_T(r, y) = j + \mathrm{dist}_T(m, y)$ and $\rho_y = \rho_m \prod_{z \in [y, m)} s_z \le 2^j \cdot 2^{\mathrm{dist}_T(m, y)} = R_r(y)$, with the stronger bound $\rho_y \le \frac{1}{4} R_r(y)$ whenever $s_y = 1/2$.

2. **Termwise charging.** Write the left-hand side as $\sum_{y \in V(T)} \ell_y$, where $\ell_y := \kappa_y \rho_y \mathbf{1}[y \text{ live}] - (\rho_y - 1)\mathbf{1}[y \in S]$ (recall $w$ is never live). Compare against $E_r = \sum_{y \ne r} e_y$ from Lemma A:
   - **Off-path ($y \notin P$), not live:** then $y \notin S$, so $\ell_y = 0 < e_y$.
   - **Off-path, live, internal ($y \notin L$):** $\ell_y \le \kappa_y \rho_y$. If $s_y = 2$, $\kappa_y \rho_y = \frac{3}{2}\rho_y \le \frac{3}{2} R_r(y) = e_y$; if $s_y = 1/2$, $\kappa_y \rho_y = 3\rho_y \le \frac{3}{4} R_r(y) < e_y$.
   - **Off-path, live leaf ($y \in L$):** since $B(y) = \{y\}$, liveness implies $y \in S$, so $\ell_y = (\kappa_y - 1)\rho_y + 1$. If $s_y = 2$, $\ell_y = \frac{1}{2}\rho_y + 1 \le \frac{1}{2} R_r(y) + 1 = e_y$; if $s_y = 1/2$, $\ell_y = 2\rho_y + 1 \le 2 \cdot \frac{1}{4} R_r(y) + 1 = e_y$.
   - **On-path, $k = 0$ ($r = w$):** $w$ is not live and $\rho_w = 1$, so $\ell_w = 0$.
   - **On-path, $k \ge 1$:**
     - For every $0 \le j \le k - 2$, $p_{j+1}$ is an internal vertex of $P$ (hence $p_{j+1} \notin L$), and $\ell_{p_j} \le \kappa_{p_j} \rho_{p_j} \le 3 \cdot 2^j = \frac{3}{2} R_r(p_{j+1}) = e_{p_{j+1}}$.
     - If $w \notin L$, the same bound gives $\ell_{p_{k-1}} \le \frac{3}{2} R_r(w) = e_w$, while $\ell_w = -(\rho_w - 1)\mathbf{1}[w \in S] \le 0$.
     - If $w \in L$, then $w \in S$ by hypothesis, so $\ell_w = 1 - \rho_w$. Since $\rho_w = \rho_{p_{k-1}} s_{p_{k-1}}^{-1}$, checking both $s_{p_{k-1}} = 2$ ($\frac{3}{2} - \frac{1}{2} = 1$) and $s_{p_{k-1}} = 1/2$ ($3 - 2 = 1$) gives
       $$\ell_{p_{k-1}} + \ell_w \le \kappa_{p_{k-1}} \rho_{p_{k-1}} - \rho_w + 1 = \rho_{p_{k-1}} + 1 \le 2^{k-1} + 1 = \frac{1}{2} R_r(w) + 1 = e_w.$$

Summing over all off-path vertices and over $P$ yields $\sum_{y \in V(T)} \ell_y \le \sum_{y \ne r} e_y = E_r$. $\square$

### Lemma F (Size bound when $v_w(c) \le 0$)
If $c$ is a nonzero configuration such that ($w \in L \implies c(w) \ge 1$) and $v_w(c) \le 0$, then $\|c\| \le \mathrm{estim}(T) - 1$.

*Proof.* By Lemmas C and D, there exists a choice $s$ with $\sum_{u \in S} \alpha_u c(u) \le \beta_s$. Letting $r \in S$ minimize $\alpha_u$ over $S$, since $c(u) \ge 1$ and $\alpha_u \ge \alpha_r > 0$ on $S$,
$$\alpha_r(\|c\| - |S|) \le \sum_{u \in S} \alpha_u(c(u) - 1) \le \beta_s - \sum_{u \in S} \alpha_u.$$
Dividing by $\alpha_r$ and adding $|S|$, Lemma E gives
$$\|c\| \le \sum_{y \text{ live}} \kappa_y \rho_y - \sum_{u \in S} (\rho_u - 1) \le E_r \le \max_{r' \in V(T)} E_{r'} = \mathrm{estim}(T) - 1. \quad\square$$

### Completion of the proof
Let $c$ be any configuration on $T$ with $\|c\| \ge \mathrm{estim}(T) \ge 3$, and choose $w \in V(T)$ maximizing $v_w(c)$.

Suppose toward a contradiction that $w \in L$ and $c(w) = 0$, and let $x$ be the unique neighbor of $w$. When $T$ is rooted at $x$, vertex $w$ is a leaf with $c(w) = 0$ and is therefore not live, while every other neighbor $z$ of $x$ has the same rooted subtree as when $T$ is rooted at $w$; hence $v_x(c) = V_w(x) =: a$. When $T$ is rooted at $w$, $B_w(x) = T \setminus \{w\}$ holds $\|c\| > 0$ pebbles, so $x$ is live and $v_w(c) = c(w) + \tau(V_w(x)) = \tau(a)$. For every integer $a \in \mathbb{Z}$, $\tau(a) < a$ (if $a \le 1$, $2a - 3 < a$; if $a \ge 2$, $\tau(a) \le a/2 < a$). Thus $v_w(c) < v_x(c)$, contradicting the maximality of $w$.

Therefore $w \in L \implies c(w) \ge 1$. Since $\|c\| \ge \mathrm{estim}(T)$, Lemma F forces $v_w(c) \ge 1$. By Lemma B, $c$ is stackable at $w$. Thus $\mathrm{stack}(T) \le \mathrm{estim}(T)$, completing the proof of Conjecture 5.6. $\square$
