# Complete Resolution of Agyingi–Gaba Question `q:modular` (`arXiv:2611.32417v1`)

**Target:** Question `q:modular` (final section) of C. A. Agyingi and Y. U. Gaba, *Smyth completeness and nonexpansive iteration in $q$-hyperconvex $T_0$-quasi-metric spaces*, [arXiv:2611.32417v1](https://arxiv.org/abs/2611.32417) (math.GN, 25 Nov 2026).

> **Question (`q:modular`, verbatim):** "Is the specialization order $(Y, \le_q)$ of the Isbell-hull of the equilateral three-point space, described in Lemma `lem:Y`, modular? Does $N_5$ occur as a sublattice of $(Y, \le_q)$, or more generally of the specialization order of some bounded $q$-hyperconvex space?"
>
> "Computational sampling of triples in $Y$ consistent with the modular law [...] returns no obvious counterexample; we conjecture that $(Y, \le_q)$ is modular but not distributive."

---

## Main Theorem

Let $X = [0, 1]^3$ equipped with the bounded $T_0$-quasi-metric
$$q(g, h) := \max_{k \in \{1, 2, 3\}} \max(h_k - g_k, 0),$$
whose specialization order is the reverse coordinatewise order:
$$g \le_q h \iff q(g, h) = 0 \iff \forall k \in \{1, 2, 3\},\; h_k \le g_k.$$
Let $Y = \{g \in [0, 1]^3 : \text{the two largest coordinates of } g \text{ coincide}\}$ (Lemma `lem:Y` of `arXiv:2611.32417v1`) and let
$$S := \{g \in [0, 1]^3 : g_3 \le \max(g_1, g_2)\}.$$
Then:
1. **$(Y, \le_q)$ is a modular, non-distributive lattice**, confirming the authors' conjecture. In particular, **$N_5$ does not occur as a sublattice of $(Y, \le_q)$**.
2. **$(S, q)$ is a bounded $q$-hyperconvex $T_0$-quasi-metric space** whose specialization order $(S, \le_q)$ is a lattice **containing $N_5$ as a sublattice** (and hence is non-modular).

---

## 1. Lattice Structure via Deflationary Retractions

Define two maps $\rho_Y, \rho_S : X \to X$ by
$$\rho_Y(g)_k := \min\Bigl(g_k,\; \max_{j \neq k} g_j\Bigr) \quad (k = 1, 2, 3), \qquad \rho_S(g) := \bigl(g_1,\; g_2,\; \min(g_3, \max(g_1, g_2))\bigr).$$

**Lemma 1.** For both $(\rho, F) = (\rho_Y, Y)$ and $(\rho, F) = (\rho_S, S)$:
1. $\rho(g) \in F$ and $\rho(g) \le_{\mathrm{coord}} g$ for all $g \in X$;
2. $\rho(g) = g \iff g \in F$;
3. $\rho$ is coordinatewise monotone: $g \le_{\mathrm{coord}} h \implies \rho(g) \le_{\mathrm{coord}} \rho(h)$;
4. $F$ is closed under coordinatewise maximum $\max(g, h)$.

Consequently, $(F, \le_q)$ is a lattice with specialization meet and join given by
$$g \wedge_q h = \max(g, h), \qquad g \vee_q h = \rho(\min(g, h)).$$

*Proof.* Properties (1)–(3) follow directly from the definitions using coordinatewise inequalities. For (4), if $g, h \in F$, then $\max(g, h) \ge_{\mathrm{coord}} g, h$ implies $\rho(\max(g, h)) \ge_{\mathrm{coord}} \rho(g) = g$ and $\rho(\max(g, h)) \ge_{\mathrm{coord}} \rho(h) = h$, hence $\rho(\max(g, h)) \ge_{\mathrm{coord}} \max(g, h) \ge_{\mathrm{coord}} \rho(\max(g, h))$, so $\max(g, h) \in F$.

Under $\le_q$ (the reverse of $\le_{\mathrm{coord}}$), $\max(g, h) \in F$ is immediately the greatest lower bound $g \wedge_q h$. For the least upper bound, $u := \rho(\min(g, h)) \in F$ satisfies $u \le_{\mathrm{coord}} \min(g, h) \le_{\mathrm{coord}} g, h$, so $g \le_q u$ and $h \le_q u$. If $x \in F$ satisfies $g \le_q x$ and $h \le_q x$, then $x \le_{\mathrm{coord}} \min(g, h)$, so $x = \rho(x) \le_{\mathrm{coord}} \rho(\min(g, h)) = u$, i.e., $u \le_q x$. Thus $u = g \vee_q h$. $\square$

---

## 2. Theorem A: $(Y, \le_q)$ is Modular and Non-Distributive

Define $v : X \to \mathbb{R}$ by
$$v(g) := \max(g_1, g_2, g_3) + \min(g_1, g_2, g_3).$$

**Step 1 (Key overlap identity).** For all $g, h \in Y$,
$$\max_{k \in \{1,2,3\}} \min(g_k, h_k) = \min\bigl(\max_k g_k,\; \max_k h_k\bigr).$$
*Proof.* Clearly $\min(g_k, h_k) \le \min(\max g, \max h)$ for every $k$, giving "$\le$". Conversely, since $g \in Y$, its maximum $M_g = \max_k g_k$ is attained on a $2$-element subset $A \subseteq \{1, 2, 3\}$; likewise $M_h = \max_k h_k$ is attained on a $2$-element subset $B \subseteq \{1, 2, 3\}$. Since $|A| + |B| = 4 > 3$, there exists $k \in A \cap B$, for which $\min(g_k, h_k) = \min(M_g, M_h)$. $\square$

**Step 2 (Valuation identity).** For all $g, h \in Y$,
$$v(g \vee_q h) + v(g \wedge_q h) = v(g) + v(h).$$
*Proof.* For any $x \in X$ with sorted coordinates $x_{(1)} \le x_{(2)} \le x_{(3)}$, we have $\rho_Y(x)$ with sorted coordinates $(x_{(1)}, x_{(2)}, x_{(2)})$, so
$$v(\rho_Y(x)) = x_{(2)} + x_{(1)} = (x_1 + x_2 + x_3) - \max_k x_k.$$
In particular, for every $y \in Y$ (since $\rho_Y(y) = y$), $v(y) = \sum_k y_k - \max_k y_k$.
Let $J = g \wedge_q h = \max(g, h) \in Y$ and $m = \min(g, h) \in X$, so $g \vee_q h = \rho_Y(m)$. Using $\sum_k J_k + \sum_k m_k = \sum_k g_k + \sum_k h_k$, $\max_k J_k = \max(\max_k g_k, \max_k h_k)$, and Step 1 ($\max_k m_k = \min(\max_k g_k, \max_k h_k)$):
$$v(g \vee_q h) + v(g \wedge_q h) = \sum_k m_k - \max_k m_k + \sum_k J_k - \max_k J_k = \sum_k g_k + \sum_k h_k - \max_k g_k - \max_k h_k = v(g) + v(h). \qquad \square$$

**Step 3 (Strict antimonotonicity of $v$ on $(Y, \le_q)$).** If $g, h \in Y$ satisfy $g \le_q h$ (i.e., $h \le_{\mathrm{coord}} g$) and $g \neq h$, then $v(h) < v(g)$.
*Proof.* Clearly $h \le_{\mathrm{coord}} g$ implies $\max h \le \max g$ and $\min h \le \min g$, so $v(h) \le v(g)$. Suppose $v(h) = v(g)$; then $\max h = \max g =: M$ and $\min h = \min g =: m$. For $y \in Y$, each coordinate equals either $M$ or $m$, and at most one coordinate can be strictly less than $M$ (when $m < M$). If $m = M$, then $g = (M, M, M) = h$. If $m < M$, then $h$ has at most one coordinate equal to $m$, and since $h \le_{\mathrm{coord}} g$, every coordinate where $g_k = m$ must also satisfy $h_k = m$; since $g$ also has a unique coordinate equal to $m$ (its minimum), that coordinate coincides for $g$ and $h$, while the other two coordinates equal $M$ in both, forcing $g = h$. $\square$

**Step 4 (Modularity and non-distributivity).** Let $a, b, c \in Y$ with $a \le_q c$. Set $\ell = a \vee_q (b \wedge_q c)$ and $r = (a \vee_q b) \wedge_q c$. In any lattice, $\ell \le_q r$. Since $a \le_q c$, we have $a \wedge_q (b \wedge_q c) = a \wedge_q b$ and $(a \vee_q b) \vee_q c = b \vee_q c$. Applying Step 2 twice on each side:
$$v(\ell) = v(a) + v(b \wedge_q c) - v(a \wedge_q b) = v(a) + v(b) + v(c) - v(b \vee_q c) - v(a \wedge_q b),$$
$$v(r) = v(a \vee_q b) + v(c) - v(b \vee_q c) = v(a) + v(b) - v(a \wedge_q b) + v(c) - v(b \vee_q c).$$
Hence $v(\ell) = v(r)$, so by Step 3, $\ell = r$. Thus $(Y, \le_q)$ is modular, and consequently contains no $N_5$ sublattice.

Finally, $0 = (0,0,0)$, $e_1 = (0,1,1)$, $e_2 = (1,0,1)$, $e_3 = (1,1,0)$, and $1 = (1,1,1)$ all belong to $Y$ and satisfy $e_i \wedge_q e_j = 1$ and $e_i \vee_q e_j = 0$ for all $i \neq j$, forming an $M_3$ sublattice; hence $(Y, \le_q)$ is not distributive. $\square$

---

## 3. Theorem B: Bounded $q$-Hyperconvex Space $(S, q)$ Containing $N_5$

Recall that a $T_0$-quasi-metric space $(S, q)$ is **$q$-hyperconvex** if for every index set $I$, points $(y_i)_{i \in I}$ in $S$, and nonnegative radii $(r_i)_{i \in I}, (s_i)_{i \in I}$ satisfying the compatibility condition
$$q(y_i, y_j) \le r_i + s_j \qquad (\forall i, j \in I),$$
there exists $z \in S$ such that $q(y_i, z) \le r_i$ and $q(z, y_i) \le s_i$ for all $i \in I$.

**Proposition 1.** $(S, q)$ is a bounded $q$-hyperconvex $T_0$-quasi-metric space.
*Proof.* As a subspace of $(X, q)$, $(S, q)$ is bounded ($q \le 1$) and $T_0$. Given a compatible family $(y_i, r_i, s_i)_{i \in I}$ in $S$, if $I = \emptyset$ then $z = (0, 0, 0) \in S$ works trivially. Otherwise, for each $k \in \{1, 2, 3\}$ define
$$L_k := \max\Bigl(0,\; \sup_{i \in I} (y_{i,k} - s_i)\Bigr), \qquad U_k := \min\Bigl(1,\; \inf_{i \in I} (y_{i,k} + r_i)\Bigr).$$
Since $0 \le y_{i,k} \le 1$ and $r_i, s_i \ge 0$, the sets $\{y_{i,k} - s_i\}$ and $\{y_{i,k} + r_i\}$ are bounded above by $1$ and below by $0$, respectively. For every $i, j \in I$, compatibility gives $y_{i,k} - y_{j,k} \le q(y_j, y_i) \le r_j + s_i$, so $y_{i,k} - s_i \le y_{j,k} + r_j$. Taking $\sup_i$ and $\inf_j$ shows $0 \le L_k \le U_k \le 1$ for $k = 1, 2, 3$.

Now set
$$z := \bigl(U_1,\; U_2,\; \min(U_3, \max(U_1, U_2))\bigr) = \rho_S(U_1, U_2, U_3).$$
Clearly $z \in S$, $L_1 \le z_1 \le U_1$, $L_2 \le z_2 \le U_2$, and $z_3 \le U_3$. To verify $L_3 \le z_3$, we already have $L_3 \le U_3$ and $0 \le \max(U_1, U_2)$; for every $i \in I$, since $y_i \in S$ we have $y_{i,3} \le \max(y_{i,1}, y_{i,2})$, so
$$y_{i,3} - s_i \le \max(y_{i,1} - s_i,\; y_{i,2} - s_i) \le \max(L_1, L_2) \le \max(U_1, U_2).$$
Taking $\sup_i$ gives $L_3 \le \max(U_1, U_2)$, hence $L_3 \le z_3 \le U_3$. Therefore for every $i \in I$ and $k \in \{1, 2, 3\}$,
$$z_k - y_{i,k} \le U_k - y_{i,k} \le r_i \quad\text{and}\quad y_{i,k} - z_k \le y_{i,k} - L_k \le s_i,$$
which (since $r_i, s_i \ge 0$) yields $q(y_i, z) \le r_i$ and $q(z, y_i) \le s_i$. $\square$

**Proposition 2.** $(S, \le_q)$ contains $N_5$ as a sublattice (and is therefore not modular).
*Proof.* Consider the five points of $S$:
$$t = \bigl(\tfrac{1}{4}, \tfrac{1}{4}, \tfrac{1}{4}\bigr), \quad c = \bigl(0, \tfrac{1}{4}, \tfrac{1}{4}\bigr), \quad a = \bigl(0, \tfrac{1}{4}, 0\bigr), \quad b = \bigl(\tfrac{1}{4}, 0, \tfrac{1}{4}\bigr), \quad o = (0, 0, 0).$$
All five satisfy $g_3 \le \max(g_1, g_2)$. Under $\le_q$ (reverse coordinatewise order):
- $t <_q c <_q a <_q o$ and $t <_q b <_q o$, with $b$ incomparable to both $c$ and $a$;
- $c \wedge_q b = \max(c, b) = (\tfrac{1}{4}, \tfrac{1}{4}, \tfrac{1}{4}) = t$ and $a \wedge_q b = \max(a, b) = (\tfrac{1}{4}, \tfrac{1}{4}, \tfrac{1}{4}) = t$;
- $a \vee_q b = \rho_S(\min(a, b)) = \rho_S(0, 0, 0) = o$ and $c \vee_q b = \rho_S(\min(c, b)) = \rho_S(0, 0, \tfrac{1}{4}) = (0, 0, 0) = o$.

Thus $\{t, c, a, b, o\}$ is a sublattice of $(S, \le_q)$ isomorphic to $N_5$, and the modular law fails explicitly:
$$c \vee_q (b \wedge_q a) = c \vee_q t = c \neq a = o \wedge_q a = (c \vee_q b) \wedge_q a. \qquad \square$$
