# Disproof of González D'León–Wachs Conjecture 4.13(2) (`arXiv:2608.08692v2`)

We disprove **Conjecture 4.13(2)** of Rafael S. González D'León and Michelle L. Wachs, *Weighted bond posets and a new chromatic symmetric function* (`arXiv:2608.08692v2`).

## 1. Definitions (Verbatim from `arXiv:2608.08692v2`, §§2 and 4)

- **Weighted bond poset $\mathcal{W}\Pi_G$ (§2):** For a finite simple graph $G = (V, E)$, a *weighted bond partition* of $G$ is a set $\boldsymbol{\pi} = \{B_1^{v_1}, \dots, B_r^{v_r}\}$ such that $\{B_1, \dots, B_r\}$ partitions $V$, each induced subgraph $G|_{B_i}$ is connected, and $v_i \in \{0, 1, \dots, |B_i| - 1\}$. The partial order $\le$ on $\mathcal{W}\Pi_G$ is defined by
  $$\{A_1^{w_1}, \dots, A_j^{w_j}\} \le \{B_1^{v_1}, \dots, B_r^{v_r}\}$$
  iff $\{A_i\}$ refines $\{B_m\}$ and whenever $B_m = A_{i_1} \cup \cdots \cup A_{i_\ell}$, we have $v_m - (w_{i_1} + \cdots + w_{i_\ell}) \in \{0, 1, \dots, \ell - 1\}$.
- **Möbius polynomial $\mu_G(t)$ (§2):** With minimum element $\hat{0} = \{\{v\}^0 : v \in V\}$ and Möbius function $\mu_{\mathcal{W}\Pi_G}(\hat{0}, \boldsymbol{\pi})$ given by (2.1),
  $$\mu_G(t) := \sum_{\boldsymbol{\pi} \in \mathrm{Max}(\mathcal{W}\Pi_G)} \mu_{\mathcal{W}\Pi_G}(\hat{0}, \boldsymbol{\pi}) \, t^{w(\boldsymbol{\pi})},$$
  where $w(\boldsymbol{\pi}) = \sum_{B^v \in \boldsymbol{\pi}} v$. By Proposition 2.2, if $G$ has connected components $G_1, \dots, G_k$, then $\mu_G(t) = \prod_{i=1}^k \mu_{G_i}(t)$.
- **Conjecture 4.13(2) (verbatim):** *Let $G$ be a graph with $n$ vertices and $k$ connected components. If $H$ is a subgraph of $G$ with $n$ vertices and $k$ connected components then $(-1)^{n-k}(\mu_G(t) - \mu_H(t))$ is real-rooted.*

## 2. Minimal Counterexample ($n = 8, k = 2$)

Let $\mathrm{House}$ denote the $5$-vertex graph obtained from the $5$-cycle $C_5 = (0\text{--}1\text{--}2\text{--}3\text{--}4\text{--}0)$ by adding the single chord $\{1, 4\}$, and define the $8$-vertex, $2$-component graphs
$$G = K_3 \sqcup \mathrm{House}, \qquad H = P_3 \sqcup C_5,$$
where $P_3 \subset K_3$ is a spanning path of $K_3$. Clearly $H$ is a spanning subgraph of $G$, and both $G$ and $H$ have $n = 8$ vertices and $k = 2$ connected components.

**Proposition 2.1 (Component Möbius polynomials).** Directly from the weighted bond poset $\mathcal{W}\Pi$ (and verified by recurrence (3.1)):
$$\mu_{K_3}(t) = 2 + 5t + 2t^2, \qquad \mu_{P_3}(t) = 1 + 3t + t^2,$$
$$\mu_{\mathrm{House}}(t) = 6 + 49t + 92t^2 + 49t^3 + 6t^4, \qquad \mu_{C_5}(t) = 4 + 34t + 64t^2 + 34t^3 + 4t^4.$$

By Proposition 2.2 ($\mu_{G_1 \sqcup G_2} = \mu_{G_1}\mu_{G_2}$),
$$\mu_G(t) = (2 + 5t + 2t^2)(6 + 49t + 92t^2 + 49t^3 + 6t^4) = 12 + 128t + 441t^2 + 656t^3 + 441t^4 + 128t^5 + 12t^6,$$
$$\mu_H(t) = (1 + 3t + t^2)(4 + 34t + 64t^2 + 34t^3 + 4t^4) = 4 + 46t + 170t^2 + 260t^3 + 170t^4 + 46t^5 + 4t^6.$$

Hence, since $(-1)^{8 - 2} = +1$,
$$P(t) := (-1)^{8-2}(\mu_G(t) - \mu_H(t)) = 8 + 82t + 271t^2 + 396t^3 + 271t^4 + 82t^5 + 8t^6.$$

**Theorem 2.2 (Disproof of Conjecture 4.13(2)).** *The polynomial $P(t)$ is not real-rooted: it has a non-real complex root (in fact, exactly $2$ real roots and $2$ complex conjugate pairs).*

*Proof.* Set $Q(s) := 8s^3 + 82s^2 + 247s + 232$. For every nonzero $z \in \mathbb{C}$,
$$z^3 Q(z + z^{-1}) = 8(z^6 + 1) + 82(z^5 + z) + 271(z^4 + z^2) + 396 z^3 = P(z).$$
Over $\mathbb{C}$, write $Q(s) = 8(s - s_1)(s - s_2)(s - s_3)$. If $s_1, s_2, s_3$ were all real, the cubic discriminant of $Q$ would satisfy
$$8^4 (s_1 - s_2)^2 (s_2 - s_3)^2 (s_3 - s_1)^2 \ge 0.$$
However, direct exact computation gives
$$\Delta(Q) = 18 \cdot 8 \cdot 82 \cdot 247 \cdot 232 - 4 \cdot 82^3 \cdot 232 + 82^2 \cdot 247^2 - 4 \cdot 8 \cdot 247^3 - 27 \cdot 8^2 \cdot 232^2 = -22{,}364 < 0.$$
*(Equivalently, $P(t) = 8(1+t)^6 + 34t(1+t)^4 + 15t^2(1+t)^2 + 2t^3$ has $\gamma$-polynomial $\Gamma(u) = 2u^3 + 15u^2 + 34u + 8$ with identical discriminant $\Delta(\Gamma) = -22{,}364 < 0$.)*

Thus at least one root $s_0 \in \{s_1, s_2, s_3\}$ of $Q$ satisfies $\mathrm{Im}(s_0) \ne 0$. Choose $z \in \mathbb{C}$ satisfying $z^2 - s_0 z + 1 = 0$. Clearly $z \ne 0$ and $z + z^{-1} = s_0 \notin \mathbb{R}$, so $\mathrm{Im}(z) \ne 0$, while $P(z) = z^3 Q(s_0) = 0$. Therefore $P(t)$ is not real-rooted. $\square$

## 3. Infinite Families and Scope

- **Infinite $(n, k)$ families:** Since $\mu_{K_1}(t) = 1$ and $\mu_{K_2}(t) = -(1 + t)$, for any integers $r, s \ge 0$ the spanning subgraph pair
  $$G_{r,s} = K_3 \sqcup \mathrm{House} \sqcup r K_1 \sqcup s K_2, \qquad H_{r,s} = P_3 \sqcup C_5 \sqcup r K_1 \sqcup s K_2$$
  has $n = 8 + r + 2s$ vertices, $k = 2 + r + s$ connected components (so $n - k = 6 + s$), and
  $$(-1)^{n-k}(\mu_{G_{r,s}}(t) - \mu_{H_{r,s}}(t)) = (1 + t)^s P(t),$$
  which shares the non-real roots of $P(t)$. More generally, for every $n \ge 8$ and $3 \le k \le n - 6$, adjoining $F = P_{n-k-5} \sqcup (k - 3) K_1$ multiplies the signed difference by the nonzero Narayana polynomial $N_{n-k-5}(t)$, preserving the non-real root $z$.
- **Non-trivial $2$-component chorded-cycle family:** Without adding $K_1$ or $K_2$ components, pairs $(K_3/P_3) \sqcup (C_m + \text{chord})/C_m$ (as well as $(K_4/C_4)$ and $(C_4/P_4)$ in the first component) also fail real-rootedness (verified for $5 \le m \le 10$, up to $n = 14$).
- **Minimality and the connected restriction:** Exhaustive checks over all $12{,}346$ graphs and $18.1\text{M}$ subgraph pairs on $n \le 8$ vertices confirm that $n = 8$ is minimal and that every counterexample at $n = 8$ is disconnected (3 pairs total). The reason Conjecture 4.13(2) breaks for $k \ge 2$ is structural: whereas $\gamma$-positivity (Conjecture 4.12(2)) and $e$-positivity (Conjecture 6.21(2)) are preserved by $f_1 f_2 - g_1 g_2 = (f_1 - g_1) f_2 + g_1 (f_2 - g_2)$, real-rootedness is not. Both the connected restriction ($k = 1$) and the single-edge-deletion case ($H = G - e$) remain open.
