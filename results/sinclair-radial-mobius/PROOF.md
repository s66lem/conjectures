# Disproof of Sinclair's Conjecture C on the Radial Derivative of the Graded Möbius Algebra

**Theorem.** *Conjecture C (front-loading / top-heaviness) of Thomas Sinclair, "The radial derivative on the graded Möbius algebra" (`arXiv:2608.18519`), is **false**. Specifically, the simple rank-$5$ graphic matroid $M(G_4)$ of the $6$-vertex, $10$-edge graph $G_4 = K_{1,1,4} + e$ satisfies*
$$H_{\beta, M(G_4)}(q) = 1 + 11q + 31q^2 + 32q^3 + 10q^4 + q^5,$$
*so $h_2^\beta(M(G_4)) = 31 < 32 = h_3^\beta(M(G_4))$ (equivalently $\delta_2 = 4 < 5 = \delta_3$), violating $h_k^\beta(M) \ge h_{r-k}^\beta(M)$ at $k = 2 \le 5/2$.*

Furthermore, the failure persists across the graphic family $G_m = K_{1,1,m} + e$ for $m = 4, 5, 6, 7$ with growing gaps, and also occurs for non-graphic binary matroids.

---

## 1. Definitions (Sinclair, `arXiv:2608.18519`, §2 & Appendix B)

Let $M$ be a simple matroid of rank $r$ on an $n$-element ground set $E$, with lattice of flats $\mathcal{L}(M) = \bigsqcup_{j=0}^r \mathcal{L}_j(M)$ and Whitney numbers of the second kind $W_j = |\mathcal{L}_j(M)|$.

- For each flat $x \in \mathcal{L}(M)$, let $\beta_x := \mathrm{rk}(x)! \cdot |\{\text{bases of } M|x\}|$ be the number of ordered atom bases of $x$.
- On the graded Möbius algebra $B(M) = \bigoplus_{j=0}^r \mathbb{Q}\mathcal{L}_j(M)$ with flat basis $\{e_x : x \in \mathcal{L}(M)\}$, the coordinate lowering operators $L_a^\beta$ ($a \in E$, Proposition 2.2) act on $y \in \mathcal{L}_j(M)$ by
  $$L_a^\beta(e_y) = \sum_{\substack{x \lessdot y \\ x \vee a = y}} \frac{\beta_x}{\beta_y} \, e_x.$$
- Let $U^\beta = \sum_{a \in E} L_a^\beta$, let $K(e_y) = \mathrm{rk}(y) \, e_y$, and let $S(e_x) = (n - |x|) \, e_x$ (invertible on all proper flats $x \neq E$). The **radial derivative** (Proposition 2.3) is
  $$D_\beta = S^{-1} U^\beta K.$$
  Setting $v_j = \sum_{x \in \mathcal{L}_j(M)} \beta_x e_x$, this satisfies $D_\beta(v_j) = j v_{j-1}$ for every $1 \le j \le r$.
- The graded cyclic module $\mathcal{C}(M) = \bigoplus_{k=0}^r \mathcal{C}_k(M)$ (graded by differential word length $k$, with $\mathcal{C}_k(M) \subseteq \mathbb{Q}\mathcal{L}_{r-k}(M)$) is generated from $\mathcal{C}_0(M) = \mathbb{Q} v_r$ via
  $$\mathcal{C}_{k+1}(M) = D_\beta(\mathcal{C}_k(M)) + \sum_{a \in E} L_a^\beta(\mathcal{C}_k(M)),$$
  with Hilbert coefficients $h_k^\beta(M) := \dim_{\mathbb{Q}} \mathcal{C}_k(M)$. The coordinate-only submodule $\mathcal{C}^0(M)$ (omitting $D_\beta$) has Hilbert coefficients $h_k^0(M)$, and the defect is $\delta_k(M) := h_k^\beta(M) - h_k^0(M)$.
- **Conjecture C (Front-loading):** For every simple rank-$r$ matroid $M$ and every $k \le r/2$, $\delta_k(M) \ge \delta_{r-k}(M)$, equivalently (by the symmetry $h_k^0(M) = h_{r-k}^0(M)$ of the Macaulay inverse system $\mathcal{C}^0$) $h_k^\beta(M) \ge h_{r-k}^\beta(M)$.

---

## 2. Explicit Counterexample $M(G_4)$ and the Graphic Family $G_m = K_{1,1,m} + e$

For $m \ge 2$, let $G_m = K_{1,1,m} + e$ be the simple graph on vertex set $\{0, 1, 2, \dots, m + 1\}$ with $n = 2m + 2$ edges:
$$E(G_m) = \bigl\{\{0, 1\},\, \{2, 3\}\bigr\} \cup \bigl\{\{0, j\},\, \{1, j\} : 2 \le j \le m + 1\bigr\}.$$
Since $G_m$ is connected and simple, its cycle matroid $M(G_m)$ is a simple graphic matroid of rank $r = m + 1$ on $n = 2m + 2$ elements.

Exact rational computation over $\mathbb{Q}$ for $m = 4$ ($G_4$, $6$ vertices, $10$ edges, rank $5$) gives:

| Degree $k$ | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| Flat rank $r - k$ | $5$ | $4$ | $3$ | $2$ | $1$ | $0$ |
| Whitney $W_{r-k}$ | $1$ | $21$ | $44$ | $33$ | $10$ | $1$ |
| $h_k^0(M(G_4))$ | $1$ | $10$ | $27$ | $27$ | $10$ | $1$ |
| $h_k^\beta(M(G_4))$ | $1$ | $11$ | **31** | **32** | $10$ | $1$ |
| Defect $\delta_k$ | $0$ | $1$ | **4** | **5** | $0$ | $0$ |

At $k = 2 \le 5/2$, we have $h_2^\beta = 31 < 32 = h_3^\beta$ ($\delta_2 = 4 < 5 = \delta_3$), refuting Conjecture C. (Note that even if the sequence were read in reverse order, $h_4^\beta = 10 < 11 = h_1^\beta$ would fail at $k = 1$; thus $H_\beta$ is neither front-loaded nor back-loaded.)

### Persistence Along $G_m$ and a Non-Graphic Example

Exact computation over $\mathbb{Q}$ confirms that Conjecture C fails for $G_4, G_5, G_6, G_7$ with growing gaps:

| $m$ | $n$ | $r$ | $H^0(M(G_m))$ | $H_\beta(M(G_m))$ | Failing $k$ |
| :---: | :---: | :---: | :--- | :--- | :---: |
| $4$ | $10$ | $5$ | $(1, 10, 27, 27, 10, 1)$ | $(1, 11, \mathbf{31}, \mathbf{32}, 10, 1)$ | $2$ |
| $5$ | $12$ | $6$ | $(1, 12, 42, 62, 42, 12, 1)$ | $(1, 13, \mathbf{48}, 74, \mathbf{49}, 12, 1)$ | $2$ |
| $6$ | $14$ | $7$ | $(1, 14, 60, 117, 117, 60, 14, 1)$ | $(1, 15, \mathbf{68}, \mathbf{143}, \mathbf{149}, \mathbf{69}, 14, 1)$ | $2, 3$ |
| $7$ | $16$ | $8$ | $(1, 16, 81, 196, 260, 196, 81, 16, 1)$ | $(1, 17, \mathbf{91}, \mathbf{236}, 330, \mathbf{246}, \mathbf{92}, 16, 1)$ | $2, 3$ |

By contrast, $K_{1,1,m}$ without the extra edge $\{2, 3\}$ satisfies $H_\beta = H^0$ (symmetric). A non-graphic counterexample also exists: the simple rank-$6$ binary matroid on $12$ elements with columns `011010, 001101, 000100, 001000, 100000, 011111, 010010, 010000, 111111, 010111, 010011, 000111` over $\mathbb{F}_2$ has $H^0 = (1, 12, 44, 66, 44, 12, 1)$ and $H_\beta = (1, 13, 50, 94, 51, 12, 1)$, failing at $k = 2$ ($50 < 51$).

---

## 3. Remarks on Minimality and Conjecture B

- Sinclair's Proposition 5.1 verified Conjecture C on all $950$ simple matroids on $8$ elements. Every $9$-edge simple graph on $6$ or $7$ vertices passed a modular screen, and all $1$-, $2$-, and $3$-element deletions of $M(G_4)$ and the $12$-element binary example satisfy Conjecture C; minimality of $n = 10$ among all simple matroids (specifically $n = 9$ non-graphic matroids) remains open.
- Screening $\sim 25{,}000$ matroids across graphic, representable ($\mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5, \mathbb{F}_{101}$), direct-sum, and projective/affine geometry families found no counterexample to Conjecture B (log-concavity).
