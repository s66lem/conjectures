# Resolution of the Song–Dalfó–Fiol–Zhang Conjecture on the Laplacian Spectral Radius of Token Graphs (`arXiv:2610.00500v1`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24573109.svg)](https://doi.org/10.5281/zenodo.24573109)

**Problem:** Conjecture in the Introduction of X. Song, C. Dalfó, M. À. Fiol, and S. Zhang, *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs*, [arXiv:2610.00500v1](https://arxiv.org/abs/2610.00500) (30 September 2026).

**Status:** **RESOLVED COMPLETELY** (formally verified in **Lean 4**):
1. **Theorem 1 (Connected Conjecture — PROVED):** For every connected non-star graph $G$ of order $n \ge 4$,
   $$\rho(F_2(G)) > \rho(G).$$
   In particular, for connected graphs of order $n \ge 4$, $\rho(F_k(G)) = \rho(G)$ holds for all $2 \le k \le \lfloor n/2 \rfloor$ **if and only if** $G \cong S_n$.
2. **Theorem 2 (Complete Equality Characterization for All Graphs):** For an arbitrary (not necessarily connected) graph $G$ of order $n \ge 4$, $\rho(F_k(G)) = \rho(G)$ holds for all $2 \le k \le \lfloor n/2 \rfloor$ **if and only if** $G$ is one of:
   - the edgeless graph $\overline{K_n}$,
   - a star plus isolated vertices $S_m \cup (n - m)K_1$ ($2 \le m \le n$), or
   - a triangle plus isolated vertices $K_3 \cup (n - 3)K_1$.

*(Note: Refutation of the literal all-graphs wording via disconnected $K_2 \cup 2K_1$ was previously noted in `trureturing`; our new results are the complete proof of the intended connected conjecture in Theorem 1 and the complete classification of all equality graphs in Theorem 2.)*

## Statement (Verbatim)

> **Conjecture.** Let $G$ be a graph of order $n (\ge 4)$, the equality $\rho(F_k(G)) = \rho(G)$ holds for all $k$ with $2 \le k \le \lfloor \frac{n}{2} \rfloor$ if and only if $G \cong S_n$.

Here $F_k(G)$ denotes the $k$-token graph of $G$ (whose vertices are the $k$-subsets of $V(G)$, with two $k$-subsets adjacent iff their symmetric difference is an edge of $G$), $\rho(\cdot)$ denotes the Laplacian spectral radius, and $S_n = K_{1, n-1}$ is the star on $n$ vertices.

## Summary of Proof

The proof uses only elementary linear algebra of symmetric Laplacians and Rayleigh quotients:

1. **Edge-difference bound (Lemma 2):** Choosing an edge $uv \in E(G)$ maximizing $|x_u - x_v|$ for a top Laplacian eigenvector $x$ of $G$ yields $\rho(G) \le |N(u) \cup N(v)|$.
2. **Dominating-vertex case:** If $G$ has a vertex $c$ of degree $n - 1$ and is not a star, then $G \supseteq S_n + pq$ for an edge $pq$ avoiding $c$. The Grone–Merris star test vector at $\{c, p\}$ in $F_2(S_n + pq)$ achieves Rayleigh quotient $> n \ge \rho(G)$ because $n \ge 4$ supplies a leaf $\ell \notin \{p, q\}$ with $\{\ell, p\}$ adjacent to $\{\ell, c\} \notin N[\{c, p\}]$.
3. **One-sided private-neighbor case:** If no vertex has degree $n - 1$ and $A_0 := N(u) \setminus N[v] = \emptyset$, then $\rho(G) \le |N(u) \cup N(v)| = d_v + 1$. Picking $z \notin N[v]$, connectivity gives $d_z \ge 1$, so $\deg_{F_2}(\{v, z\}) = d_v + d_z \ge d_v + 1$ and the Grone–Merris vector at $\{v, z\}$ yields $\rho(F_2(G)) \ge d_v + 2 > \rho(G)$. The case $B_0 := N(v) \setminus N[u] = \emptyset$ is symmetric.
4. **Product-of-stars & strict perturbation case ($A_0, B_0 \ne \emptyset$):** With $X = N(u) \setminus \{v\}$ ($a = |X| \ge 1$) and $Y = B_0$ ($b = |Y| \ge 1$), the map $(s, t) \mapsto \{s, t\}$ embeds $K_{1, a} \square K_{1, b}$ into $F_2(G)$ with eigenvalue $a + b + 2 = |N(u) \cup N(v)| =: \rho_0$ realized by the tensor eigenvector $\tilde{y} = P \otimes Q$. Picking $x_0 \in A_0$ and setting $S = \{u, x_0\} \notin W$, its neighbors in $W$ are $\{v, x_0\}$ (value $-b$) and $\{u, w\}$ for $w \in Y \cap N(x_0)$ (value $-a$), so $(L_{F_2}\tilde{y})_S = b + a|Y \cap N(x_0)| > 0$. Perturbing $z = \tilde{y} + \varepsilon e_S$ for small $\varepsilon > 0$ forces $z^\top L_{F_2} z > \rho_0 z^\top z$, whence $\rho(F_2(G)) > \rho_0 \ge \rho(G)$.
5. **General graphs (Theorem 2):** Decomposing $F_k(G)$ over connected components shows any graph with two nontrivial components satisfies $\rho(F_2(G)) \ge \rho(G_1) + \rho(G_2) > \rho(G)$; a single nontrivial component $H$ of order $\ge 4$ must be a star by Theorem 1; and for $|H| \le 3$ all three connected graphs ($K_2 = S_2$, $P_3 = S_3$, $K_3$) satisfy $\rho(F_j(H)) = \rho(H)$ for every $1 \le j \le |H| - 1$.

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical proof.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone stdlib-only verifier (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint ([DOI: 10.5281/zenodo.24573109](https://doi.org/10.5281/zenodo.24573109)).
- [SongDalfoFiolZhangTokenLaplacian.lean](../../lean/Conjectures/SongDalfoFiolZhangTokenLaplacian.lean) — Complete Lean 4 formalization.
