# Disproof of González D'León–Wachs Conjecture 4.13(2) (`arXiv:2608.08692v2`)

Counterexample, infinite family, and Lean 4 formal verification refuting **Conjecture 4.13(2)** of Rafael S. González D'León and Michelle L. Wachs, *Weighted bond posets and a new chromatic symmetric function* (`arXiv:2608.08692v2`).

## Main Results

1. **Minimal counterexample ($n = 8, k = 2$):** Let $G = K_3 \sqcup \mathrm{House}$ and $H = P_3 \sqcup C_5$, where $P_3$ is a spanning path of $K_3$ and $C_5$ is the outer $5$-cycle of the house graph. Then $H \subseteq G$ is a spanning subgraph with the same number of vertices ($n = 8$) and connected components ($k = 2$), yet
   $$(-1)^{n-k}(\mu_G(t) - \mu_H(t)) = 8 + 82t + 271t^2 + 396t^3 + 271t^4 + 82t^5 + 8t^6$$
   is **not real-rooted**: its $\gamma$-polynomial $\Gamma(u) = 2u^3 + 15u^2 + 34u + 8$ (equivalently its reciprocal cubic $Q(s) = 8s^3 + 82s^2 + 247s + 232$) has negative discriminant $\Delta = -22{,}364 < 0$, so the degree-$6$ difference has only $2$ real roots and $2$ complex conjugate pairs.
2. **Infinite families:**
   - Adding $r$ isolated vertices $K_1$ and $s$ disjoint edges $K_2$ multiplies $(-1)^{n-k}(\mu_G - \mu_H)$ by $(1 + t)^s$, preserving the non-real roots for all $n = 8 + r + 2s$, $k = 2 + r + s$; adjoining $P_{n - k - 5} \sqcup (k - 3) K_1$ covers every $(n, k)$ with $3 \le k \le n - 6$.
   - Non-trivial $2$-component pairs $(K_3 / P_3) \sqcup (C_m + \text{chord}) / C_m$ (as well as $(K_4/C_4)$ and $(C_4/P_4)$ in the first component) also fail real-rootedness (verified for $m = 5, \dots, 10$, $n$ up to $14$).
3. **Why it fails & what remains open:** Unlike $\gamma$-positivity (Conjecture 4.12(2)) and $e$-positivity (Conjecture 6.21(2)), real-rootedness is not preserved under $f_1 f_2 - g_1 g_2$. Exhaustive verification over all $12{,}346$ graphs and $18.1\text{M}$ subgraph pairs with $n \le 8$ shows that $n = 8$ is minimal and that every failure at $n = 8$ is disconnected (the connected restriction $k = 1$, and single-edge deletions $H = G - e$, remain open).

## Files

- [`PROOF.md`](PROOF.md) — Verbatim definitions, exact Möbius polynomials, 4-line algebraic non-real-rootedness proof, infinite families, and census summary.
- [`AUDIT.md`](AUDIT.md) — Cross-model audit and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe: computes $\mu_G(t)$ and $\mu_H(t)$ directly from the verbatim weighted bond poset $\mathcal{W}\Pi_G$ and via recurrence (3.1), verifies the exact $\gamma$- and reciprocal-cubic identities and discriminant $\Delta = -22{,}364 < 0$, and checks the non-trivial $2$-component chorded-cycle family).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/WachsWeightedBond.lean`](../../lean/Conjectures/WachsWeightedBond.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/gonzalez-dleon-wachs-weighted-bond/verify.py
cd lean && lake build Conjectures.WachsWeightedBond
```
