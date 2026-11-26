# Resolution of Agyingi–Gaba Question `q:modular` (`arXiv:2611.32417v1`, Modularity and $N_5$ in Specialization Orders of Bounded $q$-Hyperconvex Spaces)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24571430.svg)](https://doi.org/10.5281/zenodo.24571430)

**Problem:** Question `q:modular` (final section) of C. A. Agyingi and Y. U. Gaba, *Smyth completeness and nonexpansive iteration in $q$-hyperconvex $T_0$-quasi-metric spaces*, [arXiv:2611.32417v1](https://arxiv.org/abs/2611.32417) (25 Nov 2026).

**Status:** **RESOLVED COMPLETELY** (both parts, formally verified in **Lean 4** and independently audited):
1. **Part 1 (Isbell-hull $(Y, \le_q)$):** **YES, $(Y, \le_q)$ is modular** (and not distributive), confirming the authors' conjecture exactly; in particular, **$N_5$ does not occur** as a sublattice of $(Y, \le_q)$.
2. **Part 2 (General bounded $q$-hyperconvex spaces):** **YES, $N_5$ DOES occur** as a sublattice of the specialization order $(S, \le_q)$ of the explicit bounded $q$-hyperconvex $T_0$-quasi-metric space $S = \{g \in [0, 1]^3 : g_3 \le \max(g_1, g_2)\}$.

## Statement (Verbatim)

> **Question (`q:modular`).** Is the specialization order $(Y, \le_q)$ of the Isbell-hull of the equilateral three-point space, described in Lemma `lem:Y`, modular? Does $N_5$ occur as a sublattice of $(Y, \le_q)$, or more generally of the specialization order of some bounded $q$-hyperconvex space?

*(The authors write: "we conjecture that $(Y, \le_q)$ is modular but not distributive.")*

## Summary of Proof

Let $X = [0, 1]^3$ with the $T_0$-quasi-metric $q(g, h) = \max_{k \in \{1,2,3\}} \max(h_k - g_k, 0)$, whose specialization order is the reverse coordinatewise order ($g \le_q h \iff q(g, h) = 0 \iff \forall k,\, h_k \le g_k$). Both $Y = \{g \in [0, 1]^3 : \text{two largest coordinates of } g \text{ coincide}\}$ and $S = \{g \in [0, 1]^3 : g_3 \le \max(g_1, g_2)\}$ are fixed sets of monotone, deflationary, idempotent, $q$-nonexpansive retractions $\rho_Y, \rho_S : X \to X$, so under $\le_q$ their lattice operations are $g \wedge_q h = \max(g, h)$ and $g \vee_q h = \rho(\min(g, h))$.

1. **Modularity and non-distributivity of $(Y, \le_q)$:** Define $v(g) = \max_k g_k + \min_k g_k$. Because every $g \in Y$ attains its maximum on at least two coordinates, any two $2$-element subsets of $\{1, 2, 3\}$ overlap, yielding the key identity $\max_k \min(g_k, h_k) = \min(\max g, \max h)$ for all $g, h \in Y$. Combined with $v(\rho_Y(x)) = \sum_k x_k - \max_k x_k$, this proves $v(g \vee_q h) + v(g \wedge_q h) = v(g) + v(h)$. Moreover, $v$ is strictly decreasing under $\le_q$, forcing the modular law on $(Y, \le_q)$ (hence $N_5$ cannot occur in $Y$). The five points $\{0, (0,1,1), (1,0,1), (1,1,0), 1\}$ form an $M_3$ sublattice, so $(Y, \le_q)$ is not distributive.
2. **Bounded $q$-hyperconvex space $(S, q)$ containing $N_5$:** The subspace $S = \{g \in [0, 1]^3 : g_3 \le \max(g_1, g_2)\}$ is bounded and $T_0$, and is $q$-hyperconvex: for any compatible family $(y_i, r_i, s_i)_{i \in I}$ with $q(y_i, y_j) \le r_i + s_j$, the explicit point $z = (U_1, U_2, \min(U_3, \max(U_1, U_2)))$ (where $U_k = \min(1, \inf_i(y_{i,k} + r_i))$) belongs to $S$ and lies in every double ball. The five points $t = (\tfrac{1}{4}, \tfrac{1}{4}, \tfrac{1}{4})$, $c = (0, \tfrac{1}{4}, \tfrac{1}{4})$, $a = (0, \tfrac{1}{4}, 0)$, $b = (\tfrac{1}{4}, 0, \tfrac{1}{4})$, and $o = (0, 0, 0)$ form an $N_5$ sublattice of $(S, \le_q)$ with $c <_q a$, $c \vee_q b = a \vee_q b = o$, and $c \wedge_q b = a \wedge_q b = t$.

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical proof.
- [AUDIT.md](AUDIT.md) — Independent adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone exact rational verifier (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint.
- [AgyingiGabaQHyperconvexModular.lean](../../lean/Conjectures/AgyingiGabaQHyperconvexModular.lean) — Complete Lean 4 formalization (`Y_isModularLattice`, `Y_not_distributive`, `Y_no_N5_sublattice`, `S_isQHyperconvex`, `S_has_N5_sublattice`, `agyingi_gaba_question_modular_resolution`).
