# Disproof of Li–Nešetřil–Yang Problem 3.6 and the Weak Inequality of Problem 3.5 (`arXiv:2611.33681v1`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24560441.svg)](https://doi.org/10.5281/zenodo.24560441)

**Status:** Disproved completely (Problem 3.6 for all $k \ge 2$, the "in particular" weak inequality $\overrightarrow{\mathrm{wcol}}_k(G) \le 2\,\overrightarrow{\mathrm{wcol}}^+_k(G)$ on $P_4$, and any uniform bound $\overrightarrow{\mathrm{wcol}}_k(G) \le g(\overrightarrow{\mathrm{wcol}}^+_k(G))$ via paths $P_{2^t - 1}$; sharp positive boundary at $k = 1$) — **Lean 4 verified** (zero `sorry`, zero custom axioms, zero `native_decide`).

## Target Problems

Wenwen Li, Jaroslav Nešetřil, and Daqing Yang, *Generalized oriented chromatic numbers and directed generalized coloring numbers of graphs*, [arXiv:2611.33681v1](https://arxiv.org/abs/2611.33681v1) (25 Nov 2026), §3.2:

> **Problem 3.5.** For any graph $G$, are there linear functions $f, g$ such that for any $k \ge 1$ we have $\overrightarrow{\mathrm{col}}_k(G) \le f(\overrightarrow{\mathrm{col}}^+_k(G))$ and $\overrightarrow{\mathrm{wcol}}_k(G) \le g(\overrightarrow{\mathrm{wcol}}^+_k(G))$? In particular, do the following inequalities hold: $\overrightarrow{\mathrm{col}}_k(G) \le 2\,\overrightarrow{\mathrm{col}}^+_k(G)$ and $\overrightarrow{\mathrm{wcol}}_k(G) \le 2\,\overrightarrow{\mathrm{wcol}}^+_k(G)$?
>
> **Problem 3.6.** For any graph $G$ and any $k \ge 1$, is there an orientation $\vec{G}$ of $G$ such that $\overrightarrow{\mathrm{col}}^+_k(\vec{G}) = \lceil \overrightarrow{\mathrm{col}}_k(G)/2 \rceil$ and $\overrightarrow{\mathrm{wcol}}^+_k(\vec{G}) = \lceil \overrightarrow{\mathrm{wcol}}_k(G)/2 \rceil$?

## Main Results

1. **Forest Lemma:** For every finite forest $F$, every orientation $D$ of $F$, and every $k \ge 1$,
   $$\overrightarrow{\mathrm{col}}^+_k(D) = \overrightarrow{\mathrm{wcol}}^+_k(D) = 1.$$
2. **Disproof of Problem 3.6 (for all $k \ge 2$) and the weak factor-$2$ bound of Problem 3.5:** On the $4$-vertex path $P_4$, for every $k \ge 2$,
   $$\overrightarrow{\mathrm{wcol}}_k(P_4) = 3 > 2 = 2\,\overrightarrow{\mathrm{wcol}}^+_k(P_4),$$
   while every orientation $D$ of $P_4$ has $\overrightarrow{\mathrm{wcol}}^+_k(D) = 1 \ne 2 = \lceil \overrightarrow{\mathrm{wcol}}_k(P_4)/2 \rceil$. By subgraph monotonicity, every forest containing a $3$-edge path fails Problem 3.6 for all $k \ge 2$.
3. **Unbounded Separation (Disproof of any uniform weak bound in Problem 3.5):** For every integer $t \ge 1$, $N = 2^t - 1$, and $k \ge N - 1$, the path $P_N$ satisfies
   $$\overrightarrow{\mathrm{wcol}}_k(P_N) \ge t \qquad \text{and} \qquad \overrightarrow{\mathrm{wcol}}^+_k(P_N) = 1.$$
   Hence no function $g : \mathbb{N} \to \mathbb{N}$ satisfies $\overrightarrow{\mathrm{wcol}}_k(G) \le g(\overrightarrow{\mathrm{wcol}}^+_k(G))$ across all graphs $G$ and $k \ge 1$.
4. **Sharpness at $k = 1$:** For $k = 1$, Problem 3.6 has a positive answer for every finite graph $G$ (proved in `PROOF.md` and `paper.tex` via degeneracy duality and single-arc flip continuity).

*Lean scope note:* `Conjectures.LiNesetrilYangWcol` formally verifies Parts 1, 2, and 3 (the general forest lemma via acyclic topological ordering, the exact $P_4$ disproof of Problem 3.6 and the factor-$2$ bound for all $k \ge 2$, subgraph monotonicity, and the general binary-halving lower bound $\overrightarrow{\mathrm{wcol}}_k(P_{2^t - 1}) \ge t$ ruling out any uniform function $g$). The positive $k = 1$ boundary remark is presented in `PROOF.md` and `paper.tex`.

## Files

- [PROOF.md](PROOF.md) — complete self-contained proofs of all four parts.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/li-nesetril-yang-wcol/verify.py`).
- [LiNesetrilYangWcol.lean](../../lean/Conjectures/LiNesetrilYangWcol.lean) — complete Lean 4 formalization (`lake build Conjectures.LiNesetrilYangWcol`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
