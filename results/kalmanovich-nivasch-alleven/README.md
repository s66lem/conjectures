# Disproof of Kalmanovich–Nivasch Conjecture 9.1 on Planar All-Even Sets

Counterexample and Lean 4 formal verification refuting **Conjecture 9.1** of Daniel Kalmanovich and Gabriel Nivasch, *All-even sets in $\mathbb{R}^2$ and $\mathbb{R}^3$* (`arXiv:2610.38864`).

## Main Results

1. **Disproof of Conjecture 9.1 (36-point counterexample):** The 36-point subset $S = A \cup B$ of the regular $210$-gon given by
   $$A = 15 \cdot \{4, 5, 7, 8, 9, 10, 12, 13\}, \qquad B = \{1 + 6j : 0 \le j < 35,\; 5 \nmid j\} \pmod{210}$$
   is a planar all-even set ($m_S(u) \in \{22, 26, 32, 34, 36\}$ for every nonzero direction $u \in \mathbb{R}^2$) with **no monotonically contagious triangle** (every 3-point seed has monotone closure of size at most $28 < 36$).
2. **Separation of Property $\mathcal{C}$ from monotone contagion:** $S$ is height-rigid (parallel-line constraint matrix has rank $33 = |S| - 3$ over $\mathbb{F}_{211}$, hence over $\mathbb{R}$) and satisfies Property $\mathcal{C}$, separating $\mathcal{M}$ from $\mathcal{C}$ among planar all-even sets.
3. **Unbounded monotone seed number:** For every integer $k \ge 1$, there exists a planar all-even set $S_k$ on a regular $N_k$-gon whose smallest monotonically contagious subset has size at least $k + 1$.

## Files

- [`PROOF.md`](PROOF.md) — Self-contained proof of the 36-point counterexample, Property $\mathcal{C}$ / height-rigidity check, and unbounded seed-number family.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/KalmanovichNivaschAllEven.lean`](../../lean/Conjectures/KalmanovichNivaschAllEven.lean) — Lean 4 formalization in genuine $\mathbb{R}^2$ (`S36_isAllEven`, `S36_no_mono_contagious_triangle`, `not_conjecture_9_1`).

## Reproduction

```bash
python3 results/kalmanovich-nivasch-alleven/verify.py
cd lean && lake build Conjectures.KalmanovichNivaschAllEven
```
