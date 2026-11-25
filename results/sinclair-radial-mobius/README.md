# Disproof of Sinclair Conjecture C (Front-Loading of the Radial-Derivative Hilbert Series)

Counterexample and Lean 4 formal verification refuting **Conjecture C** of Thomas Sinclair, *The radial derivative on the graded Möbius algebra* (`arXiv:2608.18519`).

## Main Results

1. **Disproof of Conjecture C on $10$ elements:** For the connected $6$-vertex, $10$-edge simple graph $G_4 = K_{1,1,4} + \{2,3\}$, the cycle matroid $M(G_4)$ is a simple graphic matroid of rank $5$ with exact rational Hilbert vectors
   $$H^0(M(G_4)) = (1, 10, 27, 27, 10, 1), \qquad H_\beta(M(G_4)) = (1, 11, \mathbf{31}, \mathbf{32}, 10, 1).$$
   Thus $h_2^\beta = 31 < 32 = h_3^\beta$ (equivalently $\delta_2 = 4 < 5 = \delta_3$), refuting front-loading $h_k^\beta(M) \ge h_{r-k}^\beta(M)$ for $k \le r/2$ (and reversing the grading also fails at $k = 1$, since $10 < 11$).
2. **Graphic family with growing gaps ($m = 4, 5, 6, 7$):** For $G_m = K_{1,1,m} + \{2,3\}$ (rank $m + 1$ on $2m + 2$ elements), exact rational computation confirms growing violations, reaching $h_3^\beta = 236 < 246 = h_5^\beta$ at $m = 7$.
3. **Non-graphic binary counterexample:** A simple rank-$6$ binary matroid on $12$ elements has $H_\beta = (1, 13, 50, 94, 51, 12, 1)$, failing at $k = 2$ ($50 < 51$).

## Files

- [`PROOF.md`](PROOF.md) — Exact definitions, primary counterexample $M(G_4)$, graphic family $G_4 \dots G_7$, and non-graphic binary counterexample.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial referee audit and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 exact-rational verifier (stdlib only: reproduces Example 3.2 $M(K_5)$, checks $D_\beta(v_j) = j v_{j-1}$, and verifies $G_4 \dots G_7$ and the binary counterexample).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/SinclairRadialMobius.lean`](../../lean/Conjectures/SinclairRadialMobius.lean) — Lean 4 formalization (`M_G4_rank`, `M_G4_h2`, `M_G4_h3`, `not_sinclair_conjecture_C`).

## Reproduction

```bash
python3 results/sinclair-radial-mobius/verify.py
cd lean && lake build Conjectures.SinclairRadialMobius
```
