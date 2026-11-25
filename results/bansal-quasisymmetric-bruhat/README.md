# Disproof of Bansal Conjecture C / 6.11 (Shellability of Quasisymmetric Bruhat Lower Intervals)

Counterexample and Lean 4 formal verification refuting **Conjecture C (Conjecture 6.11)** of Ryan Bansal, *A Quasisymmetric Analogue of the Bruhat Order* (`arXiv:2611.02210v1`, November 2026).

## Main Results

1. **Minimal counterexample at $m = 7$ (non-shellable and non-Cohen–Macaulay):** For the zigzag tree $Z = F(1, 2, 4)$ on support $[1, 7]$ (rank $7$, one step above the paper's exhaustive $m \le 6$ search) and lower element $x = F(0, 1, 0, 1, 1, 0, 1)$ (rank $4$), the length-$3$ interval $[x, Z]$ has open order complex $\Delta((x, Z)) \cong C_6 \sqcup C_6$ — two vertex-disjoint hexagons ($6$ elements of rank $5$, $6$ of rank $6$, $12$ cover edges, $\mu(x, Z) = -1$). Because every pure $1$-dimensional shellable or Cohen–Macaulay complex must be connected, neither $[x, Z]$ nor $[\varnothing, Z]$ is shellable or Cohen–Macaulay over any field.
2. **Failure for every $m \ge 7$:** Incrementing the first code entry gives $x_1 P_F = P_{F + e_1}$ whenever the piece at $1$ is followed by a bare leaf, yielding $Z = F(1, 2, 4) \lessdot F(2, 2, 4) \lessdot \cdots \lessdot F(m - 6, 2, 4)$ (and likewise $Z \le F(1, 2, m - 3)$ via Lemma 3.1 code-raising), so zigzag lower intervals of rank $m$ fail shellability and Cohen–Macaulayness for every $m \ge 7$.
3. **Sharpness of $m = 7$:** Every one of the $1 + 2 + 5 + 14 + 42 + 132 = 196$ binary trees with $m \le 6$ internal vertices admits a recursive coatom ordering (confirming the paper's $m = 4, 5, 6$ computation), and none of the length-$3$ intervals in $\mathcal{P}_6$ is disconnected.

## Files

- [`PROOF.md`](PROOF.md) — Exact definitions, complete structure of the disconnected open interval $(x, Z) \cong C_6 \sqcup C_6$, non-shellability / non-Cohen–Macaulayness proof, and infinite zigzag family $Z_m = F(1, 2, m - 3)$ ($m \ge 7$).
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 formal verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe: rebuilds indexed forests and forest polynomials from Definition 2.3, verifies the Monk rule and Figure 5 calibration, confirms $(x, Z) \cong C_6 \sqcup C_6$, and verifies all four $m = 7$ failing zigzags).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/QuasisymmetricBruhat.lean`](../../lean/Conjectures/QuasisymmetricBruhat.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/bansal-quasisymmetric-bruhat/verify.py
cd lean && lake build Conjectures.QuasisymmetricBruhat
```
