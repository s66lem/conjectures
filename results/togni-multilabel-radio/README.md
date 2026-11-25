# Multi-label radio labelings of paths and cycles (`arXiv:2610.25863`)

Complete proof of **Conjecture 2** from Olivier Togni (*On Multi-label radio Labelings of Graphs*, `arXiv:2610.25863`, Section 5) for all $k, m \ge 1$, together with the **upper bound in Conjecture 1** for all $n, k, m \ge 1$, **exact equality in Conjecture 1 for $k = 3$ and all $m \ge 1$**, and **divisibility obstructions** explaining why modulus-$S$ toroidal schemes fail on general cycles.

Writing $S = \lceil (k+1)^2 / 2 \rceil$ and $M = mS + 1$:
- **Conjecture 2 (proved for all $k, m \ge 1$):** For every cycle $C_n$ of order $n \ge \max\{3, \lceil kSM/2 \rceil\}$ (and more sharply $n \ge \max\{3, kM \cdot \mathrm{dist}(an, S\mathbb{Z})\}$), $\lambda_k^m(C_n) \le mS$.
- **Conjecture 1 upper bound (all $n, k, m \ge 1$):** $\lambda_k^m(P_n) \le mS - 1$ (and $\lambda_k^m(C_n) \le mS - 1$ whenever $n \ge 3$ and $S \mid n$).
- **Conjecture 1 exact equality for $k = 3$ (all $m \ge 1$):** $\lambda_3^m(P_n) = 8m - 1$ for all sufficiently large $n$.

- [Complete proof](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/TogniRadio.lean) (`TogniRadio.conjecture2_cycle`, `TogniRadio.conjecture1_path_upper_bound`, `TogniRadio.lattice_min_norm`, `TogniRadio.S_val_eq_ceil`)
- [arXiv-ready LaTeX preprint](paper.tex) · [Compiled PDF](paper.pdf)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.TogniRadio` to verify Conjecture 2 and the Conjecture 1 path upper bound in Lean 4 (`v4.33.1` + Mathlib, zero `sorry`, standard axioms only). The result is internally cross-model audited and Lean-verified, but externally unrefereed; priority is not asserted.
