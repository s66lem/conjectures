# Exact facility advantage in the one-round discrete Voronoi game on a line (`arXiv:2609.24936`)

Complete **disproof of Conjecture 1** from Tamal Maharaj (*The Facility Advantage in the One-Round Discrete Voronoi Game on a Line*, `arXiv:2609.24936`, Section 4.3) for every $\ell \ge 3$, establishing the exact facility advantage
$$k^*(\ell) = 2\ell - 1 \qquad \text{for every } \ell \ge 1.$$
Maharaj's upper bound (Theorem 4.1) is already tight; Conjecture 1 ($k^*(\ell) = \ell + 1$) holds only at $\ell = 2$.

For any $\ell \ge 2$, $k \le 2\ell - 2$, and $n \ge 4\ell(\ell - 1) + 1$, the unweighted exponentially spaced voter set $V_n = \{2^0, 2^1, \dots, 2^{n-1}\} \subset \mathbb{R}$ defeats every $k$-facility placement of player $\mathcal{P}$ with a linear winning margin ($\mathcal{P}$ keeps at most $\frac{\ell - 1}{2\ell - 1} n + O(\ell)$ voters). For $\ell = 3$, already $V_{17}$ gives an explicit unit-weight counterexample with $\Gamma_{4,3}(V_{17}) = 8 < 8.5$.

- [Complete proof and disproof](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/VoronoiGame1D.lean) (`VoronoiGame1D.facilityAdvantage_eq`, `VoronoiGame1D.not_maharaj_conjecture1`, `VoronoiGame1D.powers_of_two_defeat`, `VoronoiGame1D.l3_n17_counterexample`, `VoronoiGame1D.alwaysWins_two_mul_sub_one`)
- [arXiv-ready LaTeX preprint](paper.tex) · [Compiled PDF](paper.pdf)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.VoronoiGame1D` to verify `k*(ℓ) = 2ℓ - 1` and the disproof of Conjecture 1 in Lean 4 (`v4.33.1` + Mathlib, zero `sorry`, standard axioms only). The result is internally cross-model audited and Lean-verified, but externally unrefereed; priority is not asserted.
