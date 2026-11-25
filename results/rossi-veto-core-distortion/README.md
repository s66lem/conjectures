# Exact metric distortion of the rank score veto core (`arXiv:2610.26535`)

Complete proof of the **Rank Score Veto Core Distortion Conjecture** posed by M. August Rossi (*Regularizing the Veto Core*, `arXiv:2610.26535`, October 2026, Section 3.1 after Corollary 2 and Section 5).

For every non-increasing positional scoring vector $\mathbf{s} = (s_1, \dots, s_m)$ with $1 = s_1 \ge s_2 \ge \dots \ge s_m \ge 0$, every preference profile, every consistent pseudometric $d$, every candidate $a$ in the $(\mathbf{p}^{\mathsf{unif}}, \mathbf{q}^{\mathbf{s}})$-veto core, and every candidate $b$,
$$\mathrm{SC}_d(a) \le \bigl(1 + 2(\|\mathbf{s}\|_1 - s_m)\bigr)\,\mathrm{SC}_d(b).$$
Combined with Rossi's matching lower bound (Lemma 5), the exact worst-case distortion is $1 + 2(s_1 + \dots + s_{m-1})$ — independent of the last-position score $s_m$ — attained on a finite election for every rational scoring vector (Rossi's Definition 1) and exact as a supremum for real scoring vectors.

- [Complete proof](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/RossiVetoCore.lean) (`RossiVetoCore.rank_score_veto_core_distortion_upper`, `RossiVetoCore.rank_score_veto_core_distortion_attained`)
- [arXiv-ready LaTeX preprint](paper.tex) · [Compiled PDF](paper.pdf)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.RossiVetoCore` to verify both the upper bound and rational attainment in Lean 4 (`v4.33.1` + Mathlib, zero `sorry`, standard axioms only). The result is internally cross-model audited and Lean-verified, but externally unrefereed; priority is not asserted.
