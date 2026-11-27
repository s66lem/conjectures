# Proof of the Line-Metric Distortion Conjecture of Abbaszadeh et al.

- **Status:** Proved & Lean 4 Verified
- **Source:** M. Abbaszadeh, A. Ansarifar, M. Latifian, M. Seddighin, *Metric Distortion with Preference Intensities*, [arXiv:2601.02095v1](https://arxiv.org/abs/2601.02095) (AAAI 2026), Section 6 Conjecture
- **Zenodo Preprint:** [10.5281/zenodo.24575678](https://doi.org/10.5281/zenodo.24575678)
- **Lean 4 Formalization:** [`AbbaszadehLineMetricDistortion.lean`](../../lean/Conjectures/AbbaszadehLineMetricDistortion.lean)

## Summary

For two-alternative elections on the $1$-Euclidean line under mandatory preference-intensity elicitation with threshold $\alpha \in (0, 1]$, we prove that the optimal rule $f^{\mathsf{tal}}_\alpha$ achieves worst-case metric distortion exactly

$$M(\alpha) = \max\!\left(\frac{3 - \alpha}{1 + \alpha},\, 1 + 2\alpha\right),$$

and that no deterministic voting rule achieves strictly smaller distortion.

The upper bound follows by affine normalization to $(a_1, a_2) = (0, 1)$, per-agent upper bounds on $g_t(y) = |y| - t|y - 1|$ yielding two linear forms $B_t^{(1)}(n), B_t^{(2)}(n)$ per alternative, and the coefficientwise pairing inequality $B_M^{(i)}(n) + B_M^{(j)}(\sigma n) \le 0$ for all $i, j \in \{1, 2\}$. Tightness is witnessed by the symmetric two-voter profiles $(a_1 \succ a_2, a_2 \succ a_1)$ for $\alpha < 1$ and $(a_1 \gg a_2, a_2 \gg a_1)$ for all $\alpha \in (0, 1]$.

## Files

- `PROOF.md`: Complete self-contained mathematical proof.
- `paper.tex` / `paper.pdf`: Publication-ready LaTeX preprint.
- `verify.py`: Standalone Python stdlib verifier (`python -O -W error verify.py`).
- `AUDIT.md`: Independent adversarial audit report (after audit).
