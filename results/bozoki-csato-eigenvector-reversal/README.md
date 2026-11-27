# Full Rank Reversal Between Right and Inverse Left Eigenvectors for Four Alternatives

- **Status:** Resolved (Affirmative) & Lean 4 Verified
- **Source:** S. Bozóki, L. Csató, *Theoretical properties of the eigenvector method*, [arXiv:2603.24274](https://arxiv.org/abs/2603.24274) (math.OC, March 2026), Section *Right–left asymmetry* (open question after Example 5)
- **Zenodo Preprint:** [10.5281/zenodo.24575976](https://doi.org/10.5281/zenodo.24575976)
- **Lean 4 Formalization:** [`BozokiCsatoEigenvectorReversal.lean`](../../lean/Conjectures/BozokiCsatoEigenvectorReversal.lean)

## Summary

We resolve affirmatively the open question of Bozóki and Csató asking whether a $4 \times 4$ pairwise comparison matrix can have strictly reversed rankings between its right Perron eigenvector $w^R$ and inverse left Perron eigenvector $w^{-L}$, and characterize the full-reversal class for every $n$:

- **Explicit $4 \times 4$ rational witness ($A_4$):** $\lambda_{\max} = 5$, right Perron eigenvector $w_4 = (34, 33, 32, 22)^T$ (order $1 \succ 2 \succ 3 \succ 4$), left Perron eigenvector $v_4 = (\frac{42}{17}, \frac{27}{11}, \frac{77}{32}, \frac{26}{11})^T$ so $v_4^{-1} = (\frac{17}{42}, \frac{11}{27}, \frac{32}{77}, \frac{11}{26})^T$ (order $4 \succ 3 \succ 2 \succ 1$).
- **Characterization (any $n$):** Diagonal rescaling $B = D_w^{-1} A D_w$ reduces full reversal to constant-row-sum PCMs with strictly decreasing left Perron vector $u = v \circ w$ and scaling $u_j / u_i < w_j / w_i < 1$.
- **Sharpness at $n = 3$:** Every $3 \times 3$ PCM satisfies $w^R \propto w^{-L}$, so $n = 4$ is minimal.

## Files

- `PROOF.md`: Complete self-contained mathematical proof.
- `paper.tex` / `paper.pdf`: Publication-ready LaTeX preprint.
- `verify.py`: Standalone Python stdlib verifier (`python -O -W error verify.py`).
- `AUDIT.md`: Independent adversarial audit report (PASS, 5/5 checks).
