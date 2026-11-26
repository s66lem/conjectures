# Independent Audit — Snellman's Normalized-Volume Monotonicity Conjecture (`arXiv:2611.26110v1`)

## Auditor & Scope

- **Independent auditor:** `claude-sonnet-5-5` (cross-model read-only adversarial audit, `effort: medium`).
- **Date:** 2026-11-26.
- **Verdict:** **PASS** (three minor documentation polish items identified and resolved before publication).

## Verification Summary

1. **Lean 4 Build & Axiom Hygiene**
   - `lake build Conjectures.SnellmanKozlovVolume` completed with exit code `0`, zero errors, and zero warnings.
   - `lean/Conjectures.lean` imports `Conjectures.SnellmanKozlovVolume`.
   - `#print axioms` on all six exported theorems (`rank2Sum_step_lower_bound`, `snellman_conjecture_monotone`, `snellman_strict_increase`, `snellman_equality_n2_d0`, `rank2Sum_zero`, `nvRank2_product_regime`) reported exclusively standard Lean axioms: `[propext, Classical.choice, Quot.sound]`.
   - Pattern scan for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, and `elab` in `lean/Conjectures/SnellmanKozlovVolume.lean` returned zero matches.

2. **Statement Fidelity & Modeling Scope**
   - Verified directly against Jan Snellman's `arXiv:2611.26110v1` (19 Nov 2026):
     - Corollary 16 (`cor-rank2-volume`) matches `nvKoz`, `cellFactor`, and `rank2Sum` verbatim (`j = 1..n-d`, `C(n-1+d, d+j-1)`, `∏_{k=j+1}^{j+d} C(n,k)`, `NV(Koz(n)) = ∏_{k=2}^n C(n,k)`).
     - Proposition 20 (`prop-product-regime`) gives constancy for `d ≥ n - 1` with `NV(Koz(n; 0, d)) = C(2n-2, n-1) * NV(Koz(n))^2`, matching `nvRank2_product_regime`.
     - Conjecture 21 (`conj-nv-monotone`) states that `NV(Koz(n; 0, d))` is weakly increasing in `d`, checked numerically in the preprint through `n ≤ 7`.
     - Table `tab:volumes` (`n = 3..6`) and caption value `vol(Koz(6; 0, 4)) = 270000` match `verify.py`.
   - Formalization scope (`nvRank2` defined directly from Snellman's proved volume formulas rather than formalizing Kozlov polytope triangulations from scratch) is explicitly disclosed in `README.md`, `PROOF.md`, `paper.tex`, and Lean docstrings.

3. **Mathematical & Computational Verification**
   - Independently re-derived the termwise growth identity `(d + j) t_{d+1}(j) = (n + d) C(n, j + d + 1) t_d(j)`, the last-cell gain identity `t_{d+1}(n - d - 1) = t_d(n - d - 1) + C(n, d) t_d(n - d)`, the quantitative lower bound, strict monotonicity for `(n, d) ≠ (2, 0)`, and the unique equality `NV(Koz(2; 0, 0)) = NV(Koz(2; 0, 1)) = 2`.
   - `python -O -W error results/snellman-kozlov-volume/verify.py` passed cleanly (stdlib-only, no `assert`).
   - `results/snellman-kozlov-volume/paper.pdf` compiled with zero TeX warnings.

4. **Openness Audit**
   - `arXiv:2611.26110` lists v1 only (19 Nov 2026).
   - `the-omega-institute/trureturing` issues/PRs for `2611.26110` contain no entry for Conjecture 21 (`conj-nv-monotone`) or normalized-volume monotonicity (only unrelated problems `#32792` and `#33426`).
   - Zenodo API query (`2611.26110`) returned `0` prior records.

## Polish Items Resolved

1. Added this `AUDIT.md` file referenced from `README.md`.
2. Aligned `PROOF.md` Lemma 2.1 strictness statement with `paper.tex` (`t_{d+1}(j) > t_d(j)` strictly for every `1 ≤ j ≤ n - d - 1`, since `n + d > d + j`).
3. Qualified the `README.md` Lean verification headline to state upfront that formalization starts from Snellman's proved volume formulas (Corollary 16 and Proposition 20).
