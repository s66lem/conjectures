# Independent Adversarial Audit — F. Bihan 3D Fewnomial Topological Degree (`arXiv:2611.34336v1`)

- **Auditor:** Independent read-only cross-model review (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-26
- **Verdict:** **PASS** (zero blocking defects)

## Summary of Checks

1. **Fresh Lean 4 Build:** `lake build Conjectures.BihanFewnomialDegree` (8706 jobs) and `lake env lean Conjectures/BihanFewnomialDegree.lean` (under `gpu_lock --slot ram`, `LEAN_NUM_THREADS=1`, no `-j`) both exited `0` with `0` errors and `0` warnings.
2. **Axiom Audit:** `#print axioms` on all 18 public declarations (including `bihan_3d_degree_bound`, `bihan_3d_degree_bound_of_N`, `n7_realizes_0..3`, `extremal_V8`, `extremal_V9`, `extremal_V10`, `extremal_V12`) depends only on `[propext, Classical.choice, Quot.sound]` (subset `[propext]` for the computational witnesses). No `sorryAx`, `Lean.ofReduceBool`, or custom axioms.
3. **Forbidden Tokens:** Zero hits for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, `elab`.
4. **Faithfulness:** `bihan_3d_degree_bound` proves `4 * |d| ≤ 3 * V - 8` (and `|d| ≤ 3` for `V ≤ 7`) over any linearly ordered field via the algebraic Plücker-telescoping identity `4d = 2 ∑ w_v - F_+ + F_-` and `2 w_v ≤ p_v - 1`. All `checkUASlice`, `checkUC`, and `facetsSliceZ` partitions cover `0..V-1` with no gaps or overlaps and exact facet counts `2V - 4` (`14, 16, 20` for `V = 9, 10, 12`).
5. **Independent Verifier & Docs:** `python -O -W error results/bihan-fewnomial-degree/verify.py` exited `0` (`ALL CHECKS PASSED`), verifying `N = 7` degrees `{0, 1, 2, 3}`, extremal witnesses `V = 8, 9, 10, 12` (degrees `4, 4, 5, 7`), and 2,430 random instances.
