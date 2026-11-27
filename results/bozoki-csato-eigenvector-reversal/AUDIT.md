# Independent Adversarial Audit — Result #58 (Bozóki–Csató Eigenvector Reversal)

- **Auditor:** Independent cross-model read-only audit (`claude-sonnet-5-5`, effort `medium`)
- **Target:** [`lean/Conjectures/BozokiCsatoEigenvectorReversal.lean`](../../lean/Conjectures/BozokiCsatoEigenvectorReversal.lean) and companion package in [`results/bozoki-csato-eigenvector-reversal/`](./)
- **Date:** 2026-11-26
- **Verdict:** **PASS** (5/5 checks passed)

## Audit Checks

1. **Build & Typecheck — PASS:** Independent `lake env lean` run on an out-of-repo temporary copy (`LEAN_NUM_THREADS=1`, no `-j`, gated by `gpu_lock` `ram` slot) exited with code `0` and produced `0` errors, `0` warnings, and `0` info messages (aside from the auditor's appended `#print axioms` commands).
2. **Axioms — PASS:** All 16 public declarations (`pcm_diag_eq_one`, `right_perron_unique`, `left_perron_unique`, `strictAnti_smul_of_pos`, `strictMono_inv_smul_of_pos`, `reversal_class_characterization`, `reversal_from_const_rowsum`, `A4_isPCM`, `w4_pos`, `v4_pos`, `A4_mulVec_w4`, `v4_vecMul_A4`, `w4_strictAnti`, `v4_inv_strictMono`, `bozoki_csato_four_alternatives`, `n3_right_eq_inv_left`) depend exclusively on the standard axioms `[propext, Classical.choice, Quot.sound]`.
3. **Forbidden Tokens — PASS:** Case-sensitive scan across the entire Lean file (including comments and docstrings) returned `0` hits for `sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, and `local instance`.
4. **Adversarial Specification Audit — PASS:** Verified non-vacuity and exact fidelity to Bozóki–Csató (`arXiv:2603.24274`, Section 5 / Example 5):
   - `IsPCM` captures entrywise positivity and reciprocity (`A i j * A j i = 1`, implying unit diagonal).
   - `right_perron_unique` and `left_perron_unique` establish uniqueness of positive Perron eigenvectors and eigenvalues for arbitrary entrywise-positive real matrices (`n > 0`).
   - `bozoki_csato_four_alternatives` quantifies over all positive right eigenvectors `w` and all positive left eigenvectors `v` of `A4`, proving `mu = 5`, `StrictAnti w` (`0 ≻ 1 ≻ 2 ≻ 3`), and `StrictMono (fun i => (v i)⁻¹)` (`3 ≻ 2 ≻ 1 ≻ 0`).
   - `reversal_class_characterization` and `reversal_from_const_rowsum` establish the exact diagonal-rescaling equivalence with constant-row-sum PCMs.
   - `n3_right_eq_inv_left` establishes sharpness at `n = 3` (`w = t • v⁻¹` for some `t > 0`).
   - Minor cosmetic docstring mismatch on lines 25–26 (`reversal_class_iff` / `exists_reversal_from_const_rowsum` vs. actual names `reversal_class_characterization` / `reversal_from_const_rowsum`) was corrected immediately after audit.
5. **Cross-Document Consistency & Companion Verifier — PASS:** `python -O -W error verify.py` exited `0` and printed `ALL CHECKS PASSED`. All numerical witnesses (`A4`, `w4`, `v4`, `λ = 5`), ratio inequalities, and `n = 3` formulas agree across the Lean source, `PROOF.md`, `paper.tex`, and `README.md`.
