# Independent Adversarial Audit — Kai Liang Conjecture 4.1 (`arXiv:2611.29198v1`, Misère Octal Game `0.3122`)

- **Auditor:** Independent read-only cross-model review (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-26
- **Verdict:** **PASS** (after correcting the two theorem-name typos in `README.md` and `paper.tex` flagged by the auditor; the Lean 4 proof itself passed every check with zero defects)

## Summary of Checks

1. **Fresh Lean 4 Build:** `lake build Conjectures.LiangOctal03122` (8706 jobs) and `lake env lean Conjectures/LiangOctal03122.lean` (under `gpu_lock --slot ram`, `LEAN_NUM_THREADS=1`, no `-j`) both exited `0` with `0` errors and `0` warnings.
2. **Axiom Audit:** `#print axioms` on all public theorems (`phi_iff_isMisereP`, `liang_conjecture_4_1_literal_disproof`, `liang_conjecture_4_1_ge_3`) and supporting lemmas (`checkPos_all`, `reducePair_diag_shift`, `reducePair_top_shift`, `phi_diag_shift`, `phi_top_shift`, `isMisereP_iff`, `Step03122.sum_lt`) depends only on `[propext, Classical.choice, Quot.sound]` (or subset). No `sorryAx`, `Lean.ofReduceBool`, or custom axioms.
3. **Forbidden Tokens:** Zero hits for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, `elab`.
4. **Faithfulness:** All 897 lines reviewed — `0.3122` move rules (remove 1 or 2, reduce `h > k` by `k ∈ {1, 3, 4}`, no splits), misère convention (empty position is N), literal disproof (`o(2,2,7,2) = N` vs `o(2,2,14,2) = P`), and the 98-entry `closedFormKey` for `x, y ≥ 3` all match Conjecture 4.1 with zero loopholes.
5. **Independent Verifier & Docs:** `python -O -W error results/liang-octal-03122/verify.py` exited `0` (`ALL CHECKS PASSED`). Doc theorem references in `README.md` and `paper.tex` were updated to the exact Lean names `liang_conjecture_4_1_literal_disproof` and `liang_conjecture_4_1_ge_3`, and `paper.pdf` was recompiled cleanly.
