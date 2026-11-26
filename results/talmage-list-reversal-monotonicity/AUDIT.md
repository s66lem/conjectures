# Independent Adversarial Audit — Talmage Monotonicity Conjecture (`arXiv:2611.25115v1`)

- **Auditor:** `claude-sonnet-5-5` (read-only cross-model adversarial review)
- **Date:** 2026-11-26
- **Verdict:** **PASS** (0 blocking defects)

## Summary of Checks

1. **Lean 4 Build & Standalone Compilation:**
   - `lake build Conjectures.TalmageListReversal` exited 0 (132 jobs) under `gpu_lock --slot ram` with `LEAN_NUM_THREADS=1`.
   - Forced `lake env lean Conjectures/TalmageListReversal.lean` exited 0 with empty output (0 errors, 0 warnings).
2. **Axiom Audit (`#print axioms`):**
   - Verified on all six theorems: `mem_nextStates_of_step`, `not_reversible_2_6`, `not_reversible_1_3_8_4`, `talmage_monotonicity_disproof` depend strictly on `[propext, Quot.sound]` (subset of standard axioms); `reversible_2_7` and `reversible_1_3_7_4` depend on zero axioms.
3. **Forbidden-Construct & Import Audit:**
   - Zero hits for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `set_option`, or `admit`.
   - Imported in `lean/Conjectures.lean`.
4. **Adversarial Faithfulness Audit (checked against arXiv v1 PDF):**
   - `Step` (adjacent combine and positive split) and `LegalState n` (distinct entries in `1..n`) match the paper's rules, with `Reversible L` using `listMax L`.
   - `mem_nextStates_of_step` proves completeness of `nextStates`, validating the closed-component irreversibility certificates `comp26_closed` and `comp1384_closed`.
   - `bumpMax` faithfully models replacing maximum $n$ with $n + 1$, disproving both directions of monotonicity (`[2, 6]` irreversible vs `[2, 7]` reversible; `[1, 3, 7, 4]` reversible vs `[1, 3, 8, 4]` irreversible, agreeing with Appendix A).
5. **Computational Verification & Documentation:**
   - `python -O -W error results/talmage-list-reversal-monotonicity/verify.py` exited 0 with `ALL CHECKS PASSED` (stdlib only, no `assert`).
   - Zero `\operatorname` in Markdown files, author `Salem Levinstein` (no `\thanks`), `paper.pdf` compiled with 0 TeX warnings, and arXiv confirms `v1` is the sole version.
