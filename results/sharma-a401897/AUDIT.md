# Independent Adversarial Audit — Karan Sharma OEIS A401897 (`a(n) ~ 48n / pi^2`)

**Date:** 2026-11-26  
**Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`)  
**Verdict:** **PASS** (zero blocking defects)

## Summary of Checks

1. **Lean 4 Build (`Conjectures.SharmaA401897`):**
   - `lake build Conjectures.SharmaA401897` exited `0` (3253 jobs) with zero errors and zero warnings.
   - `lake env lean Conjectures/SharmaA401897.lean` exited `0` with empty output (no warnings or info messages).
2. **Axiom Audit:**
   - `#print axioms` on all five main theorems (`shifted_gauss_circle_open`, `shifted_gauss_circle_closed`, `uniform_visibility_bound`, `rank_norm_bound`, `sharma_a401897_asymptotic`) and supporting lemmas (`visibleCount_eq_moebius_sum`, `a401897_z_strictMono`, `rank_sandwich`) depends only on `[propext, Classical.choice, Quot.sound]`.
   - Zero `sorryAx`, zero `Lean.ofReduceBool`, zero custom axioms.
3. **Forbidden Tokens:**
   - Zero occurrences of `sorry`, `admit`, `axiom `, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option`, `partial`, `trustCompiler`, or `lcProof`.
4. **Mathematical & Spec Faithfulness:**
   - `gnorm`, `InWedge`, `wedgeLt`, `wedgeRank`, `a401897_z`, `IsVisibleFrom`, `visibleSet`, `visibleCount`, and `a401897` faithfully encode OEIS A401897 (including `w = 0`, exact norm-then-`b` ordering, and exact 1-based ranking).
   - `shifted_gauss_circle_open`, `shifted_gauss_circle_closed`, `uniform_visibility_bound`, `rank_norm_bound`, and `sharma_a401897_asymptotic` are non-vacuous, explicit, and match all citations in `README.md` and `paper.tex` verbatim.
5. **Python Verifier (`verify.py`):**
   - `python -O -W error results/sharma-a401897/verify.py` exited `0` and printed `ALL CHECKS PASSED`.
