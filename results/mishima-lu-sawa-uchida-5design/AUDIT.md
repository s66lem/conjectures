# Independent Adversarial Audit — Mishima–Lu–Sawa–Uchida Problem 8.3 (`arXiv:2503.21151v4`)

**Date:** 2026-11-26  
**Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`)  
**Verdict:** **PASS** (zero blocking defects)

## Summary of Checks

1. **Lean 4 Build (`Conjectures.MishimaLuSawaUchida5Design`):**
   - `lake build Conjectures.MishimaLuSawaUchida5Design` exited `0` with zero errors and zero warnings.
   - `lake env lean Conjectures/MishimaLuSawaUchida5Design.lean` exited `0` with empty output (no warnings or info messages).
2. **Axiom Audit:**
   - `#print axioms` on all four public theorems (`mishima_problem_8_3_37_design`, `exists_odd_5design_of_ge_17`, `not_exists_odd_5design_of_le_16`, `mishima_odd_5design_iff`) depends only on `[propext, Classical.choice, Quot.sound]`.
   - Zero `sorryAx`, zero `Lean.ofReduceBool`, zero custom axioms.
3. **Forbidden Tokens:**
   - Zero occurrences of `sorry`, `admit`, `axiom `, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option`, `partial`, `trustCompiler`, or `lcProof`.
4. **Mathematical & Spec Faithfulness:**
   - `chebMoment` matches $(1, 0, \tfrac{1}{2}, 0, \tfrac{3}{8}, 0)$ for $k = 0, \dots, 5$.
   - `IsAntipodalRat5Design X n` faithfully requires $X \subset (-1, 1) \cap \mathbb{Q}$, $|X| = n$, closure under negation, and $\sum_{x \in X} x^k = n \cdot \mu_k$ for all $k < 6$.
   - `mishima_problem_8_3_37_design` gives the explicit 37-point design over denominator $240$ verified via kernel `decide` on exact integer numerators.
   - `exists_odd_5design_of_ge_17` extends the base designs $N = 17, 18, 19$ by disjoint monotone 6-point rational blocks for $t \ge 20$.
   - `not_exists_odd_5design_of_le_16` gives a self-contained 2-adic proof of non-existence for every $N \le 16$.
   - `mishima_odd_5design_iff` establishes the full biconditional $\exists X,\; \mathrm{IsAntipodalRat5Design}\,X\,(2N+1) \iff 17 \le N$, and all cited Lean theorem names in `README.md`, `PROOF.md`, and `paper.tex` match verbatim.
5. **Python Verifier (`verify.py`):**
   - `python -O -W error results/mishima-lu-sawa-uchida-5design/verify.py` exited `0` and printed `ALL CHECKS PASSED`.
