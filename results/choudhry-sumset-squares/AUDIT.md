# Independent Adversarial Audit — Choudhry `(5, 4)` and `(6, 4)` Integer Sumsets of Perfect Squares (`INTEGERS 26, 2026, #A66` / `arXiv:2508.07806`)

- **Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-27
- **Target:** `lean/Conjectures/ChoudhrySumsetSquares.lean` and `results/choudhry-sumset-squares/{README.md, PROOF.md, verify.py, paper.tex, paper.pdf}`
- **Overall Verdict:** **PASS (5/5)**

## Audit Summary

1. **Build & Typecheck (`bishop`):** **PASS.** Clean build of temporary copy with `#print axioms` appended (`rc=0`, ~32s, 18 threads, `leanprover/lean4:v4.33.1`). Zero errors, zero warnings, zero info messages other than `#print axioms`.
2. **Axiom Check:** **PASS.** All 10 public theorems depend strictly on standard axioms `[propext, Classical.choice, Quot.sound]` (with the two `decide` gcd theorems using only `[propext]`).
3. **Forbidden Tokens:** **PASS.** Case-sensitive scan across the entire Lean file (including comments and docstrings) returned 0 matches for `sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, and `local instance`.
4. **Specification & Mathematical Audit:** **PASS.**
   - `IsSquareSumset` and `IsPosDisjointSquareSumset` faithfully capture Choudhry's Sec. 6 open problem with no vacuous hypotheses or hidden loopholes.
   - All 20 sums for the primary `(5, 4)` solution and all 24 sums for the `(6, 4)` solution were independently recomputed and confirmed to match the stated roots; `A5_1` through `A5_4` are verified by `rfl` in Lean.
   - `listGcd ... = 1` certifies `gcd(A ∪ B) = 1` (hence squarefree/primitive), confirmed independently in Python.
   - Theorems 6 and 7 rigorously prove infinitely many distinct all-positive, pairwise disjoint `(5, 4)` and `(6, 4)` solutions via `(2n+2)^2` scaling and `∓1` translation.
5. **Documentation & Verifier Consistency:** **PASS.** `python -O -W error results/choudhry-sumset-squares/verify.py` outputs `ALL CHECKS PASSED`. All numbers agree across Lean, `README.md`, `PROOF.md`, `paper.tex`, and `verify.py`. Exhaustiveness counts (`max X ≤ 10000`, `40000`) are explicitly attributed to the divisor-pair search rather than Lean.
