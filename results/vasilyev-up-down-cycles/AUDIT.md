# Independent Adversarial Audit — Vasilyev Question 7.1 (`arXiv:2611.20344v2`)

- **Auditor:** Independent read-only cross-model review (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-26
- **Verdict:** **PASS** (zero blocking defects)

## Summary of Checks

1. **Fresh Lean 4 Build:** `lake build Conjectures.VasilyevUpDownCycles` (8706/8706 jobs) and `lake env lean Conjectures/VasilyevUpDownCycles.lean` (under `gpu_lock --slot ram`, `LEAN_NUM_THREADS=1`, no `-j`) both exited `0` with `0` errors and `0` warnings.
2. **Axiom Audit:** `#print axioms` on all 8 checked public declarations (`vasilyev_question_7_1_disproof`, `ratio_exceeds_three`, `cycleAt_injective`, `cycleAt_up_count`, `cycleAt_valid_steps`, `counterexampleSet`, `cycleAt`, `T`) depends only on `[propext, Classical.choice, Quot.sound]` (or subset). No `sorryAx`, `Lean.ofReduceBool`, or custom axioms.
3. **Forbidden Tokens:** Zero hits for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, `elab`.
4. **Faithfulness:** `U x = (3 * x + 1) / 2 = ⌈3x/2⌉`, `D x = (x + 1) / 2 = ⌈x/2⌉`, `T S x = if x ∈ S then U x else D x`; `vasilyev_question_7_1_disproof` establishes primitive cycle of exact length `ℓ = 382`, all vertices `≥ 2` (so strictly in `ℕ_{≥ 1}`), pairwise distinct, `a = 240` up-steps, and `3 ^ (240 + 1) < 2 ^ 382` (refuting `2 ^ ℓ < 3 ^ (a + 1)`).
5. **Independent Verifier & Docs:** `python -O -W error results/vasilyev-up-down-cycles/verify.py` exited `0` (`ALL CHECKS PASSED`), matching all parameters (`ℓ = 382`, `a = 240`, ratio `3.050403`, max element `258477331094`) across `VasilyevUpDownCycles.lean`, `PROOF.md`, `README.md`, and `paper.tex`.
