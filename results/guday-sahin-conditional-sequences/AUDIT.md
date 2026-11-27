# Independent Adversarial Audit — Güday–Şahin Conditional-Sequence Conjectures (`INTEGERS 26, 2026, #A5`)

- **Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-27
- **Target:** `lean/Conjectures/GudaySahinConditionalSequences.lean` and `results/guday-sahin-conditional-sequences/{README.md, PROOF.md, verify.py, paper.tex, paper.pdf}`
- **Overall Verdict:** **PASS (5/5)**

## Audit Summary

1. **Build & Typecheck (`bishop`):** **PASS.** Clean build of temporary copy with `#print axioms` appended (`rc=0`, `elapsed_s=35.47`, 18 threads, `leanprover/lean4:v4.33.1`). Zero errors, zero warnings, zero info messages other than the `#print axioms` output.
2. **Axiom Check:** **PASS.** All 8 public theorems depend strictly on standard axioms `[propext, Classical.choice, Quot.sound]` only:
   - `conj2_exact_corrected_formula`
   - `conj2_holds_le_five`
   - `conj2_fails_all_ge_six`
   - `conj2_counterexample_6_9`
   - `paperCond_iff_bijective_of_le_three`
   - `nonbijective_family_ge_four`
   - `instQ_decimated`
   - `guday_sahin_conjecture_1_false_real`
3. **Forbidden Tokens:** **PASS.** Case-sensitive scan across the entire Lean file (including comments and docstrings) returned 0 matches for `sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, and `local instance`.
4. **Specification & Mathematical Audit:** **PASS.**
   - Conjecture 2 definitions (`tripleBox`, `isComp3`, `inD`, `distinctParts`, `cardW`, `cardWStar`, `cardA`) faithfully match Güday–Şahin (p. 18).
   - `guday_sahin_conjecture_1_false_real` faithfully captures Equation (1) and Conjecture 1 (p. 16) at `r = 4, m = 5` over `ℝ` for every `±1` sign function `s`, every eventual threshold `N`, and both `a_{i,0} ∈ {1, -1}` conventions, with no vacuous hypotheses or truncation loopholes.
   - `nonbijective_family_ge_four` holds for every `r ≥ 4`.
   - Independent SymPy verification confirmed `instA` and `det W(0) = 57854063997551257566686800189595316225787536`.
5. **Documentation & Verifier Consistency:** **PASS.** `python -O -W error results/guday-sahin-conditional-sequences/verify.py` outputs `ALL CHECKS PASSED`. All numbers agree across Lean, `README.md`, `PROOF.md`, `paper.tex`, and `verify.py`. Per auditor's precision notes, `README.md` explicitly distinguishes the Lean-proved theorems from Theorem 1 (prose proof + symbolic verification), and `verify.py` checks the instance recurrence from `n = mr + m - 1`.
