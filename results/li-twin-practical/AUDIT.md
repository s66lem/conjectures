# Independent Adversarial Audit — Row 66 (Runbo Li Twin-Practical Conjecture 1.1)

- **Auditor:** Independent read-only cross-model review (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-27
- **Target:** `lean/Conjectures/LiTwinPractical.lean`, `results/li-twin-practical/{README.md, PROOF.md, verify.py, paper.tex}`
- **Verdict:** **PASS** on all 5 checks.

## Summary of Checks

1. **Build (`PASS`):** Compiled cleanly on remote Tincan node `johnnys` (`leanprover/lean4:v4.33.1`, `rc=0`, `ok=True`), with 0 errors, 0 warnings, and 0 info messages beyond `#print axioms`.
2. **Axioms (`PASS`):** `IsPractical`, `not_practical_pow30_add_two`, `not_practical_pow_mul30_add_two`, `li_conjecture_1_1_empty_of_dvd_thirty`, `li_conjecture_1_1_false`, and `small_exponents_witnesses` depend only on `[propext, Classical.choice, Quot.sound]`; `local_obstruction_iff_dvd_thirty` depends only on `[propext, Quot.sound]`.
3. **Forbidden tokens (`PASS`):** 0 matches across the entire file (including comments and docstrings) for `sorry`, `admit`, `axiom`, `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `unsafe`, `implemented_by`, `extern`, `partial`, `set_option`.
4. **Spec faithfulness and mathematical rigor (`PASS`):** `IsPractical` faithfully matches the standard definition (`0 < n` and every `1 ≤ m ≤ n` is a sum of distinct positive divisors of `n`); no vacuous hypotheses; `li_conjecture_1_1_false` faithfully negates Runbo Li's Conjecture 1.1 (*NNTDM* 32(3), 2026); `local_obstruction_iff_dvd_thirty` and `small_exponents_witnesses` verified without `native_decide`; `python -O -W error verify.py` exits `0` (`ALL CHECKS PASSED`).
5. **Doc consistency (`PASS`):** `README.md`, `PROOF.md`, `paper.tex`, `verify.py`, and Lean theorems are consistent, with zero `\operatorname` in `.md` files. Post-audit phrasing nit in `paper.tex` ("composite exponents" → "positive exponents not divisible by 30 outside the previously proved cases") resolved.
