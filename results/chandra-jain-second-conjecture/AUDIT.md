# Independent Adversarial Audit — Result #60 (Second Chandra–Jain Conjecture + Exact Degree Criterion)

- **Auditor:** `claude-sonnet-5-5` (independent read-only cross-model adversarial review)
- **Date:** 2026-11-27
- **Target:** `arXiv:2608.11372v3`, Section 5 (`conj:chandra-jain-second`)
- **Lean file:** [`lean/Conjectures/ChandraJainSecondConjecture.lean`](../../lean/Conjectures/ChandraJainSecondConjecture.lean)

## Audit Summary

| Check | Result | Details |
|---|---|---|
| 1. Build & typecheck | **PASS** | Temp copy with `#print axioms` on all 21 public declarations built cleanly via `lake env lean` (`rc=0`, `77.4 s`, 18 threads on `bishop`); `0` errors, `0` warnings, `0` info messages beyond axiom output. |
| 2. Axioms | **PASS** | All 21 public declarations (`cot_mul_csc_sq_eq`, `trigF_add_pi`, `trigF_sub_pi`, `trigF_add_int_mul_pi`, `trigF_neg`, `trigF_pos`, `trigF_strictAntiOn`, `trigF_complex_eq`, `natDegree_minpoly_eq_card_orbit`, `card_oddUnitsBelow_even`, `two_mul_card_oddUnitsBelow_odd`, `legendreInt_of_prime`, `legendreInt_one`, `legendreInt_mod`, `two_mul_factorization_decomp`, `cycAut_zeta`, `exists_sqrt_neg_two_mul_in_cyclotomic`, `landscapeCoeff_degree_via_sign_flip`, `chandraJain_exact_degree`, `chandraJain_dichotomy`, `chandraJain_coprime_degree`) depend only on `[propext, Classical.choice, Quot.sound]`. |
| 3. Forbidden tokens | **PASS** | Case-sensitive grep across the entire file (comments and docstrings included) for `sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, `local instance`: **0 hits**. |
| 4. Specification audit | **PASS** | `landscapeCoeff k N` matches $\frac{1}{4}\sqrt{2/N}\cot(k\pi/2N)\csc^2(k\pi/2N)$ via `cot_mul_csc_sq_eq`; algebraicity/non-degeneracy confirmed (`N₀ ≥ 2` forces `φ(N₀) ≥ 1`); `natDegree_minpoly_eq_card_orbit` verified over `CyclotomicField (8 * N) ℚ`; 7 edge cases including even-`N₀` `(6,3)`, `(12,3)` cross-checked against `sympy.minimal_polynomial`; exact criterion, dichotomy, and Zhou's coprime corollary all match `arXiv:2608.11372v3`. |
| 5. Artifacts & verification | **PASS** (after README status update) | `python -O -W error results/chandra-jain-second-conjecture/verify.py` exited `0` (`Checked 3599 pairs (3 <= N <= 120)`, `[59, 48]` split, `ALL CHECKS PASSED`), standalone stdlib-only with `0` `assert`s; `0` `\operatorname` in `.md`; `paper.pdf` matches `paper.tex`. Stale `(in progress)` line in `README.md:7` fixed before publication. |
