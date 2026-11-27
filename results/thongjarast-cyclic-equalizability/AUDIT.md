# Independent Adversarial Audit — #56 (Thongjarast Problem 2 / `prob:discard`, `arXiv:2607.18452v1`)

**Auditor:** `claude-sonnet-5-5` (independent cross-model read-only audit)  
**Verdict:** **PASS**

## Verified Checks

1. **Lean 4 Build & Standalone Typecheck:**
   - `lake build Conjectures.ThongjarastCyclicEqualizability` exited `0` (3006 jobs) with `0` errors and `0` warnings.
   - `lake env lean Conjectures/ThongjarastCyclicEqualizability.lean` exited `0` with empty output (`0` errors, `0` warnings, `0` info messages).
2. **Axiom Audit:**
   - All 7 public theorems depend exclusively on the standard Lean axioms `[propext, Classical.choice, Quot.sound]` (or a subset thereof):
     - `step3_arithmetic`: `[propext, Quot.sound]`
     - `wordU_perm_wordV`: `[propext, Classical.choice, Quot.sound]`
     - `wordU_ne_wordV`: `[propext, Quot.sound]`
     - `wordU_surjective`: `[propext, Quot.sound]`
     - `family_not_equalizable`: `[propext, Classical.choice, Quot.sound]`
     - `thongjarast_prob_discard_disproof`: `[propext, Classical.choice, Quot.sound]`
     - `smallest_counterexample_full_alphabet_equalizable`: `[propext, Classical.choice, Quot.sound]`
3. **Forbidden-Token Audit:**
   - Case-sensitive scan for `sorry`, `admit`, `axiom `, `native_decide`, `unsafe`, `implemented_by`, `extern`, `partial `, `set_option`, `local instance`, `Classical.choose_spec` returned `0` hits.
4. **Specification Faithfulness:**
   - `interleave` faithfully encodes `ins 0 ++ [w 0] ++ ins 1 ++ ... ++ [w (n-1)] ++ ins n`.
   - `CycEquiv` faithfully encodes cyclic equivalence of equal-length lists with shift `d : ℕ` modulo `L` (covering all integer shifts).
   - `CyclicallyEqualizable` restricts only the inserted letters to `σ`, leaving original letters unrestricted.
   - `thongjarast_prob_discard_disproof` quantifies universally over every finite alphabet `α` with `3 ≤ Fintype.card α`, yielding `n = 3|α|` and words `u, v` satisfying `List.Perm (ofFn u) (ofFn v)`, `u ≠ v`, `Function.Surjective u`, and `∀ c : α, ¬ CyclicallyEqualizable (Finset.univ.erase c) u v`.
   - `smallest_counterexample_full_alphabet_equalizable` explicitly verifies full-alphabet equalizability for `m = 3` at length `15` with shift `d = 10`.
5. **Computational Verifier:**
   - `python -O -W error results/thongjarast-cyclic-equalizability/verify.py` exited `0` with `ALL CHECKS PASSED`.
