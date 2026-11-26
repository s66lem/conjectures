# Independent Cross-Model Audit: Omar E. Pol's OEIS A400974, A280940, and A384225 Conjectures

**Auditor:** `claude-sonnet-5-5` (independent read-only adversarial audit)  
**Date:** 2026-11-26  
**Verdict:** **PASS** (no blocking defects)

## Summary of Checks

1. **Lean 4 Formalization (`lean/Conjectures/PolA400974.lean`):**
   - `lake build Conjectures.PolA400974` succeeded cleanly (exit 0, zero errors, zero warnings).
   - `#print axioms` on all five main theorems (`a280940Row_eq_a384225Row`, `a384222Row_eq_a001511_mul_a384225Row`, `a400974_eq_a001511_mul_a384230`, `pol_conjectures`, `pol_a400974_conjecture`) depends solely on standard axioms `[propext, Classical.choice, Quot.sound]`.
   - Hygiene grep for `sorry|axiom|native_decide|unsafe|implemented_by|admit|set_option|opaque|extern|macro|elab` returned zero matches.
   - Imported in `lean/Conjectures.lean`.

2. **Statement Fidelity:**
   - Verified directly against the live OEIS entries for A400974, A280940, and A384225.
   - Lean definitions (`a262045`, layer-run subpart counts for A280940, maximal 2-dense divisor blocks splitting at `x > 2 * prev`, and middle-element / 0-when-even extraction) faithfully match the OEIS definitions with no extra hypotheses beyond the OEIS domain `0 < n`.
   - Independent recomputation of A280940 for `n < 200` matched all 62 published OEIS terms.

3. **Mathematical Proof (`PROOF.md`):**
   - Verified the layer-run variation identity and stutter invariance (Lemma 2.1), the jump-point model $W_n$ and reversal identity $W_n(2n/e) = W_n(e-1)$ (Lemmas 3.1–3.2, Proposition 3.3), the block-to-interval correspondence and inter-block zero gaps, and the dyadic chain bijection $|B_k| = (v_2(n)+1)|B_k^{\text{odd}}|$, including edge cases $n = 1$ and powers of $2$.

4. **Verifier & Packaging:**
   - `python -O -W error results/pol-a400974/verify.py` passed (`ALL CHECKS PASSED`), covering $1 \le n \le 4096$ plus the published OEIS prefixes of A400974 ($n \le 84$) and A384230 ($n \le 87$).
   - Standalone stdlib-only verifier with no `assert` statements and raw module docstring.
   - Zero `\operatorname` in Markdown files; `paper.tex` has `\author{Salem Levinstein}` (no `\thanks`) and compiles to `paper.pdf` with zero warnings.

5. **Openness Audit:**
   - Confirmed live OEIS conjectures remain open and `the-omega-institute/trureturing` has no resolving PRs (open preregistration issue #31198 only).

## Non-Blocking Polish Items Applied
- Relabeled "Combining (1) and (2)" to "Combining Theorem 1(1) and Theorem 1(2)" in `PROOF.md` §4.
- Expanded the final sentence of Lemma 2.1 in `PROOF.md` to make the zero-collapse preservation of positive parts explicit.
