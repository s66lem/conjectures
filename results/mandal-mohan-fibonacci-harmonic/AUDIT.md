# Independent Audit Report — Mandal–Mohan Conjecture 1.19 (`arXiv:2611.32519v1`)

## Auditor & Verdict

- **Independent auditor:** Claude Sonnet 5.5 (`claude-sonnet-5-5`, read-only adversarial audit)
- **Date:** 2026-11-25
- **Verdict:** **PASS** (zero soundness blockers; all polish items resolved prior to publication)

## Checks Verified

1. **Lean 4 Build (`lake build Conjectures.MandalMohanFibonacciHarmonic` & `lake build Conjectures`):**
   - `Conjectures.MandalMohanFibonacciHarmonic` built cleanly in 26s with 0 errors and 0 warnings.
   - Full repository suite (`lake build Conjectures`, 8,814 jobs) passed with exit code `0`.

2. **Axiom & Hygiene Audit:**
   - Grep across `MandalMohanFibonacciHarmonic.lean` for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, and `admit`: **0 matches**.
   - `#print axioms` output:
     - `MandalMohanFibonacciHarmonic.mandal_mohan_harmonic_iff`: `[propext, Classical.choice, Quot.sound]`
     - `MandalMohanFibonacciHarmonic.mandal_mohan_harmonic_den_iff`: `[propext, Classical.choice, Quot.sound]`
     - `MandalMohanFibonacciHarmonic.mandal_mohan_conjecture_1_19`: `[propext, Classical.choice, Quot.sound]`
     - `MandalMohanFibonacciHarmonic.mandal_mohan_conjecture_1_19_den`: `[propext, Classical.choice, Quot.sound]`

3. **Statement Fidelity & Source Check:**
   - Verified verbatim against `https://arxiv.org/html/2611.32519v1` (Sagar Mandal and Mohan, *Integral Means of Fibonacci Numbers: Divisibility, Density, and Arithmetic Structure*, 24 Nov 2026): Theorem 1.18, the 2-adic method remark, numerical checks for $k \in \{3, 4, 5\}$ and $n \le 10^4$, and Conjecture 1.19.
   - `Nat.fib 1 = 1` and `Nat.fib 2 = 1` match the paper's indexing $F_1 = F_2 = 1$; both the `∃ m : ℕ, (m : ℚ) = fibHarmonic n k` and `(fibHarmonic n k).den = 1` formulations are proved.

4. **Independent Python Verifier (`python -O -W error results/mandal-mohan-fibonacci-harmonic/verify.py`):**
   - Stdlib-only (`fractions`, `math`), `-O`-safe (`require()`, zero `assert`), passes with exit code `0`.

## Polish Items Resolved

1. Updated the module docstring of `verify.py` to state `7 <= n <= 40 (1 <= k <= 6)` matching the loop bounds verbatim, and re-ran `python -O -W error verify.py`.
2. Added this `AUDIT.md` file referenced by `README.md`.
3. Confirmed `paper.pdf` matches `paper.tex` with 0 TeX warnings.
