# Independent Adversarial Audit — Result #29

**Target:** Clark Kimberling's May 2019 conjectures on [OEIS A308355](https://oeis.org/A308355) and [OEIS A025065](https://oeis.org/A025065) concerning the maximal initial-segment agreement between A308355 and row $n$ of [OEIS A128628](https://oeis.org/A128628).  
**Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`, effort `medium`).  
**Date:** November 26, 2026  
**Verdict:** **PASS** (zero mathematical or Lean 4 defects; all polish items resolved).

## Checks Verified

1. **Lean 4 Build & Axiom Audit**
   - `lake build Conjectures.KimberlingA308355` succeeded cleanly with 0 errors and 0 warnings.
   - `#print axioms` on `a308355_is_row_limit`, `exact_agreement_eq_A025065`, `a308355_conjecture_iff_even`, `A025065_eq_sum_partitions`, and `counterexample_n5` reported only `[propext, Classical.choice, Quot.sound]`.
   - Grep for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, and `elab` returned zero matches.
   - Imported in `lean/Conjectures.lean`.

2. **OEIS & Statement Fidelity**
   - Cross-checked directly against live OEIS internal records for A308355 (terms 1–68), A128628, A080577, and A025065 (offset 0).
   - Verified `exact_agreement_eq_A025065` establishes all three required properties (length bound, agreement on all `i < S`, and strict disagreement at index `S` for `n ≥ 3`, with full-row agreement for `n = 1, 2`).
   - Verified odd edge cases $n = 1$ (actual $1$ vs. predicted $2$), $n = 3$ ($2$ vs. $4$), and $n = 5$ ($4$ vs. $7$), and the exact parity equivalence `a308355_conjecture_iff_even`.

3. **Independent Verification Script**
   - `python -O -W error results/kimberling-a308355/verify.py` passed (stdlib-only, `-O`-safe).

4. **Polish Items Addressed**
   - Restored verbatim quotation of Kimberling's A025065 comment (including literal `A308355(n-1)`) in `README.md` and `paper.tex`, with an explicit note crediting his May 24, 2019 A025065 comment for already giving the corrected bound $\mathrm{A025065}(n)$.
   - Expanded `verify.py` to check the first 16 published terms of A025065 ($0 \le n \le 15$) and the first 30 published terms of A308355.
   - Recompiled `paper.pdf` cleanly with 0 TeX warnings and added this `AUDIT.md` file.
