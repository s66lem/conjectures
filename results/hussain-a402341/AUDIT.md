# Independent Adversarial Audit — Result #30

**Target:** Sajid Khan Hussain's [OEIS A402341](https://oeis.org/A402341) 2-adic valuation conjecture (created November 17, 2026), generalized to all power-of-two block lengths $L = 2^r$.  
**Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`, effort `medium`).  
**Date:** November 26, 2026  
**Verdict:** **PASS** (zero mathematical or Lean 4 defects).

## Checks Verified

1. **Lean 4 Build & Axiom Audit**
   - `lake build Conjectures.HussainA402341` succeeded cleanly (8706 jobs, 0 errors, 0 warnings).
   - `#print axioms` on `centralPolyCoeff_congr_centralBinom`, `padicValNat_centralPolyCoeff_even`, `oeis_A402341_conjecture`, and `oeis_A402341_congr_centralBinom` reported only `[propext, Classical.choice, Quot.sound]`.
   - Grep for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, and `elab` returned zero matches.
   - Imported in `lean/Conjectures.lean`.

2. **OEIS & Statement Fidelity**
   - Verified directly against live `https://oeis.org/A402341/internal`: all 20 published initial terms (`n = 0..19`), index $\lfloor 15n/2 \rfloor$, and verbatim conjecture statement match.
   - Verified `padicValNat_centralPolyCoeff_even` holds for all `r m : ℕ` (including `r = 0` and `n = 0`) with no hidden hypotheses or vacuities, and `oeis_A402341_conjecture` takes only `Even n`.
   - Verified `evalY`, `FitsDeg`, `R`, `Q`, `IsAdmissible`, `IsStrongAdmissible`, and `padicValNat_two_centralBinom` have zero off-by-one errors.
   - Openness confirmed across live OEIS, arXiv API (0 hits), Zenodo API (0 hits for `A402341`), and `the-omega-institute/trureturing` (0 issues, 0 PRs).

3. **Independent Verification Script**
   - `python -O -W error results/hussain-a402341/verify.py` passed cleanly (stdlib-only, `-O`-safe `require()`, checks published terms `n = 0..19`, `R_k`/`Q_r` identities and strong admissibility for `r = 1..6`, dense polynomial powers for `r = 1..5` including A402341 through `n = 160`, and large inclusion-exclusion exponents up to `n = 2048`).

4. **Documentation & Paper Consistency**
   - Zero `\operatorname` in Markdown, `\author{Salem Levinstein}` with no `\thanks`, `paper.pdf` compiled with 0 TeX warnings, and spot checks (`a(3) = 192`, `A005190`, `A025013`) verified.
