# Audit Record — Conjecture 7.4 of Gil–Liang–Odetola–Weiner (`arXiv:2609.01562v1`)

## Summary

- **Verdict:** **PASS**
- **Independent Auditor:** Claude Sonnet 5.5 (`medium`, read-only adversarial audit) + live primary-source verification against `arXiv:2609.01562v1` HTML
- **Date:** 2026-11-25

## Audit Findings

1. **Primary-Source Statement Match:** Confirmed directly against the live HTML of `arXiv:2609.01562v1` (Proposition 7.2 & Conjecture 7.4): `D_paper`, `G_paper`, `R_paper`, `conjecture74_paper`, and `sharpness_R_paper_495_240` match the paper verbatim.
2. **Forbidden Lean Constructs:** Passed. Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `unsafe`/`opaque`/`implemented_by` in Lean code.
3. **Mathematical & Lean Soundness:** Passed across all components:
   - Lemma 1 (`R_paper_eq_trafficRatio`): exact absorption identities with all denominators proved nonzero.
   - Part I unimodality (`stepLe_succ`, `stepGe_pred`, `trafficF_le_of_le_peak`, `trafficF_le_of_ge_peak`, `trafficInequality_of_peak`) and `checkRange_sound`: verified `hL`/`hR` extraction and propagation, exact `Nat.mul_div_cancel` recurrences, `c496_eq`/`c992_eq` base equalities, and exact `[496, 800)` coverage via `checkRange 304 496 ...`.
   - Part II (`W_even_mono`, `W_odd_le_even`, `W_200_bound`, `W_bound`, `one_sub_div_one_add_le_exp`, `choose_ratio_sq_le_exp`, `quad_exp_bound`, `exp_inv_801_le`, `exp_neg_half_lt`, `trafficInequality_of_ge_800`): sound Stirling-free closure for all $n \ge 800$ yielding $R_n(a)^2 < 0.996968 < 1$.
   - Assembly (`conjecture74_proved`, `conjecture74_paper`): gap-free split at $n = 800$.
4. **Independent Python Verifier:** `python -O -W error results/gil-antidiagonal-traffic/verify.py` passed all 6 exact-arithmetic checks (`98,192` pairs in `[496, 799]`, worst $R_{497}(241) \approx 0.9999552841 < 1$; sharpness $R_{495}(240) \approx 1.0000240709 > 1$; stdlib-only, `-O`-safe `require()`, `0.294 s`).
5. **Document Hygiene:** Passed. Zero `\operatorname` in Markdown; `paper.pdf` compiles via `tectonic` with zero warnings; author `Salem Levinstein` (no `\thanks`).

## Lean 4 Kernel Axiom Check

Independently verified under `leanprover/lean4:v4.33.1` + Mathlib `v4.33.1` (`lake env lean Conjectures.lean` passed across all 23 modules):

```text
'GilAntidiagonalTraffic.conjecture74_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'GilAntidiagonalTraffic.conjecture74_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
'GilAntidiagonalTraffic.sharpness_495_240' depends on axioms: [propext, Classical.choice, Quot.sound]
'GilAntidiagonalTraffic.sharpness_R_paper_495_240' depends on axioms: [propext, Classical.choice, Quot.sound]
'GilAntidiagonalTraffic.R_paper_eq_trafficRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
```
