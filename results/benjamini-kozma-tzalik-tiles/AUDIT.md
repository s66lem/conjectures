# Independent Adversarial Audit — Benjamini–Kozma–Tzalik Question 9 (`Electron. J. Combin. 33(3), 2026, #P3.28` / `arXiv:2303.07956v2`)

- **Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`, effort `medium`)
- **Date:** 2026-11-27
- **Target:** `lean/Conjectures/BenjaminiKozmaTzalikTiles.lean` and `results/benjamini-kozma-tzalik-tiles/{README.md, PROOF.md, verify.py, paper.tex, paper.pdf}`
- **Overall Verdict:** **PASS (5/5)**

## Audit Summary

1. **Build & Typecheck (`bishop`):** **PASS.** Clean build of temporary copy with `#print axioms` appended (`rc=0`, `elapsed_s=50.7`, 18 threads, `leanprover/lean4:v4.33.1`). Zero errors, zero warnings, zero info messages other than the four `#print axioms` lines.
2. **Axiom Check:** **PASS.** All 4 public theorems depend strictly on standard axioms `[propext, Classical.choice, Quot.sound]`:
   - `bkt_q9_disproof`
   - `odd_size_power_of_two_tile_exists`
   - `even_size_ge_four_no_power_of_two_tile`
   - `power_of_two_tile_size_iff`
3. **Forbidden Tokens:** **PASS.** Case-sensitive scan across the entire Lean file (including comments and docstrings) returned 0 matches for `sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, and `local instance`.
4. **Specification & Mathematical Audit:** **PASS.**
   - `Tiles` faithfully captures disjoint-union translational tiling of `ℤ`.
   - `bkt_q9_disproof` proves `{1, 4, 16} ⊆ {2^j | j ≤ 4}`, `Tiles`, and `ncard = 3`, directly refuting the second part of Question 9.
   - All edge cases (`k = 0, 1, 2, 3`, even `k ≥ 4`), `ℕ → ℤ` injectivity, Newman periodicity, Coven–Meyerowitz (T1) cyclotomic factorization, and the `Φ_{2^j}` alternating-sum obstruction are verified sound with no hidden hypotheses.
5. **Documentation & Verifier Consistency:** **PASS.** `python -O -W error results/benjamini-kozma-tzalik-tiles/verify.py` outputs `ALL CHECKS PASSED`. All docs agree on scope and values; per auditor's note, the 1-sentence T1 span bound ruling out `k = 15` for `n ≤ 15` (via `p = 5 ∣ 15`) was explicitly added to `PROOF.md` and `paper.tex`.
