# Independent Audit Report — Zai–Lv–Sabir / Tian–Dong Conjecture 1.14 (`arXiv:2611.32794v1`)

## Auditor & Verdict

- **Independent auditor:** Claude Sonnet 5.5 (`claude-sonnet-5-5`, read-only adversarial audit)
- **Date:** 2026-11-25
- **Verdict:** **PASS** (zero soundness blockers; all polish items resolved prior to publication)

## Checks Verified

1. **Lean 4 Build (`lake build Conjectures.ZaiLvSabirSplitHamilton` & `lake build Conjectures`):**
   - `Conjectures.ZaiLvSabirSplitHamilton` built cleanly in 9.9s with 0 errors and 0 warnings.
   - Imported in `lean/Conjectures.lean`.

2. **Axiom & Hygiene Audit:**
   - Grep across `ZaiLvSabirSplitHamilton.lean` for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, and `elab`: **0 matches**.
   - `#print axioms` output:
     - `ZaiLvSabirSplitHamilton.paley22_counterexample`: `[propext, Classical.choice, Quot.sound]`
     - `ZaiLvSabirSplitHamilton.circulant_counterexample_all_ge_6`: `[propext, Classical.choice, Quot.sound]`
     - `ZaiLvSabirSplitHamilton.zai_lv_sabir_conjecture_1_14_false_all_ge_5`: `[propext, Classical.choice, Quot.sound]`

3. **Statement Fidelity:**
   - `IsSplitGraph`, `IsRConnected`, `IsStarAndStarPlusEFree`, `HamiltonPath`, and `IsHamiltonConnected` faithfully encode Conjecture 1.14 of Zai, Lv, and Sabir (`arXiv:2611.32794v1`; originally Conjecture 6.1 of Tian & Dong, `arXiv:2603.12770v1`).
   - `IsStarAndStarPlusEFree G r` (every center `c` and `(r+1)`-subset `L ⊆ N(c)` spans two distinct unordered edges `e₁ ≠ e₂` in `G.edgeSet` inside `L`) is logically equivalent to forbidding both `K_{1,r+1}` and `K_{1,r+1}+e` as induced subgraphs.
   - Both the `r = 5` Paley `(11, 5, 2)` 22-vertex counterexample and the infinite `(2r+8)`-vertex circulant family for all `r ≥ 6` are transported to `SimpleGraph (Fin n)` with `n ≥ 2r + 7`.

4. **Independent Python Verifier (`python -O -W error results/zai-lv-sabir-split-hamilton/verify.py`):**
   - Stdlib-only (`itertools`), `-O`-safe (`require()`, zero `assert`), passes with exit code `0`.

## Polish Items Resolved

1. Clarified in `PROOF.md` and `paper.tex` that the $r = 4$ double-counting obstruction applies to balanced $r$-regular split graphs only, and that the $r = 4$ case of Conjecture 1.14 remains open.
2. Standardized the Tian–Dong bibliography entry in `paper.tex` to `arXiv:2603.12770v1` (noting v2 proves $r = 3$), verified verbatim against arXiv API metadata.
3. Updated `verify.py` docstring to match the exact checked ranges (`r = 6, 7` full checks, `r = 6..50` algebraic checks) and added an independent exact bitmask DP verifying non-existence of a Hamilton path between clique vertices `0` and `1` in the complete balanced split graph $K_5 + \overline{K_5}$.
4. Added this `AUDIT.md` file, recompiled `paper.pdf` with zero warnings, and re-verified `python -O -W error verify.py`.
