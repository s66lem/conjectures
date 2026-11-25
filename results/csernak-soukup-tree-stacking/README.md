# Csernák–Soukup tree stacking conjecture and literal Almost Stacked Hypothesis

Complete proposed unconditional proof of [Conjecture 5.6](https://arxiv.org/html/2610.09650) (`stack(T) = estim(T)` for every finite connected tree T) together with explicit counterexamples disproving both parts of the literal [Hypothesis 3.2 (Almost Stacked Hypothesis)](https://arxiv.org/html/2610.09650) of Csernák and Soukup (`arXiv:2610.09650`, October 2026). The tree proof avoids ASH entirely via a bottom-up greedy potential and fractional relaxation, yielding an explicit O(n²) stacking algorithm. Literal Hypothesis 3.2 fails on P₄ for stacking (least almost-stacked threshold 12 vs. `stack(P₄) = 15`, witness `(9,0,0,3)`) and on the triangle with a two-edge tail G₅ for clearing (least almost-stacked threshold 16 vs. `clear(G₅) = 22`, witness `(0,0,0,2,14)`).

- [Complete proof and disproof](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/CsernakSoukupTreeStacking.lean) (`CsernakSoukup.conjecture_5_6`, `CsernakSoukup.P4.literal_ASH_fails`, `CsernakSoukup.G5.clearing_witness`)
- [Preprint PDF](paper.pdf) · [LaTeX source](paper.tex) · [Zenodo preprint (DOI: 10.5281/zenodo.24519728)](https://doi.org/10.5281/zenodo.24519728)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.CsernakSoukupTreeStacking` to verify Conjecture 5.6 and the P₄/G₅ ASH counterexamples in Lean 4 (`v4.33.1` + Mathlib, zero `sorry`, standard axioms only). Exact BFS confirms both ASH counterexamples from first principles, and Lemmas A–F plus explicit legal move simulations pass across 1,440 tree configurations up to n = 30 (supplemented by exhaustive checks on all 94 trees n ≤ 9 and 12,112 connected graphs n ≤ 8 during internal audit). The result is internally audited and Lean-verified, but externally unrefereed; priority is not asserted.
