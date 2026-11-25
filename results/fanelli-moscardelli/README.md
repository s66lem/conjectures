# Fanelli–Moscardelli stability threshold conjecture

Complete proposed disproof of the asymptotic tightness conjecture from [Fanelli–Moscardelli (ECAI 2025, Section 5)](https://doi.org/10.3233/FAIA251234) and [google-deepmind/formal-conjectures issue #7848](https://github.com/google-deepmind/formal-conjectures/issues/7848) (`FormalConjectures/Paper/ApproximatelyStableMatching.lean`). For every integer m ≥ 3 and odd market size N = 2m + 1, every complete strict roommates preference profile admits an m-stable matching, giving K(2m + 1) ≤ m < ⌈(2m + 1)/2⌉ and refuting `stability_threshold_tight` unconditionally. The bound m ≥ 3 is sharp (K(5) = 3).

- [Complete proof](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/FanelliMoscardelli.lean) (`FanelliMoscardelli.stabilityThreshold_odd_le`, `FanelliMoscardelli.not_stability_threshold_tight`, against verbatim [Roommates.lean](../../lean/Conjectures/Roommates.lean))
- [Preprint PDF](paper.pdf) · [LaTeX source](paper.tex) · [Zenodo preprint (DOI: 10.5281/zenodo.24519727)](https://doi.org/10.5281/zenodo.24519727)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.FanelliMoscardelli` to verify the full disproof in Lean 4 (`v4.33.1` + Mathlib, zero `sorry`, standard axioms only). The constructive algorithm of §§1–7 passed full O(N²) m-blocking checks on 1,800 random and adversarial all-K₂ profiles for N ∈ {7, 9, 11, 13, 15, 21} (and 45,000+ adversarial profiles during independent audit), consistent with DRAT-checked SAT exact values K(7) = 3, K(8) = 3, K(9) = 4, and K(11) = 5. The result is internally audited and Lean-verified, but externally unrefereed; priority is not asserted.
