# Proof of Conjecture 3 (Wormald's Question) of Ghafari & Wanless (`arXiv:2607.17547v1`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24548884.svg)](https://doi.org/10.5281/zenodo.24548884)

Complete proof and Lean 4 formalization of **Conjecture 3** from Afsane Ghafari and Ian M. Wanless, *Latin Squares whose transversals intersect in unusual ways* ([arXiv:2607.17547v1](https://arxiv.org/abs/2607.17547), July 2026), attributed to a question of Nick Wormald.

## Main Results

1. **Complete classification for even orders $n \ge 22, n \ne 24$ (`ghafari_wanless_all_even_ge_22_ne_24`):** For every even integer $n \ge 22$ with $n \ne 24$, there exists a Latin square of order $n$ having no two disjoint transversals and no pinned entry. (The orders $n = 22, 26$ extend existence below Conjecture 3's threshold $n \ge 28$; $n = 24$ falls outside Conjecture 3 and is excluded by our non-wrapping gadget condition $s_h + 14 < n_0$.)
2. **Complete proof of Conjecture 3 (`ghafari_wanless_conjecture3`):** Every even integer $n \ge 28$ admits a Latin square with no two disjoint transversals and no pinned entry — settling both $n = 30$ and all even $n > 10\,000$ left open in `arXiv:2607.17547v1`.
3. **Granularity-1 modular gluing construction:** Uses an explicit modular Latin square $L_{n, n_0}$ (proving no two disjoint transversals via the $\Delta$-sum lemma and three unique row-maximum cells), four unwrapped base squares ($n_0 \in \{22, 26, 30, 32\}$), eight parametric $p$-invariant mod-16 tail families producing two completely disjoint tails for every $n$ above threshold ($102$–$126$), and 42 explicit small witnesses ($22 \le n \le 110, n \ne 24$).
4. **Lean 4 formal verification:** The entire proof is formally verified in [`lean/Conjectures/GhafariWanlessLatinTransversals.lean`](../../lean/Conjectures/GhafariWanlessLatinTransversals.lean) (and supporting modules `GhafariWanlessData`, `GhafariWanlessCore`, `GhafariWanlessTailBase`, `GhafariWanlessEvenTail`, `GhafariWanlessOddTail`) using only `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`).

## Files

- [`PROOF.md`](PROOF.md) — Complete self-contained mathematical proof.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 axiom log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks; verifies all 4 base squares, algebraic $p$-invariance and end-to-end squares for all 8 mod-16 infinite families, and all 42 small even orders).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/GhafariWanlessLatinTransversals.lean`](../../lean/Conjectures/GhafariWanlessLatinTransversals.lean) — Main Lean 4 formalization.

## Reproduction

```bash
python3 -O results/ghafari-wanless-latin-transversals/verify.py
cd lean && lake build Conjectures.GhafariWanlessLatinTransversals
```
