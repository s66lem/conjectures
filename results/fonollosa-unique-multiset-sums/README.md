# Resolution of Fonollosa's Problem 4 (Unique Multiset Sums in Finite Abelian Groups)

Complete proof and equality classification resolving **Problem 4** of José A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem* ([arXiv:2607.08366v2](https://arxiv.org/abs/2607.08366), §8) and Remark 1 of its companion paper ([arXiv:2607.09949v2](https://arxiv.org/abs/2607.09949)).

## Main Results

1. **Exact minimum order (`order_lower_bound`, `valid_at_lower_bound`):** Every finite abelian group $G$ admitting a size-$n$ family ($n \ge 1$) with unique multiset sums satisfies $|G| \ge 2^{n-1}$, improving the Nisan–Wigderson bound $\binom{2n}{n}/2^n \sim 2^n/\sqrt{\pi n}$ to the exact optimum for all $n \ge 1$.
2. **Uniqueness of Glynn's scheme (`equality_classification`):** Equality $|G| = 2^{n-1}$ holds if and only if $G \cong (\mathbb{Z}/2\mathbb{Z})^{n-1}$ is an elementary abelian $2$-group and the family is an affine basis of $G$.
3. **Sharpened cyclic bound (`cyclic_modulus_lower_bound`):** Disjointness of nonzero doubles from subset sums yields $N \ge 2^{n-1} + \lceil n / \gcd(2, N) \rceil - 1$ for cyclic groups $\mathbb{Z}/N\mathbb{Z}$ ($N \ge 1$).
4. **Lean 4 formal verification:** All theorems are formally verified in [`lean/Conjectures/FonollosaUniqueMultisetSums.lean`](../../lean/Conjectures/FonollosaUniqueMultisetSums.lean) with zero `sorry`, zero `native_decide`, and standard axioms `[propext, Classical.choice, Quot.sound]` only.

## Files

- [`PROOF.md`](PROOF.md) — Complete elementary proof, equality classification, cyclic bound, and Waring-rank comparison.
- [`AUDIT.md`](AUDIT.md) — Independent audit and Lean 4 axiom log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks across 19,523 finite abelian instances + construction for $n = 1\dots 8$).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/FonollosaUniqueMultisetSums.lean`](../../lean/Conjectures/FonollosaUniqueMultisetSums.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/fonollosa-unique-multiset-sums/verify.py
cd lean && lake build Conjectures.FonollosaUniqueMultisetSums
```
