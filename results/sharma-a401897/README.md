# Proof of Karan Sharma's OEIS A401897 Conjecture (`a(n) ~ 48n / pi^2`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24571199.svg)](https://doi.org/10.5281/zenodo.24571199)

**Problem:** Conjecture in [OEIS A401897](https://oeis.org/A401897) (Karan Sharma, Nov 9, 2026).

**Status:** **PROVED** — explicit moving-viewpoint visibility bound, rank–norm tie bound, and convergence rate $a(n) = \frac{48n}{\pi^2}(1 + O(\log n / \sqrt{n}))$, formally verified end-to-end in **Lean 4** and independently audited.

## Statement (Verbatim)

> **Name:** "Number of Gaussian integers w with N(w) < N(z) that are visible from z, where z = a+b*i is the n-th nonzero Gaussian integer with 0 <= b <= a, ordered by norm and then by b."
> **Conjecture:** "Conjecture: a(n) ~ 48*n/Pi^2."

## Summary of Proof

1. **Shifted Gauss circle bound:** For every center $c \in \mathbb{R}^2$ and radius $r > 0$, $|\#(\mathbb{Z}^2 \cap D(c, r)) - \pi r^2| \le \pi(\sqrt{2}\,r + 1/2)$.
2. **Uniform moving-viewpoint visibility:** Substituting $v = z - w$ and applying Möbius inversion gives $a(z) = \sum_{1 \le d < 2\sqrt{N}} \mu(d)\, L(z, d)$ and
   $$\left|a(z) - \frac{6 N(z)}{\pi}\right| \le \pi\sqrt{N(z)}\bigl(2 + \sqrt{2} + \sqrt{2}\ln(2\sqrt{N(z)})\bigr),$$
   uniformly in the direction of $z$.
3. **Rank–norm relation (with norm ties):** By 8-fold dihedral symmetry of the fundamental wedge $\{0 \le b \le a\}$, $|n - \pi N(z_n)/8| \le 2\sqrt{N(z_n)}$.
4. **Asymptotic:** Combining (2) and (3) yields $a(n) / (48n/\pi^2) = 1 + O(\log n / \sqrt{n}) \to 1$.

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical proof.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`PASS`).
- [verify.py](verify.py) — Standalone stdlib-only verifier (`python -O -W error verify.py`, verifies all 58 OEIS terms, Möbius identity, shifted Gauss bounds, and Propositions A & B up to $n = 15{,}874$).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint.
- [SharmaA401897.lean](../../lean/Conjectures/SharmaA401897.lean) — Complete Lean 4 formalization (`shifted_gauss_circle_open`, `shifted_gauss_circle_closed`, `uniform_visibility_bound`, `rank_norm_bound`, `sharma_a401897_asymptotic`).
