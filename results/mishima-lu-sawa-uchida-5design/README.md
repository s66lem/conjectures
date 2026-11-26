# Complete Resolution of Mishima–Lu–Sawa–Uchida Problem 8.3: Odd-Size Antipodal Rational 5-Designs for the Chebyshev Measure

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24570643.svg)](https://doi.org/10.5281/zenodo.24570643)

**Problem:** Problem 8.3 (and the odd-size spectrum) of T. Mishima, X.-N. Lu, M. Sawa, and Y. Uchida, *Geometric designs and Hilbert–Kamke equations of degree five for classical orthogonal polynomials*, [arXiv:2503.21151v4](https://arxiv.org/abs/2503.21151) (2 Apr 2026); *Research in Number Theory* **12** (2026), Paper No. 39, Section 8.

**Status:** **RESOLVED** — explicit 37-point antipodal rational 5-design over denominator 240, plus complete odd-size spectrum ($n = 2N + 1$ exists $\iff n \ge 35$), formally verified end-to-end in **Lean 4** and independently audited.

## Statement (Verbatim, Section 8)

> **Problem 8.3.** Find an antipodal $5$-design with $37$ rational points, as the smallest open case.

## Summary of Result

1. **Explicit 37-point design (Problem 8.3):**
   $$X_{37} = \{0\} \cup \left\{\pm \frac{a}{240} : a \in \{15, 57, 61, 69, 93, 129, 141, 147, 151, 183, 199, 209, 211, 215, 234, 235, 238, 239\}\right\}$$
   satisfies $\frac{1}{37}\sum_{x \in X_{37}} x^k = \int_{-1}^{1} t^k \frac{dt}{\pi\sqrt{1-t^2}}$ for all $0 \le k \le 5$.
2. **Complete odd-size spectrum:** An antipodal rational $5$-design for the Chebyshev measure with an odd number of points $n = 2N + 1$ exists **if and only if $n \ge 35$ ($N \ge 17$)**.
   - **Existence ($N \ge 17$):** Explicit base designs for $N = 17$ (denominator $1092$), $N = 18$ ($240$), and $N = 19$ ($420$), extended inductively by disjoint 6-point rational blocks $Y_t = \{\pm a(t), \pm b(t), \pm c(t)\}$ whose positive points lie in three pairwise disjoint intervals and are strictly monotone for $t \ge 20$.
   - **Non-existence ($N \le 16$):** Self-contained 2-adic valuation proof (reproving Theorem 8.1 of `arXiv:2503.21151v4`).

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical proof.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`PASS`).
- [verify.py](verify.py) — Standalone stdlib-only exact rational verifier (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint.
- [MishimaLuSawaUchida5Design.lean](../../lean/Conjectures/MishimaLuSawaUchida5Design.lean) — End-to-end Lean 4 formalization (`mishima_problem_8_3_37_design`, `mishima_odd_5design_iff`).
