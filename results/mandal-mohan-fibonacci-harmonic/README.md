# Mandal–Mohan Conjecture 1.19 (Harmonic-Type Means of Powers of Fibonacci Numbers)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24549268.svg)](https://doi.org/10.5281/zenodo.24549268)

- **Status:** **PROVED** (full classification for all $n \ge 1, k \ge 1$; settles Conjecture 1.19 for all $k \ge 3$ and reproves Theorem 1.18 for $k = 1, 2$)
- **Source:** Sagar Mandal and Mohan, *Integral Means of Fibonacci Numbers: Divisibility, Density, and Arithmetic Structure* ([arXiv:2611.32519v1](https://arxiv.org/abs/2611.32519), 24 November 2026), Conjecture 1.19
- **Lean 4 formalization:** [MandalMohanFibonacciHarmonic.lean](../../lean/Conjectures/MandalMohanFibonacciHarmonic.lean) (0 `sorry`, 0 custom axioms, 0 `native_decide`)
- **Paper:** [paper.pdf](paper.pdf) ([paper.tex](paper.tex))

## Result

For all positive integers $n \ge 1$ and $k \ge 1$,
$$H(n, k) := \frac{n^k}{\displaystyle\sum_{i=1}^n \frac{1}{F_i^k}} \in \mathbb{N} \iff n \in \{1, 2\} \text{ or } (n, k) = (3, 2).$$
In particular, for every $k \ge 3$, $H(n, k) \in \mathbb{N}$ if and only if $n \in \{1, 2\}$, proving Conjecture 1.19 of Mandal and Mohan.

## Proof Overview

For any index $q \in \{3, \dots, n\}$ such that $\gcd(F_q, F_i) = 1$ for all $1 \le i \le n$ with $i \ne q$ and $F_q \ge n$, clearing denominators in $m \sum_{i=1}^n F_i^{-k} = n^k$ yields $m(P + F_q^k Q) = n^k F_q^k P$ with $\gcd(P + F_q^k Q, F_q^k) = 1$, forcing $P + F_q^k Q \le n^k P$; yet $F_1 = F_2 = 1$ implies $Q \ge 2P$ and hence $P + F_q^k Q > 2 F_q^k P \ge 2 n^k P$, a contradiction.

- For $n \ge 12$, Bertrand's postulate supplies a prime $q \in (\lfloor n/2 \rfloor, n]$ with $q \ge 7$, which satisfies both $\gcd(F_q, F_i) = 1$ (by strong divisibility $\gcd(F_q, F_i) = F_{\gcd(q,i)}$) and $F_q \ge 2q - 1 \ge n$.
- For $7 \le n \le 11$ and $n = 5$, $q = 7$ and $q = 5$ respectively satisfy the same criterion.
- For $n = 4$ and $n = 6$, the cleared numerator is coprime to $4^k \cdot 6^k$ and $6^k \cdot 120^k$ respectively.
- For $n = 3$, integrality reduces to $2^{k+1} + 1 = 3^j$, whose only solution with $k \ge 1$ is $k = 2$ (via $3^{2t} - 1 = (3^t - 1)(3^t + 1) = 2^{k+1}$).

## Files

- [PROOF.md](PROOF.md) — Complete mathematical proof
- [AUDIT.md](AUDIT.md) — Independent cross-model audit report
- [verify.py](verify.py) — Standalone stdlib-only verifier (`python -O -W error verify.py`)
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Standalone LaTeX preprint
- [../../lean/Conjectures/MandalMohanFibonacciHarmonic.lean](../../lean/Conjectures/MandalMohanFibonacciHarmonic.lean) — Lean 4 formalization
