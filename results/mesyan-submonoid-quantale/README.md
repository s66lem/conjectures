# Resolution of Mesyan's Question 34 (Submonoid Quantales of Domains)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24566360.svg)](https://doi.org/10.5281/zenodo.24566360)

- **Source:** Z. Mesyan, *Quantales Arising From Rings*, [arXiv:2611.31109v1](https://arxiv.org/abs/2611.31109) (math.RA, 23 Nov 2026), Section 9, Question 34.
- **Preprint:** [10.5281/zenodo.24566360](https://doi.org/10.5281/zenodo.24566360)
- **Status:** First part completely resolved (splits between rings and semirings) — formally verified in Lean 4 + Mathlib (zero `sorry`, standard axioms only) and independently audited (`PASS`).
- **Lean 4 formalization:** [MesyanSubmonoidQuantale.lean](../../lean/Conjectures/MesyanSubmonoidQuantale.lean)

## Question (verbatim)

> **Question 34.** *For a domain $R$, is $R$ being commutative equivalent to $\mathcal{M}(R)$ being commutative? (See Proposition 22 (3) and subsequent comments.) More broadly, for which (semi)rings $R$ is $\mathcal{M}(R)$ commutative?*

Here a semiring has $(R, +)$ a commutative monoid, $(R, \cdot)$ a semigroup, two-sided distributivity, and $0r = r0 = 0$ (no multiplicative identity is assumed). A domain is a nonzero semiring with $rp \ne 0$ for all $r, p \ne 0$ (Remark 14). The quantale $\mathcal{M}(R)$ consists of all additive submonoids of $R$ with multiplication $S \cdot T = \{\sum_{i=1}^k s_i t_i \mid s_i \in S,\; t_i \in T\}$ (Definition 4).

## Main Results

1. **Reduction `(R)` (`submonoidMul_comm_iff`):** For any semiring $R$, $\mathcal{M}(R)$ is commutative if and only if $\langle rs \rangle = \langle sr \rangle$ for all $r, s \in R$.
2. **Theorem A (`mesyan_Q34_rings`, YES for ring domains):** For every (possibly nonunital) ring $R$ with no zero divisors, $\mathcal{M}(R)$ is commutative if and only if $R$ is commutative. This closes all prime-characteristic cases $p \ge 3$ left open by Proposition 22(3).
3. **Theorem B (`mesyan_Q34_semirings_counterexample`, NO for semiring domains):** There exists a 14-element noncommutative semiring domain $R_{14} = \{0, \infty\} \cup (\mathbb{Z}_3 \times \mathbb{Z}_2^2)$, twisted by the asymmetric bicharacter $\beta(g, h) = (-1)^{g_1 h_2} \in \mathbb{Z}_3^\times$, whose submonoid quantale $\mathcal{M}(R_{14})$ (90 submonoids) is commutative.

## Files

- [PROOF.md](PROOF.md) — complete self-contained proof of Reduction (R), Theorem A, and Theorem B.
- [AUDIT.md](AUDIT.md) — independent `claude-sonnet-5-5` adversarial audit report (`PASS`).
- [verify.py](verify.py) — standalone stdlib-only computational verification (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — publication-ready LaTeX note.
- [MesyanSubmonoidQuantale.lean](../../lean/Conjectures/MesyanSubmonoidQuantale.lean) — Lean 4 formalization of Reduction (R), Theorem A, and Theorem B.
