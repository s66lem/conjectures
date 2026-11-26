# Complete Resolution of Phuc–Danchev Problem 4.10: Tripotent + Square-Zero Matrix Decompositions over $\mathbb{F}_2$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24567080.svg)](https://doi.org/10.5281/zenodo.24567080)

**Status:** Resolved (complete negative answer for all $d \ge 7$ with $3 \nmid d$; formally verified in Lean 4 + Mathlib, zero `sorry`, standard axioms only; independently audited — see [AUDIT.md](AUDIT.md))

## Source

- **Paper:** D. V. Phuc and P. V. Danchev, *A cubic obstruction to sums of tripotent and square-zero matrices*, [`arXiv:2611.24594v2`](https://arxiv.org/abs/2611.24594) [math.RA], 21 November 2026.
- **Location:** Section 4, Problem 4.10 (p. 11).
- **Problem (verbatim):**
  > **Problem 4.10.** Determine all integers $d \ge 7$ with $3 \nmid d$ for which $\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d$. In particular, determine which orders $d = 8n + 4$, with $n \ge 2$ and $n \not\equiv 1 \pmod 3$, satisfy this equality.

Here $\mathcal{T}_d = \{T + N \in \mathrm{M}_d(\mathbb{F}_2) : T^3 = T,\; N^2 = 0\}$.

## Main Result

**Theorem.** For every integer $d \ge 7$ with $3 \nmid d$, $\mathrm{M}_d(\mathbb{F}_2) \neq \mathcal{T}_d$. In particular, no order $d = 8n + 4$ ($n \ge 1$) satisfies $\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d$. Combined with Phuc and Danchev's results ($d \in \{1, 2, 4, 5\}$ and $3 \mid d$), we obtain the complete classification:
$$\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d \iff d \in \{1, 2, 4, 5\}.$$

The proof introduces two sharp structural obstructions over any field $F$ of characteristic $2$, with $p(x) = x^3 + x^2 + 1$:
1. **Lemma A (Rank inequality, sharp):** Whenever $A = T + N \in \mathrm{M}_d(F)$ with $T^3 = T$ and $N^2 = 0$,
   $$\dim \ker p(A) \le 3\,\mathrm{rank}\, p(A).$$
   This immediately eliminates all $d = 3m + 1$ ($m \ge 2$, via $C^{\oplus m} \oplus [0]$) and all $d = 3m + 2$ ($m \ge 3$, via $C^{\oplus m} \oplus 0_2$), where $C$ is the $3 \times 3$ companion matrix of $p(x)$.
2. **Lemma B (Equality-case rigidity):** If $A = A_1 \oplus B$ with $p(A_1) = 0$, $p(B)$ invertible, and $\dim \ker p(A) = 3\,\mathrm{rank}\, p(A)$, then $A = T + N$ forces $B^3 = B^2$. Taking $B = \begin{pmatrix} 0 & 1 \\ 1 & 1 \end{pmatrix}$ ($B^3 = I_2 \neq B^2$) eliminates the final remaining case $d = 8$ via $C \oplus C \oplus B$.

## Files

- [PROOF.md](PROOF.md) — Self-contained proof of Theorem 0, Lemma A, Lemma B, and the full classification.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone stdlib-only verification script (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Standalone preprint (Zenodo DOI [`10.5281/zenodo.24567080`](https://doi.org/10.5281/zenodo.24567080)).
- [`lean/Conjectures/PhucDanchevTripotent.lean`](../../lean/Conjectures/PhucDanchevTripotent.lean) — Lean 4 formalization of Theorem 0, Lemma A, Lemma B, `phuc_danchev_problem_4_10`, and `phuc_danchev_problem_4_10_8n_plus_4`.
