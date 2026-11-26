# Proof of R. J. Mathar's OEIS A401159 Conjectures (Binary Matrices with At Most Two 1's per Row and Column)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24559959.svg)](https://doi.org/10.5281/zenodo.24559959)

**Status:** Proved completely (both open conjectures plus the general $m \le k + 1$ theorem) — **Lean 4 verified** (zero `sorry`, zero custom axioms, zero `native_decide`).

## Target Conjectures

R. J. Mathar, [OEIS A401159](https://oeis.org/A401159) (approved November 18, 2026), *"Triangle $T(n,m)$ read by rows: the number of binary $n \times m$ matrices with at most two 1's in each row or column"*:

> **Conjecture 1:** $T(n, 2) = \mathrm{A086601}(n) = \mathrm{A000124}(n)^2$.
>
> **Conjecture 2:** $T(n, 3) = 1 + n + \dfrac{11}{4}n^2 + \dfrac{13}{8}n^3 + \dfrac{1}{8}n^4 + \dfrac{3}{8}n^5 + \dfrac{1}{8}n^6$.

## Main Result

Let $A(n, m, k)$ denote the number of $n \times m$ binary matrices with at most $k$ ones in every row and every column (so $T(n, m) = A(n, m, 2)$), and let $s(n, k) = \sum_{i=0}^{k} \binom{n}{i}$ denote the number of subsets of $[n]$ of cardinality at most $k$.

**Theorem.** For all integers $n \ge 0$ and $k \ge 0$:
1. For every $0 \le m \le k$,
   $$A(n, m, k) = s(n, k)^m.$$
2. For $m = k + 1$,
   $$A(n, k + 1, k) = \sum_{j=0}^{k} (-1)^j \binom{n}{j} s(n - j, k - j)^{k + 1}.$$

**Corollaries (OEIS A401159, $k = 2$).** Setting $f(n) = s(n, 2) = 1 + n + \binom{n}{2} = \frac{n^2 + n + 2}{2} = \mathrm{A000124}(n)$:
1. $T(n, 2) = f(n)^2 = \mathrm{A000124}(n)^2 = \mathrm{A086601}(n)$ for all $n \ge 0$.
2. $T(n, 3) = f(n)^3 - n^4 + \binom{n}{2} = 1 + n + \frac{11}{4}n^2 + \frac{13}{8}n^3 + \frac{1}{8}n^4 + \frac{3}{8}n^5 + \frac{1}{8}n^6$ for all $n \ge 0$.

## Proof Summary

Identify each $n \times m$ binary matrix with the $m$-tuple $(S_1, \dots, S_m)$ of its column supports $S_c \subseteq [n]$. The column-sum constraint is $|S_c| \le k$ for every $c$, and row $r$ has sum $|\{c : r \in S_c\}| \le m$.

- When $m \le k$, every row constraint holds automatically, so the $m$ column supports are chosen independently from the $s(n, k)$ subsets of $[n]$ of size at most $k$, giving $A(n, m, k) = s(n, k)^m$.
- When $m = k + 1$, row $r$ violates the row-sum constraint if and only if $r \in S_1 \cap \dots \cap S_{k+1}$. Hence admissible matrices correspond bijectively to $(k+1)$-tuples of subsets of $[n]$ of size $\le k$ having empty common intersection. For any $J \subseteq [n]$, the number of subsets $S \subseteq [n]$ with $J \subseteq S$ and $|S| \le k$ is $s(n - |J|, k - |J|)$ (and $0$ when $|J| > k$). Applying Möbius inversion (inclusion–exclusion) over the Boolean lattice $\mathcal{P}([n])$ yields
  $$A(n, k + 1, k) = \sum_{J \subseteq [n]} (-1)^{|J|} s(n - |J|, k - |J|)^{k+1} = \sum_{j=0}^{k} (-1)^j \binom{n}{j} s(n - j, k - j)^{k+1}.$$
Specializing to $k = 2$ and expanding $(n^2 + n + 2)^3 / 8 - n^4 + n(n - 1)/2$ yields both OEIS A401159 conjectures.

## Files

- [PROOF.md](PROOF.md) — complete self-contained proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/mathar-a401159/verify.py`).
- [MatharA401159.lean](../../lean/Conjectures/MatharA401159.lean) — complete Lean 4 formalization (`lake build Conjectures.MatharA401159`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
