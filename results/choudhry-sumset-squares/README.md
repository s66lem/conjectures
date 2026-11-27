# Explicit (5, 4) and (6, 4) Integer Sumsets of Perfect Squares (Choudhry, INTEGERS 26, 2026, #A66)

**Status:** Complete, Lean 4 verified (`lean/Conjectures/ChoudhrySumsetSquares.lean`, standard axioms only), independently audited (`AUDIT.md`), and published on Zenodo: [10.5281/zenodo.24581044](https://doi.org/10.5281/zenodo.24581044).

*Scope note:* The Lean 4 formalization unconditionally proves the minimal $(5, 4)$ solution (standard primitive form and all-positive disjoint form), all five pairwise distinct primitive $(5, 4)$ solutions (`gcd = 1`), the primitive $(6, 4)$ solution (standard and positive disjoint forms), Choudhry's scaling-shift Lemma 1, and infinitely many distinct all-positive disjoint $(5, 4)$ and $(6, 4)$ solutions over $\mathbb{Z}$. The exhaustiveness counts (`max X ≤ 10000` and `max X ≤ 40000`) come from the divisor-pair search described in `PROOF.md`.

## Problem

In *Two Sets of Integers Such That All Elements of the Sumset of the Two Sets Are Perfect Squares*, *INTEGERS* **26** (2026), #A66 (`arXiv:2508.07806`, Section 6, continuing Guy's *Unsolved Problems in Number Theory*, Problem D14), A. Choudhry asks:

> It would be interesting to find a quintuple $\{a_1, a_2, \dots, a_5\}$ and a quadruple $\{b_1, b_2, \dots, b_4\}$ such that all $20$ sums $a_i + b_j$, $i = 1, \dots, 5$, $j = 1, \dots, 4$, are squares.

Before Choudhry's paper, for $m, n > 2$ only Lagrange's $(4, 4)$ family had been published.

## Results

1. **Explicit minimal $(5, 4)$ solution (resolving Choudhry's Section 6 open problem):**
   - Standard form ($b_1 = 0$, primitive with $\gcd = 1$):
     $$A = \{216^2, 567^2, 1128^2, 1848^2, 5496^2\} = \{46656, 321489, 1272384, 3415104, 30206016\},$$
     $$B = \{0, 1198800, 2695680, 22269520\}.$$
   - All-positive, pairwise disjoint form ($A' = A - 1$, $B' = B + 1$):
     $$A' = \{46655, 321488, 1272383, 3415103, 30206015\}, \qquad B' = \{1, 1198801, 2695681, 22269521\}.$$
2. **Five distinct primitive $(5, 4)$ solutions** (complete list in standard form with $\max X \le 10000$; 86 distinct $(5, 4)$ $X$-sets exist up to $\max X \le 40000$).
3. **Explicit $(6, 4)$ solution** (all $24$ sums are perfect squares, strictly exceeding Choudhry's $(5, 4)$ question; unique with $\max X \le 40000$):
   $$A_6 = \{2988^2, 4356^2, 5787^2, 11164^2, 17046^2, 23948^2\}, \qquad B_6 = \{0, 16594560, 137675520, 1202947200\},$$
   together with its all-positive disjoint shifted form $(A_6 - 1, B_6 + 1)$.
4. **Infinitely many distinct all-positive disjoint $(5, 4)$ and $(6, 4)$ solutions** over $\mathbb{Z}$ via scaling and translation $(k^2 A - t, k^2 B + t)$.

## Verification

- **Lean 4:** `lean/Conjectures/ChoudhrySumsetSquares.lean` (zero `sorry`, zero custom axioms, zero forbidden tokens).
- **Standalone Python verifier:** `python -O -W error results/choudhry-sumset-squares/verify.py` (stdlib only).
- **Full writeup:** `PROOF.md`, `paper.tex`, `paper.pdf`.
