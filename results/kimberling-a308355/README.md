# OEIS A308355 and A025065 Conjectures (Kimberling, 2019)

**Status:** Complete resolution (A308355 conjecture **disproved** for every odd $n \ge 1$; A025065 conjecture **proved** for every $n \ge 1$) · **Lean 4 verified** (zero `sorry`, zero custom axioms) · **Cross-model audited** · **Preprint:** [10.5281/zenodo.24552281](https://doi.org/10.5281/zenodo.24552281)

## Problem Statement

Let integer partitions of $n$ be written as weakly decreasing tuples of positive integers and ordered in descending lexicographic order ([OEIS A080577](https://oeis.org/A080577)). Row $n \ge 1$ of [OEIS A128628](https://oeis.org/A128628) records the number of parts of each partition of $n$ in this order, and [OEIS A308355](https://oeis.org/A308355) is the limiting row sequence of A128628 as $n \to \infty$. Let [OEIS A025065](https://oeis.org/A025065)$(n)$ count the palindromic partitions of $n$ (partitions whose parts can be permuted into a palindrome).

Two related conjectures by Clark Kimberling (May 2019) appear on the OEIS:

1. **OEIS A308355 Conjecture:** *"The length of maximal initial segment of this sequence that is identical to row $n$ of A128628 is $\mathrm{A025065}(n+1)$, for $n \ge 1$."*
2. **OEIS A025065 Conjecture:** *"a(n) is the length of maximal initial segment of A308355(n-1) that is identical to row n of A128628, for n >= 2."* (Here `"A308355(n-1)"` is a literal typo in Kimberling's comment referring to the sequence A308355 itself; this May 24, 2019 cross-reference already records the corrected value $\mathrm{A025065}(n)$ in place of the off-by-one $\mathrm{A025065}(n+1)$ on A308355.)

## Resolution Summary

We prove that for every $n \ge 1$:
- The row limit A308355 exists and equals the infinite concatenation of unrestricted blocks $B(0), B(1), B(2), \dots$, where $B(r)$ lists $1 + \mathrm{len}(\lambda)$ over all partitions $\lambda$ of $r$ in descending lexicographic order (`a308355_is_row_limit`).
- The exact length of the maximal common prefix of row $n$ of A128628 and A308355 is
  $$S(n) = \sum_{r=0}^{\lfloor n/2 \rfloor} p(r) = \mathrm{A025065}(n),$$
  settling the OEIS A025065 conjecture for every $n \ge 1$ (`exact_agreement_eq_A025065`, `A025065_eq_sum_partitions`).
- Consequently, $\mathrm{A025065}(n) = \mathrm{A025065}(n+1)$ holds if and only if $n$ is even (`a308355_conjecture_iff_even`). The displayed conjecture on OEIS A308355 **fails for every odd $n \ge 1$** (by $p((n+1)/2) > 0$), starting at $n = 1$ (actual $1$ vs. predicted $2$), $n = 3$ (actual $2$ vs. predicted $4$), and $n = 5$ (row 5 is $(1, 2, 2, 3, 3, 4, 5)$, A308355 begins $(1, 2, 2, 3, 2, 3, 4)$, so actual agreement is $4$ while $\mathrm{A025065}(6) = 7$; `counterexample_n5`).

## Files

- [`PROOF.md`](./PROOF.md) — Complete human-readable proof.
- [`paper.tex`](./paper.tex) / [`paper.pdf`](./paper.pdf) — Publication-ready LaTeX paper.
- [`verify.py`](./verify.py) — Standalone Python stdlib verifier (`python -O -W error verify.py`).
- [`AUDIT.md`](./AUDIT.md) — Independent cross-model adversarial audit report.
- [`../../lean/Conjectures/KimberlingA308355.lean`](../../lean/Conjectures/KimberlingA308355.lean) — Complete Lean 4 formalization (`exact_agreement_eq_A025065`, `a308355_conjecture_iff_even`).
