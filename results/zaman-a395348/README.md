# Proof of Rahid Zaman's OEIS A395348 Conjecture

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24560206.svg)](https://doi.org/10.5281/zenodo.24560206)

## Result

We prove Rahid Zaman's conjecture on [OEIS A395348](https://oeis.org/A395348) (Nov 18, 2026) for the two-color greedy spiral queen game (and determine the exact closed-form coordinates of both Black's sequence A395348 and Red's companion sequence [OEIS A395349](https://oeis.org/A395349) for every round):

> **Theorem.** *Let $a(n)$ (OEIS A395348) be the spiral label of the $n$-th Black queen and $b(n)$ (OEIS A395349) be the spiral label of the $n$-th Red queen on the standard square spiral starting at $0 = (0, 0)$. For every $h \ge 0$ and $j \in \{0, 1, 2, 3\}$, setting $n = 4h + 4 + j$, the placements are given by*
>
> | $j$ | Ring $r$ | Black $(x, y)$ | Red $(x, y)$ | Black label $a(n)$ |
> | :-: | :-: | :-: | :-: | :-: |
> | $0$ | $2h + 3$ | $(-r, 1)$ | $(2, -r)$ | $4r^2 + r - 1$ |
> | $1$ | $2h + 4$ | $(r, 0)$ | $(-1, r)$ | $4r^2 - 3r$ |
> | $2$ | $2h + 4$ | $(-r, 0)$ | $(-1, -r)$ | $4r^2 + r$ |
> | $3$ | $2h + 5$ | $(r, 1)$ | $(2, r)$ | $4r^2 - 3r + 1$ |
>
> *Consequently, for every integer $n \ge 2$,*
> $$a(n + 4) = a(n) + 8n + 34.$$

## Proof Overview

The proof uses an exact structural invariant rather than a large computational cutoff:

1. **Exact Parity Separation:** Every Black queen has $x + y \equiv x - y \equiv 0 \pmod{2}$ (and $y \in \{0, 1\}$), while every Red queen has $x + y \equiv x - y \equiv 1 \pmod{2}$ (and $x \in \{-1, 2\}$). Hence no Black queen ever shares a diagonal with any Red queen, making legality of every predicted target immediate.
2. **Exact Line-Set Invariants:** After the base check of rounds $0 \le n \le 7$ (ring $r \le 5$, label $\le 93$), at the start of every block $h \ge 1$ the occupied $x$-, $y$-, $(x+y)$-, and $(x-y)$-line sets of both players are exact contiguous integer (or fixed-parity) intervals.
3. **Eight-Case Induction:** Across each of the eight turns of block $h \ge 1$, every intermediate spiral cell between a player's previous queen and next target is attacked along a horizontal or vertical line except for at most two isolated cells per turn, each of which is explicitly attacked along a diagonal by an already-placed opposing queen.

## Files

- [`PROOF.md`](PROOF.md): Complete self-contained proof.
- [`verify.py`](verify.py): Standalone Python verifier (`python -O -W error verify.py`, stdlib-only) checking the greedy spiral simulation through 408 rounds (816 placements), exact line invariants, and the recurrence.
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf): Publication-ready LaTeX preprint.
- [`../../lean/Conjectures/ZamanA395348.lean`](../../lean/Conjectures/ZamanA395348.lean): Complete Lean 4 formalization of the greedy spiral queen game, exact closed-form coordinates for both colors, and Zaman's recurrence $a(n + 4) = a(n) + 8n + 34$ for all $n \ge 2$ (standard axioms only).
- [`AUDIT.md`](AUDIT.md): Independent cross-model adversarial audit report.

## Verification

```bash
python -O -W error results/zaman-a395348/verify.py
cd lean && lake build Conjectures.ZamanA395348
```
