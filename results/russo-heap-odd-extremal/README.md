# Extremal Heap-Type Permutation Generation for Every Odd $n \ge 3$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24570908.svg)](https://doi.org/10.5281/zenodo.24570908)

**Problem:** Open question in Section 10, item 2 (and Section 7 remark on odd $n$) of Luís M. S. Russo, *Heap-type permutation generation with a prescribed final arrangement*, [arXiv:2611.22780v1](https://arxiv.org/abs/2611.22780) (17 Nov 2026).

**Status:** **RESOLVED (YES, for every odd $n \ge 3$)** — completely proved with explicit closed-form parking orders at levels $n - 1$ and $n$, formally verified end-to-end in **Lean 4**, and independently audited.

## Statement (Verbatim, Section 10, Item 2)

> "We found no closed formula for the parking order at the top level and no variant for odd $n\ge7$ with the cyclic variant below it; whether other lower levels make the largest attainable arrangement reachable for odd $n$ is open."

## Summary of Result

For every odd $n \ge 3$, there exists a valid Heap-type swap schedule listing all $n!$ permutations of $\{1,\dots,n\}$ starting from $(1, 2, \dots, n)$, changing by a single transposition at each step, and terminating at $a^*_n$, the lexicographically largest odd permutation:
- $a^*_n = (n, n-1, \dots, 2, 1)$ when $n \equiv 3 \pmod 4$,
- $a^*_n = (n, n-1, \dots, 3, 1, 2)$ when $n \equiv 1 \pmod 4$.

For $n = 3$, the classic/cyclic schedule already terminates at $321$. For every odd $n \ge 5$ (with $h = (n - 3)/2$):
- **Levels $2, \dots, n - 2$:** Russo's cyclic schedule (net $(1\;n-2)$).
- **Level $n - 1$:** Zigzag parking order $(1,\, n-2,\, 2,\, n-3,\, \dots,\, h,\, h+2,\, h+1)$, whose net $Z'$ is an $(n - 1)$-cycle.
- **Level $n$:** Three-phase parking order $(n-1,\, n-2,\, \dots,\, h+2,\; h,\, h-2,\, \dots,\, r,\; h+1,\, h-1,\, \dots,\, 3-r)$ (where $r \in \{1, 2\}$, $r \equiv h + 2 \pmod 2$), which is the exact orbit of $n$ under the $n$-cycle $Z = (Z')^{-1} T$, giving final net $(Z')^n Z = T = (a^*_n)^{-1}$.

*(Note: Combined with Russo's $n \equiv 0 \pmod 4$ theorem and the independent $n \equiv 2 \pmod 4$ result, the lexicographic bound $a^*_n$ is attainable for every $n \ge 2$.)*

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical proof.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`PASS`).
- [verify.py](verify.py) — Standalone verification script (`python -O -W error verify.py`): theorem-free full recursion simulation for $n \in \{3, 5, 7, 9\}$ plus algebraic verification for all odd $5 \le n \le 1201$.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint.
- [RussoHeapOddExtremal.lean](../../lean/Conjectures/RussoHeapOddExtremal.lean) — End-to-end Lean 4 formalization (`russo_open_question_item2`).
