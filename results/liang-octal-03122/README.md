# Complete Resolution of Liang's Conjecture 4.1 (`arXiv:2611.29198v1`, Misère Octal Game `0.3122`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24568033.svg)](https://doi.org/10.5281/zenodo.24568033)

- **Source:** Kai Liang, *Quaternary games with infinite misère quotients*, [arXiv:2611.29198v1](https://arxiv.org/abs/2611.29198) (math.CO, 22 Nov 2026), Section 4.1, Conjecture 4.1.
- **Status:** Completely resolved — **false as literally stated** (fails for $\min(x, y) \le 2$), **true for all $x, y \ge 3$** with an explicit 98-entry closed form and finite translation certificate (threshold $3$ is sharp).

## Conjecture (verbatim)

> **Conjecture 4.1.** *In $0.3122$, the slice $o(2, 2, x, y)$ depends only on $(x \bmod 7,\; y \bmod 7,\; [|x - y| \le 4])$, a table of $7 \times 7 \times 2 = 98$ values. That is, the outcome is periodic in regions, with a different template near the diagonal; this difference breaks the eventual periodicity, and the diagonal and super-diagonal part is exactly the two identities of Theorem 3.7.*

In the octal game $0.3122$, from a heap of size $h$, a player may remove the entire heap when $h \in \{1, 2\}$, or replace $h$ by $h - k$ for $k \in \{1, 3, 4\}$ when $h > k$; heaps never split. Under misère play, the empty position is an $\mathcal{N}$-position, and a nonempty position is $\mathcal{P}$ if and only if none of its options is $\mathcal{P}$.

## Main Results

1. **Literal Disproof:** Without a lower bound on $x, y$, Conjecture 4.1 is **false**:
   $$o(2, 2, 7, 2) = \mathcal{N}, \qquad o(2, 2, 14, 2) = \mathcal{P},$$
   even though $(7, 2)$ and $(14, 2)$ share the key $(0, 2, \text{False})$ (both have $|x - y| > 4$).
2. **Proof for All $x, y \ge 3$ (Sharp Threshold):** For all integers $x, y \ge 3$, $o(2, 2, x, y)$ depends only on $(x \bmod 7,\; y \bmod 7,\; [|x - y| \le 4])$, all $98$ keys occur, and $o(2, 2, x, y) = \mathcal{P}$ if and only if $(x \bmod 7,\; y \bmod 7)$ belongs to
   $$B := \{(1,1),(2,2),(3,3),(5,5),(6,6),(1,6),(6,1),(2,4),(4,2),(3,5),(5,3)\},$$
   together with $\{(0, 0), (4, 4)\}$ when $|x - y| \le 4$, or $\{(0, 4), (4, 0)\}$ when $|x - y| > 4$.

## Proof Method

Consider the move-closed family $\mathcal{F}$ of positions with at most $4$ positive heaps, at most $2$ exceeding $2$, written canonically as $(h_1, h_2, h_3, h_4)$ with $h_1 \ge h_2 \ge h_3 \ge h_4 \ge 0$ and $h_3, h_4 \le 2$. With thresholds $D = 13$, $G = 5$, $C = 8$, define $\Phi$ by reducing $(h_1, h_2)$ via $\rho_1 : (h_1, h_2) \mapsto (h_1 - 7, h_2 - 7)$ while $h_2 \ge 20$, then $\rho_2 : (h_1, h_2) \mapsto (h_1 - 7, h_2)$ while $h_1 - h_2 \ge 12$ and $h_1 \ge 15$, and reading the exact misère outcome from a finite table ($h_1 \le 44$, $5{,}853$ positions). A two-part translation lemma shows that outside a finite window $W$ of $2{,}191$ positions, the misère recursion for $\Phi$ is invariant under shifting by $(7, 7)$ or $(7, 0)$; verifying $\Phi$ on $W$ establishes $\Phi = o$ on all of $\mathcal{F}$ by induction on $h_1 + h_2 + h_3 + h_4$. Because $\rho_1$ and $\rho_2$ preserve $(x \bmod 7, y \bmod 7, [|x - y| \le 4])$ for $x, y \ge 3$, the entire slice reduces to $204$ canonical pairs.

## Files

- [PROOF.md](PROOF.md) — complete self-contained proof.
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — standalone stdlib-only certificate checker (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — publication-ready LaTeX note (Zenodo DOI [`10.5281/zenodo.24568033`](https://doi.org/10.5281/zenodo.24568033)).
- [LiangOctal03122.lean](../../lean/Conjectures/LiangOctal03122.lean) — Lean 4 formalization (`phi_iff_isMisereP`, `liang_conjecture_4_1_literal_disproof`, `liang_conjecture_4_1_ge_3`, zero `sorry`, standard axioms only).
