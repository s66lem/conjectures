# Proof of Takuto Nakai's OEIS A400474 Conjecture (Triangle Interior Integer-Angle Maximum)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24559747.svg)](https://doi.org/10.5281/zenodo.24559747)

**Status:** Proved completely for every $n \ge 3$ — **Lean 4 verified** (real-angle floor reduction and combinatorial maximization; zero `sorry`, zero custom axioms, zero `native_decide`).

## Target Conjecture

Takuto Nakai, [OEIS A400474](https://oeis.org/A400474) (submitted October 25, 2026; offset 3):

> **Conjecture:** $a(n) = (n^2 - 4n + c)/3$, where $c = 6, -3, 4, 3, 0, -5$ according as $n \equiv 0, 1, 2, 3, 4, 5 \pmod 6$. Verified for $n \le 1000$.

Here $a(n)$ is the maximum, over all nondegenerate Euclidean triangles $\triangle ABC$, of the number of strictly interior points $P$ such that $\angle BPC$, $\angle CPA$, and $\angle APB$ are pairwise distinct integer multiples of $\pi / n$.

## Main Result

**Theorem.** For every integer $n \ge 3$,
$$a(n) = \frac{n^2 - 4n + c(n \bmod 6)}{3}, \qquad c(0, 1, 2, 3, 4, 5) = (6, -3, 4, 3, 0, -5).$$

## Proof Summary

1. **Geometric bijection:** For any nondegenerate triangle $\triangle ABC$ with interior angles $A, B, C > 0$ ($A + B + C = \pi$), strictly interior points $P$ correspond bijectively via $P \mapsto (\angle BPC, \angle CPA, \angle APB)$ to angle triples $(x, y, z)$ with $x + y + z = 2\pi$ and $A < x < \pi$, $B < y < \pi$, $C < z < \pi$ (existence by continuity along the constant-$\angle APB$ arc; uniqueness because two distinct circles through $B$ intersect in at most one other point, and no strictly interior point lies on the circumcircle).
2. **Reduction to integer floor triples:** Setting $p = \lfloor nA/\pi \rfloor$, $q = \lfloor nB/\pi \rfloor$, $r = \lfloor nC/\pi \rfloor$ and substituting $(u, v, w) = (n - X, n - Y, n - Z)$ turns the count into ordered triples of pairwise distinct positive integers summing to $n$ with $u < n - p$, $v < n - q$, $w < n - r$. Since $p + q + r \ge n - 2$, shrinking floors can only increase the count, and every $(p, q, r) \in \mathbb{N}^3$ with $p + q + r = n - 2$ is realized by angles $(p + 2/3)\pi/n, (q + 2/3)\pi/n, (r + 2/3)\pi/n$.
3. **Disjoint exclusions and convexity:** The three forbidden events $u \ge n - p$, $v \ge n - q$, $w \ge n - r$ are pairwise disjoint, giving count $T(n) - E_n(p) - E_n(q) - E_n(r)$ where
   $$T(n) = \frac{(n - 1)(n - 2)}{2} - 3\left\lfloor \frac{n - 1}{2} \right\rfloor + 2[3 \mid n], \qquad E_n(p) = \sum_{s=1}^{p} \Bigl(s - 1 - [2 \mid s] - 2[2s > n \wedge 3s \ne 2n]\Bigr).$$
   For $n \ge 16$, if $p > n/2$ then $q = \min(p, q, r)$ satisfies $p - q \ge 6$, so shifting $(p, q) \mapsto (p - 1, q + 1)$ strictly reduces $E_n(p) + E_n(q) + E_n(r)$. Thus every minimizer satisfies $p, q, r \le n/2$, where $D_n(s) = s - 1 - [2 \mid s]$ is weakly increasing, so balanced triples ($\max - \min \le 1$) minimize the exclusion sum and yield the exact mod-6 formula. Direct enumeration confirms $3 \le n \le 15$.

*Scope note:* The Lean 4 formalization (`Conjectures.NakaiA400474`) formally proves the exact real-angle floor reduction (`A + B + C = π`) and the complete combinatorial maximization theorem for all $n \ge 3$ (both the general $n \ge 16$ balancing proof and exact finite cases $3 \le n \le 15$). The classical Euclidean inscribed-angle bijection is presented in full in `PROOF.md` and `paper.tex`.

## Files

- [PROOF.md](PROOF.md) — complete self-contained geometric and combinatorial proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/nakai-a400474/verify.py`).
- [NakaiA400474.lean](../../lean/Conjectures/NakaiA400474.lean) — complete Lean 4 formalization (`lake build Conjectures.NakaiA400474`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
