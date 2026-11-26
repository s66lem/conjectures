# Proof That the Path Uniquely Maximizes the Hitting-Time Index Among Trees (`arXiv:2611.34295v1`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24560498.svg)](https://doi.org/10.5281/zenodo.24560498)

**Status:** Proved completely for all $n \ge 1$ (with unique equality characterization for $P_n$) — **100% Lean 4 verified** (zero `sorry`, zero custom axioms, zero `native_decide`). *(Note: concurrent independent Lean 4 work was announced the same day in unpublished GitHub issue `the-omega-institute/trureturing#34417`; priority is not asserted.)*

## Target Conjecture

José Luis Palacios, Shunya Tamura, Jason Wiberg, and Aleksandar Petojević, *The hitting time index: bounds, a sharp threshold, the proof of a conjecture and the disproof of another conjecture*, [arXiv:2611.34295v1](https://arxiv.org/abs/2611.34295v1) (25 Nov 2026), §3:

> What the $n$-path seems to attain is the maximum value of the $HT$ index among trees, and there is evidence supporting that conjecture in the recent articles [9] and [14], where the $HT$ index of some families of trees is computed, and all the values found are bounded above by $HT(P_n)$.

For a connected finite simple graph $G = (V, E)$, let $H(x, y)$ denote the expected hitting time from $x$ to $y$ for the simple random walk on $G$. The hitting-time index is
$$HT(G) = \sum_{\{x, y\} \subseteq V} \max\bigl(H(x, y),\, H(y, x)\bigr).$$

## Main Result

**Theorem.** For every tree $T$ on $n \ge 1$ vertices,
$$HT(T) \le HT(P_n),$$
with equality if and only if $T \cong P_n$.

## Proof Summary

1. **Exact hitting-time reduction on trees:** Writing $D(x) = \sum_{z \in V} d_T(x, z)$ for the transmission of $x$, the function
   $$H(x, y) = (n - 1)\, d_T(x, y) + D(y) - D(x)$$
   is the unique solution of the simple-random-walk first-step system $h(y) = 0$ and $\deg(x)\, h(x) = \deg(x) + \sum_{w \sim x} h(w)$ ($x \ne y$) on every finite tree $T$. Consequently,
   $$HT(T) = \sum_{\{x, y\} \subseteq V} \Bigl((n - 1)\, d_T(x, y) + |D(y) - D(x)|\Bigr).$$
2. **Pendant-path grafting move:** Suppose $T$ has two pendant paths $A = (A_1, \dots, A_a)$ and $B = (B_1, \dots, B_b)$ attached at a common vertex $v$, with $a \ge b \ge 1$, and the remaining core $C = V \setminus (A \cup B)$ satisfies $|C| = r + 1$ with $r \ge a$. Replacing edge $v A_1$ by $B_b A_1$ produces a tree $T'$ with one fewer leaf and strictly larger hitting-time index $HT(T') > HT(T)$:
   - For $a = b = 1$, arm symmetry $D(A_1) = D(B_1)$ pairs $(A_1, z)$ with $(B_1, z)$ for every $z \in C$, giving $HT(T') - HT(T) \ge (r + 1)(r + 2 - |r - 3|) - 1 \ge r \ge 1$.
   - For all $a \ge 2$, the core $C$ cancels from $D(A_i) - D(B_j) = i(r + b - a + i) - j(r + a - b + j)$, while $D'(A_i) - D'(B_j) = (b + i - j)(r + i + j - a) > 0$. Combining exact $A$–$B$ transmission evaluation with triangle-inequality bounds on $A$–$C$, $B$–$C$, and $B$–$B$ yields the closed-form lower bound (with $d = a - b \ge 0$, $s = r - a \ge 0$):
     $$6\bigl(HT(T') - HT(T)\bigr) \ge \bigl(12ab(a - 1) + b(b - 1)(b - 2)\bigr) s + 2b\bigl(6d^3 + (15b - 6)d^2 + 2(b - 1)(7b + 1)d + 5b^3 - 7b^2 - 2b + 1\bigr) > 0.$$
3. **Existence & leaf-count induction:** Every non-path tree has a branching vertex on a diameter; rooting at the farther diameter endpoint and choosing a deepest vertex $v$ of degree $\ge 3$ produces two pendant arms with $r \ge a \ge b \ge 1$. Iterating the grafting move strictly increases $HT$ while decreasing the leaf count by $1$, terminating uniquely at $P_n$.

## Files

- [PROOF.md](PROOF.md) — complete self-contained mathematical proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/palacios-hitting-time-trees/verify.py`).
- [PalaciosHittingTimeTrees.lean](../../lean/Conjectures/PalaciosHittingTimeTrees.lean) — complete end-to-end Lean 4 formalization over Mathlib `SimpleGraph.IsTree` (`lake build Conjectures.PalaciosHittingTimeTrees`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
