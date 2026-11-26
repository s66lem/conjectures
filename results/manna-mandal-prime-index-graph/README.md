# Resolution of Manna–Mandal Problem 7.10 (Question 2, `arXiv:2611.27642v1`): `(H1)` Does Not Imply `(H2)`

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24565009.svg)](https://doi.org/10.5281/zenodo.24565009)

**Status:** Second question of Problem 7.10 resolved in the negative via an explicit finite counterexample ($|P| = 243$, $K = P \times \mathbb{Z}_5$, $G = P \times \mathbb{Z}_{10}$) — **Lean 4 verified** ([MannaMandalPrimeIndexGraph.lean](../../lean/Conjectures/MannaMandalPrimeIndexGraph.lean)) & independently cross-model audited ([AUDIT.md](AUDIT.md)).

## Target Problem

P. Manna and S. Mandal, *On the prime index elements graph of finite groups*, [arXiv:2611.27642v1](https://arxiv.org/abs/2611.27642v1) (20 Nov 2026), §7.3:

For a finite group $G$, the **prime index elements graph** $\Gamma(G)$ has vertex set $G$, with distinct $x, y \in G$ adjacent when one of $\langle x \rangle, \langle y \rangle$ has prime index in the other. For a $p$-group $P$ and cyclic subgroup $C \le P$, let $c_P(C)$ count the cyclic subgroups of $P$ containing $C$ as a maximal subgroup, and set $N_p(P) := c_P(1)$. For a nilpotent group $K$ of odd order, a prime $p \mid |K|$, Sylow $p$-subgroup $P$ of $K$, and $m_p = |K|/|P|$, Theorem 7.6 proves two necessary conditions for $\Gamma(K \times \mathbb{Z}_2)$ to be Hamiltonian:
- **(H1)** $N_p(P) \le 2 m_p$;
- **(H2)** $c_P(C) \le 2\varphi(|C|) m_p - 1$ for every cyclic subgroup $1 \ne C \le P$.

> **Problem 7.10 (second question).** *Does (H1) imply (H2), as it does for abelian Sylow subgroups (proof of Corollary 7.8(iii))?*

(The first and third questions of Problem 7.10 — sufficiency of (H1)+(H2) and whether a Hamiltonian path implies a Hamiltonian cycle — remain open.)

## Main Result

**Theorem.** The answer is **no**. Let $A = \mathbb{Z}_9 \times \mathbb{Z}_9$, $s(a, b) = (-b, a - b)$, and $u = (-3, 3) = (6, 3) \in A$, and define the non-abelian $3$-group $P = A \times \{0, 1, 2\}$ of order $243$ with product
$$(v, i) \cdot (w, j) = \bigl(v + s^i(w) + \mathbf{1}_{i + j \ge 3}\, u,\; (i + j) \bmod 3\bigr),$$
equivalently $P = \langle a, b, x \mid a^9 = b^9 = [a, b] = 1,\; xax^{-1} = b,\; xbx^{-1} = a^{-1}b^{-1},\; x^3 = a^{-3}b^3 \rangle$. Set $K = P \times \mathbb{Z}_5$ (nilpotent of odd order $1215$) and $G = K \times \mathbb{Z}_2 \cong P \times \mathbb{Z}_{10}$. Then:
1. **(H1) holds for every prime dividing $|K|$:** for $p = 3$, $N_3(P) = 4 \le 10 = 2m_3$; for $p = 5$, $N_5(\mathbb{Z}_5) = 1 \le 486 = 2m_5$.
2. **(H2) fails at $p = 3$ and $C = \langle u \rangle$:** $c_P(\langle u \rangle) = 30 > 19 = 2\varphi(3)m_3 - 1$.
3. **Direct non-Hamiltonicity (supplementary):** Deleting the $20$-vertex cut set $S = \{(y, t) \in P \times \mathbb{Z}_{10} : y \in \{u, u^2\}\}$ splits $\Gamma(G)$ into $31 > 21 = |S| + 1$ connected components, so $\Gamma(G)$ has neither a Hamiltonian cycle nor a Hamiltonian path. (Question 2 itself is answered by items 1–2, formalized in `H1_holds_and_H2_fails_for_K`; because (H2) fails, non-Hamiltonicity is consistent with Theorem 7.6 and does not settle Question 1.)

## Files

- [PROOF.md](PROOF.md) — complete self-contained algebraic and graph-theoretic proof.
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint ([DOI: 10.5281/zenodo.24565009](https://doi.org/10.5281/zenodo.24565009)).
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/manna-mandal-prime-index-graph/verify.py`).
- [MannaMandalPrimeIndexGraph.lean](../../lean/Conjectures/MannaMandalPrimeIndexGraph.lean) — Lean 4 formalization.
