# Bihan (arXiv:2611.34336v1): Maximal Topological Degree of 3D Fewnomial Maps (`D(3, 3) = {0, 1, 2, 3}`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24567883.svg)](https://doi.org/10.5281/zenodo.24567883)

- **Source:** F. Bihan, *Descartes' rule of signs for the topological degree*, [arXiv:2611.34336v1](https://arxiv.org/abs/2611.34336) (`math.CO`, 25 Nov 2026), Introduction (after Theorem 2') and Section 5.
- **Open question (verbatim):**
  > "We do not know the maximal topological degree when $n, k \ge 3$. The first open case is $n = k = 3$, where Theorem 2 gives $|\deg F| \le 4$."
  > "For $n, k \ge 3$ we do not know whether the bound of Theorem 2 is sharp. It gives $|\deg F| \le 4$ for $n = k = 3$ and $|\deg F| \le 13$ for $n = k = 4$."
- **Resolution:** **Theorem 2 is not sharp for $n = k = 3$; in fact $D(3, 3) = \{0, 1, 2, 3\}$.** More generally, for every $3$-dimensional fewnomial map $F$ satisfying the general-position hypotheses `(UA)` and `(UC)` whose Newton polytope $P = \mathrm{conv}(A)$ has $V \le N$ vertices,
  $$|\deg F| \le \left\lfloor \frac{3V - 8}{4} \right\rfloor \le \left\lfloor \frac{3N - 8}{4} \right\rfloor.$$
  Hence $\max D(3, k) \le \lfloor 3k / 4 \rfloor + 1$ for all $k \ge 1$ (and by Bihan's duality Theorem 3, $\max D(k, 3) \le \lfloor 3k / 4 \rfloor + 1$), strictly improving Theorem 2's bound $N - 3 = k + 1$ for every $k \ge 3$ ($N \ge 7$). Exact integer witnesses realize $|\deg F| = 0, 1, 2, 3$ for $N = 7$ (establishing $D(3, 3) = \{0, 1, 2, 3\}$) and attain the bound $\lfloor (3V - 8)/4 \rfloor$ for $V = 8, 9, 10, 12$ (including an integer perturbation of the great icosahedron $\{3, 5/2\}$ of density $7$).

## Files

- [PROOF.md](PROOF.md) — Complete proof of the spherical Gauss–Bonnet upper bound $|\deg F| \le \lfloor (3V - 8)/4 \rfloor$, equality characterization, and exact realizations.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone exact integer verification (`python -O -W error verify.py`, zero third-party dependencies).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Standalone publication-ready LaTeX note (Zenodo DOI [`10.5281/zenodo.24567883`](https://doi.org/10.5281/zenodo.24567883)).
- [BihanFewnomialDegree.lean](../../lean/Conjectures/BihanFewnomialDegree.lean) — Purely algebraic Plücker-telescoping Lean 4 formalization over any linearly ordered field (`bihan_3d_degree_bound`, `n7_realizes_0..3`, `extremal_V8..V12`, zero `sorry`, standard axioms only).
