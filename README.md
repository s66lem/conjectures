# Solved conjectures in combinatorics, graph theory, and number theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24519466.svg)](https://doi.org/10.5281/zenodo.24519466)

Mathematical proofs, counterexamples, and reproducible verification code for open conjectures in combinatorics, algorithmic game theory, graph theory, and number theory.

Each result directory contains a self-contained proof (`PROOF.md`), an internal mathematical and source audit (`AUDIT.md`), an independent Python 3 verifier (`verify.py`), and (where applicable) an arXiv-ready LaTeX manuscript (`paper.tex`).

## Results

| Problem | Outcome | Preprint | Verification |
| :--- | :--- | :---: | :---: |
| **1.** [Fanelli–Moscardelli stability threshold conjecture](results/fanelli-moscardelli/) | Disproved for all odd $N \ge 7$ | [DOI](https://doi.org/10.5281/zenodo.24519727) | **Lean 4** · Audit · Python · DRAT SAT |
| **2.** [Csernák–Soukup tree stacking conjecture & literal ASH](results/csernak-soukup-tree-stacking/) | Conj. 5.6 proved; literal Hyp. 3.2 disproved | [DOI](https://doi.org/10.5281/zenodo.24519728) | **Lean 4** · Audit · Python BFS |
| **3.** [Allie–Du Preez–Hefty–Mafunda tree remoteness conjecture](results/allie-dupreez-hefty-mafunda-remoteness/) | Disproved (infinite family + $k=8$ minimizer) | [DOI](https://doi.org/10.5281/zenodo.24519729) | Audit · Python BFS |
| **4.** [Firoozbakht’s OEIS A108569 parity conjecture](results/firoozbakht-oeis-a108569/) | Disproved (infinite odd family) | — | **Lean 4** · Audit · Python |
| **5.** [Rossi rank score veto core distortion conjecture](results/rossi-veto-core-distortion/) | Proved (exact distortion $1 + 2(\|\mathbf{s}\|_1 - s_m)$) | [PDF](results/rossi-veto-core-distortion/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **6.** [Togni multi-label radio labeling conjectures](results/togni-multilabel-radio/) | Conj. 2 proved (all $k, m$); Conj. 1 upper bound & exact $k=3$ | [PDF](results/togni-multilabel-radio/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **7.** [Maharaj 1D discrete Voronoi game conjecture](results/maharaj-voronoi-game/) | Disproved for all $\ell \ge 3$; exact $k^*(\ell) = 2\ell - 1$ | [PDF](results/maharaj-voronoi-game/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |

## Reproduction

All verifiers use only the Python 3 standard library:

```bash
python3 results/fanelli-moscardelli/verify.py
python3 results/csernak-soukup-tree-stacking/verify.py
python3 results/allie-dupreez-hefty-mafunda-remoteness/verify.py
python3 results/firoozbakht-oeis-a108569/verify.py
python3 results/rossi-veto-core-distortion/verify.py
python3 results/togni-multilabel-radio/verify.py
python3 results/maharaj-voronoi-game/verify.py
```

To check the Lean 4 formalizations (Lean `v4.33.1` + Mathlib):

```bash
cd lean && lake build
```

All results are internally audited and computationally verified, but externally unrefereed; priority is not asserted.
