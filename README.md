# Solved conjectures in combinatorics, graph theory, and number theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24519466.svg)](https://doi.org/10.5281/zenodo.24519466)

Mathematical proofs, counterexamples, and reproducible verification code for open conjectures in combinatorics, algorithmic game theory, graph theory, and number theory.

Each result directory contains a self-contained proof (`PROOF.md`), an internal mathematical and source audit (`AUDIT.md`), an independent Python 3 verifier (`verify.py`), and (where applicable) an arXiv-ready LaTeX manuscript (`paper.tex`).

## Results

| Problem | Outcome | Verification |
| :--- | :--- | :---: |
| **1.** [Fanelli–Moscardelli stability threshold conjecture](results/fanelli-moscardelli/) | Disproved for all odd $N \ge 7$ | Audit · Python · DRAT SAT |
| **2.** [Csernák–Soukup tree stacking conjecture & literal ASH](results/csernak-soukup-tree-stacking/) | Conj. 5.6 proved; literal Hyp. 3.2 disproved | Audit · Python BFS |
| **3.** [Allie–Du Preez–Hefty–Mafunda tree remoteness conjecture](results/allie-dupreez-hefty-mafunda-remoteness/) | Disproved (infinite family + $k=8$ minimizer) | Audit · Python BFS |
| **4.** [Firoozbakht’s OEIS A108569 parity conjecture](results/firoozbakht-oeis-a108569/) | Disproved (infinite odd family) | Audit · Python |

## Reproduction

All verifiers use only the Python 3 standard library:

```bash
python3 results/fanelli-moscardelli/verify.py
python3 results/csernak-soukup-tree-stacking/verify.py
python3 results/allie-dupreez-hefty-mafunda-remoteness/verify.py
python3 results/firoozbakht-oeis-a108569/verify.py
```

All results are internally audited and computationally verified, but externally unrefereed; priority is not asserted.
