# Solved conjectures in combinatorics, graph theory, and number theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24519466.svg)](https://doi.org/10.5281/zenodo.24519466)

Mathematical proofs, counterexamples, and reproducible verification code for open conjectures in combinatorics, algorithmic game theory, graph theory, and number theory.

Each result directory contains a self-contained proof (`PROOF.md`), an internal mathematical and source audit (`AUDIT.md`), an independent Python 3 verifier (`verify.py`), and (where applicable) an arXiv-ready LaTeX manuscript (`paper.tex`).

## Results

| Problem | Outcome | Preprint | Verification |
| :--- | :--- | :---: | :---: |
| **1.** [Fanelli–Moscardelli stability threshold conjecture](results/fanelli-moscardelli/) | Disproved for all odd $N \ge 7$ | [DOI](https://doi.org/10.5281/zenodo.24519727) | **Lean 4** · Audit · Python · DRAT SAT |
| **2.** [Csernák–Soukup tree stacking conjecture & literal ASH](results/csernak-soukup-tree-stacking/) | Conj. 5.6 proved; literal Hyp. 3.2 disproved | [DOI](https://doi.org/10.5281/zenodo.24519728) | **Lean 4** · Audit · Python BFS |
| **3.** [Allie–Du Preez–Hefty–Mafunda tree remoteness conjecture](results/allie-dupreez-hefty-mafunda-remoteness/) | Disproved (infinite family + $k=8$ minimizer) | [DOI](https://doi.org/10.5281/zenodo.24519729) | **Lean 4** · Audit · Python BFS |
| **4.** [Firoozbakht’s OEIS A108569 parity conjecture](results/firoozbakht-oeis-a108569/) | Disproved (infinite odd family) | — | **Lean 4** · Audit · Python |
| **5.** [Rossi rank score veto core distortion conjecture](results/rossi-veto-core-distortion/) | Proved (exact distortion $1 + 2(\|\mathbf{s}\|_1 - s_m)$) | [PDF](results/rossi-veto-core-distortion/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **6.** [Togni multi-label radio labeling conjectures](results/togni-multilabel-radio/) | Conj. 2 proved (all $k, m$); Conj. 1 upper bound & exact $k=3$ | [PDF](results/togni-multilabel-radio/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **7.** [Maharaj 1D discrete Voronoi game conjecture](results/maharaj-voronoi-game/) | Disproved for all $\ell \ge 3$; exact $k^*(\ell) = 2\ell - 1$ | [PDF](results/maharaj-voronoi-game/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **8.** [Daga–Ramu exact Littlestone dimensions of intervals](results/daga-ramu-littlestone/) | Both conjectures proved (Conj. 31 & odd-$k$ unions) | [PDF](results/daga-ramu-littlestone/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **9.** [Kalmanovich–Nivasch Conjecture 9.1 on planar all-even sets](results/kalmanovich-nivasch-alleven/) | Disproved (36-point counterexample + unbounded seed family) | [PDF](results/kalmanovich-nivasch-alleven/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **10.** [Notik Singer Golomb ruler chamber-uniqueness conjecture](results/notik-singer-golomb/) | Proved for all prime powers (every cyclic PDS) | [PDF](results/notik-singer-golomb/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **11.** [Rofa regular spider 0-rotatability conjecture](results/rofa-spider-rotatability/) | Proved for all $k \ge 1, \ell \ge 1$ | [PDF](results/rofa-spider-rotatability/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **12.** [Benedetti–Menara Conjecture 7.1 ($r = 2$, flag $1$-layered families)](results/benedetti-menara-flag-layered/) | Proved $r = 2$ sharp bound $m - 1$ + halved Larman–Barnette + unconditional Thm. E(a) at $p = d - 2$ | [PDF](results/benedetti-menara-flag-layered/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **13.** [Sinclair Conjecture C (radial-derivative Hilbert series front-loading)](results/sinclair-radial-mobius/) | Disproved ($M(K_{1,1,4}+e)$: $h_2^\beta = 31 < 32 = h_3^\beta$, family $m=4..7$ + binary example) | [PDF](results/sinclair-radial-mobius/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **14.** [Arana–Haxell–Kaiser–Stehlík Conjecture 1.3 ($k = 3$, $G$-stable Kneser graphs)](results/arana-haxell-kaiser-stehlik-kneser/) | Proved completely for $k = 3$ (+ Schrijver $k = 3$, all-$k$ star obstruction at $4k-3$, $k = 4$ $C_m \sqcup K_1$ for $m \ge 39$) | [PDF](results/arana-haxell-kaiser-stehlik-kneser/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **15.** [Manabe Conjecture 57 (purely periodic three-move subtraction games)](results/manabe-subtraction-games/) | Proved in full (strengthened to all $1 \le a < b < c$ at $\mathrm{P}$-position level + Conj. 52 $\iff$ Conj. 56 for all $c > b$ + $100.9\text{M}$ census) | [PDF](results/manabe-subtraction-games/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |
| **16.** [Chen–Zwicker Conjecture 1 ($\mathrm{EF1}_{\mathrm{outer}}$ spectrum of connected graphs)](results/chen-zwicker-ef1-outer/) | Disproved (minimal $8$-vertex graph $H$: `NO` at $k=2$, `YES` at $k=3$, `NO` at $k=4$ from common binary up to heterogeneous monotone) | [PDF](results/chen-zwicker-ef1-outer/paper.pdf) | **Lean 4** · Cross-Model Audit · Python |

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
python3 results/daga-ramu-littlestone/verify.py
python3 results/kalmanovich-nivasch-alleven/verify.py
python3 results/notik-singer-golomb/verify.py
python3 results/rofa-spider-rotatability/verify.py
python3 results/benedetti-menara-flag-layered/verify.py
python3 results/sinclair-radial-mobius/verify.py
python3 results/arana-haxell-kaiser-stehlik-kneser/verify.py base
python3 results/manabe-subtraction-games/verify.py
python3 results/chen-zwicker-ef1-outer/verify.py
```

To check the Lean 4 formalizations (Lean `v4.33.1` + Mathlib):

```bash
cd lean && lake build
```

All results are internally audited and computationally verified, but externally unrefereed; priority is not asserted.
