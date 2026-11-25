# Conjecture Resolutions

Verified proofs and disproofs of open mathematical conjectures, each accompanied by a self-contained writeup, arXiv-ready LaTeX source (where applicable), and an independent zero-dependency Python verifier.

## Verified Results

| Problem | Source | Resolution | Writeup & LaTeX | Verifier |
|---|---|---|---|---|
| **Fanelli–Moscardelli Stability Threshold Conjecture** (`stability_threshold_tight`) | ECAI 2025, §5 (`doi:10.3233/FAIA251234`); `formal-conjectures` #7848 | **Disproved:** constructive proof that $K(2m+1) \le m < \lceil(2m+1)/2\rceil$ for all $m \ge 3$ (sharp at $K(5)=3$); exact $K(7)=3, K(8)=3, K(9)=4, K(11)=5$ | [DISPROOF.md](results/fanelli_moscardelli/DISPROOF.md) · [paper.tex](results/fanelli_moscardelli/paper.tex) | [verify.py](results/fanelli_moscardelli/verify.py) |
| **Tree Stacking Conjecture (Conj. 5.6) & Literal ASH (Hyp. 3.2)** | Csernák & Soukup, `arXiv:2610.09650` (Oct 2026) | **Conjecture 5.6 proved unconditionally** ($\operatorname{stack}(T) = \operatorname{estim}(T)$ for every finite tree, $O(n^2)$ algorithm); **literal Hypothesis 3.2 disproved** for stacking ($P_4$, $12$ vs $15$) and clearing ($G_5$, $16$ vs $22$) | [RESULTS.md](results/ash_2610_09650/RESULTS.md) · [paper.tex](results/ash_2610_09650/paper.tex) | [verify.py](results/ash_2610_09650/verify.py) |
| **Remoteness-Minimizing $D$-Tree Conjecture (Conj. 4.4)** | Allie, Du Preez, Hefty & Mafunda, `arXiv:2611.27685` (Nov 2026) | **Disproved:** explicit $(9,3)$-tree on $n=507$ vertices for $D=(315,116,25,21,21,1^8)$ beats all $607$ trees with $h \le 2$ ($115{,}399$ vs $\ge 115{,}501$, scaled family $t\cdot D$); plus $k=8$ counterexample ($n=8{,}918$) | [DISPROOF.md](results/remoteness_2611_27685/DISPROOF.md) · [note.tex](results/remoteness_2611_27685/note.tex) | [verify.py](results/remoteness_2611_27685/verify.py) |
| **OEIS A108569 Parity Conjecture** ($\varphi(n) = \varphi(n + \varphi(n))$) | Firoozbakht (2005); `formal-conjectures` `OEIS/108569.lean` | **Disproved:** odd counterexample $n = 5{,}095{,}354{,}107 = 3 \cdot 1033 \cdot 1{,}644{,}193$ and infinite odd family $n_j = 3^j \cdot 5{,}095{,}354{,}107$ ($j \ge 0$) | [DISPROOF.md](results/oeis_a108569/DISPROOF.md) | [verify.py](results/oeis_a108569/verify.py) |

## Reproduction

All verifiers use only the Python 3 standard library and complete in a few seconds:

```bash
python results/fanelli_moscardelli/verify.py
python results/ash_2610_09650/verify.py
python results/remoteness_2611_27685/verify.py
python results/oeis_a108569/verify.py
```

## Notes

- Each proof and disproof was checked against the original published/formalized definitions, verified computationally from scratch, and (for general theorems) audited by an independent adversarial referee pass.
- No LaTeX compiler is bundled here; the `.tex` files use standard `article` + `amsmath`/`amssymb`/`amsthm`/`hyperref` and compile directly on Overleaf or any TeX Live installation.
