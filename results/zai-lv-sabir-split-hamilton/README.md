# Disproof of Zai–Lv–Sabir / Tian–Dong Conjecture 1.14 (Hamilton-Connectedness of Split Graphs)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24549479.svg)](https://doi.org/10.5281/zenodo.24549479)

- **Status:** **DISPROVED for every $r \ge 5$** (22-vertex Paley $(11, 5, 2)$ biplane split graph at $r = 5$ + explicit $(2r + 8)$-vertex circulant split graph family for every $r \ge 6$)
- **Source:** Jingfan Zai, Wenjing Lv, and Eminjan Sabir, *Spanning cyclability of split graphs* ([arXiv:2611.32794v1](https://arxiv.org/abs/2611.32794), 24 November 2026), Conjecture 1.14 (originally Conjecture 6.1 of Tian and Dong, `arXiv:2603.12770v1`)
- **Lean 4 formalization:** [ZaiLvSabirSplitHamilton.lean](../../lean/Conjectures/ZaiLvSabirSplitHamilton.lean) (0 `sorry`, 0 custom axioms, 0 `native_decide`)
- **Paper:** [paper.pdf](paper.pdf) ([paper.tex](paper.tex))

## Result

Conjecture 1.14 asserts that for every integer $r \ge 3$, every $r$-connected $\{K_{1,r+1}, K_{1,r+1}+e\}$-free split graph on at least $2r + 7$ vertices is Hamilton-connected.

We disprove Conjecture 1.14 for **every** integer $r \ge 5$ via a unified split-circulant graph $G(m, S)$ on $2m$ vertices ($C \cong K_m$, $I \cong \overline{K_m}$, $c_a \sim i_b \iff b - a \in S \subseteq \mathbb{Z}/m\mathbb{Z}$):
- **$r = 5$:** $m = 11$, $S = \{1, 3, 4, 5, 9\} \subseteq \mathbb{Z}/11\mathbb{Z}$ (Paley $(11, 5, 2)$ biplane, $22 \ge 17 = 2\cdot 5 + 7$ vertices).
- **Every $r \ge 6$:** $m = r + 4$, $S = \{0, 1, \dots, r - 1\} \subseteq \mathbb{Z}/(r+4)\mathbb{Z}$ ($2r + 8 \ge 2r + 7$ vertices).

Every instance satisfies $|S| = r < m$ and $|S \cap (S + d)| \ge 2$ for all $d \ne 0$, which simultaneously forces $r$-connectivity, $\{K_{1,r+1}, K_{1,r+1}+e\}$-freeness, and the absence of any Hamilton path with both endpoints in $C$.

## Files

- [PROOF.md](PROOF.md) — Complete mathematical proof
- [AUDIT.md](AUDIT.md) — Independent cross-model audit report
- [verify.py](verify.py) — Standalone stdlib-only verifier (`python -O -W error verify.py`)
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Standalone LaTeX preprint
- [../../lean/Conjectures/ZaiLvSabirSplitHamilton.lean](../../lean/Conjectures/ZaiLvSabirSplitHamilton.lean) — Lean 4 formalization
