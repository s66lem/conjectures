# Tiles of $\mathbb{Z}$ Inside $\{1, 2, 4, \dots, 2^n\}$: Disproof and Complete Size Spectrum (Benjamini–Kozma–Tzalik, EJC 33(3) #P3.28)

**Status:** Complete, Lean 4 verified (`lean/Conjectures/BenjaminiKozmaTzalikTiles.lean`, standard axioms only), independently audited (`AUDIT.md`), and published on Zenodo: [10.5281/zenodo.24581640](https://doi.org/10.5281/zenodo.24581640).

*Scope note:* The Lean 4 formalization unconditionally proves the $\{1, 4, 16\}$ disproof of Question 9 (`bkt_q9_disproof`), the general odd-size construction for all odd $k \ge 1$ (`odd_size_power_of_two_tile_exists`), the general even-size impossibility for all even $k \ge 4$ (`even_size_ge_four_no_power_of_two_tile`), and the complete size spectrum `iff` (`power_of_two_tile_size_iff`). The prime-size classification via Newman's theorem and the exact counts $t(0), \dots, t(15)$ are proved in `PROOF.md`/`paper.tex` and verified in `verify.py`.

## Problem

In *The number of tiles of $\mathbb{Z}^d$*, *Electron. J. Combin.* **33(3)** (2026), #P3.28 (`arXiv:2303.07956v2`, Section 3, Question 9; Question 13 in v1, 2023), I. Benjamini, G. Kozma, and E. Tzalik ask:

> **Question 9.** How many tiles are contained in the set $\{1, 2, 4, \dots, 2^n\}$? Are the only such tiles the sets of size $1$ and $2$?

## Results

1. **Disproof of the second part:** $\{1, 4, 16\} \subset \{1, 2, 4, 8, 16\}$ is a $3$-element tile of $\mathbb{Z}$ with tiling complement $T = \{-1, 0, 1\} + 9\mathbb{Z}$. Hence $\{1, 2, \dots, 2^n\}$ contains a tile of size $3$ for every $n \ge 4$.
2. **Complete exact size spectrum:** A $k$-element subset of $\{2^j : j \ge 0\}$ tiles $\mathbb{Z}$ **if and only if** $k \in \{1, 2\}$ or $k$ is **odd**.
   - Every odd $k \ge 1$ is realized by $S_k = \{q^d : 0 \le d < k\}$ with $q = 2^r$, $r = \mathrm{ord}_{\mathrm{rad}(k)}(2)$ (or $r = \varphi(k)$), proved via lifting-the-exponent.
   - No even $k \ge 4$ can occur, proved via Newman periodicity, Coven–Meyerowitz's cyclotomic prime-power divisibility criterion (T1), and the non-divisibility of any normalized power-of-$2$ mask polynomial ($k \ge 3$) by $\Phi_{2^j}(X) = X^{2^{j-1}} + 1$.
3. **Prime-size classification & exact counts for $n \le 15$:** By Newman's theorem, for every odd prime $p$, the minimal $n$ with a $p$-element tile in $\{1, \dots, 2^n\}$ is $(p - 1)\,\mathrm{ord}_p(2)$ ($4, 16, 18, 100, \dots$ for $p = 3, 5, 7, 11, \dots$), yielding the exact tile counts $t(0), \dots, t(15) = 1, 3, 6, 10, 16, 23, 31, 40, 51, 63, 78, 94, 112, 131, 153, 176$.

## Verification

- **Lean 4:** `lean/Conjectures/BenjaminiKozmaTzalikTiles.lean` (proves the $\{1, 4, 16\}$ disproof AND the complete size spectrum $k \in \{1, 2\} \cup (2\mathbb{N} + 1)$ unconditionally with zero `sorry` and standard axioms only).
- **Standalone Python verifier:** `python -O -W error results/benjamini-kozma-tzalik-tiles/verify.py` (stdlib only).
- **Full writeup:** `PROOF.md`, `paper.tex`, `paper.pdf`.
