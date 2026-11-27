# Disproof and Complete Corrected Characterization for Dufour–Heubach Conjecture 1 on Slow A-Nim

- **Status:** Disproved & Complete Corrected Theorem Proved (Lean 4 Verified)
- **Source:** M. Dufour, S. Heubach, *On the $\mathcal{P}$-positions of some infinite families of Slow $A$-Nim*, INTEGERS 26 (2026) #G3, Section 6 ([arXiv:2404.06608v3](https://arxiv.org/abs/2404.06608), Conjecture 1 / `con:atleastk`)
- **Zenodo Preprint:** [10.5281/zenodo.24576433](https://doi.org/10.5281/zenodo.24576433)
- **Lean 4 Formalization:** [`DufourHeubachSlowANim.lean`](../../lean/Conjectures/DufourHeubachSlowANim.lean)

## Summary

We disprove Conjecture 1 of Dufour and Heubach on Slow $\{k, \dots, n\}$-Nim and prove the exact corrected characterization of all $\mathcal{P}$-positions for every $n \ge 1$, $k \ge 1$, and $p \in \mathbb{N}^n$:

1. **Disproof of Conjecture 1:**
   - At $n = 4, k = 2$, the reduced $\mathcal{P}$-position $(0, 1, 2, 2)$ violates the middle-set parity clause $o \equiv n \pmod 2$.
   - For every odd $k \ge 3$ and $n \ge (3k - 1)/2$, having $(3k - 1)/2$ stacks of height $2$ yields a reduced $\mathcal{P}$-position violating the middle-set clause $1 \le o$ (smallest: $(2, 2, 2, 2)$ at $n = 4, k = 3$).
2. **Complete Corrected Theorem (`isP_iff_div_eq`):** For every position $p \in \mathbb{N}^n$ (reduced or not), letting $\tilde p$ be its playable reduction, $D(q) = \sum_i \lceil q_i / 2 \rceil$, and $E(q) = \sum_i \lfloor q_i / 2 \rfloor$,
   $$p \text{ is a } \mathcal{P}\text{-position} \iff \left\lfloor \frac{D(\tilde p)}{k} \right\rfloor = \left\lfloor \frac{E(\tilde p)}{k} \right\rfloor.$$
   For reduced positions, this is equivalent to removing both erroneous clauses from the middle set: $s \le 2k - 2$ and $o \le \min(s, 2k - 2 - s)$.

## Files

- `PROOF.md`: Complete self-contained mathematical proof.
- `paper.tex` / `paper.pdf`: Publication-ready LaTeX preprint.
- `verify.py`: Standalone Python stdlib verifier (`python -O -W error verify.py`).
- `AUDIT.md`: Independent adversarial audit report (PASS, 5/5 checks).
