# Resolution of Güday–Şahin Conditional-Sequence Conjectures (INTEGERS 26, 2026, #A5)

**Status:** Complete, Lean 4 verified (`lean/Conjectures/GudaySahinConditionalSequences.lean`, standard axioms only), independently audited (`AUDIT.md`), and published on Zenodo: [10.5281/zenodo.24580791](https://doi.org/10.5281/zenodo.24580791).

*Scope note:* The Lean 4 formalization unconditionally proves Conjecture 2's exact corrected formula (all $m, d$ with $3 \mid d$), its $m \le 5$ validity, its $m \ge 6$ refutation, the minimal $m=6, d=9$ witness, the $r \le 3$ residue-bijectivity equivalence, the $r \ge 4$ non-bijective family, and the unconditional refutation of Conjecture 1 over $\mathbb{R}$ at $r = 4, m = 5$ for all $\pm 1$ sign assignments and all eventual cutoffs $N$. The general signed-bijection decimated recurrence (Theorem 1 / Open Problem 1) is proved in `PROOF.md`/`paper.tex` and verified symbolically for ten $(r, m)$ pairs in `verify.py`.

## Problem

In *Linear Recurrence Relations Satisfied by the General Conditional Sequences*, *INTEGERS* **26** (2026), #A5, E. Güday and M. Şahin study the general conditional sequence $\{q_n\}_{n \ge 0}$ defined for positive integers $r, m$ ($m > r$) by

$$q_n = \sum_{j=1}^{m} a_{n \bmod r,\, j}\, q_{n-j} \qquad (n \ge m),$$

and state two conjectures (pp. 16 and 18) and one open problem (p. 15):

1. **Open Problem 1 (p. 15):** Determine the signs of the coefficients in the $r$-decimated recurrence for $r = 3$.
2. **Conjecture 1 (p. 16):** For all $m > r$, $\{q_n\}$ satisfies $q_n = \sum_{s=1}^{m} A_{sr} q_{n-sr}$ where $A_d$ is a $\pm 1$-signed sum over all tuples $(d_0, \dots, d_{r-1}) \in \{0, \dots, m\}^r$ with $\sum d_k = d$ and $d_k \not\equiv k + d_0 \pmod{r}$ for $1 \le k \le r - 1$.
3. **Conjecture 2 (p. 18):** For $r = 3$ and $d \in \{0, 3, \dots, 3m\}$, the number $|\mathcal{A}_d|$ of tuples in Conjecture 1 satisfies $|\mathcal{A}_d| = w_{3,m}(d) - \tfrac{1}{2} w^*_{3,m}(d)$, where $w_{3,m}(d)$ counts all compositions of $d$ into $3$ parts in $[0, m]$ and $w^*_{3,m}(d)$ counts those with pairwise distinct parts.

## Results

- **Exact Decimated Recurrence & Open Problem 1 (all $r, m \ge 1$):** For $n \ge mr + m - 1$, $q_n = \sum_{s=1}^{m} c_s q_{n-sr}$ with
  $$c_s = \sum_{\substack{d \in \{0,\dots,m\}^r \\ \sum d_i = sr,\;\sigma_d \text{ bijective}}} \mathrm{sgn}(\sigma_d)\,(-1)^{\mathrm{nz}(d)+1} \prod_{d_i > 0} a_{i, d_i},$$
  where $\sigma_d(i) = (i - d_i) \bmod r$ and $\mathrm{nz}(d) = \#\{i : d_i > 0\}$.
- **Conjecture 1:** True for $r \le 3$ (with the exact signs above) and **false for every $r \ge 4$**. At the minimal case $r = 4, m = 5$, the conjectured support for $A_4$ has 17 terms whereas the true coefficient $c_1$ has 15 (the non-bijective tuples $(0,3,0,1)$ and $(1,0,1,2)$ vanish identically). An explicit integer instance proves that no choice of $\pm 1$ signs makes the conjectured recurrence hold eventually over $\mathbb{R}$.
- **Conjecture 2:** True for $m \le 5$ and **false for every $m \ge 6$** (minimal counterexample $m = 6, d = 9$: $|\mathcal{A}_9| = 25 \ne 22 = 37 - 30/2$). The exact formula for all $m \ge 1$ and $3 \mid d$ is
  $$2|\mathcal{A}_d| = 2 w_{3,m}(d) - w^{\bmod 3}_{3,m}(d),$$
  where $w^{\bmod 3}_{3,m}(d)$ counts compositions of $d$ into $3$ parts in $[0, m]$ with pairwise distinct residues modulo $3$.

## Verification

- **Lean 4:** `lean/Conjectures/GudaySahinConditionalSequences.lean` (zero `sorry`, zero custom axioms, zero forbidden tokens).
- **Standalone Python verifier:** `python -O -W error results/guday-sahin-conditional-sequences/verify.py` (stdlib only).
- **Full writeup:** `PROOF.md`, `paper.tex`, `paper.pdf`.
