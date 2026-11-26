# Vasilyev (arXiv:2611.20344v2), Question 7.1: Refutation of `2^l < 3^(a+1)` for Up-Down Graph Cycles

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24567319.svg)](https://doi.org/10.5281/zenodo.24567319)

- **Source:** O. Vasilyev, *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*, [arXiv:2611.20344v2](https://arxiv.org/abs/2611.20344) (`math.NT`, v1 16 Nov 2026, v2 18 Nov 2026), Section 7 ("Questions"), Question 7.1.
- **Open question (verbatim):**
  > "Does every cycle satisfy $2^\ell < 3^{a+1}$, that is, $a = \lfloor \ell \log_3 2 \rfloor$? This holds for cycles with a single run of steps up (Theorem 4.1(d)), for all cycles of length $\ell \le 30$, and for all $1{,}133{,}265{,}572$ cycles whose elements are all at most $160$; among the latter, the largest ratio $2^\ell / 3^a$ is $2.398$, for $\ell = 71$. If the answer is negative, what is the supremum of $2^\ell / 3^a$?"
- **Resolution:** **No (counterexample).** We construct an explicit simple cycle of length $\ell = 382$ in the up-down graph $G$ (with steps $U(x) = \lceil 3x/2 \rceil$ and $D(x) = \lceil x/2 \rceil$) having $a = 240$ up-steps and $142$ down-steps. It satisfies
  $$\frac{2^{382}}{3^{240}} \approx 3.050403 > 3, \qquad\text{equivalently}\qquad 3^{241} < 2^{382},$$
  so $a = 240 = \lfloor 382 \log_3 2 \rfloor - 1 \neq \lfloor \ell \log_3 2 \rfloor$. Taking $S \subset \mathbb{N}$ to be the set of $240$ up-vertices of the cycle yields a Collatz-type map $T_S$ with a primitive cycle of exact period $382$ violating $2^\ell < 3^{a+1}$. (The follow-up question of determining $\sup 2^\ell / 3^a$ remains open; our construction establishes $\sup 2^\ell / 3^a \ge 2^{382}/3^{240} \approx 3.0504$.)

## Files

- [PROOF.md](PROOF.md) — Explicit counterexample cycle, algebraic analysis via Vasilyev's product identity, and orbit verification.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone exact integer & `Fraction` verification (`python -O -W error verify.py`, zero third-party dependencies).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Standalone publication-ready LaTeX note (Zenodo DOI [`10.5281/zenodo.24567319`](https://doi.org/10.5281/zenodo.24567319)).
- [VasilyevUpDownCycles.lean](../../lean/Conjectures/VasilyevUpDownCycles.lean) — Lean 4 formalization (`vasilyev_question_7_1_disproof`, zero `sorry`, standard axioms only).
