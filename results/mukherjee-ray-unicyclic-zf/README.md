# Disproof of Log-Concavity for Unicyclic Connected Zero Forcing Polynomials (Mukherjee–Ray Problem 6.2, `arXiv:2611.10985v2`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24572283.svg)](https://doi.org/10.5281/zenodo.24572283)

**Problem:** Log-concavity question in Problem 6.2 (and minimum order for Problem 6.4) of S. Mukherjee and P. Ray, *On the connected zero forcing polynomial of finite trees*, [arXiv:2611.10985v2](https://arxiv.org/abs/2611.10985) (v2 posted 25 Nov 2026).

**Status:** **DISPROVED** (completely characterized for all tadpole graphs $T_{m,\ell}$ with $m \ge 3, \ell \ge 0$; counterexamples for every order $n \ge 7$, sharp at $n = 7$; formally verified in **Lean 4** and independently audited).

## Statement (Verbatim, Problem 6.2 of v2)

> "Determine the connected zero forcing polynomial of a unicyclic graph. Is this polynomial always log-concave?"

## Summary of Result

For $m \ge 3$ and $\ell \ge 0$, let $T_{m,\ell}$ be the tadpole graph consisting of an $m$-cycle $c_0, \dots, c_{m-1}$ with a pendant path $c_0 - t_1 - \dots - t_\ell$ of length $\ell$ attached at $c_0$ (a unicyclic graph on $n = m + \ell$ vertices).

1. **Characterization:** A vertex subset $S \subseteq V(T_{m,\ell})$ is a connected zero forcing set if and only if $T_{m,\ell}[S]$ is connected and $S$ contains two adjacent cycle vertices.
2. **Exact polynomial:** Defining $A_m(b) = b$ and $N_m(b) = m - b$ for $2 \le b \le m - 1$, $A_m(m) = 1$, $N_m(m) = 0$, and $0$ otherwise,
   $$Z_C(T_{m,\ell}, k) = N_m(k) + \sum_{a = 0}^{\ell} A_m(k - a).$$
3. **Complete log-concavity criterion:** $Z_C(T_{m,\ell}; x)$ is log-concave **if and only if $m \le 4$ or $\ell \le 1$**.
   - For all $m \ge 5$ and $\ell \ge 2$, the coefficients at sizes $2, 3, 4$ are $m, m + 2, m + 5$, violating log-concavity since $(m + 2)^2 - m(m + 5) = 4 - m < 0$.
   - The smallest counterexample is $T_{5,2}$ ($7$ vertices), with
     $$Z_C(T_{5,2}; x) = 5x^2 + 7x^3 + 10x^4 + 8x^5 + 5x^6 + x^7, \qquad 7^2 = 49 < 50 = 5 \cdot 10.$$
   - Taking $T_{5, n-5}$ gives a unicyclic counterexample for **every order $n \ge 7$**.
4. **Sharp minimality:** Exhaustive verification shows every connected graph on $\le 6$ vertices has a log-concave connected zero forcing polynomial, and $T_{5,2}$ is the unique non-log-concave unicyclic graph on $7$ vertices (also establishing $7$ as the exact minimum order for Problem 6.4, improving on the $82$-vertex non-unimodal graphs of Newton–Brimkov).

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical proof.
- [AUDIT.md](AUDIT.md) — Independent adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone stdlib-only verifier (`python -O -W error verify.py`, verifies $T_{5,2}$, brute-force characterization & closed form for $3 \le m \le 9, 0 \le \ell \le 7$, criterion for $m, \ell \le 60$, all connected graphs on $\le 6$ vertices, and uniqueness of $T_{5,2}$ among $7$-vertex unicyclic graphs).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint.
- [MukherjeeRayUnicyclicZF.lean](../../lean/Conjectures/MukherjeeRayUnicyclicZF.lean) — Complete Lean 4 formalization of the general tadpole family (`tadpole_czf_formula`, `tadpole_czf_logConcave_iff`, `tadpole_5_2_counterexample`, `unicyclic_not_logConcave_every_order_ge_7`).
