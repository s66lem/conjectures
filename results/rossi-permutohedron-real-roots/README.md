# Proof of Rossi's Conjecture 6.16 (`arXiv:2611.25741v1`, Real-Rootedness of the Permutohedron Characteristic & Full $f$-Polynomial)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24569715.svg)](https://doi.org/10.5281/zenodo.24569715)

**Status:** Proved completely for every $n \ge 3$ and formally verified in **Lean 4** (analytic proof for all $n \ge 64$; kernel-verified rational sign-alternation witnesses and exact Sturm sequences for $3 \le n \le 63$).

## Target Conjecture

Giovanni Rossi, *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*, [arXiv:2611.25741v1](https://arxiv.org/abs/2611.25741v1) (19 Nov 2026), Conjecture 6.16 (§6.5):

> **Conjecture 6.16 (Real-rootedness).** For every $n \ge 3$ the polynomial $\chi_n(t)$ has $n$ distinct positive real roots: the root $1$, exactly $n - 2$ roots in $(0, 1)$ and one root greater than $1$. Equivalently, the rank generating polynomial $R_n(w) = \sum_{x \in \mathcal{L}_n} w^{\mathrm{rk}(x) + 1}$ (the full $f$-polynomial of the permutohedron including the empty face) has only real roots, all negative.

By Theorem 6.11(1) of `arXiv:2611.25741v1`,
$$\chi_n(t) = t^n - \sum_{i=0}^{n-1} A(n, i)\, (t - 1)^i\, t^{n - 1 - i} \qquad (n \ge 3),$$
where $A(n, i)$ are the Eulerian numbers and $A_n(z) = \sum_{i=0}^{n-1} A(n, i) z^i$ is the $n$-th Eulerian polynomial.

## Main Result

**Theorem.** For every integer $n \ge 3$, $\chi_n(t)$ has $n$ distinct positive real roots: $t = 1$, exactly $n - 2$ roots in $(0, 1)$, and one root in $(1, \infty)$. Equivalently, $R_n(w)$ has only simple negative real roots.

## Proof Summary

1. **Möbius reduction:** Setting $t = z / (z - 1)$ transforms $\chi_n$ into the degree-$(n - 1)$ polynomial
   $$M_n(z) := (z - 1)^n \chi_n\!\left(\frac{z}{z - 1}\right) = (1 - z) A_n(z) + z^n,$$
   with $M_n(0) = M_n(1) = 1$ and negative leading coefficient $n + 2 - 2^n < 0$. It suffices to exhibit $n - 2$ distinct negative roots of $M_n$ (plus the automatic root in $(1, \infty)$).
2. **Paired sign-alternation criterion:** Let $K = \lfloor (n - 1) / 2 \rfloor$. By the reflection identity $M_n(-1/\sigma) = (-\sigma)^{-n}[1 - (1 + \sigma) A_n(-\sigma)]$, any points $0 < \sigma_1 < \dots < \sigma_K \le 1$ (with $\sigma_K < 1$ when $n$ is even) satisfying $(-1)^m A_n(-\sigma_m) > 0$ and $(1 + \sigma_m)|A_n(-\sigma_m)| > 1$ force $n - 2$ sign changes of $M_n$ on $(-\infty, 0)$, hence all $n - 1$ roots real and simple.
3. **Analytic construction for all $n \ge 64$:**
   - **Regime A** ($(m + 1)^2 \le n / 4$): Take $\sigma_m = (m / (m + 2))^{n/2}$. In Euler's alternating series $A_n(-\sigma) = (1 + \sigma)^{n+1} \sum_{k \ge 0} (-1)^k (k + 1)^n \sigma^k$, the $k = m$ term strictly dominates both tails with ratio $\rho = (1 - (m + 1)^{-2})^{n/2} \le e^{-2}$, yielding $(-1)^m A_n(-\sigma_m) \ge 1.21^{n/2}(1 - 2e^{-2}) > 1$.
   - **Regime B** ($(m + 1)^2 > n / 4$, $m \le K$): Take $\theta = (m + 1)\pi / (n + 1)$, $L = \pi \cot \theta$, $\sigma_m = e^{-L}$. In the polylogarithm pole expansion $\mathrm{Li}_{-n}(-\sigma) = 2\, n! \sum_{j \ge 1\text{ odd}} \mathrm{Re}(L + i\pi j)^{-(n+1)}$, the $j = 1$ term has exact sign $(-1)^{m+1}$, the tail ratio $\tau$ satisfies $\tau \le 0.038$ by a sharp integral bound, and combining $(1 + \sigma)^{n+2} / \sigma \ge 2(n + 1)$ (binomial expansion + AM–GM) with Stirling's lower bound $n! \ge \sqrt{2\pi n}(n/e)^n$ proves $(1 + \sigma_m)|A_n(-\sigma_m)| > 1$ for every $n \ge 64$.
   - **Junction ordering:** $-\ln \varepsilon_{m_0} \ge n / (m_0 + 1) \ge (n + 1) / (m_0 + 2) > \pi \cot((m_0 + 2)\pi / (n + 1)) = -\ln \sigma^B_{m_0 + 1}$.
4. **Finite range $3 \le n \le 63$:** Certified by exact integer Sturm sequences (and exact rational sign-alternation witnesses).

## Files

- [PROOF.md](PROOF.md) — complete self-contained proof.
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit (`PASS`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/rossi-permutohedron-real-roots/verify.py`).
- [RossiPermutohedronRealRoots.lean](../../lean/Conjectures/RossiPermutohedronRealRoots.lean) — complete Lean 4 formalization (`rossi_conjecture_6_16`, `rossi_full_f_polynomial_real_rooted`, zero `sorry`, standard axioms only).
