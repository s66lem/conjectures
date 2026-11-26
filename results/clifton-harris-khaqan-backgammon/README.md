# Resolution of Clifton–Harris–Khaqan Question 5.2 (`arXiv:2611.29890v1`, Backgammon Parking Motzkin Enumeration)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24564921.svg)](https://doi.org/10.5281/zenodo.24564921)

**Status:** Resolved affirmatively for every $n \ge k \ge 1$ with an explicit closed-form Motzkin-power formula and general car-$1$ prefix-length reduction lemma — **Lean 4 verified** ([CliftonHarrisKhaqanBackgammon.lean](../../lean/Conjectures/CliftonHarrisKhaqanBackgammon.lean)) & independently cross-model audited ([AUDIT.md](AUDIT.md)).

## Target Question

A. Clifton, P. E. Harris, and M. Khaqan, *Parking functions inspired by board games*, [arXiv:2611.29890v1](https://arxiv.org/abs/2611.29890v1) (23 Nov 2026), §5 (Future directions):

> **Question 5.2.** For fixed $k \in \mathbb{N}$, can $|\mathcal{O}_B^{-1}(12\cdots(k-1)(k)(n)(n-1)\cdots(k+2)(k+1))|$ for $n > k$ be expressed as a sum involving Motzkin numbers whose indices depend on $n$?

Under the backgammon parking scheme, cars $1, \dots, n$ arrive in order with preferences $\alpha = (a_1, \dots, a_n) \in [n]^n$: car $i$ takes spot $a_i$, and if a car was already parked there, that displaced car moves to the leftmost unoccupied spot. The outcome $\mathcal{O}_B(\alpha) = \pi \in S_n$ records the car ending in each spot. The paper proved only $k = 0$ ($M_n$, Theorem 1.8), $k = 1$ ($M_{n+1} - M_n$, Corollary 1.9), and $k = 2$ ($M_{n+2} - 2M_{n+1} + M_n - M_{n-1}$, Corollary 1.10).

## Main Result

Write $\pi_k(n) = 12\cdots k\, n(n-1)\cdots(k+1)$, $T(n, k) = |\mathcal{O}_B^{-1}(\pi_k(n))|$, $m(x) = \sum_{n \ge 0} M_n x^n$ for the Motzkin generating function ($m = 1 + x m + x^2 m^2$), and $B(r, i) = \frac{r - i + 1}{r + 1} \binom{r + i}{i}$ ($0 \le i \le r$) for Catalan's triangle (recursively $B(0, 0) = 1$, $B(r, i) = \sum_{t=0}^{\min(i, r-1)} B(r - 1, t)$).

**Theorem.** For every $k \ge 1$,
$$\sum_{n \ge k} T(n, k)\, x^n = x^k \sum_{i=0}^{k-1} B(k - 1, i)\, m(x)^{k + 1 - i}.$$
Equivalently, for all integers $n \ge k \ge 1$,
$$T(n, k) = \sum_{i=0}^{k-1} B(k - 1, i)\, M^{(k + 1 - i)}_{n - k}, \qquad M^{(r)}_N := \sum_{N_1 + \dots + N_r = N} M_{N_1} \cdots M_{N_r}.$$
Using $x^2 m^2 = (1 - x) m - 1$, each $T(n, k)$ also reduces to an explicit signed linear combination of Motzkin numbers $M_{n + k}, \dots, M_{n - k + 1}$ (recovering Theorem 1.6, Theorem 1.8, Corollary 1.9, and Corollary 1.10, and giving explicit formulas for $k = 3, 4, \dots$).

## Proof Summary

For any outcome $\pi$, define $P_\pi(y) = \sum_{\alpha \in \mathcal{O}_B^{-1}(\pi)} y^{L(\alpha)}$, where $L(\alpha)$ is the length of the longest prefix of pairwise distinct entries of $\alpha$, and define the linear operator $\Phi(y^j) = y + y^2 + \dots + y^{j+1}$.
1. **General car-$1$ reduction (Lemma A):** For every $\sigma \in S_{n-1}$, $P_{1 \oplus \sigma}(y) = \Phi(P_\sigma(y))$, proved by a clean two-case bijection ($a_1 = 1$ vs. $a_1 \ne 1$, where the first bump in the entire process must displace car $1$ into spot $1$).
2. **Decreasing-outcome recurrence (Lemma B):** For $\delta_n = n(n-1)\cdots 1$ ($n \ge 2$), $P_{\delta_n}(y) = y P_{\delta_{n-1}}(y) + P_{1 \oplus \delta_{n-2}}(y)$, yielding the exact bivariate generating function $A_0(x, y) = \sum_{n \ge 0} P_{\delta_n}(y) x^n = (1 - y p(x))^{-1}$ with $p(x) = x + x^2 m(x)$ and $m = (1 - p)^{-1}$.
3. **Catalan-triangle operator expansion (Lemma C):** Iterating Lemma A gives $A_k(x, 1) = x^k \sum_{j \ge 0} \Phi^k(y^j)|_{y=1}\, p^j$, and induction on $k$ via division by $m - 1 = pm$ proves $\sum_{j \ge 0} \Phi^k(y^j)|_{y=1}\, p^j = \sum_{i=0}^{k-1} B(k - 1, i)\, m^{k + 1 - i}$.

## Files

- [PROOF.md](PROOF.md) — complete self-contained proof.
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint ([DOI: 10.5281/zenodo.24564921](https://doi.org/10.5281/zenodo.24564921)).
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/clifton-harris-khaqan-backgammon/verify.py`).
- [CliftonHarrisKhaqanBackgammon.lean](../../lean/Conjectures/CliftonHarrisKhaqanBackgammon.lean) — Lean 4 formalization.
