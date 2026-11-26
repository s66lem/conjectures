# Proof of Werner Schulte's OEIS A397048 Conjectures (Shifted Falling-Factorial Connection Coefficients)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24562734.svg)](https://doi.org/10.5281/zenodo.24562734)

**Status:** Proved completely (all three open conjectures plus the general base-point $c \ge 0$ Stirling shift theorem) — **Lean 4 verified** (zero `sorry`, zero custom axioms, zero `native_decide`) and independently cross-model audited.

## Target Conjectures

Werner Schulte, [OEIS A397048](https://oeis.org/A397048) (June 14, 2026; revision #34):

$$T(n, k) = \frac{(-1)^k}{k!} \sum_{i=0}^{k} (-1)^i \binom{k}{i} (n + i)^n \qquad (0 \le k \le n).$$

> **Conjecture 1:** $T(n, k) = \sum_{i=0}^{n - k} s(n, k + i)\, S(n + k + i, n + k)$, where $s = \mathrm{A048994}$ (signed Stirling numbers of the first kind) and $S = \mathrm{A048993}$ (Stirling numbers of the second kind).
>
> **Conjecture 2:** The row sums $\sum_{k=0}^{n} T(n, k)$ equal $\mathrm{A134980}(n) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} B_j$, where $B_j = \mathrm{A000110}(j)$ is the $j$-th Bell number.
>
> **Conjecture 3:** $\sum_{i=0}^{k} T(n, i)\, \dfrac{k!}{(k - i)!} = (n + k)^n$.

## Main Result

For any base point $c \ge 0$ and integers $n, k \ge 0$, define
$$T_c(n, k) = \frac{1}{k!} \sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (c + i)^n,$$
so that $T(n, k) = T_n(n, k)$.

**Theorem.** For all integers $c, n, k \ge 0$:
1. **(Falling-factorial expansion & integrality)** $(x + c)^n = \sum_{k=0}^{n} T_c(n, k)\, (x)_k$ in $\mathbb{Q}[x]$, with $T_c(n, k) = \sum_{j=0}^{n} \binom{n}{j} c^{n - j} S(j, k) \in \mathbb{N}$ and $T_c(n, k) = 0$ for $k > n$.
2. **(General Stirling shift identity & Conjecture 1)**
   $$T_c(n, k) = \sum_{m=0}^{c} s(c, m)\, S(n + m, c + k).$$
   Setting $c = n$ (where $S(n + m, n + k) = 0$ for $m < k$) yields Conjecture 1 for every $0 \le k \le n$.
3. **(Conjecture 2)** $\sum_{k=0}^{n} T(n, k) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} B_j = \mathrm{A134980}(n)$.
4. **(Conjecture 3)** For every $n, k \ge 0$ (including $k > n$), $\sum_{i=0}^{k} T(n, i)\, \frac{k!}{(k - i)!} = (n + k)^n$.

## Proof Summary

Expand $(x + c)^n = \sum_{j=0}^{n} \binom{n}{j} c^{n - j} x^j$ and substitute $x^j = \sum_{k} S(j, k) (x)_k$ to express $(x + c)^n$ in the falling-factorial basis $\{(x)_k\}$. Binomial inversion using $\sum_{i=0}^{k} (-1)^{k-i} \binom{k}{i} (i)_m = k!\, \delta_{k, m}$ identifies the $k$-th coefficient with the OEIS formula $T_c(n, k)$, immediately yielding integrality, vanishing for $k > n$, Conjecture 2 (by summing over $k$), and Conjecture 3 (by evaluating at $x = k$). Shifting $x \mapsto x - c$ and multiplying by $(x)_c$ via $(x)_c (x - c)_k = (x)_{c+k}$ gives $x^n (x)_c = \sum_k T_c(n, k) (x)_{c+k}$; expanding the left-hand side via $(x)_c = \sum_m s(c, m) x^m$ and $x^{n+m} = \sum_K S(n + m, K) (x)_K$ and comparing coefficients of $(x)_{c+k}$ proves the general Stirling shift identity and Conjecture 1.

## Files

- [PROOF.md](PROOF.md) — complete self-contained proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/schulte-a397048/verify.py`).
- [SchulteA397048.lean](../../lean/Conjectures/SchulteA397048.lean) — complete Lean 4 formalization (`lake build Conjectures.SchulteA397048`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
