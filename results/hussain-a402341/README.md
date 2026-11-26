# Proof of the OEIS A402341 2-Adic Valuation Conjecture (and General Power-of-Two Block Lengths)

**Status:** Proved for every even $n \ge 0$ (and generalized to every block length $2^r$, $r \ge 1$) — **100% Lean 4 verified** (zero `sorry`, zero custom axioms, zero `native_decide`) · **Cross-model audited** · **Preprint:** [10.5281/zenodo.24552348](https://doi.org/10.5281/zenodo.24552348)

**Target Conjecture:** Sajid Khan Hussain, [OEIS A402341](https://oeis.org/A402341) (created November 17, 2026):
> *"Central (largest) coefficient of $(1 + x + x^2 + \dots + x^{15})^n$."*
> *"Conjecture: for even $n$, the 2-adic valuation of $a(n)$ equals $\text{A000120}(15n/2)$. Verified for $n \le 1500$."*

## Main Result

Let $s_2(t) = \text{A000120}(t)$ denote the binary digit sum (number of $1$s in the binary expansion of $t$). For every integer $r \ge 1$ and every even integer $n = 2m \ge 0$, let $N = (2^r - 1)m$ and let
$$a_r(2m) = [x^N]\left(1 + x + \cdots + x^{2^r - 1}\right)^{2m}.$$
Then:
1. **Strong central-binomial congruence:**
   $$a_r(2m) \equiv \binom{2N}{N} \pmod{2^{s_2(N) + 1}}.$$
2. **Exact 2-adic valuation:**
   $$v_2(a_r(2m)) = s_2\!\left((2^r - 1)m\right).$$

Specializing to $r = 4$ ($2^4 - 1 = 15$) yields the complete proof of the OEIS A402341 conjecture for every even $n \ge 0$:
$$a(2m) \equiv \binom{30m}{15m} \pmod{2^{s_2(15m)+1}}, \qquad v_2(a(n)) = s_2\!\left(\frac{15n}{2}\right) = \text{A000120}\!\left(\frac{15n}{2}\right).$$

The even-parity hypothesis is sharp: for odd $n = 3$, $a(3) = 192 = 2^6 \cdot 3$ has $v_2(192) = 6 \ne s_2(\lfloor 45/2 \rfloor) = s_2(22) = 3$.

## Proof Summary

Write $y = x / (1 + x)^2$ and define integer polynomials recursively by $R_0(y) = 1$ and $R_{k+1}(y) = R_k(y)^2 - 2 y^{2^k}$. By induction,
$$(1 + x)^{2^k} R_k\!\left(\frac{x}{(1+x)^2}\right) = 1 + x^{2^k},$$
so $Q_r(y) = \prod_{k=0}^{r-1} R_k(y)$ satisfies
$$1 + x + \cdots + x^{2^r - 1} = \prod_{k=0}^{r-1}(1 + x^{2^k}) = (1 + x)^{2^r - 1} Q_r\!\left(\frac{x}{(1+x)^2}\right).$$
A polynomial $F(y) = \sum c_j y^j \in \mathbb{Z}[y]$ is *admissible* if $2^{s_2(j)} \mid c_j$ for all $j$, and *strongly admissible* if $c_0 = 1$ and $2^{s_2(j)+1} \mid c_j$ for all $j > 0$. By binary subadditivity $s_2(u+v) \le s_2(u) + s_2(v)$ and $s_2(2^k) = 1$:
- Each $R_k$, and hence $Q_r$, is admissible with constant term $1$.
- Squaring an admissible polynomial with constant term $1$ yields a strongly admissible polynomial (distinct pairs $(u,v),(v,u)$ contribute a factor of $2$, while diagonal terms $u = v > 0$ satisfy $2 s_2(u) \ge s_2(2u) + 1$).
- Strong admissibility is closed under multiplication, so $Q_r(y)^{2m} = \sum_j c_j y^j$ is strongly admissible.

Extracting $[x^N]$ from $(1 + x)^{2N} Q_r(y)^{2m}$ gives
$$a_r(2m) = \sum_{j=0}^{N} c_j \binom{2(N-j)}{N-j}.$$
By Legendre's formula, $v_2\!\left(\binom{2t}{t}\right) = s_2(t)$. The $j = 0$ term is $\binom{2N}{N}$, while every $j > 0$ term is divisible by $2^{s_2(j) + 1 + s_2(N-j)}$, which is a multiple of $2^{s_2(N) + 1}$. Thus $a_r(2m) \equiv \binom{2N}{N} \pmod{2^{s_2(N)+1}}$ and $v_2(a_r(2m)) = s_2(N)$.

## Files

- [PROOF.md](PROOF.md) — complete self-contained mathematical proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/hussain-a402341/verify.py`).
- [HussainA402341.lean](../../lean/Conjectures/HussainA402341.lean) — complete Lean 4 formalization (`lake build Conjectures.HussainA402341`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
