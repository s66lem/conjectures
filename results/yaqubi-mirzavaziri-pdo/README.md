# Yaqubi–Mirzavaziri Conjecture 6.2 (`arXiv:2611.05623v1`)

**Status:** Proved unconditionally for every $k \ge 1$ · **Lean 4 verified** (zero `sorry`, zero custom axioms) · **Cross-model audited** · **Preprint:** [10.5281/zenodo.24552279](https://doi.org/10.5281/zenodo.24552279)

## Problem Statement

Let $f_m := \prod_{j \ge 1}(1 - q^{mj})$, let
$$G(q) := \frac{f_4 f_6^2}{f_1 f_3 f_{12}} = \sum_{n \ge 0} \mathrm{PDO}(n)\,q^n$$
be the generating function for partitions into odd parts with designated summands, and let $B_k(n) := [q^n] G(q)^k$ count ordered $k$-tuples of such partitions of total weight $n$.

> **Conjecture 6.2** (D. Yaqubi and M. Mirzavaziri, *Partitions with designated summands: $k$-tuples and their congruences*, [`arXiv:2611.05623v1`](https://arxiv.org/abs/2611.05623v1), 3 Nov 2026). For every integer $k \ge 1$, the largest power of $2$ dividing $B_k(4n+3)$ for all $n \ge 0$ is $2^{v_2(B_k(3))}$, except when $k \equiv 1 \pmod 8$ (where it is exactly $2^2$) or $k \equiv 6 \pmod 8$ (where it is exactly $2^3$).

## Resolution Summary

We prove Conjecture 6.2 completely for every $k \ge 1$, establishing that the exact $2$-adic valuation $\min_{n \ge 0} v_2(B_k(4n+3))$ equals:

| Residue of $k \pmod 8$ | Exact $\min_{n \ge 0} v_2(B_k(4n+3))$ | Exactness witness |
|---|---|---|
| $k \equiv 3, 7 \pmod 8$ | $0 = v_2(B_k(3))$ | $n = 0$ ($B_k(3)$) |
| $k \equiv 5 \pmod 8$ | $1 = v_2(B_k(3))$ | $n = 0$ ($B_k(3)$) |
| $k \equiv 1 \pmod 8$ | $2$ (strictly below $v_2(B_k(3)) \ge 3$ when $k \equiv 9 \pmod{16}$) | $n = 0$ ($k \equiv 1 \pmod{16}$), $n = 1$ ($B_k(7)$, $k \equiv 9 \pmod{16}$) |
| $k \equiv 2 \pmod 8$ | $2 = v_2(B_k(3))$ | $n = 0$ ($B_k(3)$) |
| $k \equiv 6 \pmod 8$ | $3$ (strictly below $v_2(B_k(3)) \ge 4$ when $k \equiv 14 \pmod{16}$) | $n = 0$ ($k \equiv 6 \pmod{16}$), $n = 1$ ($B_k(7)$, $k \equiv 14 \pmod{16}$) |
| $k \equiv 0, 4 \pmod 8$ | $v_2(k) = v_2(B_k(3))$ | $n = 0$ ($B_k(3)$) |

The proof is self-contained modulo Mathlib's pentagonal number theorem (`PowerSeries.pentagonalSeries`) and formalized end-to-end in Lean 4 without assuming any external dissection or modular-form results. In Lean 4, $G(q)$ is defined directly via the paper's eta quotient $f_4 f_6^2 / (f_1 f_3 f_{12})$, while `verify.py` additionally cross-checks $G(q)$ against the combinatorial product $\prod_{t \ge 1\text{ odd}}(1 + \sum_{m \ge 1} m\,q^{tm})$ for partitions into odd parts with designated summands:

1. **Finite polynomial Jacobi triple product → Gauss identities:** Proves $f_2(q)\varphi(-q) = f_1(q)^2$ and $f_1(q)\psi(q) = f_2(q)^2$ directly from Mathlib's pentagonal number theorem (`gauss_J2`, `gauss_J1`).
2. **Bijective $\psi(q)\psi(q^3)$ dissection:** Proves $\psi(q)\psi(q^3) = \varphi(q^6)\psi(q^4) + q\varphi(q^2)\psi(q^{12})$ via an explicit finite bijection on odd-square representations (`psi_mul_psi3`).
3. **Exact $2$-dissection of $G$ and congruences `(P1)`–`(P3)`:** Proves $4 \mid B_1(4n+3)$, $4 \mid B_2(4n+3)$, and $8 \mid B_{8s+6}(4n+3)$ purely algebraically in $(\mathbb{Z}/2\mathbb{Z})[[q]]$ and $(\mathbb{Z}/4\mathbb{Z})[[q]]$ (`cong_P1`, `cong_P2`, `cong_P3`).
4. **Frobenius congruences and exactness certificates:** Proves $2^{v_2(k)} \mid B_k(2m+1)$ for all odd indices (`dvd_B_odd`), reduces $k \equiv 1 \pmod 4$, $k \equiv 1 \pmod 8$, and $k \equiv 2 \pmod 8$ (`cong_mod2_1mod4`, `cong_mod4_1mod8`, `cong_mod4_2mod8`), proves $6 B_k(3) = k(k+2)(k+7)$ (`six_mul_B_three`), and proves $B_k(7)$ has period $32$ modulo $8$ with $B_9(7) \equiv B_{25}(7) \equiv 4 \pmod 8$ and period $64$ modulo $16$ with $B_{14}(7) \equiv B_{30}(7) \equiv B_{46}(7) \equiv B_{62}(7) \equiv 8 \pmod{16}$ (`not_eight_dvd_B_seven_9mod16`, `not_sixteen_dvd_B_seven_14mod16`).

## Files

- [`PROOF.md`](./PROOF.md) — Complete human-readable proof.
- [`paper.tex`](./paper.tex) / [`paper.pdf`](./paper.pdf) — Publication-ready LaTeX paper.
- [`verify.py`](./verify.py) — Standalone Python stdlib verifier (`python -O -W error verify.py`).
- [`AUDIT.md`](./AUDIT.md) — Independent cross-model adversarial audit report.
- [`../../lean/Conjectures/YaqubiMirzavaziriPDO.lean`](../../lean/Conjectures/YaqubiMirzavaziriPDO.lean) — Complete Lean 4 formalization (`yaqubi_mirzavaziri_conjecture_6_2`).
