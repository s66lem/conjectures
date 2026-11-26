# Proof of Snellman's Normalized-Volume Monotonicity Conjecture for Rank-Two Kozlov Polytopes (`arXiv:2611.26110v1`)

**Status:** Proved completely for all $n \ge 1$ and $d \ge 0$ (with exact strictness classification and quantitative lower bound) — **Lean 4 verified from Snellman's proved volume formulas** (Corollary `cor-rank2-volume` and Proposition `prop-product-regime`; zero `sorry`, zero custom axioms, zero `native_decide`).

**Preprint:** [doi:10.5281/zenodo.24553538](https://doi.org/10.5281/zenodo.24553538)

## Target Conjecture

Jan Snellman, *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*, [arXiv:2611.26110v1](https://arxiv.org/abs/2611.26110v1) (19 Nov 2026), Conjecture `conj-nv-monotone` (the sole conjecture in the paper):

> **Conjecture.** $\mathrm{NV}(\mathrm{Koz}(n; 0, d))$ is weakly increasing in $d$. (Verified for $n \le 7$ and $0 \le d \le n - 1$; for $d \ge n - 1$ the value is constant, by Proposition `prop-product-regime`.)

## Main Result

Using Snellman's proved volume formula (Corollary `cor-rank2-volume` for $0 \le d \le n - 1$ and Proposition `prop-product-regime` for $d \ge n - 1$),
$$\mathrm{NV}(\mathrm{Koz}(n; 0, d)) = \mathrm{NV}(\mathrm{Koz}(n)) \cdot T(n, \min(d, n - 1)), \qquad T(n, d) = \sum_{j=1}^{n-d} t_d(j),$$
where $\mathrm{NV}(\mathrm{Koz}(n)) = \prod_{k=2}^n \binom{n}{k}$ and $t_d(j) = \binom{n-1+d}{d+j-1} \prod_{k=j+1}^{j+d} \binom{n}{k}$, we prove:

1. **Weak monotonicity (Conjecture `conj-nv-monotone`):** For every $n \ge 1$, $\mathrm{NV}(\mathrm{Koz}(n; 0, d))$ is weakly increasing in $d \ge 0$.
2. **Quantitative lower bound:** For every $n \ge 2$ and $0 \le d \le n - 2$,
   $$T(n, d + 1) - T(n, d) \ge \left(\binom{n}{d} - 1\right) t_d(n - d) \ge 0.$$
3. **Exact strictness classification:** For $n \ge 2$ and $0 \le d \le n - 2$, the increase $\mathrm{NV}(\mathrm{Koz}(n; 0, d + 1)) > \mathrm{NV}(\mathrm{Koz}(n; 0, d))$ is **strict**, with the sole exception $(n, d) = (2, 0)$ where $\mathrm{NV}(\mathrm{Koz}(2; 0, 0)) = \mathrm{NV}(\mathrm{Koz}(2; 0, 1)) = 2$.

## Proof Summary

For $n \ge 2$ and $0 \le d \le n - 2$:
1. **Termwise growth:** Every surviving cell $1 \le j \le n - d - 1$ satisfies
   $$(d + j)\, t_{d+1}(j) = (n + d) \binom{n}{j + d + 1} t_d(j) > (d + j)\, t_d(j),$$
   so $t_{d+1}(j) > t_d(j)$ strictly.
2. **Last surviving cell pays for the dropped cell:** At $j = n - d - 1$, $\binom{n}{n} = 1$ gives
   $$(n - 1)\, t_{d+1}(n - d - 1) = (n + d)\, t_d(n - d - 1),$$
   while comparing adjacent cells $j = n - d - 1$ and $j = n - d$ yields
   $$(d + 1)\, t_d(n - d - 1) = (n - 1) \binom{n}{d} t_d(n - d).$$
   Combining the two identities and canceling $n - 1 > 0$ gives the exact identity
   $$t_{d+1}(n - d - 1) - t_d(n - d - 1) = \binom{n}{d} t_d(n - d).$$
3. **Conclusion:** Summing over $1 \le j \le n - d - 1$ and subtracting the single dropped cell $t_d(n - d)$ yields $T(n, d + 1) - T(n, d) \ge \bigl(\binom{n}{d} - 1\bigr) t_d(n - d) \ge 0$. Strictness follows immediately from $\binom{n}{d} \ge 2$ for $1 \le d \le n - 2$, and from the strict increase of the $j = 1$ cell when $d = 0$ and $n \ge 3$.

*Scope note:* The Lean 4 formalization defines `nvRank2` directly from Snellman's proved volume formula (Corollary `cor-rank2-volume` and Proposition `prop-product-regime`) and formally proves the monotonicity, strictness, quantitative lower bound, and boundary identities (`d = 0` and `d ≥ n - 1`).

## Files

- [PROOF.md](PROOF.md) — complete self-contained mathematical proof.
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — typeset preprint.
- [verify.py](verify.py) — standalone stdlib-only Python verifier (`python -O -W error results/snellman-kozlov-volume/verify.py`).
- [SnellmanKozlovVolume.lean](../../lean/Conjectures/SnellmanKozlovVolume.lean) — complete Lean 4 formalization (`lake build Conjectures.SnellmanKozlovVolume`).
- [AUDIT.md](AUDIT.md) — independent cross-model adversarial audit report.
