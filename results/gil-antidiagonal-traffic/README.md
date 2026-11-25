# Proof of Conjecture 7.4 of Gil–Liang–Odetola–Weiner (`arXiv:2609.01562v1`)

Complete proof and Lean 4 formalization of **Conjecture 7.4** from Juan Gil, Zhenni Liang, Ayodeji Odetola, and Michael Weiner, *Points of maximal traffic on a grid with obstruction* ([arXiv:2609.01562v1](https://arxiv.org/abs/2609.01562)).

## Main Results

1. **Conjecture 7.4 proved (`conjecture74_paper`, `conjecture74_proved`):** For every $n \ge 496$ and every $1 \le a < n/2$, $R_n(a) = G(n,a)/D(n) < 1$ (equivalently $2(2n-1)a(n-2a+1)\binom{n}{a}^2 < n(n-1)\binom{2n}{n}$). Thus for every $n \ge 496$ and every obstruction $B$ on the antidiagonal $x+y=n$, the traffic anomaly disappears and the maximum of $f_B$ on $\mathrm{Grid}(n) \setminus \{(0,0),(n,n)\}$ is attained at $(1,1)$ and $(n-1,n-1)$.
2. **Sharpness (`sharpness_R_paper_495_240`, `sharpness_495_240`):** $R_{495}(240) \approx 1.0000240709 > 1$, confirming that $496$ is the exact threshold.
3. **Lean 4 formal verification:** Fully verified in [`lean/Conjectures/GilAntidiagonalTraffic.lean`](../../lean/Conjectures/GilAntidiagonalTraffic.lean) with zero `sorry`, zero `native_decide`, and standard axioms `[propext, Classical.choice, Quot.sound]` only (combining an elementary Stirling-free analytic proof for $n \ge 800$ with unimodality and a certified incremental kernel recurrence for $496 \le n \le 799$).

## Files

- [`PROOF.md`](PROOF.md) — Complete self-contained proof (Lemmas 1–6).
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 axiom log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks across all 6 steps and all $98{,}192$ pairs for $496 \le n \le 799$).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/GilAntidiagonalTraffic.lean`](../../lean/Conjectures/GilAntidiagonalTraffic.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/gil-antidiagonal-traffic/verify.py
cd lean && lake build Conjectures.GilAntidiagonalTraffic
```
