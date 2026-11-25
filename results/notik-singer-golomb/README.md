# Proof of Notik's Singer Golomb Ruler Chamber-Uniqueness Conjecture

Complete proof and Lean 4 formal verification of the **Singer Golomb ruler chamber-uniqueness conjecture** from Section 7 of Esther Notik, *Golomb rulers with real marks: the real and integer optima agree up to ten marks* (`arXiv:2611.22656`).

## Main Results

1. **Chamber-uniqueness for all cyclic perfect difference sets (hence all Singer Golomb rulers):** For every cyclic perfect difference set $D \subset \mathbb{Z}/N\mathbb{Z}$ with $|D| \ge 2$ (in particular, every Singer difference set of order $m$ for every prime power $m$, under any unit multiplier and translation), its largest cyclic gap $G$ is unique, and cutting $D$ after $G$ produces a Golomb ruler $x = (0 = x_1 < \dots < x_n = N - G)$ that is the **unique shortest real Golomb ruler in its chamber $P_\sigma$**.
2. **Stronger componentwise gap-dominance & explicit integer dual certificate:** For every real ruler $y \in P_\sigma$, every retained successive gap satisfies $y_{i+1} - y_i \ge x_{i+1} - x_i$, proved directly from the consecutive-rank chamber inequalities for differences $1, \dots, G - 1$. Equivalently, the positive integer dual multipliers $\lambda_r = |\{i \in \{1, \dots, n - 1\} : h_i \ge r\}|$ ($1 \le r \le G - 1$) telescope to $\sum_{r=1}^{G-1} \lambda_r (\Delta_r(y) - \Delta_{r-1}(y)) = y_n \ge \sum_{r=1}^{G-1} \lambda_r = N - G$.
3. **Full Lean 4 formalization including Singer's existence theorem:** Both the general chamber-uniqueness theorem (`pds_largest_gap_unique_shortest`) and Singer's existence theorem for every prime power (`singer_pds_exists`) are verified in Lean 4 with zero `sorry` and standard axioms only.

## Files

- [`PROOF.md`](PROOF.md) — Self-contained proof with the prefix-rank argument and explicit integer dual certificate.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit, large-order computational verification log, and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/SingerGolombChamber.lean`](../../lean/Conjectures/SingerGolombChamber.lean) — Lean 4 formalization (`pds_largest_gap_unique_shortest`, `singer_pds_exists`, `IsCyclicPDS.mul_unit`, `IsCyclicPDS.translate`).

## Reproduction

```bash
python3 results/notik-singer-golomb/verify.py
cd lean && lake build Conjectures.SingerGolombChamber
```
