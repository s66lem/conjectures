# Fanelli–Moscardelli Stability Threshold Conjecture (ECAI 2025) — Disproved

- **Source:** A. Fanelli and L. Moscardelli, *Approximately Stable Matching*, ECAI 2025, Section 5 (`doi:10.3233/FAIA251234`); `google-deepmind/formal-conjectures` (`FormalConjectures/Paper/ApproximatelyStableMatching.lean`, issue #7848).
- **Conjecture (`stability_threshold_tight`):** $\exists N_0 \ge 3$ such that $\forall N \ge N_0$, $K(N) = \lceil N/2 \rceil$.
- **Result:** **Disproved unconditionally.** For every integer $m \ge 3$ and $N = 2m + 1$, every complete strict roommates profile admits an $m$-stable matching, so
  $$K(2m + 1) \le m < m + 1 = \lceil (2m + 1)/2 \rceil \qquad (\forall m \ge 3).$$
  The threshold $m \ge 3$ is sharp ($K(5) = 3$). DRAT-checked SAT upper bounds and explicit lower-bound profiles further give exact values $K(7) = 3$, $K(8) = 3$, $K(9) = 4$, and $K(11) = 5$.

## Files

- [DISPROOF.md](DISPROOF.md) — full self-contained constructive proof.
- [paper.tex](paper.tex) — arXiv-ready LaTeX manuscript.
- [verify.py](verify.py) — standalone Python 3 implementation of the proof algorithm with exhaustive $O(N^2)$ $m$-blocking checks.

## Verify

```bash
python verify.py
```
