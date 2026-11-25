# Tree Stacking Conjecture (Conj. 5.6) & Literal ASH (Hyp. 3.2) — `arXiv:2610.09650`

- **Source:** T. Csernák and D. T. Soukup, *The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem*, `arXiv:2610.09650` (Oct 2026).
- **Results:**
  1. **Conjecture 5.6 proved unconditionally:** Every finite connected tree $T$ satisfies $\mathrm{stack}(T) = \mathrm{estim}(T)$ without assuming the Almost Stacked Hypothesis, via a constructive bottom-up greedy potential and fractional relaxation ($O(n^2)$ stacking algorithm).
  2. **Literal Hypothesis 3.2 (ASH) disproved** for both stacking and clearing due to non-monotonicity of almost-stacked pebblability:
     - *Stacking ($P_4$):* least almost-stacked threshold is $12$ (all $32$ almost stacked configs stack), yet $(9,0,0,3)$ does not stack and $\mathrm{stack}(P_4) = 15$.
     - *Clearing ($G_5$, triangle + 2-edge tail):* least almost-stacked threshold is $16$ (all $80$ almost stacked configs clear), yet $(0,0,0,2,14)$ does not clear and $\mathrm{clear}(G_5) = 22$.

## Files

- [RESULTS.md](RESULTS.md) — full proof of Conjecture 5.6 and disproof details for Hypothesis 3.2.
- [paper.tex](paper.tex) — arXiv-ready LaTeX manuscript.
- [verify.py](verify.py) — standalone Python 3 verifier (exact BFS for $P_4$ and $G_5$ + Lemmas A–F and move simulation across trees $n \le 30$).

## Verify

```bash
python verify.py
```
