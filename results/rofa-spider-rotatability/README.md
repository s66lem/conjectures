# Proof of Rofa's Regular Spider 0-Rotatability Conjecture

Self-contained proof and Lean 4 formal verification settling **Rofa's regular (symmetric) spider 0-rotatability conjecture** (R. I. Rofa, `arXiv:2312.16235`, §1 & Summary; revisited for $\ell = 4$ in `arXiv:2611.29448`):

> **Theorem.** For every pair of positive integers $k, \ell \ge 1$ and every vertex $v$ of the regular spider tree $T(k, \ell)$ ($k$ legs of uniform length $\ell$ meeting at a central root $v_0$), there exists a graceful labeling $f : V(T(k, \ell)) \to \{0, 1, \dots, k\ell\}$ satisfying $f(v) = 0$.

Previously, 0-rotatability of $T(k, \ell)$ was established only for $\ell \le 3$ (Rofa, 2023) and $\ell = 4$ (`arXiv:2611.29448`, Nov 2026). This resolves all $\ell \ge 1$ and all $k \ge 1$ simultaneously. (Note: Rofa's abstract also states a broader conjecture for arbitrary irregular spiders; the present theorem settles the symmetric/regular spider conjecture completely.)

## Main Ingredients

1. **General $\alpha$-labeled leg-attachment lemma:** Given any $\alpha$-labeled finite tree (or graph) $H$ on $s$ edges with threshold $a$ and attachment vertex $v_0$ having label $c \le a$ with $0 \le a - c \le \ell - 1$, attaching $m \ge 0$ legs of length $\ell$ at $v_0$ admits a graceful labeling fixing $0$ and mapping $s \mapsto s + m\ell$.
2. **Unified self-contained proofs of both path theorems:** Using odd-sum permutations and the Walecki map, we give self-contained constructive proofs of both Rosa's path $\alpha$-labeling theorem (1977) and the arbitrary-start graceful path theorem (Flandrin–Fournier–Germa 1983 / Cattell 2007), formalized without axioms in Lean 4.
3. **Single exceptional case $(\ell, d) = (4, 2)$:** Handled by $(1,4,0,2,3)$ for $k = 1$ and the two-leg $\alpha$-labeled seed $(2,6,0,8,1), (2,7,4,5,3)$ with threshold $a = 4$ and root $c = 2$ for all $k \ge 2$.

## Files

- [`PROOF.md`](PROOF.md) — Self-contained proof (including explicit constructions of both path theorems and the leg-attachment lemma).
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial referee audit and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, implementing the exact recursive construction from the Lean 4 proof).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/SpiderRotatability.lean`](../../lean/Conjectures/SpiderRotatability.lean) — Self-contained Lean 4 formalization (`rosa_path_alpha`, `graceful_path_start`, `attach_legs_graceful`, `regular_spider_zero_rotatable`).

## Reproduction

```bash
python3 results/rofa-spider-rotatability/verify.py
cd lean && lake build Conjectures.SpiderRotatability
```
