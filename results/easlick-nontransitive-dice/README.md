# Proof of Conjecture 1 of Easlick (`arXiv:2610.40321v2`)

Complete proof and Lean 4 formalization of **Conjecture 1** from Terry Easlick, *Computer-Assisted Results for $n$-Sided Non-Transitive Dice Taking Face Values in $[n]$* ([arXiv:2610.40321v2](https://arxiv.org/abs/2610.40321), November 2026).

## Main Results

1. **Complete proof of Conjecture 1 (`easlick_conjecture1`):** For every integer $n \ge 7$, the minimal-advantage directed graph $G_n$ on non-standard $n$-sided dice with face values in $\{1, \dots, n\}$ contains a simple directed cycle of length at least $n + 1$. Combined with Easlick's Theorem 1 ($n \le 6$, independently re-verified exhaustively in `verify.py`), $n = 6$ is the unique integer $n \ge 3$ with maximum cycle length equal to $n$.
2. **Linear-rate lower bounds (`odd_cycle_exists`, `even_cycle_exists`):** Explicit 3-die zipper constructions produce simple cycles of length $3(n - 7)$ for every odd $n \ge 11$ and length $3(n - 10)$ for every even $n \ge 16$ (plus a 7-base zipper of length $15$ at $n = 14$ and kernel-verified cycles of length $n + 1$ for $n \in \{7, 8, 9, 10, 12\}$).
3. **Generalized antiautomorphism (`flipDie_antiautomorphism`):** Proves that face reversal $f(x_1, \dots, x_n) = (n + 1 - x_n, \dots, n + 1 - x_1)$ is an involutive antiautomorphism of $G_n$ for all $n$.
4. **Lean 4 formal verification:** The entire $n \ge 7$ proof, `n6_has_cycle_6`, and `flipDie_antiautomorphism` are formally verified in [`lean/Conjectures/EaslickNontransitiveDice.lean`](../../lean/Conjectures/EaslickNontransitiveDice.lean) using only `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`); the $n \le 6$ upper bounds of Easlick's Theorem 1 are independently re-verified exhaustively in `verify.py`.

## Files

- [`PROOF.md`](PROOF.md) — Complete self-contained proof.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 axiom log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks; exhaustively verifies $G_3$–$G_6$ via Tarjan's SCC algorithm and verifies cycles for $7 \le n \le 101$).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/EaslickNontransitiveDice.lean`](../../lean/Conjectures/EaslickNontransitiveDice.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/easlick-nontransitive-dice/verify.py
cd lean && lake build Conjectures.EaslickNontransitiveDice
```
