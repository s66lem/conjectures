# Disproof of Campbell's OEIS A189409 Squarefree Conjecture

Complete disproof and exact minimality proof for John M. Campbell's 2011 open question on [OEIS A189409](https://oeis.org/A189409) (also listed open in `google-deepmind/formal-conjectures`, `FormalConjectures/OEIS/189409.lean`, `OeisA189409.conjecture_1`), which asked whether every term of $a(n) = (p_n\#)^2 + 1$ (where $p_n\# = \prod_{k=0}^{n-1} p_k$ is the $n$-th primorial, OEIS A002110) is squarefree.

## Main Results

1. **Counterexample at $n = 9$:**
   $$p_9\# = 223{,}092{,}870, \qquad a(9) = 223{,}092{,}870^2 + 1 = 49{,}770{,}428{,}644{,}836{,}901 = 29^2 \cdot 53 \cdot 1{,}116{,}604{,}864{,}937,$$
   so $29^2 \mid a(9)$ and $a(9)$ is not squarefree.
2. **Exact minimality:** Every earlier term $a(0), a(1), \dots, a(8)$ is squarefree (with all large prime factors up to the $14$-digit prime $a(8) = 94{,}083{,}986{,}096{,}101$ certified deterministically via Lucas primality certificates).
3. **Lean 4 formal verification:** All main theorems (`a_9_not_squarefree`, `disproof_conjecture_1`, `a_9_factorization`, `squarefree_lt_9`, `minimal_counterexample`) are formally verified in Lean 4 directly in the kernel (zero `sorry`, zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only).

## Files

- [`PROOF.md`](PROOF.md) — Statement, modular divisibility proof, exact minimality table, and range-scan remark.
- [`AUDIT.md`](AUDIT.md) — Cross-model audit summary, Lean 4 axiom log, and verification checklist.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/CampbellA189409.lean`](../../lean/Conjectures/CampbellA189409.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/campbell-oeis-a189409/verify.py
cd lean && lake build Conjectures.CampbellA189409
```
