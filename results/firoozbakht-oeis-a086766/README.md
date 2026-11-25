# Disproof of Firoozbakht's OEIS A086766 Conjecture

Complete disproof of Farideh Firoozbakht's 2015 conjecture on [OEIS A086766](https://oeis.org/A086766) (also listed open in `google-deepmind/formal-conjectures`, `FormalConjectures/OEIS/86766.lean`, `OeisA86766.conjecture2`), which asserted that if $n > 0$ is not a power of $10$, then there exists $r \ge 1$ such that concatenating $n$ with itself $r$ times, multiplying by $10$, and adding $1$ yields a prime (i.e., $a(n) \ne 0$).

## Main Results

1. **Minimal counterexample ($4$ digits) & infinite family:** For every $k \ge 2$, the $2k$-digit integer $n_k = \frac{10(10^{2k} - 1)}{99}$ (starting at **`n = 1010`**, $101010, \dots$) is not a power of $10$ and satisfies $a(n_k) = 0$: for every $r \ge 1$,
   $$f_{n_k}(r) = \frac{10^{2(kr+1)} - 1}{99}$$
   splits algebraically as $\frac{10^{kr+1} - 1}{9} \cdot \frac{10^{kr+1} + 1}{11}$ (when $kr$ is even) or $\frac{10^{kr+1} - 1}{99} \cdot (10^{kr+1} + 1)$ (when $kr$ is odd), with both factors strictly greater than $1$.
2. **Primitive (non-periodic) counterexamples — including a $78$-digit witness:** For any even digit length $d = 2k$ and factorization $10^d - 1 = u v$ with $u < v$, $20 \mid (u + v)$, and $c = (u+v)/2$, $e = (v-u)/2$ giving $n = c^2 / 10 \in (10^{d-1}, 10^d)$, the identity
   $$(10^d - 1) f_n(r) = (c \cdot 10^{kr} - e)(c \cdot 10^{kr} + e)$$
   forces $f_n(r)$ to be composite for every $r \ge 1$ via parity-dependent divisor splits of $10^d - 1$. Examples:
   - Minimal $6$-digit primitive: **`n = 104040`** ($c = 1020, e = 201$),
   - Giant $78$-digit primitive:
     `n = 100558839880907801793259217884670002826017800775406752876641328923179557019040`.
3. **Lean 4 formal verification:** All four theorems (`disproof_minimal_1010`, `disproof_infinite_family`, `disproof_primitive_104040`, `disproof_giant78`) are formally verified in Lean 4 against the verbatim `FormalConjectures/OEIS/86766.lean` definition with zero `sorry` and standard axioms only.

## Files

- [`PROOF.md`](PROOF.md) — Verbatim statement, algebraic difference-of-squares theorem, infinite family, primitive witnesses, and 78-digit example.
- [`AUDIT.md`](AUDIT.md) — Live OEIS verification, algebraic audit, and Lean 4 axiom log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/FiroozbakhtA086766.lean`](../../lean/Conjectures/FiroozbakhtA086766.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/firoozbakht-oeis-a086766/verify.py
cd lean && lake build Conjectures.FiroozbakhtA086766
```
