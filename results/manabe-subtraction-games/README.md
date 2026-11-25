# Proof of Manabe's Conjecture 57 (Admissible Angles for Three-Move Subtraction Games)

Complete proof and Lean 4 formal verification settling **Conjecture 57** of Hikaru Manabe, *Purely Periodic Three-move Subtraction Games* (`arXiv:2609.05358v2`), in a strictly stronger form, together with the full equivalence **Conjecture 52 $\iff$ Conjecture 56** for every $c > b$ and partial period exclusions toward Conjecture 56.

## Main Results

1. **Conjecture 57 proved in full (strengthened):** For every triple of integers $1 \le a < b < c$ (without requiring $a \ge 2$, $\gcd(a,b,c) = 1$, $c \neq a + b$, or minimality of the period), the $\mathrm{P}$-position set $\mathcal{W}_0(S)$ is purely periodic of period:
   - $a + b$ if and only if $\rho \in \Theta_{a+b}$ (extending Manabe's Lemma 54 / Proposition 55 from $c \ge 2(a+b)$ to all $c > b$);
   - $c + a$ if and only if $\rho \in \Theta_{c+a}$;
   - $c + b$ if and only if $\rho \in \Theta_{c+b}$.
2. **Closed-form cyclic-interval characterization of $\Theta_{c+b}$:** Writing $\delta = b - a = \eta a + \varepsilon$ ($0 \le \varepsilon < a$), $\rho \in \Theta_{c+b}$ holds iff $(\rho - j) \bmod (a+b) \in \mathcal{Z}$ for all $1 \le j \le \varepsilon$ ($\eta$ even) or all $\varepsilon + 1 \le j \le a$ ($\eta$ odd).
3. **Conjecture 52 $\iff$ Conjecture 56 for every $c > b$:** Removes both Conjecture 57 and the $c \ge 2(a+b)$ hypothesis from Manabe's Proposition 59.
4. **Partial period exclusions toward Conjecture 56 + $100.9\text{M}$-triple census:** No pure $\mathrm{P}$-position period lies in $(c - a, c + a)$, and any pure period $p > 0$ with $c \ge p + (a + b) - \gcd(p, a + b)$ (including $(a + b) \mid p$) forces $\rho \in \Theta_{a+b}$. Exact cycle detection across $100{,}946{,}926$ primitive non-additive triples found zero counterexamples to Conjectures 52 or 56, even at the $\mathrm{P}$-position level.

## Files

- [`PROOF.md`](PROOF.md) — Self-contained proof of Theorems 3.2–3.4, Corollaries 4.1–4.2, and Proposition 4.3.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 formal verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe: matches Example 1 and Manabe's $7{,}557 / 7{,}828$ census and verifies all theorems on $15{,}000+$ unrestricted triples).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/ManabeSubtraction.lean`](../../lean/Conjectures/ManabeSubtraction.lean) — Lean 4 formalization (`period_ab_iff`, `period_ca_iff`, `period_cb_iff`, `Theta_cb_iff_explicit`, `manabe_conjecture_57`, `no_period_in_open_interval`, `fine_wilf_period_implies_Theta_ab`).

## Reproduction

```bash
python3 -O results/manabe-subtraction-games/verify.py
cd lean && lake build Conjectures.ManabeSubtraction
```
