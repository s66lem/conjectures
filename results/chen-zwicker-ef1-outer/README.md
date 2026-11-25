# Disproof of Chen–Zwicker Conjecture 1 ($\mathrm{EF1}_{\mathrm{outer}}$ Spectrum of Connected Graphs)

Counterexample and Lean 4 formal verification refuting **Conjecture 1** of Jiehua Chen and William S. Zwicker (`arXiv:2402.05884`, highlighted in Nicolas Bousquet, Frank Connor, Agnès Totschnig, and Sébastien Zeitoun, *Fair Division of Graphs: Beyond Traceability*, `arXiv:2608.29902v1`), simultaneously across every valuation class from common binary additive up to arbitrary heterogeneous monotone valuations.

## Main Results

1. **Minimal $8$-vertex counterexample $H$:** Let $H$ be the connected $8$-vertex graph obtained from $K_{2, 3}$ (bipartition $\{u, w\} \sqcup \{a, b, c\}$) by attaching one pendant leaf to each of $a, b, c$. For **every** valuation class $\mathcal{V}$ containing the common binary additive valuation $\beta = \mathbf{1}_{\{a, b, c\}}$ and contained in heterogeneous monotone valuations (including common binary additive, common additive, common monotone, heterogeneous additive, and heterogeneous monotone):
   - **$k = 2$ is NO** (witnessed by $\beta$, proved by hand and in Lean 4);
   - **$k = 3$ is YES** (exhaustively verified over all $2^8 = 256$ common binary additive valuations and over all heterogeneous monotone valuations);
   - **$k = 4$ is NO** (witnessed by $\beta$, proved by hand and in Lean 4).
   Thus the $\mathrm{EF1}_{\mathrm{outer}}$ spectrum of $H$ begins `YES, NO, YES, NO, ...`, refuting Conjecture 1 (`YES* NO* YES^∞`).
2. **Exact minimality:** Exhaustive search over all connected graphs on $\le 7$ vertices finds zero spectrum gaps under common binary additive valuations; on $8$ vertices, exactly $4$ of the $11{,}117$ connected graphs have a gap ($H$ plus $0, 1, 2,$ or $3$ edges among $\{a, b, c\}$), all with binary spectrum `Y N Y N Y Y Y Y`.
3. **Generalized family:** Adding pendant leaves to the $m$-side of $K_{s, m}$ produces `NO` on $[2, m - 1]$ and $[m + 1, m + s - 1]$ for all $s \ge 2, m \ge 3$, with computed `YES` at $k = m$ for $8$ tested pairs $(s, m)$ (giving arbitrarily wide second `NO` blocks).

## Files

- [`PROOF.md`](PROOF.md) — Exact definitions, complete hand proofs of `NO` at $k = 2$ and $k = 4$, exhaustive and monotone verification of `YES` at $k = 3$, and minimality/family summary.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit and Lean 4 formal verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe: enumerates all connected $k$-allocations of $H$ for $k = 2, 3, 4$, verifies `NO` at $k = 2, 4$ for $\beta$, and verifies `YES` at $k = 3$ for all $256$ common binary valuations and all $4$ minimal $8$-vertex gap graphs).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/ChenZwickerEF1Outer.lean`](../../lean/Conjectures/ChenZwickerEF1Outer.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/chen-zwicker-ef1-outer/verify.py
cd lean && lake build Conjectures.ChenZwickerEF1Outer
```
