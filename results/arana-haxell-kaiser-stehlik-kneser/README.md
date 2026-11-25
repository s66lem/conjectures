# Complete Proof of Arana–Haxell–Kaiser–Stehlík Conjecture 1.3 for $k = 3$

Complete proof and Lean 4 formal verification settling **Conjecture 1.3 for $k = 3$** of Carmen Arana, Penny Haxell, Tomáš Kaiser, and Matěj Stehlík, *The chromatic number of $G$-stable Kneser graphs* (`arXiv:2610.17884`), together with an exact all-$k$ star-class obstruction and the $k = 4$ asymptotic theorem for $C_m \sqcup K_1$.

## Main Results

1. **Conjecture 1.3 completely resolved for $k = 3$:** For every simple graph $G$ on $n \ge 7$ vertices, $\chi(\mathrm{KG}(G, 3)) = n - 4$ (equivalently, $G$ is $3$-tight) if and only if $G$ is a single cycle $C_n$ or a disjoint union of paths and cycles of length at least $9$ (equivalently, $\Delta(G) \le 2$ and $G$ contains no proper cycle of length $3 \le m \le 8$).
2. **Self-contained Lean 4 proof of Schrijver's $k = 3$ theorem:** The Lean 4 formalization also proves $\chi(\mathrm{KG}(C_m, 3)) = m - 4$ for every $m \ge 6$ unconditionally inside Lean, without assuming Schrijver's theorem as an axiom.
3. **Exact all-$k$ Section 2 star-class obstruction:** For every $k \ge 2$ and $m \ge 4k - 3$, no proper $(m - 2k + 2)$-coloring of $\mathrm{KG}(C_m \sqcup K_1, k)$ restricts to a star coloring on $\mathrm{KG}(C_m, k)$ (tight against Arana–Haxell–Kaiser–Stehlík's Section 2 construction for $m \le 4k - 4$).
4. **Asymptotic $k = 4$ tightness for $C_m \sqcup K_1$:** For every $m \ge 39$, $\chi(\mathrm{KG}(C_m \sqcup K_1, 4)) = m - 5$.

## Files

- [`PROOF.md`](PROOF.md) — Complete self-contained proof (necessity obstructions, Hilton–Milner cutoff $n \le 19$, nonstar triple classification + weight/branch-and-bound finite certificates, anchor + Mantel proof for $C_m \sqcup K_1$, all-$k$ star obstruction, and $k = 4$ proof).
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial referee audit (GPT-6.2 Astra prover; Claude Opus 5.5 referee) and Lean 4 formal verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe: checks all finite component certificates on orders $n = 7 \dots 19$, Schrijver base cases, and arithmetic cutoffs).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/StableKneserK3.lean`](../../lean/Conjectures/StableKneserK3.lean) & [`../../lean/Conjectures/StableKneserK3/`](../../lean/Conjectures/StableKneserK3/) — Full Lean 4 formalization (`conjecture_1_3_k3`, `schrijver_k3`, `isolate_k3`, `section_two_obstruction`).

## Reproduction

```bash
python3 results/arana-haxell-kaiser-stehlik-kneser/verify.py base
python3 results/arana-haxell-kaiser-stehlik-kneser/verify.py 13 14 15 16 17 18 19
cd lean && lake build Conjectures.StableKneserK3
```
