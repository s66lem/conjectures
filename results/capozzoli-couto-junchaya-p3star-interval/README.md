# Disproof of Capozzoli–Couto–Junchaya Conjecture 1 under ETH (`arXiv:2609.22640v1`)

Quasi-polynomial deterministic algorithm ($2^{O(\log^4 n)} = n^{O(\log^3 n)}$), cross-model adversarial audit, and Lean 4 formal verification refuting **Conjecture 1** of Idian C. Capozzoli, Yan S. Couto, and Enrique Junchaya, *Interval number for tournaments in $P_3$-convexity* (`arXiv:2609.22640v1`, Sep 2026) under the Exponential Time Hypothesis (ETH).

## Main Results

1. **Quasi-polynomial deterministic algorithm (Theorem 1):** For every $n$-vertex tournament $T$ and budget $k \ge 0$, deciding whether $\mathrm{in}_{P_3^*}(T) \le k$ can be solved deterministically in time $2^{O(\log^4 n)} = n^{O(\log^3 n)}$.
2. **Disproof of Conjecture 1 & NP-intermediateness under ETH (Corollary 1):** Assuming ETH (via the Sparsification Lemma), *$P_3^*$-interval on Tournaments* is **not NP-complete**. Combined with the $\mathsf{W[2]}$-hardness and $f(k) n^{o(k)}$ ETH lower bound of Capozzoli–Couto–Junchaya (Theorem 4.1 & Corollary 3) — whose constructed tournament $T'$ is always strongly connected for nonempty inputs — **both** *$P_3^*$-interval on Tournaments* and *$P_3^*$-interval on Strong Tournaments* are **NP-intermediate under ETH**.
3. **Structural mechanism:** Even though $\mathrm{in}_{P_3^*}(T)$ can be $\Theta(n)$ on strong tournaments (ruling out the $n^{O(\log n)}$ brute-force bound that worked for $P_3$-convexity), multiplicative greedy preprocessing leaves a demand subset $U$ on which every arc covers $< |U|/r$ vertices. Partitioning $V(T)$ into $r$ bands by $U$-out-degree $f(x) = |N^+(x) \cap U|$ gives forward orientation across non-adjacent bands (Lemma B), local triangle radius $\le 2$ (Lemma E), $4$-band decoupling (Lemma C), and empty-band gap $\le 3$ (Lemma D), yielding a balanced divide-and-conquer recursion of branching factor $2^{O(\log^2 n)}$ and depth $O(\log^2 n)$.

## Files

- [`PROOF.md`](PROOF.md) — Complete self-contained proof (Lemmas A–E, exact recursive algorithm `Solve(T, D, F, k)`, soundness, completeness, $2^{O(\log^4 n)}$ runtime bound, ETH + Sparsification corollary, and strong-tournament connectivity).
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial audit (`gpt-6.2-sol`) and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only, `-O`-safe `require()` checks): verifies Lemmas A–E across 14 tournament families, verifies exact equivalence of the recursive band-splitting solver against an independent branch-and-bound solver (with active splits on YES, NO, strong, non-strong, and $F \ne \emptyset$ constrained subproblems), and verifies Theorem 4.1 strong connectivity.
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/TournamentP3StarQP.lean`](../../lean/Conjectures/TournamentP3StarQP.lean) — Lean 4 formalization.

## Reproduction

```bash
python3 -O results/capozzoli-couto-junchaya-p3star-interval/verify.py
cd lean && lake build Conjectures.TournamentP3StarQP
```
