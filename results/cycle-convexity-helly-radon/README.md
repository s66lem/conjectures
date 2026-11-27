# Disproof of the Cycle Convexity Helly–Radon Conjecture (`arXiv:2609.34236v1`)

## Status

- **Conjecture:** Conjecture 1 of R. S. Nair, B. S. Anand, Ullas Chandran S. V., J. R. Nascimento, and A. Anil, *Computing the Helly Number, Radon Number and Rank in Cycle Convexity*, `arXiv:2609.34236v1`, Section 5 ("Conclusion"): $\mathrm{hl}_{cc}(G) = \mathrm{rd}_{cc}(G)$ for every connected graph $G$ of order $n \ge 2$.
- **Outcome:** **Disproved** via an explicit $16$-vertex, $36$-edge connected graph $G_{16}$ with $\mathrm{hl}_{cc}(G_{16}) = 5 < 6 = \mathrm{rd}_{cc}(G_{16})$ (alongside the general Levi inequality $\mathrm{hl}_{cc}(G) \le \mathrm{rd}_{cc}(G)$ for all finite graphs).
- **Lean 4 formalization:** [`lean/Conjectures/CycleConvexityHellyRadon.lean`](../../lean/Conjectures/CycleConvexityHellyRadon.lean) (complete, zero axioms beyond the standard three `[propext, Classical.choice, Quot.sound]`, zero warnings, independent cross-model audit `PASS` in [`AUDIT.md`](AUDIT.md)).
- **Preprint:** [DOI `10.5281/zenodo.24579187`](https://doi.org/10.5281/zenodo.24579187) · [`paper.pdf`](paper.pdf) (compiled from [`paper.tex`](paper.tex)).

## Counterexample Summary

Take three $K_5$ cliques $K^{(i)}$ ($i \in \mathbb{Z}_3$) on $\{s_i, t_i, u_i, p_i, q_i\}$, add a central hub $x$ adjacent to $u_0, u_1, u_2$, and add three cyclic port edges $p_i q_{i+1}$. The resulting connected graph $G_{16}$ (graph6: `O~{?GKFDw??@?BAB_DxAC`) has:
- $\mathrm{hl}_{cc}(G_{16}) = 5$ (witnessed by $\{s_0, t_0, s_1, t_1, s_2\}$),
- $\mathrm{rd}_{cc}(G_{16}) = 6$ (witnessed by $S = \{s_0, t_0, s_1, t_1, s_2, t_2\}$, which is Radon independent and convexly independent with unique Helly point $\{x\}$).

## Files

- [`PROOF.md`](PROOF.md): Complete self-contained proof of $\mathrm{hl}_{cc}(G) \le \mathrm{rd}_{cc}(G)$ and $\mathrm{hl}_{cc}(G_{16}) = 5 < 6 = \mathrm{rd}_{cc}(G_{16})$.
- [`AUDIT.md`](AUDIT.md): Independent cross-model adversarial audit report (`claude-sonnet-5-5`).
- [`verify.py`](verify.py): Standalone verification script checking all $65{,}536$ subsets of $V(G_{16})$, closed hull formulas, $\mathrm{hl}_{cc}(G_{16}) = 5$, and $\mathrm{rd}_{cc}(G_{16}) = 6$.
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf): Self-contained preprint.
