# Exact Littlestone dimensions of intervals and unions of intervals (`arXiv:2611.28727`)

Complete proof of **both open conjectures** posed by Miit Daga and Swarna Priya Ramu (*How many mistakes does it take to learn an interval? Exact Littlestone dimensions of intervals and their unions*, `arXiv:2611.28727`, November 2026):

1. **Odd-$k$ union-of-intervals conjecture:** For every odd switch budget $k \ge 1$ and domain size $n \ge 1$, $\mathrm{Ldim}(C_{n,k}) = 1 + \mathrm{Ldim}(G_k(n)) = 1 + v_k(n)$ (proved via the signed cyclic rotation $(f_1,\dots,f_n) \mapsto (f_2,\dots,f_n, 1-f_1)$).
2. **Conjecture 31 (Randomized Littlestone dimension of intervals):** The greedy cutting schedule value $G(S)$ satisfies the Bellman supersolution inequality $2G(S) - G(S') \ge 1 + (\widetilde{\lambda}(u) + \widetilde{\lambda}(v))/2$ at every finite multiset position $S$ and every legal cut $p = u + v$, proving $V(S) = G(S)$ and $\mathrm{RL}(\mathrm{Int}_m) = R(m + 1)$ for all $m \ge 0$ (via a dyadic-scale decomposition and $1/2$-Lipschitz packing inequality).

- [Complete proofs](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/LittlestoneIntervals.lean) (`LittlestoneIntervals.ldim_C_odd`, `LittlestoneIntervals.odd_switch_shattered_iff`, `LittlestoneIntervals.greedy_supersolution`, `LittlestoneIntervals.conjecture_31_bellman_eq_greedy`)
- [arXiv-ready LaTeX preprint](paper.tex) · [Compiled PDF](paper.pdf)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.LittlestoneIntervals` to verify both theorems in Lean 4 (`v4.33.1` + Mathlib, zero `sorry`, standard axioms only). The results are internally cross-model audited and Lean-verified, but externally unrefereed; priority is not asserted.
