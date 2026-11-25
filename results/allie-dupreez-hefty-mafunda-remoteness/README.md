# Allie–Du Preez–Hefty–Mafunda tree remoteness conjecture

Complete proposed disproof of [Conjecture 4.4](https://arxiv.org/html/2611.27685) of Allie, Du Preez, Hefty, and Mafunda (*Proximity and Remoteness in Trees with given Segment Sequence*, `arXiv:2611.27685`, November 2026), which conjectured that every remoteness-minimizing tree with a prescribed segment sequence D is starlike or a (Δ, 2)-D-tree. For D = (315, 116, 25, 21, 21, 1⁸) (k = 13, n = 507), an explicit (9, 3)-D-tree achieves maximum transmission 115,399, strictly below the minimum 115,501 across all 607 starlike and (Δ, 2)-D-trees (gap 102); scaling by any integer t ≥ 1 gives an infinite counterexample family t·D with gap 102t². For k = 8, D' = (5111, 3694, 79, 15, 15, 1³) (n = 8,918) has a (4, 3)-D'-tree beating all 227 trees with h ≤ 2 (gap 1,123), so its global minimizer has 3 branch vertices.

- [Complete disproof](PROOF.md)
- [LaTeX manuscript](paper.tex)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only). The verifier constructs every tree as an explicit adjacency list, recovers its segment multiset directly from the graph, and checks all-vertex transmissions on the (Δ, 3)-trees against leaf BFS on all 607 (k = 13) and 227 (k = 8) trees with h ≤ 2. The result is internally reviewed but externally unrefereed; priority is not asserted.
