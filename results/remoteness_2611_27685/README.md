# Remoteness-Minimizing $D$-Tree Conjecture (Conj. 4.4) — `arXiv:2611.27685` — Disproved

- **Source:** I. Allie, B. Du Preez, Z. Hefty, and S. Mafunda, *Proximity and Remoteness in Trees with given Segment Sequence*, `arXiv:2611.27685` (Nov 2026).
- **Conjecture 4.4:** For any segment sequence $D = (\ell_1, \dots, \ell_k)$, the $D$-tree minimizing remoteness is starlike or a $(\Delta, 2)$-$D$-tree.
- **Result:** **Disproved.**
  - For $D = (315, 116, 25, 21, 21, 1^8)$ ($k = 13$, $n = 507$), the $(9,3)$-$D$-tree $B_1\{21,21\}\text{—}315\text{—}B_2\{25\}\text{—}116\text{—}B_3\{1^8\}$ attains $\sigma_{\max} = 115{,}399$, strictly below the minimum $115{,}501$ over all $607$ starlike and $(\Delta, 2)$-$D$-trees (gap $102$). Scaling by any integer $t \ge 1$ gives an infinite counterexample family $t \cdot D$ with gap $102 t^2$.
  - For $k = 8$, $D' = (5111, 3694, 79, 15, 15, 1^3)$ ($n = 8{,}918$) has a $(4,3)$-$D'$-tree beating all $227$ trees with $h \le 2$ ($39{,}336{,}710$ vs. $39{,}337{,}833$, gap $1{,}123$); since $k = 8$ forces $h \le 3$, the global remoteness minimizer has $3$ branch vertices.

## Files

- [DISPROOF.md](DISPROOF.md) — exact transmission formula and hand-checkable case proof.
- [note.tex](note.tex) — arXiv-ready LaTeX short note.
- [verify.py](verify.py) — standalone graph-level BFS verifier enumerating every $h \le 2$ $D$-tree.

## Verify

```bash
python verify.py
```
