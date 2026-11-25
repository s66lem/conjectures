# Disproof of Bansal Conjecture C / 6.11 (`arXiv:2611.02210`)

We disprove **Conjecture C (Conjecture 6.11)** of Ryan Bansal, *A Quasisymmetric Analogue of the Bruhat Order* (`arXiv:2611.02210v1`), showing that principal lower intervals $[\varnothing, Z]$ below zigzag forests fail to be shellable — and in fact fail to be Cohen–Macaulay over any field — starting at the minimal possible rank $m = 7$ and continuing for every $m \ge 7$.

## 1. Definitions (Verbatim from `arXiv:2611.02210`, §§2 and 6)

- **Indexed forest (Definition 2.1):** An indexed tree with support $[a, b]$ is a full binary tree whose leaves occupy the consecutive number-line positions $a, a + 1, \dots, b + 1$. An indexed forest $F$ is a disjoint union of indexed trees with disjoint leaf sets; its support $\mathrm{supp}(F)$ is the union of the component supports. For each internal vertex $v \in \mathrm{IN}(F)$, $\rho(v)$ is the leftmost leaf label in the subtree rooted at $v$.
- **Forest code (Definition 2.4):** $\mathbf{c}(F) = (c_1, c_2, \dots)$ where $c_i(F) = \#\{v \in \mathrm{IN}(F) : \rho(v) = i\}$ (ignoring trailing zeros). The map $F \mapsto \mathbf{c}(F)$ is a bijection, written $F = F(\mathbf{c})$.
- **Forest polynomial (Definition 2.3):** A valid labeling $\lambda : \mathrm{IN}(F) \to \mathbb{Z}_{>0}$ satisfies $1 \le \lambda(v) \le \rho(v)$, $\lambda(v) \le \lambda(u)$ if $u$ is the left child of $v$, and $\lambda(v) < \lambda(u)$ if $u$ is the right child of $v$. Then $P_F = \sum_{\lambda \text{ valid}} \prod_{v \in \mathrm{IN}(F)} x_{\lambda(v)}$, with lexicographically minimal monomial $x^{\mathbf{c}(F)}$ (Fact 2.5).
- **Quasisymmetric Bruhat order (Definition 2.7):** Cover relation
  $$F \lessdot G \iff \exists\, i \ge 1 \text{ such that } P_G \text{ appears in the forest-basis expansion of } (x_1 + \cdots + x_i) P_F,$$
  with $\le$ the reflexive-transitive closure. Every cover increases rank $\mathrm{rk}(F) = |\mathrm{IN}(F)| = |\mathrm{supp}(F)|$ by $1$ and adds a single point to $\mathrm{supp}(F)$ (Fact 4.1).
- **Zigzag forest (Definition 6.8):** A forest $Z = F(a_1, \dots, a_k)$ whose code has no internal zeros ($a_j > 0$ for all $1 \le j \le k$).
- **Shellability (Section 6.1):** A bounded graded poset $P$ with minimum $\hat{0}$ and maximum $\hat{1}$ is shellable if the order complex $\Delta(P \setminus \{\hat{0}, \hat{1}\})$ admits an ordering $C_1, \dots, C_t$ of its maximal chains such that for every $j > 1$, $C_j \cap \bigcup_{i < j} C_i$ is pure of codimension $1$ in $C_j$. By Fact 6.1 (Wachs, Corollary 3.1.9(b)), shellability passes to every closed subinterval $[x, y] \subseteq P$.

## 2. Minimal Counterexample ($m = 7$)

Consider the zigzag tree $Z = F(1, 2, 4)$ of rank $7$ (support $[1, 7]$, leaves $1, \dots, 8$) and the rank-$4$ forest $x = F(0, 1, 0, 1, 1, 0, 1)$ (support $\{2, 4, 5, 7\}$, consisting of a cherry on $[2, 2]$, the tree $F(0, 0, 0, 1, 1)$ on $[4, 5]$, and a cherry on $[7, 7]$).

**Theorem 2.1.** The interval $[x, Z]$ in the quasisymmetric Bruhat order has length $3$, and its open part $(x, Z)$ consists of exactly $6$ elements of rank $5$ and $6$ elements of rank $6$, with exactly $12$ cover relations forming two vertex-disjoint $6$-cycles ($C_6 \sqcup C_6$):

| Component | Rank-5 element | Rank-6 upper covers in $(x, Z)$ |
| :---: | :--- | :--- |
| Hexagon 1 | $(0, 1, 0, 2, 2)$ | $(0, 1, 2, 3),\ (0, 1, 3, 0, 2)$ |
| Hexagon 1 | $(0, 1, 1, 2, 0, 0, 1)$ | $(0, 1, 2, 3),\ (1, 1, 3, 0, 0, 0, 1)$ |
| Hexagon 1 | $(0, 1, 2, 0, 1, 0, 1)$ | $(0, 1, 3, 0, 2),\ (1, 1, 3, 0, 0, 0, 1)$ |
| Hexagon 2 | $(0, 1, 0, 1, 3)$ | $(0, 2, 0, 4),\ (0, 2, 1, 0, 3)$ |
| Hexagon 2 | $(0, 2, 0, 2, 0, 0, 1)$ | $(0, 2, 0, 4),\ (0, 2, 3, 0, 0, 0, 1)$ |
| Hexagon 2 | $(0, 2, 1, 0, 1, 0, 1)$ | $(0, 2, 1, 0, 3),\ (0, 2, 3, 0, 0, 0, 1)$ |

In particular, $\Delta((x, Z))$ is a disconnected pure $1$-dimensional simplicial complex (homotopy equivalent to $S^1 \sqcup S^1$, with $\widetilde{H}_0(\Delta((x, Z)); \mathbb{Z}) \cong \mathbb{Z}$, $\widetilde{H}_1(\Delta((x, Z)); \mathbb{Z}) \cong \mathbb{Z}^2$, and $\mu(x, Z) = -1$).

**Corollary 2.2 (Disproof of Conjecture C / 6.11).**
1. The interval $[x, Z]$ is neither shellable nor Cohen–Macaulay over any field.
2. Consequently, the zigzag principal lower interval $[\varnothing, Z]$ is neither shellable nor Cohen–Macaulay over any field.
3. For every $m \ge 7$, both the zigzag forest $Z_m = F(m - 6, 2, 4)$ and $Z'_m = F(1, 2, m - 3)$ of rank $m$ satisfy $Z \le Z_m$ and $Z \le Z'_m$, so $[\varnothing, Z_m]$ and $[\varnothing, Z'_m]$ are neither shellable nor Cohen–Macaulay over any field.

*Proof.*
(1) A pure $1$-dimensional simplicial complex $\Delta$ is a graph without isolated vertices. In any shelling $e_1, \dots, e_t$ of its edges, each edge $e_j$ ($j > 1$) meets $\bigcup_{i < j} e_i$ in a pure $0$-dimensional subcomplex, hence in at least one vertex; by induction on $j$, $\bigcup_{i \le j} e_i$ is connected, so $\Delta$ must be connected. Likewise, a $1$-dimensional Cohen–Macaulay complex over any field $\mathbb{k}$ has $\widetilde{H}_0(\Delta; \mathbb{k}) = 0$, hence must be connected. Because $\Delta((x, Z)) \cong C_6 \sqcup C_6$ has two connected components, $[x, Z]$ is neither shellable nor Cohen–Macaulay over any field.

(2) By Fact 6.1 (shellability passes to closed intervals), non-shellability of $[x, Z] \subseteq [\varnothing, Z]$ implies non-shellability of $[\varnothing, Z]$. Similarly, for any maximal chain $\varnothing \lessdot x_1 \lessdot x_2 \lessdot x_3 \lessdot x$, the order complex $\Delta((x, Z))$ is the link of the face $\{x_1, x_2, x_3, x\}$ in $\Delta((\varnothing, Z))$, so $[\varnothing, Z]$ cannot be Cohen–Macaulay over any field.

(3) Whenever $c_{E(1) + 1}(F) = 0$ (the component at leaf $1$ is followed by a bare leaf), incrementing $c_1$ by $1$ adds a new root above leaf $1$ whose right child is that bare leaf and whose valid label is forced to be $1$, giving the exact identity $x_1 P_F = P_{F + e_1}$ and hence a single-term Monk cover $F \lessdot F + e_1$. Iterating from $Z = F(1, 2, 4)$ gives $Z = F(1, 2, 4) \lessdot F(2, 2, 4) \lessdot \cdots \lessdot F(m - 6, 2, 4) = Z_m$ (formalized in Lean 4 as `not_bansal_conjecture_C`). Likewise, Lemma 3.1 (code-raising) gives $Z = F(1, 2, 4) \lessdot F(1, 2, 5) \lessdot \cdots \lessdot F(1, 2, m - 3) = Z'_m$. In both cases $[x, Z]$ is a closed subinterval of the rank-$m$ zigzag lower interval, so the same obstruction applies for every $m \ge 7$. $\square$

## 3. Minimality and Census Summary

- For $m \le 6$, every one of the $1 + 2 + 5 + 14 + 42 + 132 = 196$ binary trees admits a recursive coatom ordering (reproducing Section 6.4 of `arXiv:2611.02210`), and no length-$3$ interval in $\mathcal{P}_6$ is disconnected; thus $m = 7$ is minimal.
- In $\mathcal{P}_7$, exactly $12$ of the $45{,}878$ length-$3$ intervals have disconnected open intervals, hitting $4$ of the $64$ rank-$7$ zigzags: $(1, 2, 4)$, $(1, 2, 3, 1)$, $(2, 2, 1, 2)$, and $(2, 2, 1, 1, 1)$. All $45{,}878$ intervals pass the Möbius sign test $(-1)^r \mu \ge 0$, showing that connectivity (not Möbius sign) is the obstruction.
