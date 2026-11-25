# Disproof of Conjecture 4.4 of `arXiv:2611.27685` (Tree Remoteness with Given Segment Sequence)

**Paper:** Imran Allie, Brandon Du Preez, Zion Hefty, and Sonwabile Mafunda, *Proximity and Remoteness in Trees with given Segment Sequence*, `arXiv:2611.27685` (November 2026).

> **Conjecture 4.4 (`arXiv:2611.27685`):** Let $D = (\ell_1, \ell_2, \dots, \ell_k)$ be a segment sequence. Then the $D$-tree with minimum remoteness is starlike (a $(\Delta, 1)$-$D$-tree) or a $(\Delta, 2)$-$D$-tree.

**Result (Disproof):** Conjecture 4.4 is **false**. We exhibit explicit segment sequences (and an infinite scaled family $t \cdot D$, $t \ge 1$) whose remoteness-minimizing $D$-tree has **$h = 3$ branch vertices** and strictly beats every starlike and every $(\Delta, 2)$-$D$-tree. All claims are verified both by hand below and by explicit graph-level BFS in [verify.py](verify.py).

---

## 1. Exact Transmission Formula

By Section 1 of `arXiv:2611.27685`, a segment sequence $D = (\ell_1, \dots, \ell_k)$ specifies the edge lengths of the segments of a tree of order $n = 1 + S$, where $S := \sum_{i=1}^k \ell_i$. Since every $D$-tree has the same order $n$, minimizing remoteness $\rho(T) = \frac{1}{n-1} \max_{v \in V(T)} \sigma(v, T)$ is equivalent to minimizing the maximum transmission $\sigma_{\max}(T) := \max_{v \in V(T)} \sigma(v, T)$, which is attained at a leaf (Observation 2.7 of `arXiv:2611.27685`).

For any leaf $v$ at the end of a pendant segment $s$ attached at branch vertex $B$, let $d(B, S_i)$ be the distance from $B$ to the nearer endpoint of segment $S_i$. Counting vertex $B$ with segment $s$ and the remaining $\ell_i$ vertices of each segment $S_i$ ($i \ne s$) at distances $\ell_s + d(B, S_i) + 1, \dots, \ell_s + d(B, S_i) + \ell_i$ from $v$ gives the exact identity
$$\sigma(v, T) = C(D) + \ell_s (S - \ell_s) + \sum_{i=1}^k \ell_i \, d(B, S_i), \qquad C(D) := \sum_{i=1}^k \frac{\ell_i(\ell_i + 1)}{2}.$$
Note that $C(D)$ depends only on $D$, and $\sigma(v, T) - C(D)$ is a homogeneous quadratic in $(\ell_1, \dots, \ell_k)$.

---

## 2. Counterexample 1 (Order $n = 507$, $k = 13$)

Let
$$D = (315,\, 116,\, 25,\, 21,\, 21,\, \underbrace{1, 1, 1, 1, 1, 1, 1, 1}_{8}),$$
so $k = 13$, $S = 506$, $n = 507$, and $C(D) = 57{,}351$.

Consider the **$(9, 3)$-$D$-tree** $T^*$ with three branch vertices $B_1, B_2, B_3$ joined by internal segments $B_1 \text{—}315\text{—} B_2 \text{—}116\text{—} B_3$ and pendant segments:
- $\{21, 21\}$ at $B_1$ ($\deg(B_1) = 3$),
- $\{25\}$ at $B_2$ ($\deg(B_2) = 3$),
- $\{1^8\}$ at $B_3$ ($\deg(B_3) = 9$).

### Transmissions in $T^*$ ($\sigma - C(D)$)
- **Leaf on a $21$-segment at $B_1$:** $21 \cdot 485 + 315 \cdot (25 + 116) + (315 + 116) \cdot 8 = 10{,}185 + 44{,}415 + 3{,}448 = \mathbf{58{,}048}$.
- **Leaf on the $25$-segment at $B_2$:** $25 \cdot 481 + 315 \cdot 42 + 116 \cdot 8 = 12{,}025 + 13{,}230 + 928 = 26{,}183$.
- **Leaf on a $1$-segment at $B_3$:** $1 \cdot 505 + 116 \cdot (25 + 315) + (116 + 315) \cdot 42 = 505 + 39{,}440 + 18{,}102 = 58{,}047$.

Hence
$$\sigma_{\max}(T^*) = 57{,}351 + 58{,}048 = \mathbf{115{,}399}, \qquad \rho(T^*) = \frac{115{,}399}{506} \approx 228.0613.$$

### Lower bound for every $D$-tree $T$ with $h \le 2$ branch vertices
1. **$315$ is a pendant segment** (covering the unique starlike tree $h = 1$ and all $h = 2$ trees with internal segment $\ne 315$): the leaf on $315$ satisfies
   $$\sigma - C(D) \ge 315 \cdot (506 - 315) = 315 \cdot 191 = 60{,}165 > 58{,}048.$$
2. **$h = 2$ with $315$ as the unique internal segment** joining branch vertices $a$ and $b$: then $116$ is pendant, say at $a$, and the pendant length sums $W_a, W_b$ satisfy $W_a + W_b = 191$.
   - The leaf on $116$ at $a$ has $\sigma - C(D) = 116 \cdot 390 + 315 W_b = 45{,}240 + 315 W_b$. If $W_b \ge 41$, this is at least $45{,}240 + 12{,}915 = 58{,}155 > 58{,}048$.
   - Otherwise $W_b \le 40$. Let $m \in \{1, 21, 25\}$ be the longest pendant segment attached at $b$:
     - If $m = 1$: at most eight $1$-segments sit at $b$, so $W_b \le 8$ and $W_a \ge 183$. A leaf on $1$ at $b$ has $\sigma - C(D) = 505 + 315 W_a \ge 505 + 57{,}645 = \mathbf{58{,}150} > 58{,}048$.
     - If $m = 21$: since $21 + 21 > 40$ and $21 + 25 > 40$, $b$ holds one $21$ and at most eight $1$'s, so $W_b \le 29$, $W_a \ge 162$, and the leaf on $21$ at $b$ has $\sigma - C(D) \ge 10{,}185 + 315 \cdot 162 = 61{,}215 > 58{,}048$.
     - If $m = 25$: since $25 + 21 > 40$, $b$ holds one $25$ and at most eight $1$'s, so $W_b \le 33$, $W_a \ge 158$, and the leaf on $25$ at $b$ has $\sigma - C(D) \ge 12{,}025 + 315 \cdot 158 = 61{,}795 > 58{,}048$.

Thus every $D$-tree $T$ with $h \le 2$ satisfies
$$\sigma_{\max}(T) \ge 57{,}351 + 58{,}150 = \mathbf{115{,}501} > \mathbf{115{,}399} = \sigma_{\max}(T^*)$$
(strict gap $102$; minimum among $h \le 2$ trees is attained by $a\{116, 25, 21, 21\} \text{—}315\text{—} b\{1^8\}$).

**Infinite family:** Because $\sigma - C(D)$ is homogeneous of degree $2$ in the segment lengths, every integer multiple $t \cdot D$ ($t \ge 1$) with the correspondingly scaled $(9, 3)$-tree is a counterexample with strict transmission gap $102 t^2$.

---

## 3. Counterexample 2 ($k = 8$, Globally Optimal $(4, 3)$-Tree)

For $k = 8$ segments, let
$$D = (5111,\, 3694,\, 79,\, 15,\, 15,\, 1,\, 1,\, 1), \qquad n = 8{,}918,$$
and take the $(4, 3)$-$D$-tree $T^* = B_1\{15, 15\} \text{—}5111\text{—} B_2\{79\} \text{—}3694\text{—} B_3\{1, 1, 1\}$. Explicit graph-level BFS ([verify.py](verify.py)) confirms:
- $\sigma_{\max}(T^*) = 39{,}336{,}710$,
- minimum $\sigma_{\max}$ over all $227$ $D$-trees with $h \le 2$ is $39{,}337{,}833$ (strict gap $1{,}123$).

Because a tree with $h$ branch vertices has at least $h + 2$ leaves and $h - 1$ internal segments (so $k \ge 2h + 1$), $k = 8$ forces $h \le 3$; hence $T^*$ beats every starlike and every $(\Delta, 2)$-$D$-tree, and the global remoteness minimizer for $D$ has $h = 3$.

**Why the paper's search missed it:** The authors tested sequences of the form $(b\ell, c\ell, \ell, \dots, \ell)$, which have only one short-segment tier. Introducing a medium pendant tier (`25, 21, 21` alongside `1^8`, or `79, 15, 15` alongside `1^3`) makes *both* long segments too costly to leave pendant, forcing a $(\Delta, 3)$-tree with two internal long segments.
