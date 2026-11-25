# Disproof of Conjecture 9.1 on Planar All-Even Sets (`arXiv:2610.38864`)

We **disprove Conjecture 9.1** of Daniel Kalmanovich and Gabriel Nivasch (*All-even sets in $\mathbb{R}^2$ and $\mathbb{R}^3$*, `arXiv:2610.38864`, October 2026): there exists a 36-point planar all-even set $S \subset \mathbb{R}^2$ (a subset of the regular $210$-gon) that has **no monotonically contagious triangle**.

Furthermore:
1. $S$ is **height-rigid** (rigidity matrix rank $33 = 36 - 3$) and admits a (non-monotone) **contagious triangle** (Property $\mathcal{C}$), thereby separating Property $\mathcal{M}$ from Property $\mathcal{C}$ among planar all-even sets and answering the first separation question in Section 9 of `arXiv:2610.38864`.
2. Generalizing the construction yields an **infinite family** of planar all-even sets $S_k$ ($k \ge 2$) requiring at least $k + 1$ initial seed vertices under the one-vertex-at-a-time monotone contagion rule (and in particular giving infinitely many counterexamples to Conjecture 9.1 for all $k \ge 3$).

---

## 1. The 36-Point Counterexample on the Regular 210-Gon

Identify $G := \mathbb{Z}/210\mathbb{Z}$ with the vertices of the regular $210$-gon on the unit circle via
$$p_j := \left(\cos\frac{2\pi j}{210},\; \sin\frac{2\pi j}{210}\right) \in \mathbb{R}^2 \qquad (j \in G).$$
Define the two disjoint index layers
$$A := 15 \cdot \{4, 5, 7, 8, 9, 10, 12, 13\} \subset G \quad (|A| = 8),$$
$$B := \{1 + 6j : 0 \le j < 35,\; 5 \nmid j\} \subset G \quad (|B| = 28),$$
and set $S := \{p_j : j \in A \cup B\} \subset \mathbb{R}^2$. Since every element of $A$ satisfies $i \equiv 0 \pmod 3$ and every element of $B$ satisfies $i \equiv 1 \pmod 3$, the layers $A$ and $B$ are disjoint and $|S| = 36$.

---

## 2. Proof That $S$ Is All-Even

Recall that a finite nonempty set $S \subset \mathbb{R}^2$ is **all-even** if for every nonzero vector $u \in \mathbb{R}^2$, the number of occupied lines perpendicular to $u$,
$$m_S(u) := \bigl|\{\langle p, u \rangle : p \in S\}\bigr|,$$
is even.

Writing $\zeta := e^{2\pi i / 210}$, the complex difference along any chord $p_i p_j$ ($i \neq j$) factors as
$$\zeta^j - \zeta^i = 2i \sin\left(\frac{\pi(j - i)}{210}\right) \exp\left(\frac{\pi i (i + j)}{210}\right).$$
Therefore two nondegenerate chords $p_i p_j$ and $p_k p_l$ of the regular $210$-gon are parallel if and only if
$$i + j \equiv k + l \pmod{210}$$
(see also Section 6 of `arXiv:2610.38864`). Because a line meets the unit circle in at most two points, for any direction $u \neq 0$:
- If no chord of $S$ is perpendicular to $u$, then all $36$ projections $\langle p, u \rangle$ are distinct, so $m_S(u) = 36$ (even).
- If some chord $p_i p_j$ ($i \neq j$) is perpendicular to $u$, let $s := i + j \in G$. Then the chords of $S$ perpendicular to $u$ are precisely the unordered distinct pairs $\{a, b\} \subset A \cup B$ with $a + b = s$, so $m_S(u) = 36 - c_s$, where $c_s := |\{\{a, b\} \subset A \cup B : a \neq b,\; a + b = s\}|$.

Hence $S$ is all-even if and only if $c_s$ is even for every $s \in G$. Split $c_s = c_s^{AA} + c_s^{BB} + c_s^{AB}$ by layer:

1. **Pairs within $A$ ($c_s^{AA}$):** Removing the factor $15$, work modulo $14$ with $A_0 = \{4, 5, 7, 8, 9, 10, 12, 13\} \subset \mathbb{Z}/14\mathbb{Z}$. For residues $0, 1, \dots, 13 \pmod{14}$, the unordered distinct pair counts are
   $$(2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2),$$
   every entry of which is even. (Sums not divisible by $15$ have $c_s^{AA} = 0$.)
2. **Pairs within $B$ ($c_s^{BB}$):** Removing the shift $1$ and factor $6$, work modulo $35$ with $B_0 = (\mathbb{Z}/35\mathbb{Z}) \setminus K$, where $K = 5\mathbb{Z}/35\mathbb{Z}$ is the subgroup of order $7$. In all of $\mathbb{Z}/35\mathbb{Z}$, each residue $r$ has $(35 - 1)/2 = 17$ unordered distinct pairs summing to $r$ (since $35$ is odd, $2x = r$ has a unique solution).
   - If $r \in K$, an excluded pair has one endpoint in $K$ iff both endpoints lie in $K$; there are $(7 - 1)/2 = 3$ distinct pairs inside $K$, leaving $17 - 3 = 14$ (even).
   - If $r \notin K$, each of the $7$ elements $x \in K$ pairs uniquely with $r - x \notin K$, giving $7$ excluded pairs and leaving $17 - 7 = 10$ (even).
   (Sums $s \not\equiv 2 \pmod 6$ have $c_s^{BB} = 0$.)
3. **Mixed pairs ($c_s^{AB}$):** Let $H := 30\mathbb{Z}/210\mathbb{Z}$ (order $7$). Since $30 = 6 \cdot 5$, shifting $j \mapsto j + 5$ preserves $5 \nmid j$, so $B$ is $H$-invariant ($B + H = B$). The set $A = 15\{4, 5, 7, 8, 9, 10, 12, 13\}$ meets two $H$-cosets: the even multipliers $15\{4, 8, 10, 12\} \subset H$ (size $4$) and the odd multipliers $15\{5, 7, 9, 13\} \subset 15 + H$ (size $4$). Because $s - a \in B$ depends only on the $H$-coset of $a$, each occupied $H$-coset of $A$ contributes either $0$ or $4$ mixed pairs, so $c_s^{AB} \in \{0, 4, 8\}$ is always even.

Therefore $c_s$ is even for every $s \in G$ (explicitly $m_S(u) \in \{22, 26, 32, 34, 36\}$ across all directions), so $S$ is a planar all-even set. $\blacksquare$

---

## 3. Proof That $S$ Has No Monotonically Contagious Triangle

By Section 5 of `arXiv:2610.38864`, starting from a set $U \subseteq S$ of three non-collinear points (every triple on a circle is non-collinear), the monotone contagion rule repeatedly adds a point $y \in S \setminus U$ whenever there exist $x, p, q \in U$ with $p \neq q$ and $xy \parallel pq$. On the regular $210$-gon, $xy \parallel pq$ holds if and only if
$$x + y \equiv p + q \pmod{210}, \qquad \text{i.e.,} \qquad y = p + q - x \in G.$$

Let $\lambda(z) \in \{0, 1\} \subset \mathbb{Z}/3\mathbb{Z}$ be the residue $z \bmod 3$, so $\lambda(z) = 0$ for $z \in A$ and $\lambda(z) = 1$ for $z \in B$.

**Invariant 1 (Layer multiset preservation).** Reducing $x + y = p + q$ modulo $3$ gives $\lambda(x) + \lambda(y) \equiv \lambda(p) + \lambda(q) \pmod 3$. The three unordered pairs from $\{0, 1\}$ have distinct sums modulo $3$: $0 + 0 \equiv 0$, $0 + 1 \equiv 1$, and $1 + 1 \equiv 2$. Therefore $\{\lambda(x), \lambda(y)\} = \{\lambda(p), \lambda(q)\}$ as multisets in every legal move.

- **Pure triangle ($T \subset A$ or $T \subset B$):** Every move from a subset of a single layer produces a point in that same layer, so the monotone closure stays inside $A$ (size $8 < 36$) or $B$ (size $28 < 36$).

- **Mixed triangle ($T$ meets both $A$ and $B$):** One layer contains two vertices $u_1, u_2$ of $T$, and the other layer contains one vertex $w$ of $T$. Let $D := \langle u_1 - u_2 \rangle \le G$ be the subgroup generated by $u_1 - u_2$. Let $c_0, c_1 \in G$ be the coset representatives of $T \cap A$ and $T \cap B$ modulo $D$, so $T \subseteq U^* := (A \cap (c_0 + D)) \cup (B \cap (c_1 + D))$.
  We claim $U^*$ is closed under monotone contagion: for any $x, p, q \in U^*$ and $y = p + q - x \in S$, Invariant 1 forces $\{\lambda(x), \lambda(y)\} = \{\lambda(p), \lambda(q)\}$, hence
  $$c_{\lambda(p)} + c_{\lambda(q)} - c_{\lambda(x)} = c_{\lambda(y)}$$
  and therefore $y \in c_{\lambda(y)} + D$, so $y \in U^*$.
  - If the doubled layer is $A$, then $u_1 - u_2 \in 15G$, so $D \subseteq 15G$. However, $B$ contains $1 + 6 = 7$ and $1 + 12 = 13$ with difference $6 \notin 15G$, so $B$ cannot lie in a single $D$-coset. Hence $U^* \subsetneq S$.
  - If the doubled layer is $B$, then $u_1 - u_2 \in 6G$, so $D \subseteq 6G$. However, $A$ contains $60$ and $75$ with difference $15 \notin 6G$ (every element of $6G$ is even modulo $210$), so $A$ cannot lie in a single $D$-coset. Hence $U^* \subsetneq S$.

In every case, no triangle in $S$ has monotone closure equal to $S$, disproving Conjecture 9.1. $\blacksquare$

---

## 4. Height-Rigidity and Separation of Property $\mathcal{M}$ from Property $\mathcal{C}$

- **Height-rigidity ($\mathrm{rank}\,R(S) = 33$):** For each chord direction $s \in G$ with at least two chords, pick a reference chord $(k, l)$ and for each other chord $(i, j)$ with $i + j = s$ form the row $e(\mathbf{e}_j - \mathbf{e}_i) - d(\mathbf{e}_l - \mathbf{e}_k)$ over $\mathbb{Z}[\zeta]$, where $d = \zeta^j - \zeta^i$ and $e = \zeta^l - \zeta^k$. Because $d/e \in \mathbb{R} \setminus \{0\}$, each row is a nonzero complex multiple of a real admissibility row. Under the ring homomorphism $\mathbb{Z}[\zeta] \to \mathbb{F}_{211}$ sending $\zeta \mapsto 2$ (valid because $211$ is prime and $2$ has multiplicative order $210$ mod $211$), Gaussian elimination produces a $33 \times 33$ nonzero minor over $\mathbb{F}_{211}$, hence over $\mathbb{Z}[\zeta]$. Thus $\mathrm{rank}_{\mathbb{R}} R(S) \ge 33 = 36 - 3$, and since the affine functions $1, x, y$ span a $3$-dimensional subspace of $\ker R(S)$, $\mathrm{rank}_{\mathbb{R}} R(S) = 33$ and $S$ is height-rigid.
- **Property $\mathcal{C}$ holds:** Under non-monotone class-merge contagion (Section 5 of `arXiv:2610.38864`), $S$ admits a contagious triangle merging all $36$ points (verified explicitly in `verify.py`), giving a second certificate of height-rigidity and separating Property $\mathcal{M}$ from Property $\mathcal{C}$ among planar all-even sets.

---

## 5. Infinite Family Requiring Unbounded Monotone Seeds

Extending the monotone contagion rule to an arbitrary initial seed $T \subseteq S$, we construct for every integer $k \ge 2$ a planar all-even set $S_k$ requiring at least $k + 1$ initial vertices to close monotonically (and hence yielding an infinite family of counterexamples to Conjecture 9.1 for all $k \ge 3$).

For $k \ge 2$ and $0 \le i \le k$, let $H_i \subset \mathbb{R}/\mathbb{Z}$ be the cyclic subgroup of order $3 \cdot 5^i$. Put $M := 2^{k+2}$ and define $k$ disjoint layers on $\mathbb{R}/\mathbb{Z}$:
$$L_i := \frac{2^{i-1}}{M |H_k|} + (H_i \setminus H_{i-1}), \qquad 1 \le i \le k,$$
mapped to the unit circle via $t \mapsto e^{2\pi i t}$.

1. **All-evenness:** Fix $1 \le i \le k$ and set $h := |H_{i-1}| = 3 \cdot 5^{i-1} \equiv 3 \pmod 4$. Inside $H_i \setminus H_{i-1}$ (size $4h$):
   - A sum in $H_{i-1}$ has $(5h - 1)/2 - (h - 1)/2 = 2h$ unordered distinct pairs (even).
   - A sum in $H_i \setminus H_{i-1}$ has $(5h - 1)/2 - h = (3h - 1)/2$ unordered distinct pairs (even since $h \equiv 3 \pmod 4 \implies 3h - 1 \equiv 0 \pmod 4$).
   For $1 \le i < j \le k$, we have $H_i \subseteq H_{j-1}$, so $L_j$ is invariant under translation by $H_i$. Hence for any mixed sum $s$, the number of pairs $(a, b) \in L_i \times L_j$ with $a + b = s$ is either $0$ or $|L_i| = 4h$ (even). Thus $S_k = \bigcup_{i=1}^k L_i$ is all-even.
2. **Seed lower bound ($\ge k + 1$):** Multiplying angles by $M|H_k|$ and reducing modulo $M$ sends every point of $L_i$ to the binary tag $2^{i-1} \in \mathbb{Z}/M\mathbb{Z}$. Since all pairwise sums $2^{i-1} + 2^{j-1} \le 2^k < M = 2^{k+2}$ are distinct by uniqueness of binary representations, every monotone move $x + y = p + q$ preserves the multiset of layer tags. Consequently, no layer without an initial seed can ever be reached; and if a seed contains at most one point per layer ($|T| \le k$), no first move can even fire (matching the layer of $x$ to one of $p, q$ forces $x$ to equal that point, yielding $y$ equal to the other already-present point). Thus every monotonically contagious seed of $S_k$ has size at least $k + 1$. $\blacksquare$
