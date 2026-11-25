# Proof of Arana–Haxell–Kaiser–Stehlík Conjecture 1.3 for $k = 3$

**Theorem 1 (Conjecture 1.3 at $k = 3$).** *Let $G$ be a simple graph on $n \ge 7$ vertices. Then $\chi(\mathrm{KG}(G, 3)) = n - 4$ if and only if $G$ is a cycle or $G$ is a disjoint union of paths and cycles in which every cycle has length at least $9$.*

This settles the $k = 3$ case of **Conjecture 1.3** of Carmen Arana, Penny Haxell, Tomáš Kaiser, and Matěj Stehlík, *The chromatic number of $G$-stable Kneser graphs* (`arXiv:2610.17884`), where even the simplest case $C_{n-1} \sqcup K_1$ ($n - 1 \ge 9$) was previously known only asymptotically (Theorem 1.4). We also establish an all-$k$ obstruction showing why the Section 2 coloring construction cannot cross $m = 4k - 3$, and prove $4$-tightness of $C_m \sqcup K_1$ for all $m \ge 39$.

---

## 1. Minimum Counterexample Reduction

Necessity follows from Theorem 1.2 of `arXiv:2610.17884`: if $G$ on $n \ge 7$ vertices has a vertex of degree $\ge 3$ or properly contains a cycle of length $\le 8$, then $\chi(\mathrm{KG}(G, 3)) \le n - 5$.

For sufficiency, suppose for contradiction that a counterexample exists, and choose one $G$ of **minimum order $n$**. By Schrijver's theorem, single cycles and path forests (spanning subgraphs of cycles) are $3$-tight. Hence $G$ contains at least one cycle of length $\ge 9$ and at least one vertex outside it, so $n \ge 10$. Adding ground edges restricts the vertex set of $\mathrm{KG}(G, 3)$ and cannot increase its chromatic number; thus we may join all path components end-to-end into a single path, and close that path into a cycle if it has $\ge 9$ vertices. Hence $G$ has at most one path component, of order at most $8$, and at least one cycle of length $\ge 9$.

Put $q = n - 5$, and consider a proper $q$-coloring of $\mathrm{KG}(G, 3)$ (equivalently, a cover of the $G$-stable triples by $q$ intersecting families). Every color class must have **empty total intersection** (be *nonstar*): if some color class had a common ground vertex $v$, deleting $v$ would leave a qualifying graph $G - v$ on $n - 1 \ge 9 \ge 7$ vertices colored with at most $q - 1 = (n - 1) - 5$ colors, contradicting minimality (or Schrijver's theorem if $G - v$ is a single cycle or path forest).

### Hilton–Milner Cutoff $n \le 19$

Let $p$ be the number of path components of $G$ (including isolated vertices) and $s$ the number of isolated vertices. Then $|E(G)| = n - p$ and $\sum_{v \in V(G)} \binom{\deg(v)}{2} = n - 2p + s$. Because $G$ is triangle-free and has maximum degree at most $2$, inclusion-exclusion on edges gives the exact number of $G$-stable triples:
$$|V(\mathrm{KG}(G, 3))| = \binom{n}{3} - |E(G)|(n - 2) + \sum_{v \in V(G)} \binom{\deg(v)}{2} = \frac{n(n - 4)(n - 5)}{6} + p(n - 4) + s \ge \frac{n(n - 4)(n - 5)}{6}.$$
By the Hilton–Milner theorem (proved directly by the classification in Section 3 below), every nonstar intersecting family of $3$-subsets of an $n$-set ($n \ge 7$) has size at most $3n - 8$. For $n \ge 20$,
$$\frac{n(n - 4)(n - 5)}{6} - (n - 5)(3n - 8) = \frac{(n - 5)(n^2 - 22n + 48)}{6} > 0,$$
contradicting the existence of a $q$-cover. Therefore any minimum counterexample has **$n \le 19$**.

---

## 2. The Cycle Plus Isolated Vertex Case $C_m \sqcup K_1$ ($m \ge 9$)

**Theorem 2.** *For every $m \ge 9$, $\chi(\mathrm{KG}(C_m \sqcup K_1, 3)) = m - 3$.*

*Proof.* Let $z$ be the isolated vertex and assume for contradiction that $\mathrm{KG}(C_m \sqcup K_1, 3)$ admits a proper coloring with $q = m - 4$ colors. Its restriction to $\mathrm{SG}(m, 3) = \mathrm{KG}(C_m, 3)$ is optimal by Schrijver's theorem, so every color appears on $C_m$.

1. **Anchor property (Section 3 of `arXiv:2610.17884`):** For each color $i$, some cycle triple $A_i$ of color $i$ has a disjoint cycle triple of every other color (otherwise every cycle triple of color $i$ could be greedily recolored to a missing color, contradicting $\chi(\mathrm{SG}(m, 3)) = q$). If another cycle triple $W$ of color $i$ met $A_i$ in only $1$ vertex, then $\{z\} \cup (A_i \setminus W)$ would be a stable triple disjoint from $W$ and from every cycle triple disjoint from $A_i$, leaving it no legal color. Hence every cycle triple of color $i$ meets $A_i$ in at least $2$ points.
2. **Nonstar property:** No full color class has a common ground vertex $x$; otherwise deleting $x$ leaves a $(q - 1)$-coloring of $C_m$ (if $x = z$) or $P_{m-1} \sqcup K_1$ (a spanning subgraph of $C_m$, if $x \in V(C_m)$), both contradicting $\chi(\mathrm{SG}(m, 3)) = q$.
3. **All $m \ge 15$ via Mantel's theorem:** Form the graph $H$ on $V(C_m)$ consisting of the $m$ edges of $C_m$ together with the $3$ pairs inside each of the $q = m - 4$ anchors $A_1, \dots, A_q$. Every $3$-subset of $V(C_m)$ either contains an edge of $C_m$ or is a cycle-stable triple (hence contains a pair of its color's anchor), so $\overline{H}$ is triangle-free. By Mantel's theorem,
   $$\binom{m}{2} - \left\lfloor \frac{m^2}{4} \right\rfloor \le |E(H)| \le m + 3q = 4m - 12.$$
   At $m = 15$ this gives $49 \le 48$, and incrementing $m$ increases the left-hand side by $\lfloor m/2 \rfloor \ge 7$ and the right-hand side by $4$. Thus no $q$-coloring exists for any $m \ge 15$.
4. **Remaining lengths $9 \le m \le 14$:** For each fixed anchor $A$, partition the remaining cycle-stable triples meeting $A$ in $2$ points into three groups indexed by the pair $p \subset A$. Any color class containing two triples $p \cup \{u\}, p \cup \{v\}$ in a group forces every $z$-member of that color to meet $p$ (avoiding $p$ while meeting $A$ forces the two cycle points to include the unique vertex of $A \setminus p$ and both $u$ and $v$, impossible). Hence each color class is contained in a maximal candidate obtained by selecting, in each of the three groups, either $\emptyset$, a singleton, or the full group, and adjoining all stable $z$-triples meeting every chosen cycle triple. Restricting to nonstar candidates and assigning dihedral-invariant integer weights (verified in `verify.py`):
   - For $m = 12, 13, 14$, the total weight $W$ exceeds $q B$ directly ($8102 > 8 \cdot 1004 = 8032$, $9425 > 9 \cdot 1003 = 9027$, $10857 > 10 \cdot 999 = 9990$).
   - For $m = 9, 10, 11$, exact branch-and-bound over maximal nonstar candidates (using the lower bound $w_{\mathrm{uncov}} - (t - 1)B$ on each selected family) exhausts all covers with zero solutions. $\square$

---

## 3. Classification of Nonstar Intersecting Triple Families and Finite Cases ($10 \le n \le 19$)

Let $\mathcal{F}$ be an intersecting family of $3$-subsets with empty total intersection (no $1$-point transversal).

- **No $2$-point transversal ($\tau(\mathcal{F}) \ge 3$):** Then $|\mathcal{F}| \le 10$ (the Frankl–Ota–Tokushige bound, verified directly by finite branching from the two canonical seeds $\{012, 034, 123\}$ and $\{012, 034, 135\}$ in `verify.py`).
- **$2$-point transversal $\{x, y\}$:** Include all triples containing $\{x, y\}$ in a covering template; the remaining triples have the form $\{x\} \cup e$ ($e \in L_x$) and $\{y\} \cup f$ ($f \in L_y$) where $L_x, L_y$ are nonempty cross-intersecting graphs on $V \setminus \{x, y\}$. Exactly one of four cases holds:
  1. Some link has a single edge $e$: $\mathcal{F}$ lies in a **Hilton–Milner template** (a triple $A$ plus all triples containing a fixed vertex $v \notin A$ and meeting $A$; size $\le 3n - 8$).
  2. Some link is a star of $\ge 3$ edges centered at $a$: every edge of the other link contains $a$, so $\mathcal{F}$ lies in the **triangle template** (all triples with $\ge 2$ points in $\{x, y, a\}$; size $\le 3n - 8$).
  3. Some link is a $2$-edge star $\{au, av\}$: every edge of the other link meets $a$ or equals $uv$, so $\mathcal{F}$ lies in the **two-pair template** (all triples containing $xy$ or $ya$, plus $yuv, xau, xav$).
  4. Neither link is a star or singleton: either one link is a triangle (forcing both links onto its $3$ vertices) or both contain two disjoint edges (forcing both links onto the same $4$-element set $D$). For each of the $6$ edges $e \subset D$, $\{x\} \cup e$ and $\{y\} \cup (D \setminus e)$ are disjoint, so at most $6$ triples beyond those containing $\{x, y\}$ occur.

Note that this four-case classification also proves $|\mathcal{F}| \le 3n - 8$ (Hilton–Milner for $k = 3$) directly.

### Exhaustion of Remaining Minimum Counterexamples ($10 \le n \le 19$)

By Theorem 2, a minimum counterexample is not of the form $C_m \sqcup K_1$, so it is either $C_m \sqcup P_r$ ($m \ge 9$, $2 \le r \le 8$), two cycles $C_{m_1} \sqcup C_{m_2}$ ($m_1, m_2 \ge 9$), or $C_9 \sqcup C_9 \sqcup K_1$ ($n = 19$). (Three cycles need $\ge 27$ vertices; two cycles plus $P_2$ need $\ge 20$.)

1. **Orders $n \le 12$:** Every such graph is a subgraph (possibly after vertex deletion) of $C_9 \sqcup P_3$ or $C_{10} \sqcup P_2$. By Corollary 2.2 of `arXiv:2610.17884` ($k$-tightness passes to subgraphs via edge deletion and adding a star class for deleted vertices), it suffices that $\chi(\mathrm{KG}(C_9 \sqcup P_3, 3)) = 8$ and $\chi(\mathrm{KG}(C_{10} \sqcup P_2, 3)) = 8$. Both graphs have $120$ stable triples; exact verification confirms neither admits a $7$-coloring.
2. **Order $n = 13$ ($C_9 \sqcup P_4$, $C_{10} \sqcup P_3$, $C_{11} \sqcup P_2$):** Explicit orbit-invariant integer weight vectors give $W > 8B$ directly over all four template types and the $\le 10$-triple bound:
   - $C_9 \sqcup P_4$: $W = 80{,}673 > 8 \cdot 10{,}003 = 80{,}024$.
   - $C_{10} \sqcup P_3$: $W = 80{,}715 > 8 \cdot 10{,}008 = 80{,}064$.
   - $C_{11} \sqcup P_2$: $W = 80{,}729 > 8 \cdot 10{,}003 = 80{,}024$.
3. **Orders $14 \le n \le 19$:** Using cardinalities, let $d = \max_{x \ne y} |\mathrm{pair}(x, y)|$ and $s = \max(10, d + 6)$, bounding all Case 4 and no-pair-transversal families. Whenever $u$ triples remain uncovered and $t$ colors remain, some class must cover at least $\lceil u / t \rceil$ uncovered triples; at every visited node $\lceil u / t \rceil > s$, so branching over Templates 1–3 of size $> s$ is exact. Exhaustion rules out every graph in orders $14 \dots 19$ (including $C_9 \sqcup C_9$, $C_9 \sqcup C_{10}$, and $C_9 \sqcup C_9 \sqcup K_1$).

This completes the proof of Theorem 1. $\square$

---

## 4. Two Results for Higher $k$

### 4.1 Exact Obstruction at $m = 4k - 3$ for the Section 2 Construction (All $k \ge 2$)

**Proposition 3.** *For all $k \ge 2$ and $m \ge 4k - 3$, no proper coloring of $\mathrm{KG}(C_m \sqcup K_1, k)$ with $q = m - 2k + 2$ colors restricts on $\mathrm{SG}(m, k)$ to color classes all contained in stars.*

*Proof.* Suppose each cycle color class has a center. All $q$ colors appear on $C_m$ and their centers are distinct (otherwise two colors could merge, violating Schrijver's theorem). Let $C \subset V(C_m)$ be the set of $q$ centers. Reassign every $z$-containing stable $k$-set that meets $C$ to the color of some center it contains; this remains proper because all such sets share $z$ and every cycle set of that color contains its center.

Every color must now contain a stable $k$-set disjoint from $C$ (otherwise every member of that color contains its center $x$, and deleting $x$ gives a $(q - 1)$-coloring of $P_{m-1} \sqcup K_1$, contradicting Schrijver's theorem). Because $C$ is a proper subset of $V(C_m)$ of size $q = m - 2k + 2 \ge 2k - 1$, $C$ induces a path forest on at least $2k - 1$ vertices, which always contains an independent $k$-set $T \subseteq C$. Since every color has a member disjoint from $C$ (hence disjoint from $T$), $T$ has no available color. $\square$

### 4.2 Explicit $k = 4$ Cutoff ($m \ge 39$) and General Finite Reduction

1. **All-$k$ Turán bound for $C_m \sqcup K_1$:** The anchor argument yields a graph $H$ on $C_m$ with at most $m + (m - 2k + 2)\binom{k}{2}$ edges whose complement is $K_k$-free, forcing $\frac{m^2}{2(k-1)} - \frac{m}{2} \le m + (m - 2k + 2)\binom{k}{2}$. For $k = 4$, this gives $(m^2 - 45m + 216)/6 \le 0$, impossible for all **$m \ge 40$**.
2. **Tightness at $k = 4, m = 39$ ($q = 33$):** For each color class choose a minimal subset of the $6$ pairs of its $4$-point anchor $A$ hitting every cycle member of that color, and let $t$ be the number of classes requiring all $6$ pairs. Turán's theorem requires at least $39^2/6 - 39/2 = 234 \le 39 + 5 \cdot 33 + t$, so $t \ge 30$. In any of those $t$ classes, each pair $p \subset A$ has a member $U_p$ with $U_p \cap A = p$, so every member meeting $A$ in $p$ has its outside pair meeting the fixed outside pair of $U_{A \setminus p}$, giving at most $2(39 - 4) - 3 = 67$ members per pair $p$, hence at most $1 + 4 \cdot 35 + 6 \cdot 67 = 543$ cycle members. The remaining $\le 3$ classes each have at most $\binom{38}{3} = 8{,}436$ members by Erdős–Ko–Rado. Thus at most $30 \cdot 543 + 3 \cdot 8{,}436 = 41{,}598 < 39\binom{34}{3}/4 = 58{,}344$ stable $4$-sets are covered, proving $4$-tightness for all **$m \ge 39$**.
3. **All-$k$ finite reduction:** For any fixed $k \ge 3$, comparing the Hilton–Milner bound $\binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$ against $\binom{n}{k} - n\binom{n-2}{k-2}$ reduces sufficiency of Conjecture 1.3 to finitely many ground vertices $n \le k(k - 1)(k + 2) + 1$ (sharply $n \le 19$ for $k = 3$, and $n \le 52$ for $k = 4$, failing from $n \ge 53$).
