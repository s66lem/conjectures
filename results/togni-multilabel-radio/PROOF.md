# Multi-Label Radio Labelings of Paths and Cycles (`arXiv:2610.25863`)

We resolve **Conjecture 2** of Olivier Togni (*On Multi-label radio Labelings of Graphs*, `arXiv:2610.25863`, Section 5) for all $k, m \ge 1$, establish the **upper bound in Conjecture 1** for all $n, k, m \ge 1$, prove **exact equality in Conjecture 1 for $k = 3$ and all $m \ge 1$**, and prove a **divisibility obstruction** explaining why modulus-$S$ toroidal constructions cannot close on arbitrary cycle lengths.

---

## 1. Definitions and Main Results

Following Togni (`arXiv:2610.25863`, Definition 1.1), for integers $m, k \ge 1$ and a connected graph $G = (V, E)$, an **$(m, k)$-radio labeling** of $G$ assigns to each vertex $x \in V$ an $m$-element subset $\ell(x) \subset \mathbb{N}$ such that for all (not necessarily distinct) $x, y \in V$ and all $c_x \in \ell(x)$, $c_y \in \ell(y)$ with $(x, c_x) \neq (y, c_y)$,
$$|c_x - c_y| \ge k + 1 - d_G(x, y),$$
where $d_G(x, y)$ is the shortest-path distance in $G$. Equivalently, representing $\ell$ by the $m|V|$ incidences $(x, c)$ with $c \in \ell(x)$, every two distinct incidences satisfy
$$d_G(x, y) + |c_x - c_y| \ge k + 1.$$
The **span** of $\ell$ is $\max_{x, c \in \ell(x)} c - \min_{x, c \in \ell(x)} c$, and the **$(m, k)$-radio number** $\lambda_k^m(G)$ is the minimum span over all $(m, k)$-radio labelings of $G$.

Write
$$D := k + 1, \qquad S := \left\lceil \frac{(k+1)^2}{2} \right\rceil = \left\lceil \frac{D^2}{2} \right\rceil.$$
Note that $S = 2r^2$ when $D = 2r$ (odd $k$), and $S = 2r^2 + 2r + 1 = r^2 + (r+1)^2$ when $D = 2r+1$ (even $k$). In every case $S \ge D$.

**Theorem 1 (Conjecture 1 Upper Bound — All $n, k, m \ge 1$).** *For all integers $n, k, m \ge 1$,*
$$\lambda_k^m(P_n) \le mS - 1.$$
*Moreover, $\lambda_k^m(C_n) \le mS - 1$ whenever $n \ge 3$ and $S \mid n$.*

**Theorem 2 (Resolution of Conjecture 2 — All $k, m \ge 1$).** *Set $M := mS + 1$ and let $a := k$ for odd $k$ and $a := k + 1$ for even $k$. For every integer $n \ge \max\{3, \lceil kSM/2 \rceil\}$ (and more sharply, whenever $n \ge \max\{3, kM \cdot \mathrm{dist}(an, S\mathbb{Z})\}$),*
$$\lambda_k^m(C_n) \le mS.$$

**Theorem 3 (Exact Resolution of Conjecture 1 for $k = 3$ — All $m \ge 1$).** *For every integer $m \ge 1$, there exists $n_0 = n_0(m)$ such that for all $n \ge n_0$,*
$$\lambda_3^m(P_n) = 8m - 1.$$

**Theorem 4 (Modulus-$S$ Toroidal Obstruction).** *For $k \ge 1$, consider a toroidal one-label assignment on $\mathbb{Z}_n \times \mathbb{Z}_S$ assigning one color $c(i) \in \mathbb{Z}_S$ per vertex $i \in \mathbb{Z}_n$ such that distinct incidences $(i, c(i))$ and $(j, c(j))$ have toroidal Manhattan distance at least $D$ (which is forced by any modular scheme $f(v_i) = L_{y(i)}$ with $L_y = \{y + jS : 0 \le j < m\}$ when $m \ge 2$). For all sufficiently large $n$:*
1. *If $k$ is even ($D = 2r+1$), such a toroidal assignment exists if and only if $S \mid n$.*
2. *If $k$ is odd ($D = 2r$), such a toroidal assignment exists only if $D \mid n$.*

---

## 2. Proof of Theorem 1: The Lattice Construction

Define $a := k = 2r - 1$ when $D = 2r$ (odd $k$), and $a := k + 1 = 2r + 1$ when $D = 2r + 1$ (even $k$). Consider the integer lattice
$$L := \{(h, z) \in \mathbb{Z}^2 : z \equiv a h \pmod{S}\}.$$

**Lemma 2.1.** *Every nonzero vector $(h, z) \in L \setminus \{(0, 0)\}$ satisfies $|h| + |z| \ge D$.*

*Proof.* Since $L$ has index $S$ in $\mathbb{Z}^2$, any two vectors $e_1, e_2 \in L$ with $|\det(e_1, e_2)| = S$ form a $\mathbb{Z}$-basis of $L$.

- **Case 1: $D = 2r$ ($r \ge 1$, $S = 2r^2$, $a = 2r - 1$).** Set $e_1 = (r, -r)$ and $e_2 = (r+1, r-1)$. Check membership in $L$:
  $$a r - (-r) = (2r - 1)r + r = 2r^2 = S,$$
  $$a(r+1) - (r-1) = (2r-1)(r+1) - (r-1) = 2r^2 = S.$$
  Check the determinant:
  $$\det\begin{pmatrix} r & r+1 \\ -r & r-1 \end{pmatrix} = r(r-1) + r(r+1) = 2r^2 = S.$$
  Hence $e_1, e_2$ is a $\mathbb{Z}$-basis of $L$. For any $(h, z) = u e_1 + v e_2 \in L \setminus \{(0, 0)\}$ with $u, v \in \mathbb{Z}$:
  - Its coordinate sum is $h + z = u(r - r) + v((r+1) + (r-1)) = 2rv$. If $v \neq 0$, then $|h| + |z| \ge |h + z| = 2r|v| \ge 2r = D$.
  - If $v = 0$, then $u \neq 0$ and $(h, z) = (ru, -ru)$, so $|h| + |z| = 2r|u| \ge 2r = D$.

- **Case 2: $D = 2r + 1$ ($r \ge 1$, $S = 2r^2 + 2r + 1$, $a = 2r + 1$).** Set $e_1 = (r, -r-1)$ and $e_2 = (r+1, r)$. Check membership in $L$:
  $$a r - (-r-1) = (2r+1)r + r + 1 = 2r^2 + 2r + 1 = S,$$
  $$a(r+1) - r = (2r+1)(r+1) - r = 2r^2 + 2r + 1 = S.$$
  Check the determinant and orthogonality:
  $$\det\begin{pmatrix} r & r+1 \\ -r-1 & r \end{pmatrix} = r^2 + (r+1)^2 = S, \qquad e_1 \cdot e_2 = r(r+1) - (r+1)r = 0,$$
  and $\|e_1\|_2^2 = \|e_2\|_2^2 = S$. For $(h, z) = u e_1 + v e_2 \neq (0, 0)$:
  - If $u^2 + v^2 = 1$, then $(h, z) \in \{\pm e_1, \pm e_2\}$, which has $|h| + |z| = r + (r+1) = D$.
  - If $u^2 + v^2 \ge 2$, then by Cauchy–Schwarz / monotonicity of $\ell_1 \ge \ell_2$,
    $$|h| + |z| \ge \sqrt{h^2 + z^2} = \sqrt{(u^2 + v^2)S} \ge \sqrt{2S} = \sqrt{D^2 + 1} > D.$$

This proves Lemma 2.1. $\blacksquare$

*Proof of Theorem 1.* On $P_n$ with vertices $0, 1, \dots, n-1$, assign to vertex $i$ the $m$ labels
$$\ell(i) := \{(a i \bmod S) + jS : 0 \le j < m\},$$
where $a i \bmod S \in \{0, \dots, S-1\}$. All labels lie in $\{0, \dots, mS - 1\}$, so the span is at most $mS - 1$, and at each vertex the $m$ labels are distinct. For any two distinct incidences $(i, c)$ and $(i', c')$, we have $c \equiv a i \pmod S$ and $c' \equiv a i' \pmod S$, so $(h, z) := (i' - i, c' - c)$ is a nonzero vector in $L$. By Lemma 2.1,
$$d_{P_n}(i, i') + |c - c'| = |h| + |z| \ge D = k + 1.$$
When $n \ge 3$ and $S \mid n$, the same assignment is well-defined on $C_n$ because $a(i + n) \equiv a i \pmod S$. Lifting any shortest cycle arc between $i$ and $i'$ to an integer displacement $h$ with $|h| = d_{C_n}(i, i')$ and $i' \equiv i + h \pmod n$, we still have $c' - c \equiv a(i + h) - a i = ah \pmod S$, so $(h, c' - c) \in L \setminus \{(0, 0)\}$ and $|h| + |c' - c| \ge D$. $\blacksquare$

---

## 3. Proof of Theorem 2 (Conjecture 2)

Let $k, m \ge 1$, $M := mS + 1$, and let $a \in \{k, k+1\}$ be as in Section 2. Let $n \ge 3$ satisfy
$$n \ge k M \cdot \mathrm{dist}(an, S\mathbb{Z}).$$
Since $\mathrm{dist}(an, S\mathbb{Z}) \le S/2$, this holds in particular whenever $n \ge \max\{3, \lceil kSM/2 \rceil\}$.

Choose an integer $t$ minimizing $|t S - a n|$, so that
$$|t S - a n| = \mathrm{dist}(an, S\mathbb{Z}) \le \frac{n}{k M}.$$
(If $an/S$ is a half-integer, either nearest integer works.)

For all integers $i, j \in \mathbb{Z}$, define
$$F(i, j) := \left\lfloor \frac{M}{m}\left(\frac{t i}{n} + j\right) \right\rfloor = \left\lfloor \frac{M(t i + j n)}{m n} \right\rfloor.$$
At vertex $i \in \mathbb{Z}_n$ of $C_n$, assign the set of least nonnegative residues modulo $M$:
$$\ell(i) := \{F(i, j) \bmod M : 0 \le j < m\} \subseteq \{0, 1, \dots, M - 1\} = \{0, 1, \dots, mS\}.$$

**Step 1: Periodicity and well-definedness on $C_n$.** For all $i, j \in \mathbb{Z}$, direct substitution yields two exact identities:
$$F(i + n, j) = F(i, j + t), \qquad F(i, j + m) = F(i, j) + M.$$
From the second identity, the residue $F(i, j) \bmod M$ depends only on $j \bmod m$, so $\{F(i, j) \bmod M : j \in \mathbb{Z}\} = \{F(i, j) \bmod M : 0 \le j < m\}$. From the first identity, shifting $i \mapsto i + n$ simply shifts the index $j \mapsto j + t$ and leaves the residue set unchanged. Hence $\ell(i)$ depends only on $i \bmod n$.

**Step 2: Cardinality $m$ and same-vertex separation.** Fix $i \in \mathbb{Z}$. For any $j \in \mathbb{Z}$, the unrounded argument increases by $M/m = S + 1/m > S$ when $j$ increases by $1$. Therefore
$$F(i, j + 1) - F(i, j) \ge \left\lfloor \frac{M}{m} \right\rfloor = \begin{cases} S & \text{if } m \ge 2, \\ S + 1 & \text{if } m = 1, \end{cases}$$
so $F(i, j + 1) - F(i, j) \ge S$ in all cases. Moreover, $F(i, 0) < F(i, 1) < \dots < F(i, m) = F(i, 0) + M$. Consequently, the $m$ residues $F(i, 0) \bmod M, \dots, F(i, m - 1) \bmod M$ are pairwise distinct, and their cyclic spacing on $\mathbb{Z}/M\mathbb{Z}$ (including the wraparound step from $j = m - 1$ to $j = m$) is at least $S$. Since ordinary integer distance is at least cyclic distance modulo $M$, any two distinct labels at vertex $i$ satisfy
$$|c_1 - c_2| \ge S \ge D = k + 1.$$

**Step 3: Distinct-vertex separation.** Let $x, y \in V(C_n)$ be distinct vertices with $1 \le d_{C_n}(x, y) \le k$ (pairs at distance $\ge k + 1$ require separation $\le 0$, which holds trivially). Choose integer lifts $i, i + h \in \mathbb{Z}$ representing $x, y$ such that $1 \le |h| = d_{C_n}(x, y) \le k$.

Let $c_1 \in \ell(x)$ and $c_2 \in \ell(y)$. By definition of $\ell(x)$, there exist $j_0 \in \{0, \dots, m - 1\}$ and $q_1 \in \mathbb{Z}$ such that $c_1 = F(i, j_0) - q_1 M$. By the shift identity $F(i, j + m) = F(i, j) + M$, setting $j := j_0 - q_1 m \in \mathbb{Z}$ gives the **exact** equality $c_1 = F(i, j)$ (with no modulo operation). Similarly, there exists $j' \in \mathbb{Z}$ such that $c_2 = F(i + h, j')$ exactly.

Set
$$z := a h + S(j' - j) \in \mathbb{Z}.$$
Then $(h, z) \in L$ and $h \neq 0$, so by Lemma 2.1, $|h| + |z| \ge D$, which gives
$$|z| \ge D - |h| \ge 1.$$
Now compute the difference between the unrounded arguments of $F(i + h, j')$ and $F(i, j)$:
$$\Delta := \frac{M}{m}\left(\frac{t(i + h)}{n} + j'\right) - \frac{M}{m}\left(\frac{t i}{n} + j\right) = \frac{M}{m}\left(\frac{t h}{n} + (j' - j)\right).$$
Substituting $j' - j = (z - a h)/S$ and $M = mS + 1$ yields
$$\Delta = \frac{M}{m S} z + \frac{M}{m}\left(\frac{t}{n} - \frac{a}{S}\right) h = \left(1 + \frac{1}{m S}\right) z + \frac{M(t S - a n)}{m n S} h.$$
By our choice of $t$ and hypothesis $|t S - a n| \le n / (k M)$, together with $|h| \le k$, the error term satisfies
$$\left|\frac{M(t S - a n)}{m n S} h\right| \le \frac{M \cdot (n / (k M)) \cdot k}{m n S} = \frac{1}{m S}.$$
Therefore, by the reverse triangle inequality and $|z| \ge 1$,
$$|\Delta| \ge \left(1 + \frac{1}{m S}\right)|z| - \frac{1}{m S} = |z| + \frac{|z| - 1}{m S} \ge |z| \ge D - |h|.$$
Finally, for any real numbers $u, v$ and any integer $K \ge 0$, if $|u - v| \ge K$ then $|\lfloor u \rfloor - \lfloor v \rfloor| \ge K$ (assuming without loss of generality $u \ge v + K$, monotonicity of floor gives $\lfloor u \rfloor \ge \lfloor v + K \rfloor = \lfloor v \rfloor + K$). Applying this with $K = D - |h| \in \mathbb{Z}_{\ge 1}$ gives
$$|c_2 - c_1| = |F(i + h, j') - F(i, j)| \ge D - |h| = k + 1 - d_{C_n}(x, y).$$

All labels lie in $\{0, \dots, mS\}$, so $\lambda_k^m(C_n) \le mS$. $\blacksquare$

---

## 4. Proof of Theorem 3: Exact Equality for $k = 3$ and All $m \ge 1$

For $k = 3$ we have $D = 4$ and $S = 8$. By Theorem 1 (and Togni Proposition 4.4), $\lambda_3^m(P_n) \le 8m - 1$ for all $n, m \ge 1$. Moreover, $\lambda_3^m(P_n)$ is non-decreasing in $n$, because restricting any $(m, 3)$-radio labeling of $P_{n+1}$ to its first $n$ vertices yields a valid $(m, 3)$-radio labeling of $P_n$ of no greater span. It therefore suffices to show that for every $m \ge 1$, there is some $n$ with $\lambda_3^m(P_n) \ge 8m - 1$.

Suppose for contradiction that for every $n \ge 1$, $P_n$ admits an $(m, 3)$-radio labeling of span at most $8m - 2$. By translating labels, we may assume every label lies in $\{0, 1, \dots, 8m - 2\}$. Since separation constraints only act on vertices at distance at most $3$, the legality of appending a label set at vertex $i$ depends only on the triple of label sets $(\ell(i-3), \ell(i-2), \ell(i-1))$. There are only finitely many such triples (at most $\binom{8m-1}{m}^3$). Choosing $n$ larger than the number of triples, some triple repeats in the labeling of $P_n$, producing a periodic $(m, 3)$-radio labeling of $\mathbb{Z}$ with some period $p \ge 1$. Repeating the period if necessary, let $N \ge 8$ be a multiple of $p$. Then we obtain a set of $mN$ incidences (centers) in $\mathbb{Z}_N \times \{0, 1, \dots, 8m - 2\}$, with $m$ centers in each column $i \in \mathbb{Z}_N$, such that any two distinct centers have toroidal horizontal distance plus vertical distance at least $4$.

Define the 8-element shape $B \subset \mathbb{Z} \times \{-1, 0, 1\}$ with horizontal sections:
- height $-1$: $\{0, 1\}$ (size $2$),
- height $0$: $\{-1, 0, 1, 2\}$ (size $4$),
- height $+1$: $\{0, 1\}$ (size $2$).

Direct verification shows that the Manhattan diameter of $B$ is $3$: the horizontal span within height $0$ is $2 - (-1) = 3$; between height $0$ and height $\pm 1$, the maximum horizontal difference is $2$ plus vertical difference $1$; between height $-1$ and height $+1$, the maximum horizontal difference is $1$ plus vertical difference $2$. Because $N \ge 8$, the translates $(i, y) + B \subset \mathbb{Z}_N \times \mathbb{Z}$ centered at the $mN$ incidences are pairwise disjoint (if two translates shared a point, their centers would have toroidal Manhattan distance at most $3$, impossible).

For $y \in \mathbb{Z}$, let $f_y$ be the number of centers at height $y$, with $f_y = 0$ for $y \notin \{0, \dots, 8m - 2\}$. Counting how many disjoint translates cover points of $\mathbb{Z}_N \times \{y\}$ gives, for every $y \in \mathbb{Z}$,
$$2 f_{y-1} + 4 f_y + 2 f_{y+1} \le N. \tag{1}$$
Sum (1) over the $4m$ even heights $y = 0, 2, 4, \dots, 8m - 2$. Each even height $y \in \{0, 2, \dots, 8m-2\}$ contributes $4 f_y$. Each odd height $2j + 1 \in \{1, 3, \dots, 8m - 3\}$ lies strictly between two consecutive even heights $2j$ and $2j + 2$ in the range, so it contributes $2 f_{2j+1} + 2 f_{2j+1} = 4 f_{2j+1}$. Thus
$$4 m N = 4 \sum_{y=0}^{8m-2} f_y = \sum_{j=0}^{4m-1} (2 f_{2j-1} + 4 f_{2j} + 2 f_{2j+1}) \le 4m N.$$
Hence equality holds in (1) at every even height $y = 2j$ ($0 \le j \le 4m - 1$):
$$4 f_{2j} = N - 2 f_{2j-1} - 2 f_{2j+1}. \tag{2}$$

Set $b_j := f_{2j+1} \ge 0$ for $0 \le j \le 4m - 2$, with boundary values $b_{-1} := f_{-1} = 0$ and $b_{4m-1} := f_{8m-1} = 0$. For each odd height $y = 2j + 1$ ($0 \le j \le 4m - 2$), substitute (2) for $f_{2j}$ and $f_{2j+2}$ into (1) at $y = 2j + 1$:
$$2\left(\frac{N - 2b_{j-1} - 2b_j}{4}\right) + 4 b_j + 2\left(\frac{N - 2b_j - 2b_{j+1}}{4}\right) \le N,$$
which simplifies to
$$2 b_j \le b_{j-1} + b_{j+1} \qquad (0 \le j \le 4m - 2).$$
Thus $(b_{-1}, b_0, \dots, b_{4m-1})$ is a nonnegative discrete-convex sequence with $b_{-1} = b_{4m-1} = 0$, so $b_j = 0$ for all $j$ (if $\max_j b_j > 0$, a first index attaining the maximum violates $2 b_j \le b_{j-1} + b_{j+1}$).

Plugging $f_{\text{odd}} = 0$ back into (2) yields $f_{2j} = N/4$ for every $0 \le j \le 4m - 1$ (in particular $4 \mid N$). Any two centers at the same height $2j$ must have horizontal cyclic distance at least $4$, so placing $N/4$ centers on $\mathbb{Z}_N$ forces them to occupy a single residue class $r_j \pmod 4$. For two consecutive even heights $2j$ and $2j+2$ (vertical distance $2$), their horizontal distances must be at least $2$, which rules out $r_{j+1} \equiv r_j$ and $r_{j+1} \equiv r_j \pm 1 \pmod 4$. Hence $r_{j+1} \equiv r_j + 2 \pmod 4$ for every $j$.

By induction, all residue classes $r_j$ have the same parity modulo $2$. Therefore every center lies in a column $i \in \mathbb{Z}_N$ of that single parity, contradicting the fact that every column has $m \ge 1$ centers. This contradiction establishes $\lambda_3^m(P_n) = 8m - 1$ for all sufficiently large $n$. $\blacksquare$

---

## 5. Proof of Theorem 4: Modulus-$S$ Toroidal Obstruction

Suppose we have $n$ centers on the discrete torus $\mathbb{Z}_n \times \mathbb{Z}_S$ with minimum toroidal Manhattan distance $D = k + 1$, and take $n \ge 2D$. Let $f_y$ ($y \in \mathbb{Z}_S$) be the number of centers with vertical coordinate $y$, so $\sum_{y \in \mathbb{Z}_S} f_y = n$. For $b \ge 1$, define the triangular kernel $T_b(j) := \max(b - |j|, 0)$ periodized modulo $S$ (valid since $2b - 1 \le S$). Its discrete second difference modulo $S$ satisfies
$$T_b(j - 1) - 2 T_b(j) + T_b(j + 1) = -2\delta_0(j) + \delta_b(j) + \delta_{-b}(j).$$

- **Case 1: Even $k$ ($D = 2r + 1$, $S = 2r^2 + 2r + 1$).** Let $B \subset \mathbb{Z}^2$ be the Manhattan ball of radius $r$: $\{(x, y) : |x| + |y| \le r\}$. Its diameter is $2r = D - 1$, its horizontal section at height $y$ has size $2(r - |y|) + 1 = T_r(y) + T_{r+1}(y)$, and its cardinality is $|B| = 2r^2 + 2r + 1 = S$. Because $n \ge 2D$, the $n$ translates of $B$ by the $n$ centers embed disjointly into $\mathbb{Z}_n \times \mathbb{Z}_S$; since they have total cardinality $nS = |\mathbb{Z}_n \times \mathbb{Z}_S|$, they partition the torus exactly. Counting covered points at each row $y \in \mathbb{Z}_S$ gives
  $$((T_r + T_{r+1}) * f)_y = n \qquad (\forall y \in \mathbb{Z}_S).$$
  Applying the discrete second difference annihilates the constant $n$ and yields
  $$4 f_y = f_{y-r} + f_{y+r} + f_{y-r-1} + f_{y+r+1} \qquad (\forall y \in \mathbb{Z}_S).$$
  At a height $y^*$ maximizing $f_y$, all four neighbors $y^* \pm r, y^* \pm (r+1)$ must also attain the maximum. Since $\gcd(r, r+1) = 1$, the steps $r$ and $r+1$ generate $\mathbb{Z}_S$, so $f_y$ is constant on $\mathbb{Z}_S$. Thus $n = \sum_{y \in \mathbb{Z}_S} f_y = S f_0$, so $S \mid n$. Conversely, Theorem 1 supplies a valid toroidal assignment whenever $S \mid n$.

- **Case 2: Odd $k$ ($D = 2r$, $S = 2r^2$).** Let $B \subset \mathbb{Z}^2$ be the union of two radius-$(r-1)$ Manhattan balls centered at $(0, 0)$ and $(1, 0)$. Its diameter is $2(r-1) + 1 = 2r - 1 = D - 1$, its horizontal section at height $y$ has size $2(r - |y|) = 2 T_r(y)$, and its cardinality is $|B| = 2r^2 = S$. Again, for $n \ge 2D$ the $n$ translates partition $\mathbb{Z}_n \times \mathbb{Z}_S$ exactly, giving $(2 T_r * f)_y = n$ for all $y \in \mathbb{Z}_S$. Taking the second difference yields
  $$2 f_y = f_{y-r} + f_{y+r} \qquad (\forall y \in \mathbb{Z}_S).$$
  By the maximum principle on each coset of $\langle r \rangle \subset \mathbb{Z}_S$ (which has size $S/r = 2r = D$), $f_y$ is constant on each coset. Hence $n = \sum_{y \in \mathbb{Z}_S} f_y = 2r \sum_{y=0}^{r-1} f_y$, so $D = 2r \mid n$. $\blacksquare$
