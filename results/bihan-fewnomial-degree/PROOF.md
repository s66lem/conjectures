# Resolution of Bihan's First Open Case (`n = k = 3`) for the Topological Degree of Fewnomial Maps

## 1. Problem Statement

Let $F(x) = \sum_{i=1}^N C_i x^{a_i}$ be a real fewnomial map on $\mathbb{R}_{>0}^n$ with $n$ components and $N = n + k + 1$ monomials, whose exponent matrix $A$ (with columns $(1, a_i)$) and coefficient matrix $C$ (with columns $C_i \in \mathbb{R}^n$) satisfy the uniform general-position hypotheses `(UA)` and `(UC)` of Bihan ([arXiv:2611.34336v1](https://arxiv.org/abs/2611.34336)): all maximal minors of $A$ and $C$ are nonzero. Let $D(n, k)$ denote the set of values of $|\deg F|$ over all such maps.

Theorem 2 of Bihan yields $|\deg F| < \frac{1}{2} \min(M(n, N), M(k, N))$, where $M(n, N)$ is the maximal number of facets of a simplicial $n$-polytope with $N$ vertices. For $n = 3$, $M(3, N) = 2N - 4$, so Theorem 2 gives $|\deg F| \le N - 3 = k + 1$. After Theorem 2' and at the end of Section 5, Bihan states:

> "We do not know the maximal topological degree when $n, k \ge 3$. The first open case is $n = k = 3$, where Theorem 2 gives $|\deg F| \le 4$."
> "For $n, k \ge 3$ we do not know whether the bound of Theorem 2 is sharp. It gives $|\deg F| \le 4$ for $n = k = 3$ and $|\deg F| \le 13$ for $n = k = 4$."

We prove that Theorem 2 is not sharp for $n = 3$ and any $k \ge 3$ ($N \ge 7$), and determine $D(3, 3)$ completely.

---

## 2. Main Theorem

**Theorem 1.** *Let $n = 3$ and let $F(x) = \sum_{i=1}^N C_i x^{a_i}$ satisfy `(UA)` and `(UC)`. Let $V \le N$ be the number of vertices of the Newton polytope $P = \mathrm{conv}(A) \subset \mathbb{R}^3$. Then*
$$|\deg F| \le \left\lfloor \frac{3V - 8}{4} \right\rfloor \le \left\lfloor \frac{3N - 8}{4} \right\rfloor.$$
*Consequently, for every $k \ge 1$,*
$$\max D(3, k) \le \left\lfloor \frac{3k}{4} \right\rfloor + 1, \qquad \max D(k, 3) \le \left\lfloor \frac{3k}{4} \right\rfloor + 1.$$

**Corollary 2.** *$D(3, 3) = \{0, 1, 2, 3\}$. In particular, $|\deg F| = 4$ is impossible for $n = k = 3$, so Bihan's Theorem 2 is not sharp for $n = k = 3$ (nor for any $n = 3$, $k \ge 3$).*

---

## 3. Proof of Theorem 1

### Step 1: Spherical geodesic map
By `(UA)`, the Newton polytope $P = \mathrm{conv}(A) \subset \mathbb{R}^3$ is a simplicial $3$-polytope with $V \le N$ vertices and $F = 2V - 4$ triangular facets (by Euler's formula $V - E + F = 2$ and $2E = 3F$). Every point of $A$ on $\partial P$ is a vertex of $P$.

By Lemma 1.1 and Theorem 1.3 of Bihan (arXiv:2611.34336v1), $\deg F$ equals the topological degree of the continuous map $g : \partial P \to S^2$ obtained by mapping each vertex $a_s \in \partial P$ to $C_s$, extending affinely on each facet, and projecting radially onto $S^2$. Under `(UC)`, any three columns $C_i, C_j, C_k$ are linearly independent, so $g$ maps each oriented facet $t = (i, j, k)$ (ordered counterclockwise when viewed from outside $P$) homeomorphically onto the spherical geodesic triangle $\Delta_t \subset S^2$ spanned by $u_i = C_i/\|C_i\|$, $u_j = C_j/\|C_j\|$, $u_k = C_k/\|C_k\|$. Its orientation sign is $\varepsilon_t = \mathrm{sgn}\det(C_i, C_j, C_k) \in \{+1, -1\}$.

Let $F_+$ and $F_-$ denote the numbers of facets with $\varepsilon_t = +1$ and $\varepsilon_t = -1$, respectively, so $F_+ + F_- = F = 2V - 4$. For every generic unit vector $u \in S^2$ (lying outside the finitely many great-circle arcs spanned by pairs $C_i, C_j$),
$$d := \deg F = \deg g = \sum_{t : u \in \Delta_t} \varepsilon_t.$$
Integrating over $u \in S^2$ with respect to normalized surface area yields
$$4\pi d = \sum_{t} \varepsilon_t \, \mathrm{Area}(\Delta_t).$$

### Step 2: Spherical Gauss–Bonnet identity
For each spherical triangle $\Delta_t$, Girard's theorem gives
$$\mathrm{Area}(\Delta_t) = \alpha_{t,i} + \alpha_{t,j} + \alpha_{t,k} - \pi,$$
where $\alpha_{t,v} \in (0, \pi)$ is the interior spherical angle of $\Delta_t$ at vertex $v \in t$. Substituting this into the area sum and regrouping the angles by vertex $v$ of $P$, we obtain
$$4\pi d = \sum_{v \in V(P)} \left( \sum_{t \ni v} \varepsilon_t \alpha_{t,v} \right) - \pi (F_+ - F_-).$$

Fix a vertex $v$ of $P$, and let $a_1, \dots, a_{\delta_v}$ be the vertices of its link in $\partial P$ in counterclockwise cyclic order viewed from outside $P$. In the oriented tangent plane $T_{u_v} S^2 = u_v^\perp$ (oriented by the outward normal $u_v$), let $w_i \in T_{u_v} S^2 \setminus \{0\}$ be the unit tangent direction along the geodesic arc from $u_v$ to $u_{a_i}$ (well-defined because $C_v$ and $C_{a_i}$ are linearly independent by `(UC)`). For the facet $t_i = (v, a_i, a_{i+1})$, the determinant $\det(C_v, C_{a_i}, C_{a_{i+1}})$ has sign $\varepsilon_{t_i}$, so the signed angle from $w_i$ to $w_{i+1}$ in $T_{u_v} S^2$ is precisely $\theta_{t_i} = \varepsilon_{t_i} \alpha_{t_i, v} \in (-\pi, \pi) \setminus \{0\}$.

Because the cyclic sequence of unit vectors $w_1, w_2, \dots, w_{\delta_v}, w_1$ forms a closed loop in $S^1 \subset T_{u_v} S^2$, the total signed turn is an integer multiple of $2\pi$:
$$\sum_{t \ni v} \varepsilon_t \alpha_{t,v} = 2\pi w_v \qquad (w_v \in \mathbb{Z}).$$
Dividing the area identity by $\pi$ yields the exact integer identity
$$4d = 2 \sum_{v \in V(P)} w_v - F_+ + F_-.$$

### Step 3: Local winding bound and global summation
Let $p_v$ be the number of positive facets ($\varepsilon_t = +1$) incident to vertex $v$. Since $\alpha_{t,v} \in (0, \pi)$ for every facet $t \ni v$ and negative facets contribute strictly negatively (if any exist), we have
$$2\pi w_v = \sum_{t \ni v,\, \varepsilon_t = +1} \alpha_{t,v} - \sum_{t \ni v,\, \varepsilon_t = -1} \alpha_{t,v} < \pi p_v.$$
The inequality is strict even when $p_v = 0$ because $\delta_v \ge 3$ forces at least three negative facets at $v$, giving $2\pi w_v < 0 = \pi p_v$. Dividing by $\pi$, we obtain $2 w_v < p_v$, and since both $2w_v$ and $p_v$ are integers,
$$2 w_v \le p_v - 1.$$

Summing over all $V$ vertices of $P$ and using $\sum_{v} p_v = 3 F_+$ (each positive triangular facet has $3$ vertices), we obtain
$$4d = 2 \sum_{v} w_v - F_+ + F_- \le (3 F_+ - V) - F_+ + F_- = 2 F_+ + F_- - V = F + F_+ - V.$$
Since $F_+ \le F = 2V - 4$, this yields
$$4d \le 2F - V = 2(2V - 4) - V = 3V - 8.$$

### Step 4: Symmetry and duality
Negating the first coordinate of every column $C_i$ preserves `(UC)` and multiplies every determinant $\det(C_i, C_j, C_k)$ (and hence $\deg F$) by $-1$. Applying the bound to the negated map gives $-4d \le 3V - 8$. Therefore
$$4|d| \le 3V - 8 \implies |d| \le \left\lfloor \frac{3V - 8}{4} \right\rfloor \le \left\lfloor \frac{3N - 8}{4} \right\rfloor.$$
For $N = k + 4$, $\lfloor (3(k+4) - 8)/4 \rfloor = \lfloor (3k + 4)/4 \rfloor = \lfloor 3k/4 \rfloor + 1$. By Bihan's Gale-duality Theorem 3 ($D(n, k) = D(k, n)$), the same upper bound holds for $D(k, 3)$.

### Remark on Equality
Equality $4d = 3V - 8$ requires simultaneously $F_+ = F$ (every facet positively oriented, so $p_v = \delta_v$) and $2w_v = \delta_v - 1$ for every vertex $v$ (so every vertex has odd degree $\delta_v$). In that case $g : \partial P \to S^2$ is an orientation-preserving branched covering of degree $d$ with ramification index $w_v$ at vertex $v$, and Riemann–Hurwitz matches: $\sum_v (w_v - 1) = \frac{1}{2}\sum_v (\delta_v - 3) = \frac{1}{2}(6V - 12 - 3V) = \frac{3V-12}{2} = 2d - 2$.

---

## 4. Exact Integer Realizations (`D(3, 3) = {0, 1, 2, 3}` and Extremal Cases)

For $n = k = 3$ ($N = 7$), Theorem 1 gives $|\deg F| \le \lfloor (21 - 8)/4 \rfloor = 3$. In `verify.py`, explicit $3 \times 7$ integer exponent and coefficient matrices $(A, C)$ satisfying `(UA)` and `(UC)` realize $|\deg F| = 0, 1, 2, 3$, proving $D(3, 3) = \{0, 1, 2, 3\}$. For example, the degree-$3$ witness is:
- $A$: $(3, 1, 3), (11, 4, -1), (-4, 2, 6), (-5, 3, -5), (-10, -3, 9), (0, -7, 2), (3, 2, -7)$,
- $C$: $(-13, 15, -22), (10, -25, 14), (-20, 0, 23), (11, 17, -22), (-8, -26, 13), (9, 28, 5), (-24, -15, 10)$.

Further exact integer realizations in `verify.py` attain $|\deg F| = \lfloor (3V - 8)/4 \rfloor$ with $V = N$ for:
- $V = 8$: $|\deg F| = 4$ (on the all-odd triangulation with vertex degrees $(3, 3, 5^6)$),
- $V = 9$: $|\deg F| = 4$,
- $V = 10$: $|\deg F| = 5$,
- $V = 12$: $|\deg F| = 7$ (an integer perturbation of the regular icosahedron $A$ mapped to its Galois conjugate $\varphi \mapsto -1/\varphi$, realizing the great icosahedron $\{3, 5/2\}$ of density $7$).

Because adding interior points to $P$ does not alter $\deg F$, $\max D(3, k)$ is nondecreasing in $k$, and we obtain $\max D(3, k) = \lfloor 3k/4 \rfloor + 1$ for $k = 3, 4, 5, 6, 8$.
