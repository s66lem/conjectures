# Complete Proof of Takuto Nakai's OEIS A400474 Conjecture

## 1. Statement

For an integer $n \ge 3$, let $a(n)$ ([OEIS A400474](https://oeis.org/A400474)) denote the maximum, over all nondegenerate Euclidean triangles $\triangle ABC$, of the number of strictly interior points $P$ such that the three angles $\angle BPC, \angle CPA, \angle APB$ are pairwise distinct integer multiples of $\pi / n$.

**Theorem 1 (OEIS A400474 Conjecture).** *For every integer $n \ge 3$,*
$$a(n) = \frac{n^2 - 4n + c(n \bmod 6)}{3}, \qquad c(0, 1, 2, 3, 4, 5) = (6, -3, 4, 3, 0, -5).$$

## 2. Geometric Bijection

Let $\triangle ABC$ be a nondegenerate triangle with interior angles $A, B, C \in (0, \pi)$, $A + B + C = \pi$. For any strictly interior point $P$, set $(x, y, z) = (\angle BPC, \angle CPA, \angle APB)$.

### Lemma 2.1 (Admissible angle triples)
*The map $P \mapsto (\angle BPC, \angle CPA, \angle APB)$ is a bijection from the strict interior of $\triangle ABC$ onto the set*
$$\Omega(A, B, C) = \{(x, y, z) \in \mathbb{R}^3 : x + y + z = 2\pi,\; A < x < \pi,\; B < y < \pi,\; C < z < \pi\}.$$

*Proof.*
- **Well-definedness:** If $P$ is strictly interior to $\triangle ABC$, then the rays $PA, PB, PC$ partition the full angle around $P$, so $x + y + z = 2\pi$ and $0 < x, y, z < \pi$. Moreover, $\angle PAB < A$ and $\angle PBA < B$, so $z = \pi - \angle PAB - \angle PBA > \pi - A - B = C$. Symmetrically $x > A$ and $y > B$.
- **Surjectivity:** Fix $(x, y, z) \in \Omega(A, B, C)$. For any $t \in (0, \pi - z)$, the ray from $A$ on the $C$-side of $AB$ making angle $t$ with $AB$ and the ray from $B$ on the $C$-side of $AB$ making angle $\pi - z - t$ with $BA$ meet at a unique point $P(t)$ with $\angle AP(t)B = z$, depending continuously on $t$ by the Law of Sines. The point $P(t)$ lies strictly inside $\triangle ABC$ if and only if $0 < t < A$ and $0 < \pi - z - t < B$, i.e.
  $$t_{\min} := \max(0, \pi - z - B) < t < \min(A, \pi - z) =: t_{\max}.$$
  This open interval is nonempty because $z > C = \pi - A - B$ implies $\pi - z - B < A$, while $z < \pi$ gives $0 < \pi - z$ and $A > 0, B > 0$.
  - As $t \to t_{\min}^+$: if $\pi - z - B > 0$, then $P(t)$ approaches a strictly interior point of side $BC$, so $\angle BP(t)C \to \pi$; if $\pi - z - B \le 0$, then $P(t) \to B$ along the ray making angle $\pi - z$ with $BA$, so $\angle BP(t)C \to \pi - (B - (\pi - z)) = 2\pi - z - B$ (which equals $\pi$ when $\pi - z - B = 0$). Hence $\lim_{t \to t_{\min}^+} \angle BP(t)C = \min(\pi, 2\pi - z - B)$.
  - As $t \to t_{\max}^-$: if $A < \pi - z$, then $P(t)$ approaches a strictly interior point of side $AC$ where $\angle CPA \to \pi$, so $\angle BP(t)C \to 2\pi - \pi - z = \pi - z$; if $A \ge \pi - z$, then $P(t) \to A$ and $\angle BP(t)C \to \angle BAC = A$ (which equals $\pi - z$ when $A = \pi - z$). Hence $\lim_{t \to t_{\max}^-} \angle BP(t)C = \max(A, \pi - z)$.
  Since $(x, y, z) \in \Omega(A, B, C)$, we have $x > A$, $x = 2\pi - y - z > \pi - z$ (as $y < \pi$), $x < \pi$, and $x = 2\pi - y - z < 2\pi - B - z$ (as $y > B$). Thus $x$ lies strictly between the two endpoint limits. By the Intermediate Value Theorem, there exists $t \in (t_{\min}, t_{\max})$ with $\angle BP(t)C = x$, and hence $\angle CP(t)A = 2\pi - x - z = y$.
- **Injectivity:** By the inscribed-angle theorem, all points on the $C$-side of $AB$ with $\angle APB = z$ lie on a unique circle $\Gamma_{AB}(z)$ through $A$ and $B$ (whose center lies on the perpendicular bisector of $AB$ at signed distance $\frac{|AB|}{2}\cot z$ toward $C$). Similarly, all points on the $A$-side of $BC$ with $\angle BPC = x$ lie on a unique circle $\Gamma_{BC}(x)$ through $B$ and $C$. If $\Gamma_{AB}(z) = \Gamma_{BC}(x)$, then this common circle passes through $A, B, C$, so it is the circumcircle of $\triangle ABC$; however, a strictly interior point is a strict convex combination of $A, B, C$ and cannot lie on the circumcircle by strict convexity of the closed disk. Thus $\Gamma_{AB}(z) \ne \Gamma_{BC}(x)$. Two distinct circles intersect in at most two points; since $B$ is already an intersection point, there is at most one strictly interior point $P \in \Gamma_{AB}(z) \cap \Gamma_{BC}(x)$. $\square$

## 3. Reduction to Integer Floor Triples

Fix $n \ge 3$ and a triangle with angles $A, B, C > 0$, $A + B + C = \pi$. Write
$$p = \left\lfloor \frac{nA}{\pi} \right\rfloor, \qquad q = \left\lfloor \frac{nB}{\pi} \right\rfloor, \qquad r = \left\lfloor \frac{nC}{\pi} \right\rfloor.$$
An integer triple $(X, Y, Z) \in \mathbb{Z}^3$ satisfies $X + Y + Z = 2n$, $X, Y, Z$ pairwise distinct, and $(X\pi/n, Y\pi/n, Z\pi/n) \in \Omega(A, B, C)$ if and only if $p < X < n$, $q < Y < n$, $r < Z < n$. Substituting $u = n - X$, $v = n - Y$, $w = n - Z$, this is equivalent to $(u, v, w)$ belonging to the set
$$\mathcal{S}_n(p, q, r) = \bigl\{(u, v, w) \in \mathbb{N}_+^3 : u + v + w = n,\; u, v, w \text{ pairwise distinct},\; u < n - p,\; v < n - q,\; w < n - r\bigr\}.$$

### Lemma 3.1 (Reduction to floor sum $n - 2$)
*For every nondegenerate triangle, $p, q, r \in \mathbb{N}$ satisfy $p + q + r \ge n - 2$. Moreover,*
$$a(n) = \max_{\substack{p, q, r \in \mathbb{N} \\ p + q + r = n - 2}} |\mathcal{S}_n(p, q, r)|.$$

*Proof.* Since $\frac{nA}{\pi} < p + 1$, $\frac{nB}{\pi} < q + 1$, and $\frac{nC}{\pi} < r + 1$, summing gives $n < p + q + r + 3$, so $p + q + r \ge n - 2$. Decreasing any of $p, q, r$ relaxes the upper bounds $u < n - p, v < n - q, w < n - r$, so $|\mathcal{S}_n(p, q, r)| \le |\mathcal{S}_n(p', q', r')|$ whenever $p' \le p, q' \le q, r' \le r$. Hence every triangle's count is bounded above by some triple with $p' + q' + r' = n - 2$. Conversely, given any $p, q, r \in \mathbb{N}$ with $p + q + r = n - 2$, the positive angles
$$A = \frac{(p + 2/3)\pi}{n}, \qquad B = \frac{(q + 2/3)\pi}{n}, \qquad C = \frac{(r + 2/3)\pi}{n}$$
satisfy $A + B + C = \pi$ and have exact floors $(p, q, r)$, realizing $|\mathcal{S}_n(p, q, r)|$. $\square$

## 4. Disjoint Exclusions and Minimization

Let $\mathcal{U}_n = \{(u, v, w) \in \mathbb{N}_+^3 : u + v + w = n,\; u, v, w \text{ pairwise distinct}\}$.

### Lemma 4.1 (Total count and disjoint exclusion decomposition)
1. *The unrestricted count is*
   $$T(n) := |\mathcal{U}_n| = \frac{(n - 1)(n - 2)}{2} - 3\left\lfloor \frac{n - 1}{2} \right\rfloor + 2[3 \mid n].$$
2. *For every $(p, q, r) \in \mathbb{N}^3$ with $p + q + r = n - 2$, the three forbidden subsets $\{u \ge n - p\}$, $\{v \ge n - q\}$, $\{w \ge n - r\}$ of $\mathcal{U}_n$ are pairwise disjoint, and*
   $$|\mathcal{S}_n(p, q, r)| = T(n) - E_n(p) - E_n(q) - E_n(r),$$
   *where*
   $$E_n(p) = \sum_{s=1}^{p} D_n(s), \qquad D_n(s) = s - 1 - [2 \mid s] - 2[2s > n \wedge 3s \ne 2n].$$

*Proof.*
1. The number of ordered triples $(u, v, w) \in \mathbb{N}_+^3$ summing to $n$ is $\binom{n - 1}{2} = \frac{(n - 1)(n - 2)}{2}$. Those with $u = v$ correspond to $1 \le u \le \lfloor (n - 1)/2 \rfloor$ (with $w = n - 2u \ge 1$), giving $\lfloor (n - 1)/2 \rfloor$ triples, and symmetrically for $v = w$ and $w = u$. Any two of these equalities force $u = v = w = n/3$, which exists iff $3 \mid n$. Inclusion–exclusion gives $T(n) = \binom{n - 1}{2} - 3\lfloor (n - 1)/2 \rfloor + 2[3 \mid n]$.
2. If $(u, v, w) \in \mathcal{U}_n$ satisfied both $u \ge n - p$ and $v \ge n - q$, then $u + v \ge 2n - p - q = n + r + 2 > n$, contradicting $w = n - u - v \ge 1$. Thus the three forbidden sets are pairwise disjoint, and by symmetry each has size $E_n(p) = |\{(u, v, w) \in \mathcal{U}_n : u \ge n - p\}|$. Writing $s = n - u = v + w$, the condition $u \ge n - p$ becomes $1 \le s \le p$ (note $p \le n - 2$, so $u = n - s \ge 2 \ge 1$). For fixed $1 \le s \le p$, there are $s - 1$ positive pairs $(v, w)$ summing to $s$:
   - One pair has $v = w$ iff $2 \mid s$ (namely $(s/2, s/2)$).
   - Pairs with $v = u = n - s$ or $w = u = n - s$ exist iff $1 \le n - s < s$, i.e. $2s > n$. There are $2$ such ordered pairs, $(n - s, 2s - n)$ and $(2s - n, n - s)$, which coincide with each other (and with $(s/2, s/2)$) iff $n - s = 2s - n$, i.e. $3s = 2n$. When $3s = 2n$, $s$ is even and that single pair was already removed by $[2 \mid s]$.
   Thus the number of triples in $\mathcal{U}_n$ with $v + w = s$ is exactly $D_n(s) = s - 1 - [2 \mid s] - 2[2s > n \wedge 3s \ne 2n]$. $\square$

### Lemma 4.2 (Balancing minimizes exclusions for $n \ge 16$)
*For every $n \ge 16$, the minimum of $E_n(p) + E_n(q) + E_n(r)$ over $p + q + r = n - 2$ is attained by a balanced triple ($\max(p, q, r) - \min(p, q, r) \le 1$), in which every coordinate is at most $n / 2$.*

*Proof.* Among all minimizers of $E_n(p) + E_n(q) + E_n(r)$ over $p + q + r = n - 2$, choose one minimizing $p^2 + q^2 + r^2$. By symmetry assume $p \ge r \ge q$.
- **Step 1 ($2p \le n$):** Suppose for contradiction that $2p > n$, so $2p \ge n + 1$. Then $2q \le q + r = n - 2 - p$, so $4q \le 2n - 4 - 2p \le n - 5$, while $4p \ge 2n + 2$, giving $4(p - q) \ge n + 7 \ge 23$ and hence $p - q \ge 6$. Replacing $(p, q)$ by $(p - 1, q + 1)$ changes the exclusion sum by $D_n(q + 1) - D_n(p)$. Since $D_n(p) \ge p - 4$ and $D_n(q + 1) \le q$, we have
  $$D_n(p) - D_n(q + 1) \ge (p - 4) - q \ge 2 > 0,$$
  contradicting minimality of $E_n(p) + E_n(q) + E_n(r)$. Thus $2p \le n$.
- **Step 2 ($p - q \le 1$):** Suppose $p \ge q + 2$. Then $q + 1 \le p - 1 < p \le n/2$. For every $1 \le s \le n/2$, we have $2s \le n$, so $D_n(s) = s - 1 - [2 \mid s]$, which is weakly increasing in $s$ ($D_n(2k - 1) = D_n(2k) = 2k - 2$). Hence $D_n(q + 1) \le D_n(p)$, so replacing $(p, q)$ by $(p - 1, q + 1)$ does not increase $E_n(p) + E_n(q) + E_n(r)$ while strictly decreasing $p^2 + q^2 + r^2$ by $2(p - q - 1) \ge 2$, contradiction. Therefore $p - q \le 1$. $\square$

## 5. Proof of Theorem 1

For every $0 \le p \le n/2$, summing $D_n(s) = s - 1 - [2 \mid s]$ over $1 \le s \le p$ gives $E_n(0) = 0$ and $E_n(p) = \lfloor (p - 1)^2 / 2 \rfloor$ for $p \ge 1$; in particular,
$$E_n(2k - 1) = 2(k - 1)^2, \qquad E_n(2k) = 2k(k - 1), \qquad E_n(2k + 1) = 2k^2.$$
For $n \ge 16$, write $n = 6k + j$ with $j \in \{0, 1, 2, 3, 4, 5\}$ (so $k \ge 2$). The balanced triple summing to $n - 2$ has coordinates and exclusion sum:
- $j = 0$: $(2k - 1, 2k - 1, 2k) \implies 2 \cdot 2(k - 1)^2 + 2k(k - 1) = 6k^2 - 10k + 4$.
- $j = 1$: $(2k - 1, 2k, 2k) \implies 2(k - 1)^2 + 2 \cdot 2k(k - 1) = 6k^2 - 8k + 2$.
- $j = 2$: $(2k, 2k, 2k) \implies 3 \cdot 2k(k - 1) = 6k^2 - 6k$.
- $j = 3$: $(2k, 2k, 2k + 1) \implies 2 \cdot 2k(k - 1) + 2k^2 = 6k^2 - 4k$.
- $j = 4$: $(2k, 2k + 1, 2k + 1) \implies 2k(k - 1) + 2 \cdot 2k^2 = 6k^2 - 2k$.
- $j = 5$: $(2k + 1, 2k + 1, 2k + 1) \implies 3 \cdot 2k^2 = 6k^2$.

Subtracting from $T(6k + j)$ in each residue class gives:
- $j = 0$: $T = 18k^2 - 18k + 6$, $a(6k) = 12k^2 - 8k + 2 = \frac{n^2 - 4n + 6}{3}$.
- $j = 1$: $T = 18k^2 - 12k$, $a(6k + 1) = 12k^2 - 4k - 2 = \frac{n^2 - 4n - 3}{3}$.
- $j = 2$: $T = 18k^2 - 6k$, $a(6k + 2) = 12k^2 = \frac{n^2 - 4n + 4}{3}$.
- $j = 3$: $T = 18k^2$, $a(6k + 3) = 12k^2 + 4k = \frac{n^2 - 4n + 3}{3}$.
- $j = 4$: $T = 18k^2 + 6k$, $a(6k + 4) = 12k^2 + 8k = \frac{n^2 - 4n}{3}$.
- $j = 5$: $T = 18k^2 + 12k$, $a(6k + 5) = 12k^2 + 12k = \frac{n^2 - 4n - 5}{3}$.

Finally, for $3 \le n \le 15$, direct finite evaluation of $\max_{p + q + r = n - 2} (T(n) - E_n(p) - E_n(q) - E_n(r))$ yields
$$0, 0, 0, 6, 6, 12, 16, 20, 24, 34, 38, 48, 56,$$
matching $(n^2 - 4n + c(n \bmod 6))/3$ in every case. This proves Theorem 1 for all $n \ge 3$. $\square$
