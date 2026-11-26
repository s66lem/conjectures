# Complete Proof That the Path Uniquely Maximizes the Tree Hitting-Time Index (`arXiv:2611.34295v1`)

## 1. Statement

Let $G = (V, E)$ be a finite connected simple graph on $n = |V|$ vertices, and let $H_G(x, y)$ denote the expected hitting time from $x$ to $y$ for the simple random walk on $G$ (with $H_G(y, y) = 0$). The *hitting-time index* of $G$ is
$$HT(G) = \sum_{\{x, y\} \subseteq V} \max\bigl(H_G(x, y),\, H_G(y, x)\bigr).$$
In [arXiv:2611.34295v1](https://arxiv.org/abs/2611.34295v1) (§3, p. 10), Palacios, Tamura, Wiberg, and Petojević conjecture that among all trees on $n$ vertices, the path $P_n$ maximizes $HT(T)$.

**Theorem 1.** *For every finite tree $T$ on $n \ge 1$ vertices,*
$$HT(T) \le HT(P_n),$$
*with equality if and only if $T \cong P_n$.*

For $n = 1$ and $n = 2$, every tree is isomorphic to $P_n$ ($HT(P_1) = 0$, $HT(P_2) = 1$). Assume $n \ge 2$ below.

## 2. Exact First-Step Reduction on Trees

For any vertex $x \in V$, let $D_T(x) = \sum_{z \in V} d_T(x, z)$ be its transmission.

### Lemma 2.1 (Unique neighbor toward a vertex)
*Let $T$ be a tree and $x \ne z$ vertices of $T$. Then there is a unique neighbor $w_0 \in N_T(x)$ with $d_T(w_0, z) = d_T(x, z) - 1$, and every other neighbor $w \in N_T(x) \setminus \{w_0\}$ satisfies $d_T(w, z) = d_T(x, z) + 1$. Consequently,*
$$\sum_{w \in N_T(x)} \bigl(d_T(w, z) - d_T(x, z)\bigr) = \deg_T(x) - 2.$$

*Proof.* Let $x = u_0, u_1, \dots, u_k = z$ ($k = d_T(x, z) \ge 1$) be the unique path from $x$ to $z$ in $T$. Taking $w_0 = u_1$ gives $d_T(w_0, z) = k - 1$. For any neighbor $w \in N_T(x) \setminus \{w_0\}$, prepending the edge $w x$ to the $x$–$z$ path yields a simple path of length $k + 1$ from $w$ to $z$ (since $w \ne u_1$ and $T$ is acyclic, $w$ cannot lie on $u_0 \cdots u_k$). By uniqueness of paths in a tree, $d_T(w, z) = k + 1$. Summing $d_T(w, z) - d_T(x, z)$ over $w \in N_T(x)$ gives $(-1) + (\deg_T(x) - 1)(+1) = \deg_T(x) - 2$. $\square$

### Lemma 2.2 (Closed-form hitting time and uniqueness)
*For any finite tree $T$ on $n \ge 2$ vertices and any target $y \in V$, the function*
$$h_y(x) = (n - 1)\, d_T(x, y) + D_T(y) - D_T(x)$$
*is the unique function $h : V \to \mathbb{R}$ satisfying $h(y) = 0$ and the first-step Markov equations*
$$\deg_T(x)\, h(x) = \deg_T(x) + \sum_{w \in N_T(x)} h(w) \qquad (\forall x \ne y).$$
*Hence $H_T(x, y) = (n - 1)\, d_T(x, y) + D_T(y) - D_T(x)$ and*
$$HT(T) = \sum_{\{x, y\} \subseteq V} \Bigl((n - 1)\, d_T(x, y) + |D_T(y) - D_T(x)|\Bigr).$$

*Proof.* Clearly $h_y(y) = 0$. Fix $x \ne y$. Summing Lemma 2.1 over all $z \in V \setminus \{x\}$ (there are $n - 1$ such vertices), and adding the $z = x$ term $\sum_{w \in N_T(x)} (d_T(w, x) - d_T(x, x)) = \deg_T(x)$, we obtain
$$\sum_{w \in N_T(x)} \bigl(D_T(w) - D_T(x)\bigr) = \deg_T(x) + (n - 1)(\deg_T(x) - 2) = n \deg_T(x) - 2(n - 1).$$
Therefore,
$$\sum_{w \in N_T(x)} \bigl(h_y(w) - h_y(x)\bigr) = (n - 1)(\deg_T(x) - 2) - \bigl(n \deg_T(x) - 2(n - 1)\bigr) = -\deg_T(x),$$
which rearranges to $\deg_T(x)\, h_y(x) = \deg_T(x) + \sum_{w \in N_T(x)} h_y(w)$.

For uniqueness, suppose $h_1, h_2$ both solve the system and set $f = h_1 - h_2$. Then $f(y) = 0$ and $\deg_T(x)\, f(x) = \sum_{w \in N_T(x)} f(w)$ for all $x \ne y$. Let $M = \max_{u \in V} f(u)$, attained at some $x_0$. Walking along any path from $x_0$ to $y$, if $u \ne y$ satisfies $f(u) = M$, then $\sum_{w \in N_T(u)} (M - f(w)) = 0$ with $M - f(w) \ge 0$ for all $w \in N_T(u)$, forcing $f(w) = M$ for every neighbor $w$ of $u$. By induction along the path, $M = f(y) = 0$, so $f \le 0$. Applying the same argument to $-f$ yields $f \ge 0$, hence $h_1 = h_2$.

Finally, $\max(H_T(x, y), H_T(y, x)) = (n - 1)\, d_T(x, y) + \max(D_T(y) - D_T(x), D_T(x) - D_T(y)) = (n - 1)\, d_T(x, y) + |D_T(y) - D_T(x)|$. $\square$

## 3. Pendant-Path Grafting Move

Suppose $T$ contains a vertex $v$ with two disjoint pendant paths $A = (A_1, \dots, A_a)$ and $B = (B_1, \dots, B_b)$ attached at $v$ (with edges $v A_1, A_1 A_2, \dots, A_{a-1} A_a$ and $v B_1, B_1 B_2, \dots, B_{b-1} B_b$, and no other edges incident to $A \cup B$), where $a \ge b \ge 1$. Write $C = V \setminus (A \cup B)$ (so $v \in C$) and let $|C| = r + 1$. Assume $r \ge a$, and set $m = n - 1 = a + b + r$.

Define $T'$ by deleting the edge $v A_1$ and adding the edge $B_b A_1$. Clearly $T'$ is a tree on the same vertex set $V$. Since $\deg_{T'}(v) = \deg_T(v) - 1 \ge 2$ (as $v$ retains neighbor $B_1$ and at least one neighbor in $C$, because $|C| = r + 1 \ge a + 1 \ge 2$), $\deg_{T'}(B_b) = 2$ (was $1$), and all other degrees are unchanged, $T'$ has exactly one fewer leaf than $T$.

### Lemma 3.1 (Distances and transmissions under grafting)
*Let $\delta(x) = D_{T'}(x) - D_T(x)$. Then:*
1. *Distances within $A$, within $B$, within $C$, and between $B$ and $C$ are unchanged. For every $A_i \in A$ and $z \in C$, $d_{T'}(A_i, z) = d_T(A_i, z) + b$. For every $A_i \in A$ and $B_j \in B$, $d_T(A_i, B_j) = i + j$ and $d_{T'}(A_i, B_j) = i + b - j = d_T(A_i, B_j) + (b - 2j)$.*
2. *The transmission increments are*
   $$\delta(A_i) = br, \qquad \delta(B_j) = a(b - 2j), \qquad \delta(z) = ab \quad (z \in C).$$
3. *For every $1 \le i \le a$ and $1 \le j \le b$, writing $X_i = D_T(A_i) - D_T(v)$ and $Y_j = D_T(B_j) - D_T(v)$,*
   $$X_i = i(r + b - a + i), \qquad Y_j = j(r + a - b + j),$$
   *so $u_{ij} := D_T(A_i) - D_T(B_j) = X_i - Y_j$, and*
   $$u'_{ij} := D_{T'}(A_i) - D_{T'}(B_j) = u_{ij} + b(r - a) + 2aj = (b + i - j)(r + i + j - a) > 0.$$

*Proof.* Part (1) is immediate from the unique paths in $T$ and $T'$. For (2):
- $\delta(A_i) = \sum_{z \in C} b + \sum_{j=1}^b (b - 2j) = b(r + 1) + b^2 - b(b + 1) = br$.
- $\delta(B_j) = \sum_{i=1}^a (b - 2j) = a(b - 2j)$.
- $\delta(z) = \sum_{i=1}^a b = ab$.

For (3), in $T$ every $z \in C$ satisfies $d_T(A_i, z) - d_T(v, z) = i$ and every $B_j \in B$ satisfies $d_T(A_i, B_j) - d_T(v, B_j) = i$, while within $A$:
$$\sum_{k=1}^a \bigl(|i - k| - k\bigr) = \sum_{k=1}^i (i - 2k) + \sum_{k=i+1}^a (-i) = -i - i(a - i) = i(i - a - 1).$$
Adding $i(r + 1) + ib$ gives $X_i = i(r + b - a + i)$, and symmetrically $Y_j = j(r + a - b + j)$. Then
$$u'_{ij} = X_i - Y_j + \delta(A_i) - \delta(B_j) = i(r + b - a + i) - j(r + a - b + j) + b(r - a) + 2aj = (b + i - j)(r + i + j - a).$$
Since $b + i - j \ge i \ge 1$ and $r + i + j - a \ge i + j \ge 2$ (as $r \ge a$), $u'_{ij} > 0$. $\square$

### Lemma 3.2 (Strict increase of $HT$)
*Under the assumptions $r \ge a \ge b \ge 1$, we have $HT(T') > HT(T)$.*

*Proof.* Partition unordered vertex pairs into six families: $A$–$A$, $C$–$C$, $A$–$C$, $B$–$C$, $B$–$B$, and $A$–$B$. Pairs inside $A$ and inside $C$ have zero change in both distance and transmission difference.

**Case 1: $a = b = 1$ ($r \ge 1$, $m = r + 2$).**
By arm symmetry exchanging $A_1$ and $B_1$ in $T$, we have $D_T(A_1) = D_T(B_1)$. For each $z \in C$, let $u = D_T(A_1) - D_T(z) = D_T(B_1) - D_T(z)$. Since $\delta(A_1) - \delta(z) = r - 1$ and $\delta(B_1) - \delta(z) = -2$, the triangle inequality gives
$$|u + (r - 1)| + |u - 2| \ge |2u + r - 3| \ge 2|u| - |r - 3|.$$
Combined with the distance gain $m \cdot 1 = r + 2$ on $(A_1, z)$, the pair of edges $(A_1, z), (B_1, z)$ contributes at least $(r + 2) - |r - 3|$ to $HT(T') - HT(T)$. Note $(r + 2) - |r - 3| = 2r - 1 \ge 1$ for $1 \le r \le 3$ and equals $5 \ge 1$ for $r \ge 3$, so every $z \in C$ contributes at least $1$. For the single pair $(A_1, B_1)$, the distance changes by $-1$ (contributing $-m = -(r + 2)$) while $|D_{T'}(A_1) - D_{T'}(B_1)| - |D_T(A_1) - D_T(B_1)| = (r + 1) - 0 = r + 1$, a net change of $-1$. Summing over the $r + 1$ vertices of $C$ and the pair $(A_1, B_1)$ gives
$$HT(T') - HT(T) \ge (r + 1) - 1 = r \ge 1 > 0.$$

**Case 2: $a \ge 2$ ($1 \le b \le a \le r$).**
We bound each of the four active families:

1. **$A$–$C$:** Each of the $a(r + 1)$ pairs has distance gain $b$ and transmission-difference shift $w = \delta(A_i) - \delta(z) = b(r - a) \ge 0$, so its net contribution is at least $mb - b(r - a) = b(2a + b)$. Total: $\ge ab(r + 1)(2a + b)$.
2. **$B$–$C$:** Each pair $(B_j, z)$ has $\Delta d = 0$ and shift $\delta(B_j) - \delta(z) = -2aj$, so its contribution is at least $-2aj$. Summing over $z \in C$ and $1 \le j \le b$ gives $\ge -(r + 1) \cdot 2a \frac{b(b + 1)}{2} = -ab(r + 1)(b + 1)$.
   Combining $A$–$C$ and $B$–$C$ yields
   $$\Delta_{AC} + \Delta_{BC} \ge ab(r + 1)(2a - 1).$$
3. **$B$–$B$:** For $1 \le j < k \le b$, $\Delta d = 0$ and $\delta(B_k) - \delta(B_j) = -2a(k - j)$, so the contribution is at least $-2a(k - j)$. Summing over $1 \le j < k \le b$ uses $\sum_{1 \le j < k \le b} (k - j) = \frac{b(b^2 - 1)}{6}$, giving
   $$\Delta_{BB} \ge -\frac{ab(b^2 - 1)}{3}.$$
4. **$A$–$B$:** The distance sum changes by $\sum_{i=1}^a \sum_{j=1}^b (b - 2j) = -ab$, contributing $-mab = -ab(a + b + r)$. For the transmission term $\sum_{i=1}^a \sum_{j=1}^b (u'_{ij} - |u_{ij}|)$, set $d = a - b \ge 0$ and $s = r - a \ge 0$. Since $u'_{ij} = u_{ij} + w_{ij} > 0$ with $w_{ij} = bs + 2aj > 0$, we have
   $$u'_{ij} - |u_{ij}| = \min(w_{ij},\, u'_{ij} + u_{ij}),$$
   and direct expansion gives
   $$u'_{ij} + u_{ij} = (b + 2i - 2j)s + 2i(i + b) - 2j^2 - 2jd.$$
   - If $i < j$ (so $1 \le i < j \le b$), then $u_{ij} = (i - j)(r + i + j) - (i + j)d < 0$, so $u'_{ij} - |u_{ij}| = u'_{ij} + u_{ij}$ holds with equality.
   - If $i \ge j$, then $b + 2i - 2j \ge b > 0$ and $2i(i + b) - 2j^2 \ge 2j(j + b) - 2j^2 = 2jb \ge 0$, so $u'_{ij} + u_{ij} \ge -2jd$. Since also $w_{ij} > 0 \ge -2jd$, we have $u'_{ij} - |u_{ij}| \ge -2jd$.

   Summing over all $1 \le i \le a, 1 \le j \le b$: the $-2jd$ term appears on every pair and sums to $-2d \cdot a \frac{b(b + 1)}{2} = -ab(b + 1)d$; meanwhile over $1 \le i < j \le b$ we have the elementary identities
   $$\sum_{1 \le i < j \le b} (b + 2i - 2j) = \frac{b(b - 1)(b - 2)}{6}, \qquad \sum_{1 \le i < j \le b} \bigl(2i(i + b) - 2j^2\bigr) = -\frac{b(b^2 - 1)}{3}.$$
   Hence
   $$\Delta_{AB}^{\mathrm{abs}} \ge \frac{b(b - 1)(b - 2)}{6}\, s - \frac{b(b^2 - 1)}{3} - ab(b + 1)d.$$

Multiplying the combined lower bound by $6$ and substituting $a = b + d$, $r = b + d + s$ yields the exact polynomial identity
$$6\bigl(HT(T') - HT(T)\bigr) \ge \bigl(12ab(a - 1) + b(b - 1)(b - 2)\bigr) s + 2b\Bigl(6d^3 + (15b - 6)d^2 + 2(b - 1)(7b + 1)d + (5b^3 - 7b^2 - 2b + 1)\Bigr).$$
Since $a \ge 2$, $b \ge 1$, $d \ge 0$, $s \ge 0$:
- The coefficient of $s$ satisfies $12ab(a - 1) + b(b - 1)(b - 2) > 0$.
- In the constant-in-$s$ bracket: if $b = 1$, then $a \ge 2$ forces $d \ge 1$, so the bracket equals $6d^3 + 9d^2 - 3 \ge 12 > 0$; if $b \ge 2$, then $15b - 6 > 0$, $2(b - 1)(7b + 1) > 0$, and $5b^3 - 7b^2 - 2b + 1 = (b - 2)(5b^2 + 3b + 4) + 9 \ge 9 > 0$.

Therefore $6(HT(T') - HT(T)) > 0$, proving $HT(T') > HT(T)$. $\square$

## 4. Existence of the Grafting Move and Completion of Proof

### Lemma 4.1 (Every non-path tree admits a valid grafting move)
*Let $T$ be a finite tree on $n \ge 2$ vertices that is not isomorphic to $P_n$. Then $T$ contains a vertex $v$ and two disjoint pendant paths $A = (A_1, \dots, A_a)$ and $B = (B_1, \dots, B_b)$ at $v$ such that $|V \setminus (A \cup B)| = r + 1$ with $r \ge a \ge b \ge 1$.*

*Proof.* Since $T \not\cong P_n$, $T$ has a vertex of degree at least $3$. Let $p, q \in V$ maximize $d_T(p, q) =: L$ (a diameter of $T$). Some vertex $w$ on the unique $p$–$q$ path $P$ satisfies $\deg_T(w) \ge 3$ (otherwise every vertex on $P$ has degree $\le 2$, so no edge can leave $P$, forcing $V = P$ and $T \cong P_n$). Swapping $p$ and $q$ if necessary, assume $d_T(p, w) \ge d_T(q, w)$, so $2\, d_T(p, w) \ge L$.

Among all vertices of $T$ with degree $\ge 3$, choose $v$ maximizing $d_T(p, v)$. Then $d_T(p, v) \ge d_T(p, w) \ge L / 2$, and in particular $v \ne p$ (since if $v = p$ then $d_T(p, w) = 0 \implies L = 0$, impossible for $n \ge 2$). By Lemma 2.1, $v$ has a unique neighbor closer to $p$, and since $\deg_T(v) \ge 3$, $v$ has at least two neighbors $u_1, u_2$ farther from $p$ than $v$.

Every vertex $x$ in the subtree of $T - v u_1$ containing $u_1$ satisfies $d_T(p, x) > d_T(p, v)$, hence $\deg_T(x) \le 2$ by maximality of $v$. Thus the component of $u_1$ in $T - v u_1$ is a pendant path attached at $v$, and likewise for $u_2$. Label the longer path $A = (A_1, \dots, A_a)$ and the shorter $B = (B_1, \dots, B_b)$, so $a \ge b \ge 1$.

Finally, $d_T(p, A_a) = d_T(p, v) + a \le L$ by definition of the diameter $L$, so
$$a \le L - d_T(p, v) \le d_T(p, v).$$
Every vertex on the unique $p$–$v$ path has distance at most $d_T(p, v)$ from $p$, whereas every vertex of $A \cup B$ has distance strictly greater than $d_T(p, v)$ from $p$. Thus the $p$–$v$ path lies entirely inside $C = V \setminus (A \cup B)$ and contains $d_T(p, v) + 1$ distinct vertices, giving $r + 1 = |C| \ge d_T(p, v) + 1 \ge a + 1$, hence $r \ge a$. $\square$

### Proof of Theorem 1
We proceed by strong induction on the number of leaves $\ell(T) = |\{u \in V : \deg_T(u) = 1\}|$ among trees $T$ on a fixed finite vertex set $V$ of size $n \ge 2$. Every tree on $n \ge 2$ vertices has $\ell(T) \ge 2$, and $\ell(T) = 2$ if and only if $T \cong P_n$ (since $\sum_{u \in V} \deg_T(u) = 2n - 2$ implies $\sum_{\deg(u) \ge 3} (\deg(u) - 2) = \ell(T) - 2$).
- **Base case ($\ell(T) = 2$):** $T \cong P_n$, so $HT(T) = HT(P_n)$ by graph-isomorphism invariance of $HT$.
- **Inductive step ($\ell(T) \ge 3$):** $T \not\cong P_n$, so by Lemma 4.1 and Lemma 3.2 there exists a tree $T'$ on $V$ with $\ell(T') = \ell(T) - 1$ and $HT(T) < HT(T')$. By the induction hypothesis, $HT(T') \le HT(P_n)$, giving the strict inequality $HT(T) < HT(P_n)$. $\square$
