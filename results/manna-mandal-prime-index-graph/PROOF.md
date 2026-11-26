# Disproof of Manna–Mandal Problem 7.10 (Question 2, `arXiv:2611.27642v1`)

## 1. Statement

Let $G$ be a finite group. The **prime index elements graph** $\Gamma(G)$ has vertex set $G$, with distinct $x, y \in G$ adjacent whenever one of $\langle x \rangle, \langle y \rangle$ has prime index in the other. For a $p$-group $P$ and cyclic subgroup $C \le P$, let $c_P(C)$ denote the number of cyclic subgroups of $P$ containing $C$ as a maximal subgroup, and set $N_p(P) := c_P(1)$ (the number of subgroups of order $p$).

For a nilpotent group $K$ of odd order and a prime $p \mid |K|$ with Sylow $p$-subgroup $P \le K$ and $m_p := |K|/|P|$, Manna and Mandal ([arXiv:2611.27642v1](https://arxiv.org/abs/2611.27642v1), §7.3, Theorem 7.6) show that $\Gamma(K \times \mathbb{Z}_2)$ being Hamiltonian requires:
- **(H1)** $N_p(P) \le 2 m_p$, and
- **(H2)** $c_P(C) \le 2\varphi(|C|) m_p - 1$ for every cyclic subgroup $1 \ne C \le P$.

The second question of **Problem 7.10** asks whether **(H1)** implies **(H2)** in general, as it does for abelian Sylow subgroups (Corollary 7.8(iii)).

**Theorem 1.** *Let $A = \mathbb{Z}_9 \times \mathbb{Z}_9$ (written additively), let $s : A \to A$ be the automorphism $s(a, b) = (-b, a - b)$, and let $u = (-3, 3) = (6, 3) \in A$. Define $P = A \times \{0, 1, 2\}$ with multiplication*
$$(v, i) \cdot (w, j) = \bigl(v + s^i(w) + \varepsilon_{i, j}\, u,\; (i + j) \bmod 3\bigr), \qquad \varepsilon_{i, j} := \begin{cases} 1 & \text{if } i + j \ge 3, \\ 0 & \text{otherwise.} \end{cases}$$
*Let $K = P \times \mathbb{Z}_5$ and $G = K \times \mathbb{Z}_2 \cong P \times \mathbb{Z}_{10}$. Then:*
1. *$P$ is a non-abelian $3$-group of order $243$, so $K$ is a nilpotent group of odd order $1215$.*
2. *(H1) holds for every prime dividing $|K|$: $N_3(P) = 4 \le 10 = 2m_3$ and $N_5(\mathbb{Z}_5) = 1 \le 486 = 2m_5$.*
3. *(H2) fails for $p = 3$ at the cyclic subgroup $C = \langle (u, 0) \rangle$ of order $3$: $c_P(C) = 30 > 19 = 2\varphi(3)m_3 - 1$.*
4. *Removing the $20$-vertex cut set $S = \{(y, t) \in P \times \mathbb{Z}_{10} : y \in \{(u, 0), (2u, 0)\}\}$ separates $\Gamma(G)$ into at least $31$ components (in fact exactly $31$); consequently $\Gamma(G)$ has neither a Hamiltonian cycle nor a Hamiltonian path.*

## 2. Proof

**Step 1: $P$ is a group of order $243$.** Direct evaluation on the basis of $A = \mathbb{Z}_9^2$ gives
$$s(1, 0) = (0, 1), \qquad s^2(1, 0) = (-1, -1), \qquad s^3(1, 0) = (1, 0),$$
and $s(0, 1) = (-1, -1)$, $s^2(0, 1) = (1, 0)$, $s^3(0, 1) = (0, 1)$, so $s^3 = \mathrm{id}_A$ and $1 + s + s^2 = 0$ on $A$. Moreover, $s(6, 3) = (-3, 3) = (6, 3)$ in $\mathbb{Z}_9^2$, so $s(u) = u$.

For any $x = (v, i)$, $y = (w, j)$, $z = (r, k) \in P$, because $s$ is an automorphism fixing $u$ with $s^3 = \mathrm{id}$, the first coordinates of $(xy)z$ and $x(yz)$ are respectively
$$v + s^i(w) + s^{i + j}(r) + (\varepsilon_{i, j} + \varepsilon_{(i + j) \bmod 3,\, k})\, u, \qquad v + s^i(w) + s^{i + j}(r) + (\varepsilon_{j, k} + \varepsilon_{i,\, (j + k) \bmod 3})\, u.$$
Both carry sums equal $\lfloor (i + j + k) / 3 \rfloor$, and the second coordinates both equal $(i + j + k) \bmod 3$; hence multiplication is associative. Clearly $(0, 0)$ is a two-sided identity, and every $(v, i)$ has explicit inverse $(-v, 0)$ for $i = 0$ and $(s^{3 - i}(-v - u),\, 3 - i)$ for $i \in \{1, 2\}$. Thus $P$ is a group of order $9^2 \cdot 3 = 243 = 3^5$.

**Step 2: Element orders and $N_3(P) = 4$.** Using $1 + s + s^2 = 0$ and $s(u) = u$:
- For every $v \in A$, $(v, 1)^3 = (v + s(v) + s^2(v) + u, 0) = (u, 0)$.
- For every $v \in A$, $(v, 2)^3 = (v + s^2(v) + u + s(v) + u, 0) = (2u, 0)$.

Since $u = (6, 3)$ has order $3$ in $A$, all $162$ elements outside $A \times \{0\}$ have cube in $\{(u, 0), (2u, 0)\}$ and therefore have order $9$. Inside $A \times \{0\} \cong \mathbb{Z}_9^2$, the elements of order $3$ are precisely the $8$ nonzero elements of $3A \times \{0\}$. Hence $P$ has exactly $8$ elements of order $3$, giving $N_3(P) = 8 / 2 = 4$ subgroups of order $3$.

**Step 3: $c_P(\langle (u, 0) \rangle) = 30$ and failure of (H2).** Let $C = \langle (u, 0) \rangle \le P$ (order $3$). A cyclic subgroup $D \le P$ contains $C$ as a maximal subgroup if and only if $D = \langle y \rangle$ for an element $y \in P$ of order $9$ with $y^3 \in \{(u, 0), (2u, 0)\}$. Such elements $y$ are:
- all $162$ elements with $i \in \{1, 2\}$ (by Step 2);
- the elements $(v, 0) \in A \times \{0\}$ with $3v \in \{u, 2u\} = \{(6, 3), (3, 6)\}$ in $\mathbb{Z}_9^2$, i.e. $v \equiv (2, 1)$ or $(1, 2) \pmod 3$. Each of these $2$ classes mod $3$ has $3^2 = 9$ lifts in $\mathbb{Z}_9^2$, contributing $18$ elements.

Each cyclic subgroup of order $9$ has $\varphi(9) = 6$ generators, so
$$c_P(C) = \frac{162 + 18}{6} = 30.$$
For $K = P \times \mathbb{Z}_5$ we have $m_3 = 5$ and $m_5 = 243$. Thus:
- **(H1)** holds at both primes: $N_3(P) = 4 \le 10 = 2m_3$ and $N_5(\mathbb{Z}_5) = 1 \le 486 = 2m_5$.
- **(H2)** fails at $p = 3$ and $C = \langle (u, 0) \rangle$: $c_P(C) = 30 > 19 = 2 \cdot 2 \cdot 5 - 1 = 2\varphi(|C|)m_3 - 1$.

(The same $P$ also fails (H2) with $K = P \times \mathbb{Z}_7$, since $30 > 2 \cdot 2 \cdot 7 - 1 = 27$.)

**Step 4: Direct proof that $\Gamma(G)$ has no Hamiltonian cycle or path.** Let $G = P \times \mathbb{Z}_{10}$ and let
$$S = \{(y, t) \in G : y \in \{(u, 0), (2u, 0)\},\; t \in \mathbb{Z}_{10}\}, \qquad |S| = 2 \cdot 10 = 20.$$
Define a $31$-valued branch label $\beta : G \setminus S \to \{D \le P \text{ cyclic} : |D| = 9,\; C \le D\} \cup \{\bot\}$ by setting $\beta(y, t) = \langle y \rangle$ if $y^3 \in \{(u, 0), (2u, 0)\}$ and $\beta(y, t) = \bot$ otherwise. All $31$ values are attained on $G \setminus S$ (each of the $30$ cyclic subgroups $D$ via $(y, 0)$ for a generator $y$ of $D$, and $\bot$ via $(1_P, 0)$).

Suppose $g = (g_3, g')$ and $h = (h_3, h')$ in $G \setminus S$ are adjacent in $\Gamma(G)$; by symmetry assume $\langle g \rangle < \langle h \rangle$ with prime index. Then $g = h^k$ for some integer $k$, so $\langle g_3 \rangle \le \langle h_3 \rangle$ in $P$.
- If $|\langle g_3 \rangle| = |\langle h_3 \rangle|$, then $\langle g_3 \rangle = \langle h_3 \rangle$, so $g_3^3 \in \{(u, 0), (2u, 0)\} \iff h_3^3 \in \{(u, 0), (2u, 0)\}$, hence $\beta(g) = \beta(h)$.
- If $|\langle g_3 \rangle| < |\langle h_3 \rangle|$, then $|\langle g_3 \rangle| \le 3$ (so $g_3^3 = 1_P$ and $\beta(g) = \bot$). Moreover, if $h_3^3 \in \{(u, 0), (2u, 0)\}$, then $|\langle h_3 \rangle| = 9$ and $\langle h_3 \rangle$ has a unique subgroup of order $3$, namely $C = \langle (u, 0) \rangle$. Since $|\langle g_3 \rangle| \in \{1, 3\}$ and $g \notin S$, we cannot have $|\langle g_3 \rangle| = 3$; wait — could $|\langle g_3 \rangle| = 1$? No! Because $[\langle h \rangle : \langle g \rangle]$ is prime, the ratio $|\langle h_3 \rangle| / |\langle g_3 \rangle|$ divides that prime and hence equals $1$ or $3$ (never $9$!). Thus $|\langle g_3 \rangle| = 3$ is forced, giving $g_3 \in \{(u, 0), (2u, 0)\}$ and $g \in S$, a contradiction. Therefore $h_3^3 \notin \{(u, 0), (2u, 0)\}$ as well, so $\beta(h) = \bot = \beta(g)$.

Thus $\beta$ is constant on every edge of $\Gamma(G) - S$, so $\Gamma(G) - S$ has at least $31$ connected components (and `verify.py` confirms exactly $31$). Deleting $20$ vertices from a Hamiltonian path leaves at most $21$ contiguous segments (and at most $20$ from a Hamiltonian cycle); since $31 > 21$, $\Gamma(G)$ has neither a Hamiltonian path nor a Hamiltonian cycle. $\square$
