# Proof of Werner Schulte's OEIS A397048 Conjectures

## 1. Statement and Definitions

In [OEIS A397048](https://oeis.org/A397048) (Werner Schulte, June 14, 2026; revision #34), the triangle $T(n, k)$ ($0 \le k \le n$) is defined by
$$T(n, k) = \frac{(-1)^k}{k!} \sum_{i=0}^{k} (-1)^i \binom{k}{i} (n + i)^n = \frac{1}{k!} \sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (n + i)^n.$$
More generally, for any integer base point $c \ge 0$ and integers $n, k \ge 0$, define
$$T_c(n, k) = \frac{1}{k!} \sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (c + i)^n,$$
so that $T(n, k) = T_n(n, k)$.

The OEIS entry lists three open conjectures:
- **Conjecture 1:** $T(n, k) = \sum_{i=0}^{n - k} s(n, k + i)\, S(n + k + i, n + k)$, where $s(a, b) = \mathrm{A048994}(a, b)$ are the signed Stirling numbers of the first kind and $S(a, b) = \mathrm{A048993}(a, b)$ are the Stirling numbers of the second kind.
- **Conjecture 2:** The row sums $\sum_{k=0}^{n} T(n, k)$ equal $\mathrm{A134980}(n) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} B_j$, where $B_j = \sum_{k=0}^{j} S(j, k) = \mathrm{A000110}(j)$ is the $j$-th Bell number.
- **Conjecture 3:** $\sum_{i=0}^{k} T(n, i)\, \dfrac{k!}{(k - i)!} = (n + k)^n$.

## 2. Preliminaries on Falling Factorials and Stirling Numbers

For $k \in \mathbb{N}$, define the falling-factorial polynomial $(x)_k \in \mathbb{Q}[x]$ recursively by $(x)_0 = 1$ and $(x)_{k + 1} = (x)_k (x - k)$. For every integer $m \ge 0$,
$$(m)_k = \begin{cases} \dfrac{m!}{(m - k)!} = k! \binom{m}{k}, & k \le m, \\ 0, & k > m. \end{cases}$$

**Lemma 2.1 (Uniqueness of falling-factorial coordinates).** *If $\sum_{k=0}^{N} a_k (x)_k = \sum_{k=0}^{N} b_k (x)_k$ in $\mathbb{Q}[x]$, then $a_k = b_k$ for all $0 \le k \le N$.*

*Proof.* By strong induction on $k \le N$. Suppose $a_j = b_j$ for all $j < k$. Evaluating both sides at $x = k$, all terms with $j > k$ vanish because $(k)_j = 0$, while terms with $j < k$ cancel by the induction hypothesis. Thus $a_k \cdot k! = b_k \cdot k!$, and since $k! \ne 0$ in $\mathbb{Q}$ we conclude $a_k = b_k$. $\square$

**Lemma 2.2 (Shift splitting).** *For all $c, k \in \mathbb{N}$, $(x)_c \cdot (x - c)_k = (x)_{c + k}$ in $\mathbb{Q}[x]$.*

*Proof.* Induction on $k$. For $k = 0$ both sides equal $(x)_c$. For the step $k \to k + 1$:
$$(x)_c (x - c)_{k + 1} = (x)_c (x - c)_k (x - c - k) = (x)_{c + k} (x - (c + k)) = (x)_{c + k + 1}. \quad \square$$

**Lemma 2.3 (Stirling expansions).** *Define $s(n, k) \in \mathbb{Z}$ and $S(n, k) \in \mathbb{N}$ by $s(0, 0) = S(0, 0) = 1$, $s(0, k) = S(0, k) = 0$ for $k \ge 1$, $s(n + 1, 0) = S(n + 1, 0) = 0$, and for $k \ge 1$:*
$$s(n + 1, k) = s(n, k - 1) - n\, s(n, k), \qquad S(n + 1, k) = S(n, k - 1) + k\, S(n, k).$$
*Then $s(n, k) = S(n, k) = 0$ for $k > n$, and for every $n \in \mathbb{N}$:*
$$(x)_n = \sum_{k=0}^{n} s(n, k)\, x^k, \qquad x^n = \sum_{k=0}^{n} S(n, k)\, (x)_k.$$

*Proof.* Both identities follow by induction on $n$ using $(x)_{n + 1} = x (x)_n - n (x)_n$ and $x (x)_k = (x)_{k + 1} + k (x)_k$. $\square$

**Lemma 2.4 (Binomial orthogonality).** *For all $k, m \in \mathbb{N}$,*
$$\sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (i)_m = \begin{cases} k!, & m = k, \\ 0, & m \ne k. \end{cases}$$

*Proof.* If $m > k$, then $(i)_m = 0$ for every $0 \le i \le k$, so the sum is $0$. If $m \le k$, then $(i)_m = m! \binom{i}{m}$ vanishes for $i < m$; substituting $i = m + r$ ($0 \le r \le k - m$) and using $\binom{k}{m + r} \binom{m + r}{m} = \binom{k}{m} \binom{k - m}{r}$ gives
$$\sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (i)_m = m! \binom{k}{m} \sum_{r=0}^{k - m} (-1)^{(k - m) - r} \binom{k - m}{r} = m! \binom{k}{m} (1 - 1)^{k - m},$$
which equals $k!$ when $m = k$ and $0$ when $m < k$. $\square$

## 3. Proofs of the Main Theorems

**Theorem 3.1 (Binomial–Stirling formula, integrality, and falling-factorial expansion).** *For all $c, n, k \in \mathbb{N}$,*
$$T_c(n, k) = \sum_{j=0}^{n} \binom{n}{j} c^{n - j} S(j, k) \in \mathbb{N}.$$
*In particular, $T_c(n, k) = 0$ whenever $k > n$, and*
$$(x + c)^n = \sum_{k=0}^{n} T_c(n, k)\, (x)_k \qquad \text{in } \mathbb{Q}[x].$$

*Proof.* Set $U_c(n, k) = \sum_{j=0}^{n} \binom{n}{j} c^{n - j} S(j, k)$. Note $U_c(n, k) = 0$ for $k > n$ since $S(j, k) = 0$ for $j \le n < k$. By the binomial theorem and Lemma 2.3,
$$(x + c)^n = \sum_{j=0}^{n} \binom{n}{j} c^{n - j} x^j = \sum_{j=0}^{n} \binom{n}{j} c^{n - j} \sum_{m=0}^{n} S(j, m)\, (x)_m = \sum_{m=0}^{n} U_c(n, m)\, (x)_m.$$
Now fix any $k \in \mathbb{N}$ and set $N = \max(n, k)$ (so $U_c(n, m) = 0$ for $m > n$). Evaluating the identity at $x = i$ ($0 \le i \le k$), multiplying by $(-1)^{k - i} \binom{k}{i}$, summing over $i = 0, \dots, k$, and applying Lemma 2.4 gives
$$k!\, T_c(n, k) = \sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (c + i)^n = \sum_{m=0}^{N} U_c(n, m) \sum_{i=0}^{k} (-1)^{k - i} \binom{k}{i} (i)_m = k!\, U_c(n, k).$$
Dividing by $k! \ne 0$ yields $T_c(n, k) = U_c(n, k) \in \mathbb{N}$ and $(x + c)^n = \sum_{k=0}^{n} T_c(n, k) (x)_k$. $\square$

**Theorem 3.2 (Conjecture 3, valid for all $n, k \ge 0$).** *For all integers $n, k \ge 0$,*
$$\sum_{i=0}^{k} T(n, i)\, \frac{k!}{(k - i)!} = (n + k)^n.$$

*Proof.* Set $c = n$ and $N = \max(n, k)$. By Theorem 3.1 (and $T(n, i) = 0$ for $i > n$), $(x + n)^n = \sum_{i=0}^{N} T(n, i)\, (x)_i$. Evaluating at $x = k$, terms with $i > k$ vanish since $(k)_i = 0$, while for $0 \le i \le k$ we have $(k)_i = k! / (k - i)!$. Hence $(n + k)^n = \sum_{i=0}^{k} T(n, i)\, k! / (k - i)!$. $\square$

**Theorem 3.3 (General Stirling shift theorem and Conjecture 1).** *For all $c, n, k \in \mathbb{N}$ with $k \le n$,*
$$T_c(n, k) = \sum_{m=0}^{c} s(c, m)\, S(n + m, c + k).$$
*In particular, taking $c = n$ gives Conjecture 1:*
$$T(n, k) = \sum_{i=0}^{n - k} s(n, k + i)\, S(n + k + i, n + k).$$

*Proof.* Substituting $x \mapsto x - c$ in Theorem 3.1 gives $x^n = \sum_{j=0}^{n} T_c(n, j)\, (x - c)_j$. Multiplying both sides by $(x)_c$ and applying Lemma 2.2 yields
$$x^n (x)_c = \sum_{j=0}^{n} T_c(n, j)\, (x)_{c + j} = \sum_{K=0}^{c + n} a_K (x)_K,$$
where $a_K = T_c(n, K - c)$ for $c \le K \le c + n$ and $a_K = 0$ for $K < c$. On the other hand, expanding $(x)_c$ and $x^{n + m}$ by Lemma 2.3 gives
$$x^n (x)_c = \sum_{m=0}^{c} s(c, m)\, x^{n + m} = \sum_{m=0}^{c} s(c, m) \sum_{K=0}^{c + n} S(n + m, K)\, (x)_K = \sum_{K=0}^{c + n} \left(\sum_{m=0}^{c} s(c, m)\, S(n + m, K)\right) (x)_K$$
(using $S(n + m, K) = 0$ whenever $K > n + m$). By Lemma 2.1, comparing the coefficients of $(x)_{c + k}$ ($0 \le k \le n$) gives $T_c(n, k) = \sum_{m=0}^{c} s(c, m)\, S(n + m, c + k)$.

When $c = n$, every summand with $m < k$ satisfies $n + m < n + k$, so $S(n + m, n + k) = 0$. Re-indexing $m = k + i$ for $0 \le i \le n - k$ gives $T(n, k) = \sum_{i=0}^{n - k} s(n, k + i)\, S(n + k + i, n + k)$. $\square$

**Theorem 3.4 (Conjecture 2).** *For every integer $n \ge 0$,*
$$\sum_{k=0}^{n} T(n, k) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} B_j = \mathrm{A134980}(n).$$

*Proof.* Summing Theorem 3.1 with $c = n$ over $0 \le k \le n$ and exchanging finite sums (using $S(j, k) = 0$ for $k > j$):
$$\sum_{k=0}^{n} T(n, k) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} \sum_{k=0}^{n} S(j, k) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} \sum_{k=0}^{j} S(j, k) = \sum_{j=0}^{n} \binom{n}{j} n^{n - j} B_j = \mathrm{A134980}(n). \quad \square$$
