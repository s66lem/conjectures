# Complete Proof of the OEIS A402341 Valuation Conjecture and Its Power-of-Two Generalization

## 1. Statement

Let $s_2(t) = \text{A000120}(t)$ denote the binary digit sum of a nonnegative integer $t$, i.e., the number of $1$s in the base-$2$ expansion of $t$. For any integer $r \ge 1$ and any integer $n \ge 0$, define
$$P_r(x) = 1 + x + x^2 + \cdots + x^{2^r - 1}, \qquad a_r(n) = [x^{\lfloor (2^r - 1)n / 2 \rfloor}] P_r(x)^n.$$
When $r = 4$, $P_4(x) = 1 + x + \cdots + x^{15}$ and $a_4(n) = \text{A402341}(n)$ is the central (largest) coefficient of $(1 + x + \cdots + x^{15})^n$, introduced by Sajid Khan Hussain on November 17, 2026 ([OEIS A402341](https://oeis.org/A402341)) with the conjecture:

> **Conjecture (OEIS A402341).** *For even $n$, the 2-adic valuation of $a(n)$ equals $\text{A000120}(15n/2)$. Verified for $n \le 1500$.*

We prove a stronger congruence for every power-of-two block length $2^r$:

**Theorem 1.** *For every integer $r \ge 1$ and every even integer $n = 2m \ge 0$, put $N = (2^r - 1)m$. Then*
$$a_r(2m) \equiv \binom{2N}{N} \pmod{2^{s_2(N) + 1}},$$
*and consequently*
$$v_2(a_r(2m)) = s_2(N) = \text{A000120}\!\left(\frac{(2^r - 1)n}{2}\right).$$

**Corollary 2 (OEIS A402341).** *Taking $r = 4$, for every even $n = 2m \ge 0$,*
$$a(2m) \equiv \binom{30m}{15m} \pmod{2^{s_2(15m)+1}} \quad \text{and} \quad v_2(a(n)) = s_2\!\left(\frac{15n}{2}\right).$$

## 2. Elementary Properties of $s_2$ and Central Binomial Coefficients

**Lemma 2.1.** *For all nonnegative integers $u, v, k$:*
1. $s_2(0) = 0$, $s_2(2u) = s_2(u)$, $s_2(2u+1) = s_2(u) + 1$, and $s_2(2^k) = 1$.
2. *If $u > 0$, then $s_2(u) \ge 1$.*
3. *Subadditivity: $s_2(u + v) \le s_2(u) + s_2(v)$.*
4. *For all $t \ge 0$, $v_2\!\left(\binom{2t}{t}\right) = s_2(t)$.*

*Proof.* Items (1) and (2) follow immediately from the base-$2$ representation. For (3), write $u = 2a + b$ and $v = 2c + d$ with $b, d \in \{0, 1\}$. If $b + d \le 1$, then $s_2(u+v) = s_2(a+c) + b + d \le s_2(a) + s_2(c) + b + d = s_2(u) + s_2(v)$ by strong induction on $u + v$. If $b = d = 1$, then $s_2(u+v) = s_2(a+c+1) \le s_2(a+c) + 1 \le s_2(a) + s_2(c) + 1 < s_2(u) + s_2(v)$ (using the easy induction $s_2(w+1) \le s_2(w) + 1$).

For (4), first observe by induction on $m$ that $v_2((2m)!) = m + v_2(m!)$, since $(2(m+1))! = 2(m+1)(2m+1)(2m)!$ and $2m+1$ is odd. Strong induction on $t$ then yields Legendre's identity $v_2(t!) + s_2(t) = t$: for $t = 2m$, $v_2((2m)!) + s_2(2m) = m + v_2(m!) + s_2(m) = 2m$; for $t = 2m+1$, $v_2((2m+1)!) + s_2(2m+1) = v_2((2m)!) + s_2(m) + 1 = 2m + 1$. Finally, from $\binom{2t}{t}(t!)^2 = (2t)!$,
$$v_2\!\left(\binom{2t}{t}\right) = v_2((2t)!) - 2v_2(t!) = \bigl(t + v_2(t!)\bigr) - 2v_2(t!) = t - v_2(t!) = s_2(t). \quad \square$$

## 3. Polynomial Factorization in $y = x / (1 + x)^2$

For any nonnegative integer $D$ and any polynomial $F(y) = \sum_j c_j y^j \in \mathbb{Z}[y]$ satisfying $2j \le D$ whenever $c_j \ne 0$, define the homogenization
$$\text{eval}_D(F)(x) = \sum_j c_j x^j (1 + x)^{D - 2j} \in \mathbb{Z}[x].$$
Clearly $\text{eval}_D$ is $\mathbb{Z}$-linear, and if $F, G$ satisfy the degree bounds for $D_1, D_2$ respectively, then
$$\text{eval}_{D_1}(F) \cdot \text{eval}_{D_2}(G) = \text{eval}_{D_1 + D_2}(FG)$$
because $(D_1 - 2j) + (D_2 - 2k) = (D_1 + D_2) - 2(j+k)$ whenever $2j \le D_1$ and $2k \le D_2$.

Define polynomials $R_k(y) \in \mathbb{Z}[y]$ recursively by
$$R_0(y) = 1, \qquad R_{k+1}(y) = R_k(y)^2 - 2 y^{2^k} \quad (k \ge 0).$$
For instance, $R_1(y) = 1 - 2y$, $R_2(y) = 1 - 4y + 2y^2$, and $R_3(y) = 1 - 8y + 20y^2 - 16y^3 + 2y^4$.

**Lemma 3.1.** *For every $k \ge 0$, every nonzero monomial $y^j$ of $R_k$ satisfies $2j \le 2^k$, and*
$$\text{eval}_{2^k}(R_k)(x) = 1 + x^{2^k}.$$

*Proof.* By induction on $k$. For $k = 0$, $R_0 = 1$ has $2 \cdot 0 \le 1$ and $\text{eval}_1(1) = 1 + x$. Assuming the claim for $k$, $R_k^2$ satisfies the degree bound for $2 \cdot 2^k = 2^{k+1}$ and $2 y^{2^k}$ has $2 \cdot 2^k = 2^{k+1}$, so $R_{k+1}$ satisfies the bound for $2^{k+1}$ and
$$\text{eval}_{2^{k+1}}(R_{k+1}) = \text{eval}_{2^k}(R_k)^2 - 2 x^{2^k} (1 + x)^0 = (1 + x^{2^k})^2 - 2 x^{2^k} = 1 + x^{2^{k+1}}. \quad \square$$

Now set $Q_r(y) = \prod_{k=0}^{r-1} R_k(y)$. Since $\sum_{k=0}^{r-1} 2^k = 2^r - 1$, multiplicativity of $\text{eval}$ and the binary product identity $\prod_{k=0}^{r-1} (1 + x^{2^k}) = \sum_{i=0}^{2^r - 1} x^i = P_r(x)$ yield:

**Proposition 3.2.** *For every $r \ge 0$, every nonzero monomial $y^j$ of $Q_r$ satisfies $2j \le 2^r - 1$, and*
$$\text{eval}_{2^r - 1}(Q_r)(x) = P_r(x).$$
*In particular, for every $m \ge 0$ and $N = (2^r - 1)m$, every nonzero monomial $y^j$ of $Q_r(y)^{2m}$ satisfies $j \le N$, and*
$$\text{eval}_{2N}\bigl(Q_r^{2m}\bigr)(x) = P_r(x)^{2m}.$$

Extracting the coefficient of $x^N$ from both sides of Proposition 3.2, since
$$[x^N]\bigl(x^j (1 + x)^{2N - 2j}\bigr) = [x^{N-j}](1 + x)^{2(N-j)} = \binom{2(N-j)}{N-j},$$
we obtain the exact expansion
$$a_r(2m) = \sum_{j = 0}^{N} c_j \binom{2(N-j)}{N-j}, \qquad c_j = [y^j] Q_r(y)^{2m}. \tag{1}$$

## 4. Admissibility and Strong Admissibility

Call a polynomial $F(y) \in \mathbb{Z}[y]$ *admissible* if $2^{s_2(j)} \mid [y^j]F$ for all $j \ge 0$, and *strongly admissible* if $[y^0]F = 1$ and $2^{s_2(j)+1} \mid [y^j]F$ for all $j > 0$.

**Lemma 4.1.**
1. *If $F$ and $G$ are admissible, then $F - G$ and $FG$ are admissible.*
2. *Every $R_k$ ($k \ge 0$), and hence every $Q_r$ ($r \ge 0$), is admissible with constant term $1$.*
3. *If $F$ is admissible with $[y^0]F = 1$, then $F^2$ is strongly admissible.*
4. *If $F$ and $G$ are strongly admissible, then $FG$ is strongly admissible.*

*Proof.*
(1) Closure under subtraction is immediate. For $FG$, each term $([y^u]F)([y^v]G)$ with $u + v = j$ is divisible by $2^{s_2(u) + s_2(v)}$, hence by $2^{s_2(j)}$ by Lemma 2.1(3).

(2) By induction on $k$: $R_0 = 1$ is admissible with constant term $1$. Given $R_k$, the square $R_k^2$ is admissible by (1), and $-2 y^{2^k}$ is admissible because $s_2(2^k) = 1$; since $2^k > 0$, $[y^0]R_{k+1} = ([y^0]R_k)^2 = 1$. Multiplying over $k = 0, \dots, r-1$ gives the same for $Q_r$.

(3) Clearly $[y^0](F^2) = ([y^0]F)^2 = 1$. For any $j > 0$, write $f_u = [y^u]F$ and decompose
$$[y^j](F^2) = \sum_{u+v=j} f_u f_v = 2 \sum_{\substack{u+v=j \\ u < v}} f_u f_v + \sum_{\substack{u+v=j \\ u = v}} f_u f_v.$$
For each pair with $u < v$ and $u + v = j$, admissibility and Lemma 2.1(3) give $2^{s_2(j)} \mid f_u f_v$, so the factor of $2$ produces divisibility by $2^{s_2(j)+1}$. For the diagonal term (present only when $j = 2u$ with $u > 0$), $f_u^2$ is divisible by $2^{2 s_2(u)}$; since $u > 0$, Lemma 2.1(2) gives $s_2(u) \ge 1$, so $2 s_2(u) \ge s_2(u) + 1 = s_2(2u) + 1 = s_2(j) + 1$.

(4) Clearly $[y^0](FG) = 1$. For $j > 0$ and any $u + v = j$, at least one of $u, v$ is positive. If $u > 0$, then $2^{s_2(u)+1} \mid [y^u]F$ and $2^{s_2(v)} \mid [y^v]G$ (trivially if $v = 0$, and from $s_2(v)+1 \ge s_2(v)$ if $v > 0$), so their product is divisible by $2^{s_2(u) + s_2(v) + 1}$, hence by $2^{s_2(j)+1}$. If $u = 0$, then $v = j > 0$ and $([y^0]F)([y^j]G) = [y^j]G$ is divisible by $2^{s_2(j)+1}$. $\square$

## 5. Completion of the Proof of Theorem 1

By Lemma 4.1(2)–(4), $Q_r(y)^{2m} = (Q_r(y)^2)^m$ is strongly admissible for every $r \ge 0$ and $m \ge 0$. Hence in the expansion (1), $c_0 = 1$ and $2^{s_2(j)+1} \mid c_j$ for every $j > 0$.

For each $j > 0$ with $j \le N$, Lemma 2.1(4) gives $2^{s_2(N-j)} \mid \binom{2(N-j)}{N-j}$, so
$$2^{s_2(j) + 1 + s_2(N-j)} \;\Big|\; c_j \binom{2(N-j)}{N-j}.$$
By binary subadditivity (Lemma 2.1(3)), $s_2(j) + s_2(N-j) \ge s_2(N)$, whence $2^{s_2(N)+1}$ divides every $j > 0$ summand in (1). Therefore
$$a_r(2m) - \binom{2N}{N} = \sum_{j=1}^{N} c_j \binom{2(N-j)}{N-j} \equiv 0 \pmod{2^{s_2(N)+1}}.$$
Since $v_2\!\left(\binom{2N}{N}\right) = s_2(N)$ by Lemma 2.1(4), we have $2^{s_2(N)} \mid \binom{2N}{N}$ and $2^{s_2(N)+1} \nmid \binom{2N}{N}$, and the congruence modulo $2^{s_2(N)+1}$ transfers both properties to $a_r(2m)$. In particular $a_r(2m) \ne 0$ and $v_2(a_r(2m)) = s_2(N)$. $\square$

## 6. Sharpness for Odd $n$

The hypothesis that $n$ is even cannot be dropped. For $r = 4$ and $n = 3$, $\lfloor 15 \cdot 3 / 2 \rfloor = 22$ has $s_2(22) = s_2(10110_2) = 3$, whereas $a_4(3) = 192 = 2^6 \cdot 3$ has $v_2(a_4(3)) = 6$. Conceptually, $Q_r(y)$ itself is only admissible and not strongly admissible ($[y^1]Q_r = -2(2^{r-1} - 1)$ has $2$-adic valuation $1 = s_2(1)$ for $r \ge 2$), so for odd $n$ the $j = 1$ term in the expansion of $Q_r(y)^n$ can cancel the leading central binomial term modulo $2^{s_2(N)+1}$.
