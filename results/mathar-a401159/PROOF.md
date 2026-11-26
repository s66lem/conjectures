# Proof of R. J. Mathar's OEIS A401159 Conjectures

## 1. Problem Statement

In [OEIS A401159](https://oeis.org/A401159) (approved November 18, 2026), R. J. Mathar defines the triangle $T(n, m)$ as the number of binary $n \times m$ matrices with at most two $1$'s in each row and at most two $1$'s in each column, and states two conjectures in the Formula section:

- **Conjecture 1:** $T(n, 2) = \mathrm{A086601}(n) = \mathrm{A000124}(n)^2$.
- **Conjecture 2:**
  $$T(n, 3) = 1 + n + \frac{11}{4}n^2 + \frac{13}{8}n^3 + \frac{1}{8}n^4 + \frac{3}{8}n^5 + \frac{1}{8}n^6.$$

(In Mathar's companion note [a247158.pdf](https://oeis.org/A247158/a247158.pdf), Table 2 tabulates $T(n, m)$ via a recurrence without closed forms for fixed $m$.)

We prove a general closed-form theorem for binary matrices with at most $k$ ones per row and column whenever $m \le k + 1$, and deduce both conjectures immediately as the $k = 2$ specialization.

## 2. General Theorem

For integers $n, m, k \ge 0$, let $A(n, m, k)$ be the number of $n \times m$ matrices $M \in \{0, 1\}^{n \times m}$ such that:
- every row sum satisfies $\sum_{c=1}^{m} M_{r, c} \le k$ for all $r \in [n]$, and
- every column sum satisfies $\sum_{r=1}^{n} M_{r, c} \le k$ for all $c \in [m]$.

In particular, $T(n, m) = A(n, m, 2)$. Define
$$s(n, k) = \sum_{i=0}^{k} \binom{n}{i},$$
which equals the number of subsets of $[n]$ of cardinality at most $k$ (with the convention $\binom{n}{i} = 0$ for $i > n$).

**Theorem 1.** *For all integers $n \ge 0$ and $k \ge 0$:*
1. *If $0 \le m \le k$, then*
   $$A(n, m, k) = s(n, k)^m.$$
2. *For $m = k + 1$,*
   $$A(n, k + 1, k) = \sum_{j=0}^{k} (-1)^j \binom{n}{j} s(n - j, k - j)^{k + 1},$$
   *where terms with $j > n$ vanish because $\binom{n}{j} = 0$.*

### Proof

Identify each binary matrix $M \in \{0, 1\}^{n \times m}$ with its $m$-tuple of column supports
$$(S_1, \dots, S_m) \in \mathcal{P}([n])^m, \qquad S_c = \{r \in [n] : M_{r, c} = 1\}.$$
This correspondence is a bijection. Under this identification:
- the $c$-th column sum is $|S_c|$, so the column constraints become $|S_c| \le k$ for all $c \in [m]$;
- the $r$-th row sum is $|\{c \in [m] : r \in S_c\}| \le m$.

**Part 1 ($0 \le m \le k$).** Because every row sum is at most $m \le k$, the row constraints are automatically satisfied by every tuple $(S_1, \dots, S_m)$. Hence admissible matrices correspond bijectively to $\mathcal{F}_{n, k}^m$, where $\mathcal{F}_{n, k} = \{S \subseteq [n] : |S| \le k\}$. Partitioning $\mathcal{F}_{n, k}$ by cardinality gives $|\mathcal{F}_{n, k}| = \sum_{i=0}^{k} \binom{n}{i} = s(n, k)$, and therefore $A(n, m, k) = s(n, k)^m$.

**Part 2 ($m = k + 1$).** For a tuple $S = (S_1, \dots, S_{k+1}) \in \mathcal{F}_{n, k}^{k+1}$, the sum of row $r$ is at most $k + 1$, and equals $k + 1$ if and only if $r \in S_c$ for every $c \in [k + 1]$. Writing
$$B(S) = \bigcap_{c=1}^{k+1} S_c = \{r \in [n] : \forall c \in [k+1],\; r \in S_c\},$$
the tuple $S$ satisfies all row constraints if and only if $B(S) = \emptyset$.

For every finite set $A \subseteq [n]$, the alternating sum over subsets of $A$ satisfies the Boolean-lattice identity
$$\sum_{J \subseteq A} (-1)^{|J|} = \begin{cases} 1 & \text{if } A = \emptyset, \\ 0 & \text{if } A \ne \emptyset. \end{cases}$$
(Indeed, if $A = \emptyset$ the single term $J = \emptyset$ gives $1$; if $a \in A$, then $J \mapsto J \triangle \{a\}$ is a sign-reversing involution on $\mathcal{P}(A)$.)

Summing this indicator over $S \in \mathcal{F}_{n, k}^{k+1}$ and interchanging the order of summation gives
$$A(n, k + 1, k) = \sum_{S \in \mathcal{F}_{n, k}^{k+1}} \sum_{J \subseteq B(S)} (-1)^{|J|} = \sum_{J \subseteq [n]} (-1)^{|J|} \bigl|\{S \in \mathcal{F}_{n, k}^{k+1} : J \subseteq B(S)\}\bigr|.$$
Notice that $J \subseteq B(S)$ holds if and only if $J \subseteq S_c$ for every $c \in [k + 1]$. Thus the inner count factors as $N(J)^{k + 1}$, where
$$N(J) = \bigl|\{U \subseteq [n] : J \subseteq U \text{ and } |U| \le k\}\bigr|.$$
- If $|J| > k$, no subset $U \supseteq J$ has $|U| \le k$, so $N(J) = 0$ and $N(J)^{k+1} = 0$ (since $k + 1 \ge 1$).
- If $|J| = j \le k$, the map $U \mapsto U \setminus J$ is a bijection from $\{U \subseteq [n] : J \subseteq U,\; |U| \le k\}$ onto $\{V \subseteq [n] \setminus J : |V| \le k - j\}$. Since $|[n] \setminus J| = n - j$, we obtain $N(J) = s(n - j, k - j)$.

Grouping subsets $J \subseteq [n]$ by cardinality $j = |J|$ (there are $\binom{n}{j}$ subsets of size $j$, with $\binom{n}{j} = 0$ whenever $j > n$), we conclude that
$$A(n, k + 1, k) = \sum_{j=0}^{k} (-1)^j \binom{n}{j} s(n - j, k - j)^{k + 1}. \qquad \square$$

## 3. Proofs of the Two OEIS A401159 Conjectures

Set $k = 2$, and write
$$f(n) = s(n, 2) = \binom{n}{0} + \binom{n}{1} + \binom{n}{2} = 1 + n + \frac{n(n - 1)}{2} = \frac{n^2 + n + 2}{2} = \frac{n(n + 1)}{2} + 1 = \mathrm{A000124}(n).$$

### Corollary 1 (Conjecture 1)

Applying Theorem 1(1) with $k = 2$ and $m = 2$,
$$T(n, 2) = A(n, 2, 2) = s(n, 2)^2 = f(n)^2 = \mathrm{A000124}(n)^2 = \mathrm{A086601}(n)$$
for every integer $n \ge 0$. $\square$

### Corollary 2 (Conjecture 2)

Applying Theorem 1(2) with $k = 2$ gives
$$T(n, 3) = A(n, 3, 2) = \binom{n}{0} s(n, 2)^3 - \binom{n}{1} s(n - 1, 1)^3 + \binom{n}{2} s(n - 2, 0)^3.$$
We evaluate the three terms for every integer $n \ge 0$:
- For $j = 0$: $\binom{n}{0} s(n, 2)^3 = f(n)^3 = \frac{(n^2 + n + 2)^3}{8}$.
- For $j = 1$: if $n \ge 1$, then $s(n - 1, 1) = \binom{n-1}{0} + \binom{n-1}{1} = 1 + (n - 1) = n$, so $\binom{n}{1} s(n - 1, 1)^3 = n^4$; if $n = 0$, both $\binom{0}{1} s(0, 1)^3 = 0$ and $0^4 = 0$. Hence the $j = 1$ term equals $-n^4$ for all $n \ge 0$.
- For $j = 2$: $s(m, 0) = \binom{m}{0} = 1$ for all $m \ge 0$, so $\binom{n}{2} s(n - 2, 0)^3 = \binom{n}{2} = \frac{n(n - 1)}{2}$ for all $n \ge 0$.

Therefore,
$$T(n, 3) = \frac{(n^2 + n + 2)^3}{8} - n^4 + \frac{n(n - 1)}{2}.$$
Expanding $(n^2 + n + 2)^3 = n^6 + 3n^5 + 9n^4 + 13n^3 + 18n^2 + 12n + 8$, we obtain
$$\begin{aligned}
8\,T(n, 3) &= (n^6 + 3n^5 + 9n^4 + 13n^3 + 18n^2 + 12n + 8) - 8n^4 + (4n^2 - 4n) \\
&= 8 + 8n + 22n^2 + 13n^3 + n^4 + 3n^5 + n^6.
\end{aligned}$$
Dividing by $8$ yields
$$T(n, 3) = 1 + n + \frac{11}{4}n^2 + \frac{13}{8}n^3 + \frac{1}{8}n^4 + \frac{3}{8}n^5 + \frac{1}{8}n^6$$
for every integer $n \ge 0$. $\square$

## 4. Machine Verification

- **Lean 4 (`lean/Conjectures/MatharA401159.lean`):** Formally proves Theorem 1(1), Theorem 1(2), Corollary 1 (`mathar_A401159_conj1`), and Corollary 2 (`mathar_A401159_conj2_nat` and `mathar_A401159_conj2_rat`) directly over binary matrices `Fin n → Fin m → Bool`, using only standard Lean axioms `[propext, Classical.choice, Quot.sound]`.
- **Python (`results/mathar-a401159/verify.py`):** Independently checks Theorem 1(1)–(2) against brute-force enumeration of all $2^{nm}$ binary matrices ($nm \le 18$, $k \in \{1, 2, 3\}$), against a row-by-row dynamic program ($n \le 15$, $k \in \{1, 2, 3\}$), against the published OEIS A401159 entries ($1 \le n \le 9$, $m \le 3$), and against both conjectured closed forms for $0 \le n < 2000$.
