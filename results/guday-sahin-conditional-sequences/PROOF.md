# Complete Proof: Resolution of Güday–Şahin Conditional-Sequence Conjectures (INTEGERS 26, 2026, #A5)

## 1. Problem Setup and Verbatim Statements

In *Linear Recurrence Relations Satisfied by the General Conditional Sequences* (*INTEGERS* **26**, 2026, #A5), E. Güday and M. Şahin study the general conditional sequence $\{q_n\}_{n \ge 0}$ defined for positive integers $r, m$ ($m > r$) by

$$q_n = \sum_{j=1}^{m} a_{i, j}\, q_{n-j} \qquad \text{for } n \equiv i \pmod{r},\; n \ge m, \tag{1}$$

with real coefficients $a_{i, j}$ ($0 \le i \le r-1$, $1 \le j \le m$) and convention $a_{i, 0} = -1$ (p. 15).

- **Open Problem 1 (p. 15):** Determine the sign of the coefficients in the $r = 3$ decimated recurrence (Relation (12)).
- **Conjecture 1 (p. 16):** For positive integers $m > r$, $\{q_n\}$ satisfies
  $$q_n = A_r q_{n-r} + A_{2r} q_{n-2r} + \dots + A_{mr} q_{n-mr},$$
  where
  $$A_d = \sum_{\substack{d = d_0 + \dots + d_{r-1} \\ 0 \le d_0, \dots, d_{r-1} \le m \\ \text{(R)}}} \pm\, a_{0, d_0} a_{1, d_1} \cdots a_{r-1, d_{r-1}}$$
  and condition **(R)** requires $d_k \not\equiv k + d_0 \pmod{r}$ for every $1 \le k \le r - 1$.
- **Conjecture 2 (p. 18):** For $r = 3$ and $d \in \{0, 3, \dots, 3m\}$, let $\mathcal{A}_d$ be the set of monomials $a_{0, d_0} a_{1, d_1} a_{2, d_2}$ with $(d_0, d_1, d_2) \in \{0, \dots, m\}^3$, $d_0 + d_1 + d_2 = d$, satisfying **(R)**. Then
  $$|\mathcal{A}_d| = w_{3,m}(d) - \frac{w^*_{3,m}(d)}{2},$$
  where $w_{3,m}(d)$ is the number of ordered partitions of $d$ into $3$ parts in $[0, m]$ and $w^*_{3,m}(d)$ counts those with pairwise distinct parts.

---

## 2. Exact Decimated Recurrence and Solution of Open Problem 1

**Theorem 1 (Signed Bijection Formula, all $r, m \ge 1$).** Let $R = \mathbb{Z}[a_{i,j}]$ and set $a_{i,0} = -1$. For any tuple $d = (d_0, \dots, d_{r-1}) \in \{0, \dots, m\}^r$, define $\sigma_d : \mathbb{Z}_r \to \mathbb{Z}_r$ by $\sigma_d(i) = (i - d_i) \bmod r$ and $\mathrm{nz}(d) = \#\{i : d_i > 0\}$. Then for every $n \ge mr + m - 1$,

$$q_n = \sum_{s=1}^{m} c_s\, q_{n - sr}, \qquad c_s = \sum_{\substack{d \in \{0,\dots,m\}^r \\ \sum d_i = sr,\; \sigma_d \text{ bijective}}} \mathrm{sgn}(\sigma_d)\, (-1)^{\mathrm{nz}(d)+1} \prod_{d_i > 0} a_{i, d_i}.$$

In particular, distinct tuples yield distinct monomials, so as a polynomial in the indeterminates $a_{i,j}$, $c_s$ has coefficient $\mathrm{sgn}(\sigma_d)(-1)^{\mathrm{nz}(d)+1} \in \{\pm 1\}$ on bijective tuples and $0$ on every non-bijective tuple.

**Proof.** Group consecutive terms into blocks $X_k = (q_{kr}, q_{kr+1}, \dots, q_{kr+r-1})^\top \in R^r$. With $a_{i,0} = -1$, equation (1) for $n = kr + i$ reads $\sum_{j=0}^{m} a_{i,j} q_{kr+i-j} = 0$. Writing $i - j = t - \ell r$ with $t \in \{0, \dots, r-1\}$ and $\ell \ge 0$ gives the block recurrence

$$\sum_{\ell=0}^{L} P_\ell X_{k-\ell} = 0, \qquad (P_\ell)_{i, t} = a_{i,\, i - t + \ell r},$$

where $a_{i, j} = 0$ outside $0 \le j \le m$ and $L = \lceil m/r \rceil + 1$ satisfies $rL \ge m$. Since $P_0$ is lower triangular with diagonal entries $a_{i,0} = -1$, we have $\det P_0 = (-1)^r$ and $P_0 \in \mathrm{GL}_r(R)$.

Let $Q(\mu) = \sum_{\ell=0}^{L} P_\ell \mu^{L-\ell}$ and let $C$ be the $rL \times rL$ block companion matrix of the monic matrix polynomial $L(\mu) = P_0^{-1} Q(\mu)$ acting on $(X_{k-1}, \dots, X_{k-L}) \in R^{rL}$. Block Gaussian elimination gives $\det(\mu I - C) = \det L(\mu) = (-1)^r \det Q(\mu)$ over $R$.

Let $\pi : R^{rL} \to R^m$ project onto the $m$ most recent entries $v_{kr-1} = (q_{kr-1}, \dots, q_{kr-m})$. Because the recurrence (1) has depth at most $m$, $X_k$ depends only on $v_{kr-1}$, so $\pi C = M \pi$, where $M = C_{r-1} \cdots C_0$ is the $m \times m$ monodromy matrix (product of the single-step companion matrices $C_i$ for residue $i$). On $\ker \pi$, the new block $X_k$ is $0$ and the shift pushes zeros through the $rL$-window, so $C|_{\ker \pi}$ is nilpotent. Since $\pi$ is split-surjective over $R$, $\det(\mu I - C) = \mu^{rL - m} \det(\mu I - M)$, giving

$$\chi_M(\mu) = \det(\mu I - M) = (-1)^r \mu^m \det\!\left(\sum_{\ell=0}^{L} P_\ell \mu^{-\ell}\right).$$

Entry $(i, t)$ of $\sum_\ell P_\ell \mu^{-\ell}$ equals $\sum_{j \equiv i-t \pmod r} a_{i,j} \mu^{\lfloor (i-j)/r \rfloor}$. Expanding the $r \times r$ determinant by Leibniz's formula chooses one $j = d_i \in \{0, \dots, m\}$ in each row $i$ such that $t = \sigma_d(i) = (i - d_i) \bmod r$ is a bijection on $\{0, \dots, r-1\}$. Its exponent of $\mu$ is

$$\sum_{i=0}^{r-1} \left\lfloor \frac{i - d_i}{r} \right\rfloor = \frac{1}{r} \sum_{i=0}^{r-1} \bigl(i - d_i - \sigma_d(i)\bigr) = -\frac{1}{r}\sum_{i=0}^{r-1} d_i.$$

Thus

$$\chi_M(\mu) = \mu^m + (-1)^r \sum_{s=1}^{m} \mu^{m-s} \sum_{\substack{\sum d_i = sr \\ \sigma_d \text{ bijective}}} \mathrm{sgn}(\sigma_d) \prod_{i=0}^{r-1} a_{i, d_i}.$$

For every residue class $\rho \in \mathbb{Z}_r$, the state vector $v_n$ advances by $v_{n+r} = M^{(\rho)} v_n$, where $M^{(\rho)}$ is a cyclic rotation of $C_{r-1} \cdots C_0$. All cyclic rotations share the same characteristic polynomial $\chi_M(\mu)$. By Cayley–Hamilton, $v_{n+mr} = \sum_{s=1}^{m} c_s v_{n+(m-s)r}$ with

$$c_s = -(-1)^r \sum_{\substack{\sum d_i = sr \\ \sigma_d \text{ bijective}}} \mathrm{sgn}(\sigma_d) \prod_{i=0}^{r-1} a_{i, d_i}.$$

Since $a_{i,0} = -1$ appears $r - \mathrm{nz}(d)$ times in $\prod_i a_{i, d_i}$, the overall sign of $\prod_{d_i > 0} a_{i, d_i}$ is $-(-1)^r (-1)^{r - \mathrm{nz}(d)} \mathrm{sgn}(\sigma_d) = \mathrm{sgn}(\sigma_d)(-1)^{\mathrm{nz}(d)+1}$. This proves Theorem 1 and resolves **Open Problem 1** (for $r = 3$, every degree-3 term has $\mathrm{nz}(d) = 3$, so its sign is $+\mathrm{sgn}(\sigma_d)$, matching Relation (12)). $\blacksquare$

---

## 3. Exact Threshold ($r \le 3$ vs $r \ge 4$) and Unconditional Refutation of Conjecture 1

Condition **(R)** says precisely that $\sigma_d(k) \ne \sigma_d(0)$ for all $1 \le k \le r - 1$.

- **Case $r \le 3$:** Under $\sum_{i=0}^{r-1} d_i \equiv 0 \pmod{r}$, we have $\sum_{i=0}^{r-1} \sigma_d(i) \equiv \sum_{i=0}^{r-1} i \pmod{r}$. For $r = 1$ and $r = 2$, $\sigma_d(k) \ne \sigma_d(0)$ immediately implies injectivity. For $r = 3$, if $\sigma_d(1) = \sigma_d(2) = x$, then $\sigma_d(0) + 2x \equiv 0 + 1 + 2 \equiv 0 \pmod{3}$ forces $\sigma_d(0) \equiv x \pmod{3}$, violating **(R)**. Hence for $r \in \{1, 2, 3\}$, **(R)** is equivalent to bijectivity of $\sigma_d$, and Conjecture 1 holds with the signs of Theorem 1 (formalized in `paperCond_iff_bijective_of_le_three`).
- **Case $r \ge 4$:** Consider the explicit tuple $d^* = (0, r-1, 0, 1, 0, \dots, 0) \in \{0, \dots, m\}^r$ (for any $m > r \ge 4$). Its sum is $r$, it satisfies **(R)** (since $d^*_0 = 0$, $d^*_1 = r-1 \not\equiv 1$, $d^*_3 = 1 \not\equiv 3$, and $d^*_k = 0 \not\equiv k$ for $k \notin \{0, 1, 3\}$), yet $\sigma_{d^*}(1) = \sigma_{d^*}(2) = \sigma_{d^*}(3) = 2 \pmod{r}$, so $\sigma_{d^*}$ is not bijective (`nonbijective_family_ge_four`).

### Concrete Integer Counterexample for $r = 4, m = 5$ (All Sign Choices, All Cutoffs $N$)

Set $a_{1,3} = a_{3,1} = 1$ and $a_{i,j} = 3(((7i + 5j) \bmod 11) + 1)$ for all other $(i, j) \in \{0,1,2,3\} \times \{1,2,3,4,5\}$, with initial values $(q_0, q_1, q_2, q_3, q_4) = (2, -1, 5, 3, 7)$.

1. The state vector $v_k = (q_{4k+4}, q_{4k+3}, q_{4k+2}, q_{4k+1}, q_{4k})^\top$ satisfies $v_{k+1} = M v_k$ for all $k \ge 0$, where $M = C_0 C_3 C_2 C_1$ is the integer $5 \times 5$ matrix
   $$M = \begin{pmatrix} 12297 & 42294 & 2400 & 35847 & 63756 \\ 363 & 1248 & 72 & 1047 & 1881 \\ 171 & 591 & 33 & 507 & 891 \\ 6 & 21 & 1 & 18 & 33 \\ 1 & 0 & 0 & 0 & 0 \end{pmatrix}.$$
2. Direct matrix arithmetic verifies
   $$M^5 = 13596 M^4 + 68961 M^3 + 83853 M^2 - 562923 M + 74844 I.$$
   Hence $q_{4k+24} = \sum_{s=1}^{5} c_s q_{4k+24-4s}$ for all $k \ge 0$, with $(c_1, c_2, c_3, c_4, c_5) = (13596, 68961, 83853, -562923, 74844)$.
3. Let $K$ be the $5 \times 5$ decimated companion matrix for $(c_1, \dots, c_5)$, and let $W(t)$ be the $5 \times 5$ Krylov matrix with entries $W(t)_{s, j} = q_{4(t+j) + 20 - 4s}$ ($0 \le s, j \le 4$). Then $W(t+1) = K W(t)$, so $W(t) = K^t W(0)$. Since $\det K = c_5 = 74844 \ne 0$ and $\det W(0) = 57854063997551257566686800189595316225787536 \ne 0$, we have $\det W(t) = 74844^t \det W(0) \ne 0$ for every $t \ge 0$.
4. Suppose Conjecture 1 held over $\mathbb{R}$ for some sign function $s : \{0, \dots, 5\}^4 \to \{\pm 1\}$ and some threshold $N$ (under either convention $a_{i,0} = 1$ or $a_{i,0} = -1$). Evaluating at $n = 4(N + j) + 24 \ge N$ ($j = 0, \dots, 4$) and subtracting the true recurrence yields $\delta^\top W(N) = 0$ where $\delta_k = A_{4(k+1)} - c_{k+1}$. Multiplying on the right by $\mathrm{adj}(W(N))$ gives $\det(W(N))\, \delta = 0$, hence $\delta = 0$ and in particular $A_4 = c_1 = 13596 \equiv 0 \pmod{3}$.
5. However, of the $17$ tuples in `conjTuples4 4`, the single tuple $t^* = (0, 3, 0, 1)$ has monomial value $a_{1,3} a_{3,1} = 1$ (and $a_{0,0} a_{2,0} = (\pm 1)^2 = 1$), whereas each of the other $16$ tuples contains at least one factor $a_{i,j}$ divisible by $3$. Thus $A_4 \equiv s(t^*) \equiv \pm 1 \pmod{3}$, contradicting $A_4 = 13596 \equiv 0 \pmod{3}$.

This proves `guday_sahin_conjecture_1_false_real`. $\blacksquare$

---

## 4. Exact Corrected Formula and Disproof of Conjecture 2

**Theorem 2 (Exact Count and Threshold for Conjecture 2).** Let $m \ge 1$ and $3 \mid d$. Let $T = \{(d_1, d_2, d_3) \in \{0, \dots, m\}^3 : d_1 + d_2 + d_3 = d\}$, so $|T| = w_{3,m}(d)$, and let $w^{\bmod 3}_{3,m}(d)$ be the number of triples in $T$ whose residues modulo $3$ are pairwise distinct. Then:

1. (**Exact formula, all $m, d$ with $3 \mid d$:**) $2|\mathcal{A}_d| = 2 w_{3,m}(d) - w^{\bmod 3}_{3,m}(d)$.
2. (**Validity for $m \le 5$:**) If $m \le 5$, then $w^{\bmod 3}_{3,m}(d) = w^*_{3,m}(d)$, so Conjecture 2 holds.
3. (**Failure for every $m \ge 6$:**) For every $m \ge 6$, $w^{\bmod 3}_{3,m}(9) < w^*_{3,m}(9)$, so $2|\mathcal{A}_9| \ne 2 w_{3,m}(9) - w^*_{3,m}(9)$. At the minimal counterexample $m = 6, d = 9$, we have $w_{3,6}(9) = 37$, $w^*_{3,6}(9) = 30$, $w^{\bmod 3}_{3,6}(9) = 24$, and $|\mathcal{A}_9| = 25 \ne 22 = 37 - 30/2$.

**Proof.** Because $d_1 + d_2 + d_3 = d \equiv 0 \pmod{3}$, if any two parts share a residue $x \pmod{3}$, then the third satisfies $2x + y \equiv 0 \pmod{3}$, hence $y \equiv x \pmod{3}$. Thus $T$ partitions disjointly into $T_{\mathrm{eq}}$ (all three parts congruent mod $3$) and $T_{\mathrm{dist}}$ (residues mod $3$ pairwise distinct).

- Every triple in $T_{\mathrm{eq}}$ satisfies $d_2 \equiv d_1 \not\equiv d_1 + 1 \pmod{3}$ and $d_3 \equiv d_1 \not\equiv d_1 + 2 \pmod{3}$, so $T_{\mathrm{eq}} \subseteq \mathcal{A}_d$.
- On $T_{\mathrm{dist}}$, the involution $(d_1, d_2, d_3) \mapsto (d_1, d_3, d_2)$ preserves $T_{\mathrm{dist}}$ and maps $T_{\mathrm{dist}} \cap D$ bijectively onto $T_{\mathrm{dist}} \setminus D$ (since for distinct residues mod $3$, $d_2 \not\equiv d_1 + 1 \land d_3 \not\equiv d_1 + 2$ holds if and only if $(d_2, d_3) \equiv (d_1 + 2, d_1 + 1) \pmod{3}$, which swapping $d_2$ and $d_3$ turns into $(d_1 + 1, d_1 + 2)$). Hence $2|T_{\mathrm{dist}} \cap D| = |T_{\mathrm{dist}}|$.

Summing gives $2|\mathcal{A}_d| = 2|T_{\mathrm{eq}}| + |T_{\mathrm{dist}}| = 2|T| - |T_{\mathrm{dist}}| = 2 w_{3,m}(d) - w^{\bmod 3}_{3,m}(d)$.

Clearly $T_{\mathrm{dist}} \subseteq T^*$ (distinct residues imply distinct integers). A triple lies in $T^* \setminus T_{\mathrm{dist}}$ if and only if its three parts are pairwise distinct and all congruent modulo $3$, requiring three distinct elements of the same residue class in $\{0, \dots, m\}$, i.e. $x < x+3 < x+6 \le m$, which is impossible for $m \le 5$ and holds for $(0, 3, 6)$ (and its $6$ permutations, summing to $9$) for every $m \ge 6$. $\blacksquare$

*(Side remark on Example 5 of Güday–Şahin, $m = 4, d = 6$: the paper lists $w_{3,4}(6) = 13$ and $|\mathcal{A}_6| = 10$, omitting the $6$ permutations of $(1, 2, 3)$; the true values are $w_{3,4}(6) = 19$, $w^*_{3,4}(6) = 12$, and $|\mathcal{A}_6| = 13 = 19 - 12/2$.)*
