# Complete Proof of Omar E. Pol's OEIS A400974, A280940, and A384225 Conjectures

## 1. Definitions and Statement

Fix a positive integer $n \ge 1$. Write $n = 2^v m$ with $v = v_2(n) \ge 0$ and $m$ odd, and set $Q = 2^{v+1}$, so $2n = Qm$ and the ruler function is $\text{A001511}(n) = v + 1$.

### 1.1 Symmetric Representation Width Word and Subparts

Set $r = \max\{j \ge 1 : j(j+1) \le 2n\} = \lfloor(\sqrt{8n+1}-1)/2\rfloor$. Following OEIS A237048, A249223, and A262045:
- For $1 \le j \le r$, let $b_j = 1$ if $j \mid \bigl(n - j(j+1)/2\bigr)$ and $b_j = 0$ otherwise.
- For $1 \le k \le r$, let $w_k = \sum_{j=1}^k (-1)^{j+1} b_j$ (with $w_0 = 0$).
- The full width word of the symmetric representation of $\sigma(n)$ is the palindrome
  $$\mathcal{W}(n) = (w_1, \dots, w_r, w_r, \dots, w_1) \qquad (\text{OEIS A262045}).$$

Partition $\mathcal{W}(n)$ into its maximal contiguous runs of positive entries (its *parts*) $P_1, \dots, P_s$. Within a part $p = (p_0, \dots, p_{L-1})$, a *width-one layer subpart* at height $h \ge 1$ is a maximal contiguous run of indices with $p_i \ge h$; let $\Lambda(p) = \sum_{h=1}^{\max p} (\text{number of maximal runs of entries } \ge h \text{ in } p)$. Then:
- Row $n$ of **OEIS A280940** is $(\Lambda(P_1), \dots, \Lambda(P_s))$.
- **OEIS A384230** is $\Lambda(P_{(s+1)/2})$ if $s$ is odd, and $0$ if $s$ is even.

### 1.2 Maximal $2$-Dense Divisor Blocks

Let $1 = e_0 < e_1 < \dots < e_{d-1} = n$ be the sorted positive divisors of $n$. Split this list at every index $i$ where $e_{i+1} > 2 e_i$ to obtain the maximal $2$-dense divisor blocks $B_1, \dots, B_t$. Then:
- Row $n$ of **OEIS A384222** is $(|B_1|, \dots, |B_t|)$.
- Row $n$ of **OEIS A384225** is $(|B_1^{\text{odd}}|, \dots, |B_t^{\text{odd}}|)$, where $B_k^{\text{odd}} = \{e \in B_k : e \text{ odd}\}$.
- **OEIS A400974** is $|B_{(t+1)/2}|$ if $t$ is odd, and $0$ if $t$ is even.

### 1.3 Main Theorem

**Theorem 1.** *For every positive integer $n \ge 1$:*
1. *(OEIS A280940 and A384225 Conjecture 1)* $s = t$, and $\Lambda(P_k) = |B_k^{\text{odd}}|$ for every $1 \le k \le t$.
2. *(OEIS A384225 Conjecture 2)* $|B_k| = (v_2(n) + 1) |B_k^{\text{odd}}|$ for every $1 \le k \le t$.
3. *(OEIS A400974)* $\text{A400974}(n) = \text{A001511}(n) \cdot \text{A384230}(n)$.

## 2. Layer-Run Variation Identity and Stutter Invariance

For a list $L$ of nonnegative integers, let $\text{dedup}(L)$ denote the list obtained by collapsing consecutive equal entries.

**Lemma 2.1.** *For every finite list $p = (p_0, \dots, p_{L-1})$ of nonnegative integers (with convention $p_{-1} = 0$),*
$$\Lambda(p) = \sum_{i=0}^{L-1} \max(0, p_i - p_{i-1}).$$
*Consequently, $\Lambda(\text{dedup}(p)) = \Lambda(p)$, and the sequence of layer-run counts of the positive parts of any list $L$ depends only on $\text{dedup}(L)$.*

*Proof.* For each integer $h \ge 1$, a maximal contiguous run of entries $\ge h$ in $p$ starts at index $i$ if and only if $p_{i-1} < h \le p_i$. Hence the number of runs at height $h$ equals $\#\{0 \le i < L : p_{i-1} < h \le p_i\}$. Summing over $1 \le h \le \max p$ and interchanging sums gives
$$\Lambda(p) = \sum_{i=0}^{L-1} \#\{h \ge 1 : p_{i-1} < h \le p_i\} = \sum_{i=0}^{L-1} \max(0, p_i - p_{i-1}).$$
Repeating an entry adds $\max(0, x - x) = 0$, so $\Lambda(\text{dedup}(p)) = \Lambda(p)$. Moreover, because zeros only separate distinct positive parts, collapsing any contiguous run of zeros to a single zero leaves the number of positive parts and the boundaries between them unchanged, while collapsing adjacent equal positive entries replaces each positive part $P$ by $\text{dedup}(P)$, which preserves $\Lambda(P)$. $\square$

## 3. The Interval-Count Model $W_n$ and Symmetry

Define for every integer $x \ge 0$:
$$W_n(x) = \#\{d \mid m : d \le x < Q d\}.$$
Clearly $W_n(0) = 0$, and for every $x \ge 0$,
$$W_n(x+1) - W_n(x) = \mathbf{1}_{x+1 \mid m} - \mathbf{1}_{\exists d \mid m,\; x+1 = Qd}. \tag{1}$$
Because every divisor of $m$ is odd while every multiple of $Q = 2^{v+1}$ is even, the two indicator sets are disjoint. Let $E = \{d : d \mid m\} \cup \{Qd : d \mid m\}$ be the set of jump points of $W_n$; then for $x \ge 1$, $W_n(x) \ne W_n(x-1)$ if and only if $x \in E$.

**Lemma 3.1.** *For every $1 \le k \le r$, $w_k = W_n(k)$.*

*Proof.* For $1 \le j \le r$, since $j(j+1)$ is even and $j(j+1)/2 \le n$, divisibility $j \mid \bigl(n - j(j+1)/2\bigr)$ is equivalent to $2j \mid \bigl(2n - j(j+1)\bigr)$, i.e., $j \mid 2n$ and $2n/j \equiv j + 1 \pmod 2$.
- If $j$ is odd, $\gcd(j, Q) = 1$, so $j \mid Qm = 2n \iff j \mid m$; in that case $2n/j = Q(m/j)$ is automatically even, matching $j + 1 \equiv 0 \pmod 2$.
- If $j$ is even, $2n/j$ must be odd, which means $Q \mid j$ and $j/Q \mid m$, i.e., $j = Qd$ for some $d \mid m$.

Hence $(-1)^{j+1} b_j = \mathbf{1}_{j \mid m} - \mathbf{1}_{\exists d \mid m,\; j = Qd} = W_n(j) - W_n(j-1)$ for every $1 \le j \le r$. Summing from $j = 1$ to $k$ gives $w_k = W_n(k) - W_n(0) = W_n(k)$. $\square$

**Lemma 3.2 (Reversal Identity).** *For every positive divisor $e \mid 2n$,*
$$W_n(2n / e) = W_n(e - 1).$$

*Proof.* The involution $d \mapsto m/d$ bijects the divisors of $m$ onto themselves. Since $de \cdot (m/d) = em$ and $de \cdot (2n/e) = dQm$, multiplying by $de > 0$ gives
$$m/d \le 2n/e \iff em \le dQm \iff e \le Qd \iff e - 1 < Qd,$$
$$2n/e < Q(m/d) \iff dQm < eQm \iff d < e \iff d \le e - 1.$$
Thus $d \mapsto m/d$ bijects $\{d \mid m : d \le e - 1 < Qd\}$ onto $\{d' \mid m : d' \le 2n/e < Qd'\}$. $\square$

**Proposition 3.3.** *Let $\mathcal{U}(n) = (W_n(1), W_n(2), \dots, W_n(2n-1))$. Then*
$$\text{dedup}(\mathcal{W}(n)) = \text{dedup}(\mathcal{U}(n)).$$

*Proof.* Every $e \in E$ divides $2n$, and $e \mapsto 2n/e$ is a fixed-point-free involution on $E$ (it swaps odd divisors of $m$ with even multiples of $Q$). For $e \in E$, we have $e \le r \iff e(e+1) \le 2n \iff e < 2n/e$. Let $1 = e_0 < e_1 < \dots < e_{s-1}$ be the elements of $E_{\text{lo}} = E \cap [1, r]$. Then $E \setminus \{2n\} = E_{\text{lo}} \cup E_{\text{hi}}$, where $E_{\text{hi}} = \{2n/e_{s-1} < \dots < 2n/e_1\}$.

Since $W_n$ changes value only at $E$, compressing $(W_n(1), \dots, W_n(r))$ yields $(W_n(e_0), \dots, W_n(e_{s-1}))$, and compressing $\mathcal{U}(n)$ yields $(W_n(e_0), \dots, W_n(e_{s-1}), W_n(2n/e_{s-1}), \dots, W_n(2n/e_1))$. For each $1 \le i \le s-1$, Lemma 3.2 gives $W_n(2n/e_i) = W_n(e_i - 1) = W_n(e_{i-1})$, because no jump point lies strictly between $e_{i-1}$ and $e_i$. Hence
$$\text{dedup}(\mathcal{U}(n)) = (W_n(e_0), \dots, W_n(e_{s-1}), W_n(e_{s-2}), \dots, W_n(e_0)).$$
By Lemma 3.1, $\mathcal{W}(n) = (W_n(1), \dots, W_n(r), W_n(r), \dots, W_n(1))$, whose compression is the exact same palindrome $(W_n(e_0), \dots, W_n(e_{s-1}), W_n(e_{s-2}), \dots, W_n(e_0))$. $\square$

## 4. Correspondence with Maximal $2$-Dense Divisor Blocks

Every positive divisor $e \mid n$ writes uniquely as $e = 2^i d$ with $0 \le i \le v$ and $d \mid m$. For each $d \mid m$, the dyadic half-open intervals $[2^i d, 2^{i+1} d)$ ($0 \le i \le v$) partition $[d, Qd)$. Consequently, for every integer $x \ge 1$,
$$W_n(x) > 0 \iff \exists d \mid m,\; d \le x < Qd \iff \exists e \mid n,\; e \le x < 2e. \tag{2}$$

Let $B_1, \dots, B_t$ be the maximal $2$-dense blocks of sorted divisors of $n$, and let $a_k = \min B_k$, $c_k = \max B_k$. Then $a_1 = 1$, $c_t = n$, and $2c_k < a_{k+1}$ for each $1 \le k < t$.

- **Inside each block interval $[a_k, 2c_k)$:** Because consecutive elements $e < e'$ of $B_k$ satisfy $e' \le 2e$, the intervals $[e, 2e)$ for $e \in B_k$ cover $[a_k, 2c_k)$ with no gap. By (2), $W_n(x) > 0$ for every $x \in [a_k, 2c_k)$.
- **In each inter-block gap $[2c_k, a_{k+1})$:** Every divisor $e \mid n$ satisfies either $e \le c_k$ (whence $2e \le 2c_k \le x$) or $e \ge a_{k+1}$ (whence $e > x$). By (2), $W_n(x) = 0$ for every $x \in [2c_k, a_{k+1})$, and this gap is nonempty since $2c_k < a_{k+1}$.

Therefore, the maximal positive runs of $\mathcal{U}(n) = (W_n(1), \dots, W_n(2n-1))$ are precisely the $t$ sequences $U_k = (W_n(a_k), W_n(a_k + 1), \dots, W_n(2c_k - 1))$ ($1 \le k \le t$), in exact order.

### Proof of Theorem 1(1)
By Lemma 2.1 and Proposition 3.3, $s = t$ and $\Lambda(P_k) = \Lambda(U_k)$ for every $1 \le k \le t$. Since $W_n(a_k - 1) = 0$ (at $k = 1$, $W_n(0) = 0$; for $k \ge 2$, $a_k - 1 \in [2c_{k-1}, a_k)$), Lemma 2.1 and equation (1) yield
$$\Lambda(U_k) = \sum_{x = a_k}^{2c_k - 1} \max(0, W_n(x) - W_n(x-1)) = \#\{d \mid m : a_k \le d < 2c_k\}.$$
Any odd divisor $d \in B_k$ divides $m$ and satisfies $a_k \le d \le c_k < 2c_k$. Conversely, any $d \mid m$ with $a_k \le d < 2c_k$ divides $n$, cannot lie in an earlier block (all elements $< a_k$), and cannot lie in a later block (all elements $\ge a_{k+1} > 2c_k$), so $d \in B_k^{\text{odd}}$. Hence $\Lambda(P_k) = |B_k^{\text{odd}}|$.

### Proof of Theorem 1(2)
If $e$ and $2e$ are both divisors of $n$, they cannot be separated by a gap $> 2 \cdot \text{prev}$, so $e$ and $2e$ must belong to the same maximal $2$-dense block $B_k$. By induction on $i$, for every odd divisor $d \mid m$ and every $0 \le i \le v$, we have $2^i d \in B_k \iff d \in B_k$. Thus the unique factorization map $e \mapsto (v_2(e), e / 2^{v_2(e)})$ gives a bijection
$$B_k \xrightarrow{\;\sim\;} \{0, 1, \dots, v\} \times B_k^{\text{odd}},$$
proving $|B_k| = (v + 1) |B_k^{\text{odd}}| = \text{A001511}(n) \cdot |B_k^{\text{odd}}|$.

### Proof of Theorem 1(3)
Combining Theorem 1(1) and Theorem 1(2), the two lists $(|B_1|, \dots, |B_t|)$ and $(\Lambda(P_1), \dots, \Lambda(P_s))$ have the same length $t = s$ and satisfy $|B_k| = \text{A001511}(n) \cdot \Lambda(P_k)$ for every $k$. Taking the middle element when $t$ is odd and $0$ when $t$ is even yields $\text{A400974}(n) = \text{A001511}(n) \cdot \text{A384230}(n)$. $\square$
