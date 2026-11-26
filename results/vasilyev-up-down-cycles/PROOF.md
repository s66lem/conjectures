# Negative Resolution of Question 7.1 of Vasilyev (arXiv:2611.20344v2)

## 1. Problem Statement

For any subset $S \subseteq \mathbb{N} = \{1, 2, 3, \dots\}$, O. Vasilyev ([arXiv:2611.20344v2](https://arxiv.org/abs/2611.20344)) defines the Collatz-type map $T_S : \mathbb{N} \to \mathbb{N}$ by
$$T_S(x) = \begin{cases} U(x) := \lceil 3x / 2 \rceil & \text{if } x \in S, \\ D(x) := \lceil x / 2 \rceil & \text{if } x \notin S. \end{cases}$$
The *up-down graph* $G$ on $\mathbb{N}$ has directed edges $x \to U(x)$ and $x \to D(x)$ for each $x \in \mathbb{N}$. By Vasilyev's Dictionary proposition (Section 2), the primitive cycles of all maps $T_S$ correspond bijectively to the simple directed cycles of $G$. For a cycle $c = (x_0, x_1, \dots, x_{\ell-1})$ of length $\ell$ with $a$ up-steps ($x_{i+1} = U(x_i)$) and $\ell - a$ down-steps ($x_{i+1} = D(x_i)$), Theorem 4.1(c) yields $3^a < 2^\ell$ and the exact product identity
$$\frac{2^\ell}{3^a} = \prod_{i=0}^{\ell-1} \left(1 + \frac{e_i}{c_i x_i}\right),$$
where $e_i = x_i \bmod 2 \in \{0, 1\}$, $c_i = 3$ on an up-step, and $c_i = 1$ on a down-step.

In Section 7, **Question 7.1** asks:
> "Does every cycle satisfy $2^\ell < 3^{a+1}$, that is, $a = \lfloor \ell \log_3 2 \rfloor$? This holds for cycles with a single run of steps up (Theorem 4.1(d)), for all cycles of length $\ell \le 30$, and for all $1{,}133{,}265{,}572$ cycles whose elements are all at most $160$; among the latter, the largest ratio $2^\ell / 3^a$ is $2.398$, for $\ell = 71$. If the answer is negative, what is the supremum of $2^\ell / 3^a$?"

---

## 2. Main Result

**Theorem.** *Question 7.1 has a negative answer: there exists a subset $S \subset \mathbb{N}$ and a primitive cycle $c = (x_0, x_1, \dots, x_{381})$ of $T_S$ of length $\ell = 382$ with $a = 240$ up-steps such that*
$$3^{241} < 2^{382}.$$
*In particular, $2^\ell / 3^a = 2^{382} / 3^{240} \approx 3.050403 > 3$ and $a = 240 = \lfloor 382 \log_3 2 \rfloor - 1 \neq \lfloor \ell \log_3 2 \rfloor$.*

---

## 3. Explicit Counterexample and Mechanism

### Why small cycles stay below $3$
By Theorem 4.1(c), even vertices contribute factor $1$ to $2^\ell/3^a$, odd up-vertices contribute $1 + 1/(3x)$, and odd down-vertices contribute $1 + 1/x$. Moreover, Theorem 4.1(d) bounds the ratio above by $\prod_j (p_j + 1)/(p_j - 1)$ over the local minima (up-run starting vertices) $p_j$ of the cycle. Consequently, exceeding $3$ requires multiple up-runs returning to small integers while accumulating many small odd down-steps ($7, 11, 13, 19, 25, 31, 37, 39, 43, 49, 61, 65, \dots$).

### Explicit 382-cycle
The complete 382-vertex simple cycle `CYCLE` is given verbatim in `verify.py`. It consists of $382$ pairwise distinct integers in $[2, 258{,}477{,}331{,}094]$ partitioned into $13$ alternating up-runs and down-runs, starting at
$$2 \xrightarrow{U} 3 \xrightarrow{U} 5 \xrightarrow{U} 8 \xrightarrow{U} 12 \xrightarrow{U} 18 \xrightarrow{U} 27 \xrightarrow{U} 41 \xrightarrow{U} \cdots \xrightarrow{U} 5394 \xrightarrow{D} 2697 \xrightarrow{D} \cdots \xrightarrow{D} 11 \xrightarrow{D} 6 \xrightarrow{U} 9 \xrightarrow{U} \cdots$$
and closing via
$$\cdots \xrightarrow{D} 97 \xrightarrow{D} 49 \xrightarrow{D} 25 \xrightarrow{D} 13 \xrightarrow{D} 7 \xrightarrow{D} 4 \xrightarrow{D} 2.$$
Its $13$ up-run starts (local minima) are
$$2,\; 6,\; 10,\; 16,\; 20,\; 29,\; 33,\; 38,\; 40,\; 42,\; 46,\; 51,\; 56.$$

### Exact verification
1. **Distinct positive vertices:** All $382$ entries satisfy $x_i \ge 2$ and are pairwise distinct.
2. **Valid up-down steps:** For every $i \in \{0, \dots, 381\}$ (indices modulo $382$), either $x_{i+1} = U(x_i) = \lfloor (3x_i + 1)/2 \rfloor$ or $x_{i+1} = D(x_i) = \lfloor (x_i + 1)/2 \rfloor$. Because $x_i \ge 2$, we always have $D(x_i) < x_i < U(x_i)$, so the step direction at each vertex is uniquely determined.
3. **Counts and exact inequality:** Exactly $a = 240$ steps are up-steps and $142$ are down-steps. Direct integer arithmetic gives:
   - $2^{382} = 9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704$,
   - $3^{241} = 9687725061507120312158495580550917796426619839523251513329086812944808568617534785161369767311066873140028406651043$,
   so $3^{241} < 2^{382}$ and $2^{382} / 3^{240} \approx 3.050403 > 3$.
4. **Primitive cycle of $T_S$:** Defining $S := \{x_i \mid x_{i+1} = U(x_i)\}$, pairwise distinctness ensures $T_S(x_i) = x_{i+1}$ for every $i$, so $T_S^k(2) = x_{k \bmod 382}$ for all $k \ge 0$, making $c$ a primitive cycle of $T_S$ of exact period $382$.

### Remark on the follow-up supremum question
The follow-up part of Question 7.1 asks for $\sup 2^\ell / 3^a$ over all cycles of $G$. Our explicit cycle establishes $\sup 2^\ell / 3^a \ge 2^{382}/3^{240} \approx 3.0504$ (and extending the greedy Kronecker-bridge construction yields still larger ratios, e.g., $\approx 3.72$ at $\ell = 12{,}913$). Determining whether $\sup 2^\ell / 3^a = \infty$ remains open.
