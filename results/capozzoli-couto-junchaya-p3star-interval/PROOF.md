# Disproof of Conjecture 1 (under ETH): $P_3^*$-interval on Tournaments is in Quasi-Polynomial Time and is NP-intermediate

**Target Conjecture:** Conjecture 1 of Idian C. Capozzoli, Yan S. Couto, and Enrique Junchaya, *Interval number for tournaments in $P_3$-convexity* (`arXiv:2609.22640v1`, Sep 2026, Section 5):

> **Conjecture 1:** *$P_3^*$-interval on Tournaments* — given a tournament $T$ and a positive integer $k$, decide whether $\mathrm{in}_{P_3^*}(T) \le k$ — is **NP-complete**.

**Main Result:**
We **disprove Conjecture 1 under the Exponential Time Hypothesis (ETH)**:

1. **Theorem 1 (Quasi-Polynomial Algorithm):** *$P_3^*$-interval on Tournaments* can be solved deterministically in quasi-polynomial time $n^{O(\log^3 n)} = 2^{O(\log^4 n)}$ on any $n$-vertex tournament $T$.
2. **Corollary 1 (NP-intermediateness under ETH):** Assuming ETH, *$P_3^*$-interval on Tournaments* is **not NP-complete**. Combined with its $\mathsf{W[2]}$-hardness and $f(k) n^{o(k)}$ ETH lower bound (Theorem 4.1 and Corollary 3 of Capozzoli–Couto–Junchaya), it is **NP-intermediate under ETH**, both on general tournaments and when restricted to **strong** tournaments.

---

## 1. Preliminaries and Exact Definitions

Following Capozzoli, Couto, and Junchaya (`arXiv:2609.22640v1`, Sections 1.1 and 4.2):

- A **tournament** $T = (V(T), A(T))$ is an orientation of a complete graph (no self-loops, and for every distinct $u, v \in V(T)$, exactly one of $u \to v$ or $v \to u$ belongs to $A(T)$). Write $N^+(v) = \{w \in V(T) : v \to w\}$ and $N^-(v) = \{u \in V(T) : u \to v\}$.
- In **distance-two convexity** ($P_3^*$-convexity), for any $S \subseteq V(T)$, $I_{P_3^*}(S)$ is the union of $S$ and all vertices lying on a shortest directed path of length $2$ between two vertices of $S$. By **Lemma 4** of the paper, on a tournament $T$, a directed path $u \to v \to w$ is shortest if and only if $w \to u \in A(T)$ (i.e., $u \to v \to w \to u$ is an oriented triangle), so:
  $$I_{P_3^*}(S) = S \cup \{v \in V(T) : \exists u, w \in S \text{ such that } u \to v \to w \to u \text{ is an oriented triangle}\}.$$
  Equivalently, for each arc $w \to u \in A(T)$, the set of *additional* vertices covered by the pair $\{u, w\}$ is $N^+(u) \cap N^-(w)$, and
  $$I_{P_3^*}(S) = S \cup \bigcup_{\substack{u, w \in S \\ w \to u \in A(T)}} \bigl(N^+(u) \cap N^-(w)\bigr).$$
- A set $S \subseteq V(T)$ is a **$P_3^*$-interval set** of $T$ if $I_{P_3^*}(S) = V(T)$, and $\mathrm{in}_{P_3^*}(T) = \min\{|S| : I_{P_3^*}(S) = V(T)\}$.
- Clearly $I_{P_3^*}$ is **monotone**: $S_1 \subseteq S_2 \implies I_{P_3^*}(S_1) \subseteq I_{P_3^*}(S_2)$.

---

## 2. Structural Band Decomposition Theorem

Let $T = (V, A)$ be a tournament on $n = |V|$ vertices, let $U \subseteq V$ be a nonempty subset of size $m = |U|$, and let $r \ge 6$ be an integer. Suppose $U$ satisfies the **low-coverage condition**:
$$\forall (w \to u) \in A(T), \qquad |N^+(u) \cap N^-(w) \cap U| < \frac{m}{r}. \tag{$\star$}$$

For every vertex $x \in V(T)$, define its **$U$-out-degree**:
$$f(x) := |N^+(x) \cap U| \in \{0, 1, \dots, m\}.$$

### Lemma A (Lipschitz Bound on Backward Arcs)
Under $(\star)$, for every arc $w \to u \in A(T)$:
$$f(u) - f(w) \le |N^+(u) \cap N^-(w) \cap U| < \frac{m}{r}.$$

**Proof.** Let $X = N^+(u) \cap U$ and $Y = N^+(w) \cap U$. For any $v \in X \setminus Y$, we have $v \in U$, $u \to v$, and $w \not\to v$. We have $v \ne u$ (irreflexivity) and $v \ne w$ (asymmetry, since $w \to u$ and $u \to v$). Because $T$ is a tournament and $w \not\to v$, it follows that $v \to w$, so $v \in N^+(u) \cap N^-(w) \cap U$ (this holds whether or not $u$ or $w$ lies in $U$). Hence $X \setminus Y \subseteq N^+(u) \cap N^-(w) \cap U$, and
$$f(u) - f(w) = |X| - |Y| \le |X \setminus Y| \le |N^+(u) \cap N^-(w) \cap U| < \frac{m}{r}. \qquad \square$$

Now partition the **entire** vertex set $V(T)$ into $r$ disjoint **bands** $C_1, C_2, \dots, C_r$:
$$C_i := \left\{x \in V(T) : \frac{r - i}{r} m < f(x) \le \frac{r - i + 1}{r} m\right\} \quad (1 \le i \le r - 1),$$
$$C_r := \left\{x \in V(T) : 0 \le f(x) \le \frac{1}{r} m\right\}.$$
For convenience, define $C_j := \emptyset$ for $j < 1$ or $j > r$, and write $C_{\le b} = \bigcup_{i \le b} C_i$, $C_{\ge a} = \bigcup_{i \ge a} C_i$.

### Lemma B (Forward Orientation Across Non-Adjacent Bands)
For all $1 \le i < j \le r$ with $j \ge i + 2$, every $x \in C_i$ and every $y \in C_j$ satisfy $x \to y \in A(T)$.

**Proof.** Since $j \le r$ and $j \ge i + 2$, we have $i \le r - 2 \le r - 1$, so $x \in C_i$ satisfies the strict lower bound $f(x) > \frac{r - i}{r} m$. Whether $j \le r - 1$ or $j = r$, $y \in C_j$ satisfies the weak upper bound $f(y) \le \frac{r - j + 1}{r} m \le \frac{r - i - 1}{r} m$. Therefore $f(x) - f(y) > \frac{m}{r}$. By Lemma A, $y \to x$ is impossible; since $x \ne y$ and $T$ is a tournament, $x \to y \in A(T)$. $\square$

### Lemma E (Local Triangle Radius $\le 2$)
Every oriented triangle $\{u, v, w\}$ in $T$ with $v \in C_i$ satisfies $u, w \in C_{i-2} \cup C_{i-1} \cup C_i \cup C_{i+1} \cup C_{i+2}$.

**Proof.** Suppose for contradiction that $u \in C_j$ with $j \le i - 3$. Since $i \ge j + 3 \ge j + 2$, Lemma B gives $u \to v$, so the oriented triangle is $u \to v \to w \to u$.
- Since $w \to u$ and $u \in C_j$, Lemma B forces $w \in C_{\le j+1} \subseteq C_{\le i-2}$.
- Since $v \to w$ and $v \in C_i$, Lemma B forces $w \in C_{\ge i-1}$.
Since $C_{\le i-2} \cap C_{\ge i-1} = \emptyset$, this is a contradiction. The case $j \ge i + 3$ is symmetric ($v \to u \implies$ cycle $v \to u \to w \to v$, forcing $w \in C_{\ge j-1} \cap C_{\le i+1} = \emptyset$). By symmetry of $u$ and $w$, both lie in $C_{i-2} \cup \dots \cup C_{i+2}$. $\square$

### Lemma C (4-Band Decoupling Lemma)
Fix any $t \in \{2, \dots, r - 4\}$ and define:
$$L_t := \bigcup_{i=1}^{t-1} C_i, \qquad W_t := C_t \cup C_{t+1} \cup C_{t+2} \cup C_{t+3}, \qquad R_t := \bigcup_{i=t+4}^{r} C_i.$$
Then:
1. Every oriented triangle in $T$ containing a vertex of $L_t \cup C_t \cup C_{t+1}$ lies entirely in $L_t \cup W_t$.
2. Every oriented triangle in $T$ containing a vertex of $C_{t+2} \cup C_{t+3} \cup R_t$ lies entirely in $W_t \cup R_t$.

**Proof.** Any vertex of $L_t \cup C_t \cup C_{t+1} = C_{\le t+1}$ and any vertex of $R_t = C_{\ge t+4}$ have band indices differing by at least $(t + 4) - (t + 1) = 3$, so by Lemma E no oriented triangle can contain both. Claim (2) is symmetric ($C_{\ge t+2}$ vs. $C_{\le t-1}$). $\square$

### Lemma D (Empty-Band Gap Bound $\le 3$)
Assume $(\star)$ and $\frac{2m}{r} > 1$. Then:
1. $U \cap (C_1 \cup C_2) \ne \emptyset$ and $U \cap (C_{r-1} \cup C_r) \ne \emptyset$.
2. If $1 \le i_1 < i_2 \le r$ satisfy $U \cap C_{i_1} \ne \emptyset$, $U \cap C_{i_2} \ne \emptyset$, and $U \cap C_i = \emptyset$ for all $i_1 < i < i_2$, then $i_2 - i_1 - 1 \le 3$.
3. Consequently, among any $4$ consecutive bands $C_j, C_{j+1}, C_{j+2}, C_{j+3}$ ($1 \le j \le r - 3$), at least one band intersects $U$ (and hence (2) holds even without requiring $U \cap C_{i_1}, U \cap C_{i_2}$ to be occupied).

**Proof.** We first establish two symmetric claims for any partition $U = A \sqcup B$ with $A \to B$:

- **Claim 1:** If $B \ne \emptyset$ with $s = |B|$, then $\max_{w \in B} f(w) > s - \frac{2m}{r}$.
  *Proof:* Since $A \to B$, every $w \in B$ has $f(w) = d^+_{T[B]}(w)$. Let $w^* \in B$ maximize $d^+_{T[B]}(w)$, let $M_B = d^+_{T[B]}(w^*)$, $O = N^+_{T[B]}(w^*)$, and $I = N^-_{T[B]}(w^*)$, so $|O| = M_B$ and $|I| = s - 1 - M_B$. If $|I| = 0$, then $M_B = s - 1 > s - \frac{2m}{r}$ since $\frac{2m}{r} > 1$. Otherwise $|I| \ge 1$; for every $y \in I$, we have $y \to w^*$ and
  $$M_B \ge d^+_{T[B]}(y) = 1 + d^+_{T[I]}(y) + |N^+_{T[B]}(y) \cap O| = 1 + d^+_{T[I]}(y) + M_B - |N^+_{T[B]}(w^*) \cap N^-_{T[B]}(y)|.$$
  By $(\star)$ and $B \subseteq U$, $|N^+_{T[B]}(w^*) \cap N^-_{T[B]}(y)| \le |N^+(w^*) \cap N^-(y) \cap U| < \frac{m}{r}$, so $d^+_{T[I]}(y) < \frac{m}{r} - 1$ for all $y \in I$. Summing over $y \in I$ gives $\frac{|I|(|I|-1)}{2} < |I|(\frac{m}{r} - 1)$. Dividing by $|I| \ge 1$ yields $|I| < \frac{2m}{r} - 1$, hence $M_B = s - 1 - |I| > s - \frac{2m}{r}$.

- **Claim 2:** If $A \ne \emptyset$ with $s = |B| = m - |A|$, then $\min_{u \in A} f(u) < s + \frac{2m}{r}$.
  *Proof:* Since $A \to B$, every $u \in A$ has $f(u) = s + d^+_{T[A]}(u)$. Let $u^* \in A$ minimize $d^+_{T[A]}(u)$ (equivalently maximize $d^-_{T[A]}(u)$), let $m_A = d^+_{T[A]}(u^*)$, $O_A = N^+_{T[A]}(u^*)$, and $I_A = N^-_{T[A]}(u^*)$. If $m_A = 0$, then $f(u^*) = s < s + \frac{2m}{r}$. Otherwise $m_A \ge 1$; for every $z \in O_A$, we have $u^* \to z$ and
  $$|I_A| \ge d^-_{T[A]}(z) = 1 + d^-_{T[O_A]}(z) + |I_A| - |N^+_{T[A]}(z) \cap N^-_{T[A]}(u^*)| > 1 + d^-_{T[O_A]}(z) + |I_A| - \frac{m}{r},$$
  so $d^-_{T[O_A]}(z) < \frac{m}{r} - 1$ for all $z \in O_A$. Summing over $z \in O_A$ gives $\frac{m_A(m_A - 1)}{2} < m_A(\frac{m}{r} - 1)$, whence $m_A < \frac{2m}{r} - 1 < \frac{2m}{r}$, and $f(u^*) = s + m_A < s + \frac{2m}{r}$.

Now deduce (1)–(3):
- **(1):** Taking $A = \emptyset, B = U$ ($s = m$) in Claim 1 gives $\max_{w \in U} f(w) > \frac{r - 2}{r} m$, so the maximizer lies in $C_1 \cup C_2$. Taking $A = U, B = \emptyset$ ($s = 0$) in Claim 2 gives $\min_{u \in U} f(u) < \frac{2m}{r}$, so the minimizer lies in $C_{r-1} \cup C_r$.
- **(2):** Let $g = i_2 - i_1 - 1$. If $g = 0$, the claim is trivial. Otherwise $g \ge 1$, so $i_2 \ge i_1 + 2$ and $i_1 \le r - 2$. Set $A = U \cap C_{\le i_1} \ne \emptyset$ and $B = U \cap C_{\ge i_2} \ne \emptyset$. Since $U \cap C_i = \emptyset$ for $i_1 < i < i_2$, $U = A \sqcup B$, and Lemma B gives $A \to B$. By Claims 1 and 2, there exist $u^* \in A$ and $w^* \in B$ with $f(u^*) - f(w^*) < (s + \frac{2m}{r}) - (s - \frac{2m}{r}) = \frac{4m}{r}$. On the other hand, $u^* \in C_{\le i_1}$ ($i_1 \le r - 2$) gives $f(u^*) > \frac{r - i_1}{r} m$, and $w^* \in C_{\ge i_2}$ gives $f(w^*) \le \frac{r - i_2 + 1}{r} m$, so $f(u^*) - f(w^*) > \frac{g m}{r}$. Thus $g < 4$, i.e., $g \le 3$.
- **(3):** Suppose $C_j, C_{j+1}, C_{j+2}, C_{j+3}$ ($1 \le j \le r - 3$) were all disjoint from $U$. If $j = 1$ or $j = r - 3$, this contradicts (1). If $2 \le j \le r - 4$, then by (1) both $C_{\le j-1}$ (which contains $C_1$) and $C_{\ge j+4}$ (which contains $C_r$) — wait: for $j = 2$, $C_2 \cap U = \emptyset$ and $U \cap (C_1 \cup C_2) \ne \emptyset$ force $U \cap C_1 \ne \emptyset$; symmetrically for $j = r - 4$, $U \cap C_r \ne \emptyset$ — so in every case $2 \le j \le r - 4$, there exist maximal $i_1 < j$ and minimal $i_2 > j + 3$ with $U \cap C_{i_1} \ne \emptyset$ and $U \cap C_{i_2} \ne \emptyset$, giving an empty gap $i_2 - i_1 - 1 \ge 4$, contradicting (2). $\square$

---

## 3. The Quasi-Polynomial Algorithm

We solve the self-contained generalized subproblem:

> **`Solve(T, D, F, k)`**
> **Input:** An $n$-vertex tournament $T = (V, A)$, a demand set $D \subseteq V$, a fixed pre-selected set $F \subseteq V$, and an integer budget $k \ge 0$.
> **Question:** Does there exist $S \subseteq V$ with $|S| \le k$ such that $D \subseteq I_{P_3^*}(S \cup F)$?

The original problem *$P_3^*$-interval on Tournaments* on $(T, k)$ is `Solve(T, V(T), ∅, k)`.

### Algorithm Description

Let $\ell := \lfloor \log_2 n \rfloor + 1$ (for $n \ge 1$, so $2^\ell > n$ and $\ell \ge \ln n$). For $n \le 2$, decide directly in $O(1)$ time. Assume $n \ge 3$ (so $\ell \ge 2$), and set $K_0 := 8000 \ell$.

0. **Trivial Budget Guard ($k \ge n$):**
   Return **YES** immediately (witnessed by $S = V(T)$).

1. **Base Case ($k \le K_0$):**
   Enumerate all subsets $S \subseteq V$ of size $|S| \le k$. If any satisfies $D \subseteq I_{P_3^*}(S \cup F)$, return **YES**; otherwise return **NO**.

2. **Multiplicative Greedy Preprocessing ($K_0 < k < n$):**
   Set
   $$r := \left\lfloor \frac{k}{40 \ell} \right\rfloor.$$
   (Since $k > 8000 \ell$, we have $r \ge 200$, $r \le \frac{k}{40 \ell}$, and $r > \frac{k}{41 \ell}$.)
   Initialize $S_{\text{greedy}} \leftarrow \emptyset$ and $U \leftarrow D \setminus I_{P_3^*}(F)$.
   While **$U \ne \emptyset$** and there exists an arc $w \to u \in A(T)$ such that $|N^+(u) \cap N^-(w) \cap U| \cdot r \ge |U|$:
   - $S_{\text{greedy}} \leftarrow S_{\text{greedy}} \cup \{u, w\}$,
   - $U \leftarrow U \setminus \bigl(\{u, w\} \cup (N^+(u) \cap N^-(w))\bigr)$.

   If $|S_{\text{greedy}}| + |U| \le k$, return **YES** immediately.

3. **Band Partition and Recursive Branching:**
   Let $m := |U|$. Compute $f(x) = |N^+(x) \cap U|$ for all $x \in V(T)$ and construct the $r$ bands $C_1, \dots, C_r$ using exact integer cross-multiplied comparisons $(r - i) m < f(x) \cdot r \le (r - i + 1) m$.
   Define the disjoint $4$-band window starting indices:
   $$t_q := \lceil r/3 \rceil + 4q \qquad \text{for } q = 0, 1, \dots, Q - 1,$$
   where $Q$ is the largest integer such that $t_{Q-1} \le \lfloor 2r/3 \rfloor - 4$.
   Set:
   $$s_{\max} := \left\lfloor \frac{15 k}{r} \right\rfloor, \qquad \delta := \left\lceil \frac{r}{30} \right\rceil.$$
   For each $q \in \{0, \dots, Q - 1\}$ (with $t = t_q$, $W_t = C_t \cup C_{t+1} \cup C_{t+2} \cup C_{t+3}$):
   - Set $D_L := D \cap (L_t \cup C_t \cup C_{t+1})$ and $D_R := D \cap (C_{t+2} \cup C_{t+3} \cup R_t)$.
   - For every subset $S_W \subseteq W_t$ with $|S_W| \le s_{\max}$, and every pair of integers $k_L, k_R \ge 0$ satisfying
     $$k_L + |S_W| + k_R \le k, \qquad k_L \le k - \delta, \qquad k_R \le k - \delta,$$
     recursively call `Solve(T, D_L, F ∪ S_W, k_L)` and `Solve(T, D_R, F ∪ S_W, k_R)`. If both return **YES**, return **YES**.

   If no branch returns YES, return **NO**.

---

## 4. Proof of Correctness

We prove by strong induction on $k$ that `Solve(T, D, F, k)` returns **YES** if and only if there exists $S \subseteq V$ with $|S| \le k$ and $D \subseteq I_{P_3^*}(S \cup F)$.

### Trivial & Base Cases ($k \ge n$ or $k \le K_0$)
If $k \ge n$, $S = V(T)$ has $|S| = n \le k$ and $D \subseteq V(T) \subseteq I_{P_3^*}(V(T) \cup F)$. If $k \le K_0$, exhaustive enumeration is exact by definition.

### Soundness (Algorithm returns YES $\implies$ valid $S$ exists)
- **Early YES in Step 2:** Set $S := S_{\text{greedy}} \cup U \subseteq V$. Then $|S| \le |S_{\text{greedy}}| + |U| \le k$. Every $v \in D$ either lies in $I_{P_3^*}(F)$, or was removed from $U$ in some greedy iteration (hence lies in $\{u, w\} \cup (N^+(u) \cap N^-(w)) \subseteq I_{P_3^*}(S_{\text{greedy}})$), or remains in $U \subseteq S$. By monotonicity of $I_{P_3^*}$, $D \subseteq I_{P_3^*}(S \cup F)$.
- **YES in Step 3:** By the inductive hypothesis (since $k_L, k_R \le k - \delta < k$), there exist $S_1, S_2 \subseteq V$ with $|S_1| \le k_L$, $|S_2| \le k_R$, $D_L \subseteq I_{P_3^*}(S_1 \cup S_W \cup F)$, and $D_R \subseteq I_{P_3^*}(S_2 \cup S_W \cup F)$. Setting $S := S_1 \cup S_W \cup S_2 \subseteq V$ gives $|S| \le k_L + |S_W| + k_R \le k$, and by monotonicity of $I_{P_3^*}$, $D = D_L \cup D_R \subseteq I_{P_3^*}(S \cup F)$.

### Completeness (Valid $S^*$ exists $\implies$ Algorithm returns YES)
Suppose $S^* \subseteq V$ satisfies $|S^*| \le k$ and $D \subseteq I_{P_3^*}(S^* \cup F)$, with $K_0 < k < n$, and assume Step 2 did not already return YES.

1. **Termination of greedy loop, lower bound on $m = |U|$, and validity of Lemmas A–E:**
   Every iteration of Step 2 strictly decreases $|U|$ (since $U \ne \emptyset$ and $|N^+(u) \cap N^-(w) \cap U| \ge \lceil |U|/r \rceil \ge 1$), multiplying $|U|$ by at most $(1 - 1/r)$. Since $(1 - 1/r)^r < 1/2$ for all $r \ge 1$ (equivalently $2(r - 1)^r < r^r$, as $(1 + \frac{1}{r-1})^r > 1 + \frac{r}{r-1} > 2$ for $r \ge 2$), every $r$ iterations strictly halve $|U|$. Starting from $|U| \le n < 2^\ell$, after $r \ell$ iterations we would have $|U| < 2^\ell \cdot 2^{-\ell} = 1$, forcing $U = \emptyset$. Thus at most $r \ell$ iterations occur, giving
   $$|S_{\text{greedy}}| \le 2 r \ell \le \frac{k}{20} < \frac{k}{10}$$
   (using $r \le \frac{k}{40 \ell}$). Because Step 2 did not return YES, $|S_{\text{greedy}}| + m > k$, so
   $$m = |U| > \frac{9}{10} k, \qquad \frac{m}{r} > \frac{9k/10}{k/(40 \ell)} = 36 \ell \ge 72 > 1.$$
   Because the greedy loop terminated with $m > 0$, $(\star)$ holds for $U$ and $r$, and $\frac{2m}{r} > 144 > 1$. Hence Lemmas A, B, C, D, and E all apply to the bands $C_1, \dots, C_r$.

2. **Existence of a light window $W_{t_{q^*}}$:**
   Count the pairwise disjoint $4$-band windows $W_{t_0}, \dots, W_{t_{Q-1}}$:
   $$\lfloor 2r/3 \rfloor - 4 - \lceil r/3 \rceil \ge \left(\frac{2r}{3} - \frac{2}{3}\right) - 4 - \left(\frac{r}{3} + \frac{2}{3}\right) = \frac{r - 16}{3},$$
   so
   $$Q = \left\lfloor \frac{\lfloor 2r/3 \rfloor - 4 - \lceil r/3 \rceil}{4} \right\rfloor + 1 > \frac{r - 16}{12} \ge \frac{23}{300} r > \frac{r}{15} \qquad (\text{since } r \ge 200).$$
   By pigeonhole over the pairwise disjoint windows $W_{t_0}, \dots, W_{t_{Q-1}}$,
   $$\sum_{q=0}^{Q-1} |S^* \cap W_{t_q}| \le |S^*| \le k \implies \exists q^* \in \{0, \dots, Q - 1\} \text{ with } |S^* \cap W_{t_{q^*}}| \le \left\lfloor \frac{k}{Q} \right\rfloor \le \left\lfloor \frac{15 k}{r} \right\rfloor = s_{\max}.$$

3. **Lower bounds on $|S^* \cap L_t|$ and $|S^* \cap R_t|$ (where $t = t_{q^*}$):**
   Take any $v \in U \cap C_i$. Since $U \subseteq D \setminus I_{P_3^*}(F)$ and $D \subseteq I_{P_3^*}(S^* \cup F)$, either $v \in S^*$ or $v$ lies in an oriented triangle $\{u, v, w\}$ with $u, w \in S^* \cup F$. In the latter case, $u$ and $w$ cannot both lie in $F$ (as $v \notin I_{P_3^*}(F)$), so at least one of $u, w$ lies in $S^*$. By Lemma E, both $u$ and $w$ lie in $C_{i-2} \cup \dots \cup C_{i+2}$. Therefore:
   $$U \cap C_i \ne \emptyset \implies S^* \cap (C_{i-2} \cup C_{i-1} \cup C_i \cup C_{i+1} \cup C_{i+2}) \ne \emptyset.$$
   Take $\lfloor (t - 1)/8 \rfloor$ disjoint full blocks of $8$ consecutive bands $C_{8b+1}, \dots, C_{8b+8}$ inside $L_t = C_1 \cup \dots \cup C_{t-1}$ ($0 \le b < \lfloor (t-1)/8 \rfloor$). In each block, the middle $4$ bands $C_{8b+3}, \dots, C_{8b+6}$ contain at least one band $C_i$ intersecting $U$ by Lemma D(3), so $S^*$ contains at least one vertex in $C_{i-2} \cup \dots \cup C_{i+2} \subseteq C_{8b+1} \cup \dots \cup C_{8b+8}$. Thus, using $t \ge \lceil r/3 \rceil$ and $r \ge 200$:
   $$|S^* \cap L_t| \ge \left\lfloor \frac{t - 1}{8} \right\rfloor \ge \left\lfloor \frac{r/3 - 1}{8} \right\rfloor > \frac{r - 27}{24} \ge \frac{173}{4800} r > \frac{r}{30},$$
   so $|S^* \cap L_t| \ge \lceil r/30 \rceil = \delta$.
   Symmetrically, $R_t = C_{t+4} \cup \dots \cup C_r$ contains $r - t - 3 \ge \frac{r}{3} + 1$ bands, giving $\lfloor (r - t - 3)/8 \rfloor > \frac{r - 21}{24} > \frac{r}{30}$, so $|S^* \cap R_t| \ge \delta$.

4. **Decoupling of $S^*$ at $t = t_{q^*}$:**
   Set $S_L := S^* \cap L_t$, $S_W := S^* \cap W_t$, $S_R := S^* \cap R_t$, and $k_L := |S_L|$, $k_R := |S_R|$.
   - $|S_W| \le s_{\max}$, $k_L + |S_W| + k_R = |S^*| \le k$, and $k_L, k_R \le k - \delta$.
   - Take any $v \in D_L = D \cap (L_t \cup C_t \cup C_{t+1})$. Since $v \in I_{P_3^*}(S^* \cup F)$, either $v \in S^* \cup F$ (and $v \notin R_t \implies v \in S_L \cup S_W \cup F$), or $v$ lies in an oriented triangle $\{u, v, w\}$ with $u, w \in S^* \cup F$. By Lemma C(1), neither $u$ nor $w$ can lie in $R_t$ (even if in $F \cap R_t$), so $u, w \in S_L \cup S_W \cup F$, giving $v \in I_{P_3^*}(S_L \cup S_W \cup F)$. Thus $D_L \subseteq I_{P_3^*}(S_L \cup S_W \cup F)$.
   - Symmetrically, by Lemma C(2), $D_R \subseteq I_{P_3^*}(S_R \cup S_W \cup F)$.

   Hence the branch $(q^*, S_W, k_L, k_R)$ is explored by Step 3, and by the inductive hypothesis both recursive calls return **YES**, so `Solve(T, D, F, k)` returns **YES**. $\square$

---

## 5. Running Time Analysis and Disproof of Conjecture 1

For fixed $n \ge 3$, define $\tau(k)$ to be the maximum worst-case running time of `Solve(T, D, F, k')` over all $n$-vertex tournaments $T$, $D, F \subseteq V(T)$, and budgets $k' \le k$.

- **Base case ($k \le K_0 = 8000 \ell$):**
  Checking each subset takes $O(n^3)$ time, and there are at most $(n + 1)^{K_0}$ subsets, so
  $$\tau(K_0) \le O(n^3) \cdot (n + 1)^{8000 \ell} = 2^{O(\log^2 n)}.$$

- **Recursive step ($K_0 < k < n$):**
  Steps 2 and 3 (greedy loop and band construction) run in $O(n^4)$ time, and each enumerated branch performs $O(n^2)$ setup work before making two recursive calls. Since $r > \frac{k}{41 \ell}$, we have
  $$s_{\max} = \left\lfloor \frac{15 k}{r} \right\rfloor \le 615 \ell, \qquad \delta = \left\lceil \frac{r}{30} \right\rceil \ge \frac{k}{1230 \ell}.$$
  The number of branches $(q, S_W, k_L, k_R)$ is at most
  $$B \le Q \cdot (n + 1)^{s_{\max}} \cdot (k + 1)^2 \le n (n + 1)^2 (n + 1)^{615 \ell} = 2^{O(\log^2 n)}.$$
  Each branch makes two recursive calls with budgets at most $k' \le k - \delta \le \lfloor k(1 - \frac{1}{1230 \ell}) \rfloor$, so by monotonicity of $\tau$:
  $$\tau(k) \le O(n^4) + B \cdot \Bigl(O(n^2) + 2 \, \tau\!\Bigl(\Bigl\lfloor k \Bigl(1 - \frac{1}{1230 \ell}\Bigr) \Bigr\rfloor\Bigr)\Bigr).$$

- **Recursion depth and total time:**
  Starting from $k < n < 2^\ell$, after $h$ levels the budget is at most $n \cdot e^{-h/(1230 \ell)}$. For $h = \lceil 1230 \ell^2 \rceil = O(\log^2 n)$, this is at most $n e^{-\ell} < 1 < K_0$. Unrolling the recurrence to depth $h$ yields:
  $$\tau(n) \le (2 B)^h \cdot \bigl(O(n^4) + \tau(K_0)\bigr) = \bigl(2^{O(\log^2 n)}\bigr)^{O(\log^2 n)} = 2^{O(\log^4 n)} = n^{O(\log^3 n)}.$$
  (If the input budget $k \ge n$, Step 0 exits immediately after reading the input.)

### Corollary 1 (Disproof of Conjecture 1 under ETH)
1. **Not NP-complete under ETH:** Suppose *$P_3^*$-interval on Tournaments* were $\mathsf{NP}$-complete, so 3-SAT reduces to it in polynomial time, mapping any 3-SAT formula on $v$ variables and $m$ clauses to an instance $(T, k)$ with $|V(T)| = O((v + m)^c)$ for a constant $c \ge 1$. By the Sparsification Lemma (Impagliazzo–Paturi–Zane, 2001), for every $\varepsilon > 0$, any 3-SAT formula on $v$ variables reduces to at most $2^{\varepsilon v}$ 3-SAT formulas each with $m = O_\varepsilon(v)$ clauses. Running the reduction and `Solve` on each sparse formula decides the original 3-SAT instance in time
   $$2^{\varepsilon v} \cdot 2^{O(\log^4(O_\varepsilon(v)^c))} = 2^{\varepsilon v + o(v)},$$
   which holds for every $\varepsilon > 0$ and therefore decides 3-SAT in $2^{o(v)}$ time, falsifying ETH.
2. **NP-intermediate under ETH (general and strong tournaments):**
   - Membership in $\mathsf{NP}$ is immediate ($I_{P_3^*}(S) = V(T)$ is verifiable in $O(n^3)$ time).
   - Not in $\mathsf{P}$ under ETH follows directly from Corollary 3 of Capozzoli–Couto–Junchaya (no $f(k) n^{o(k)}$ algorithm under ETH).
   - In Theorem 4.1 of Capozzoli–Couto–Junchaya, for every nonempty tournament $T$, the constructed tournament $T'$ on $V(T_1) \cup V(T_2) \cup \{x, y, z\}$ contains the directed $3$-cycles $x \to u_1 \to u_2 \to x$ (for every $u \in V(T)$) and $x \to y \to z \to x$, all sharing $x$ and covering $V(T')$. Hence $T'$ is always strongly connected, so **both** *$P_3^*$-interval on Tournaments* and *$P_3^*$-interval on Strong Tournaments* are **NP-intermediate under ETH**. $\square$
