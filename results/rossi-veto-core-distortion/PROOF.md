# Exact Metric Distortion of the Rank Score Veto Core (`arXiv:2610.26535`)

We prove the **Rank Score Veto Core Distortion Conjecture** of M. August Rossi (*Regularizing the Veto Core*, `arXiv:2610.26535`, Abstract, Section 3.1 after Corollary 2, and Section 5): for every positional scoring vector $\mathbf{s} = (s_1, \dots, s_m)$ with $1 = s_1 \ge s_2 \ge \dots \ge s_m \ge 0$, the worst-case metric distortion of the $(\mathbf{p}^{\mathsf{unif}}, \mathbf{q}^{\mathbf{s}})$-veto core equals $1 + 2(\|\mathbf{s}\|_1 - s_m)$, matching Rossi's lower bound (Lemma 5) and showing that distortion is independent of the last-position score $s_m$.

---

## 1. Definitions and Main Theorem

Following Rossi (`arXiv:2610.26535`, Sections 2–3):

- Let $\mathcal{V}$ be a finite nonempty set of $n \ge 1$ voters and $\mathcal{C}$ a finite set of $m \ge 2$ candidates. Each voter $u \in \mathcal{V}$ submits a strict total order $\succ_u$ on $\mathcal{C}$, writing $x \succcurlyeq_u y$ for $x \succ_u y$ or $x = y$, and $\mathrm{pos}_u(c) \in \{1, \dots, m\}$ for the rank of $c$ on $u$'s ballot ($1$ = first place, $m$ = last place).
- A **scoring vector** $\mathbf{s} = (s_1, \dots, s_m) \in \mathbb{R}^m$ satisfies $1 = s_1 \ge s_2 \ge \dots \ge s_m \ge 0$. (Rossi's Definition 1 additionally requires $\mathbf{s} \in \mathbb{Q}_+^m$; our upper bound requires no rationality assumption and therefore applies to all real non-increasing scoring vectors as well.) Write
  $$S := \|\mathbf{s}\|_1 = \sum_{j=1}^m s_j \ge 1, \qquad T := S - s_m = \sum_{j=1}^{m-1} s_j \ge 1.$$
- The uniform voter weight vector is $\mathbf{p}^{\mathsf{unif}}(u) = 1/n$, and the normalized rank-score candidate weight vector is
  $$\mathbf{q}^{\mathbf{s}}(c) := \frac{1}{n S} \sum_{u \in \mathcal{V}} s_{\mathrm{pos}_u(c)}, \qquad \sum_{c \in \mathcal{C}} \mathbf{q}^{\mathbf{s}}(c) = 1.$$
- A candidate $a \in \mathcal{C}$ is **blocked** by a voter coalition $S' \subseteq \mathcal{V}$ if there exists a proper subset $\mathcal{D} \subsetneq \mathcal{C}$ such that $c \succ_u a$ for all $u \in S'$ and all $c \in \mathcal{D}$, and $|S'|/n > 1 - \mathbf{q}^{\mathbf{s}}(\mathcal{D})$. The **$(\mathbf{p}^{\mathsf{unif}}, \mathbf{q}^{\mathbf{s}})$-veto core** consists of all unblocked candidates.
- A pseudometric $d : (\mathcal{V} \cup \mathcal{C})^2 \to \mathbb{R}_{\ge 0}$ (symmetric, reflexive, satisfying the triangle inequality) is **consistent** with the profile if $d(u, x) < d(u, y) \implies x \succ_u y$ for all $u \in \mathcal{V}$ and $x, y \in \mathcal{C}$ (equivalently, $x \succcurlyeq_u y \implies d(u, x) \le d(u, y)$, with arbitrary tie-breaking at equal distances). The social cost of $c \in \mathcal{C}$ is $\mathrm{SC}_d(c) := \sum_{u \in \mathcal{V}} d(u, c)$.

**Theorem (Tight Upper Bound for the Rank Score Veto Core).** *Let $m \ge 2$, $n \ge 1$, and let $\mathbf{s} = (s_1, \dots, s_m) \in \mathbb{R}^m$ satisfy $1 = s_1 \ge s_2 \ge \dots \ge s_m \ge 0$. For every preference profile, every consistent pseudometric $d$, every candidate $a$ in the $(\mathbf{p}^{\mathsf{unif}}, \mathbf{q}^{\mathbf{s}})$-veto core, and every candidate $b \in \mathcal{C}$,*
$$\mathrm{SC}_d(a) \le \bigl(1 + 2(\|\mathbf{s}\|_1 - s_m)\bigr)\,\mathrm{SC}_d(b).$$

*Remark on tightness and edge cases.*
1. The multiplicative inequality handles $\mathrm{SC}_d(b) = 0$ directly without $0/0$ ambiguity: if $\mathrm{SC}_d(b) = 0$, then $\mathrm{SC}_d(a) = 0$ for every veto-core candidate $a$.
2. Combined with Rossi's Lemma 5, for every rational scoring vector (Rossi's Definition 1), the worst-case distortion is **attained** on a finite election and equals exactly $1 + 2T = 1 + 2(\|\mathbf{s}\|_1 - s_m)$. For real scoring vectors with irrational $T$, Lemma 5 with $n_2 = \lfloor n_1 T \rfloor$ as $n_1 \to \infty$ shows that $1 + 2T$ is exact as a supremum over finite elections.
3. Special cases recover all known tight values: $m = 2$ gives $3$; $s_m = 0$ gives $1 + 2\|\mathbf{s}\|_1$; and $s_1 = \dots = s_m = 1$ (proportional veto core) gives $2m - 1$.

---

## 2. Proof

Write $\delta := d(a, b) \ge 0$ and $\mathbf{q} := \mathbf{q}^{\mathbf{s}}$.

**Preliminary case: $\delta = 0$ (including $a = b$).** By the triangle inequality and symmetry, $|d(u, a) - d(u, b)| \le d(a, b) = 0$ for every $u \in \mathcal{V}$, so $\mathrm{SC}_d(a) = \mathrm{SC}_d(b) \le (1 + 2T)\,\mathrm{SC}_d(b)$ since $T \ge 0$ and $\mathrm{SC}_d(b) \ge 0$.

Assume henceforth that $\delta > 0$ (in particular $a \neq b$). Partition $\mathcal{V}$ into
$$A := \{u \in \mathcal{V} : a \succ_u b\}, \qquad B := \{u \in \mathcal{V} : b \succ_u a\}.$$
For each candidate $c \in \mathcal{C}$ and voter $u \in \mathcal{V}$, define:
- $N_a(u) := \{c \in \mathcal{C} : a \succcurlyeq_u c\}$ (note $a \in N_a(u)$),
- $\rho_c := \min(d(b, c), \delta) \in [0, \delta]$ (note $\rho_a = \delta$ and $\rho_b = 0$),
- $m_u := \min_{c \in N_a(u)} \rho_c \in [0, \delta]$,
- $M_u := \max_{e \succcurlyeq_u c} (\rho_e - \rho_c) \ge 0$ (nonnegative by taking $e = c$),
- $W_u := \sum_{c \in \mathcal{C}} s_{\mathrm{pos}_u(c)} \rho_c$.

### Step 1: Upper bound on $\mathrm{SC}_d(a)$

- If $u \in A$, then $a \succ_u b$, so consistency gives $d(u, a) \le d(u, b)$.
- If $u \in B$, then for every $c \in N_a(u)$ we have $a \succcurlyeq_u c$, so consistency and the triangle inequality give
  $$d(u, a) \le d(u, c) \le d(u, b) + d(b, c).$$
  Taking the minimum over $c \in N_a(u)$, and noting that $\min_{c \in N_a(u)} d(b, c) \le d(b, a) = \delta$ (as $a \in N_a(u)$), capping at $\delta$ does not change the minimum: $\min_{c \in N_a(u)} d(b, c) = \min_{c \in N_a(u)} \rho_c = m_u$. Thus $d(u, a) \le d(u, b) + m_u$.

Summing over all $u \in A \cup B = \mathcal{V}$ gives
$$\mathrm{SC}_d(a) \le \mathrm{SC}_d(b) + \sum_{u \in B} m_u. \tag{1}$$

### Step 2: Lower bound on $\mathrm{SC}_d(b)$

Let $u \in \mathcal{V}$ and $e \succcurlyeq_u c$. By consistency $d(u, e) \le d(u, c)$, so two applications of the triangle inequality yield
$$d(b, e) \le d(b, u) + d(u, e) \le d(b, u) + d(u, c) \le d(b, u) + d(u, b) + d(b, c) = 2 d(u, b) + d(b, c).$$
Because $x \mapsto \min(x, \delta)$ is non-decreasing and $1$-Lipschitz,
$$\rho_e - \rho_c \le \max\bigl(0, d(b, e) - d(b, c)\bigr) \le 2 d(u, b).$$
Taking the maximum over all pairs $e \succcurlyeq_u c$ gives $M_u \le 2 d(u, b)$, and summing over $u \in \mathcal{V}$ yields
$$\sum_{u \in \mathcal{V}} M_u \le 2\,\mathrm{SC}_d(b). \tag{2}$$

### Step 3: Veto core inequality via layer-cake integration

For every threshold $t \in [0, \delta)$, set
$$U_t := \{c \in \mathcal{C} : \rho_c > t\}, \qquad \mathcal{D}_t := \mathcal{C} \setminus U_t = \{c \in \mathcal{C} : \rho_c \le t\}, \qquad S_t := \{u \in \mathcal{V} : m_u > t\}.$$
Then:
- $b \in \mathcal{D}_t$ (since $\rho_b = 0 \le t$) and $a \notin \mathcal{D}_t$ (since $\rho_a = \delta > t$), so $\mathcal{D}_t$ is a nonempty proper subset of $\mathcal{C}$.
- $u \in S_t \iff \forall c \in N_a(u),\, \rho_c > t \iff N_a(u) \subseteq U_t$. In particular, $b \notin N_a(u)$ for every $u \in S_t$, so $S_t \subseteq B$.
- For every $u \in S_t$ and every $c \in \mathcal{D}_t$, we have $c \notin N_a(u)$ and hence $c \succ_u a$.

Because $a$ is unblocked in the $(\mathbf{p}^{\mathsf{unif}}, \mathbf{q})$-veto core,
$$\frac{|S_t|}{n} \le 1 - \mathbf{q}(\mathcal{D}_t) = \mathbf{q}(U_t) \qquad \forall t \in [0, \delta).$$
Integrating (equivalently, taking a finite telescoping sum over the sorted distinct values of $\{\rho_c : c \in \mathcal{C}\}$) over $t \in [0, \delta)$ and using $\int_0^\delta \mathbf{1}_{x > t}\,dt = x$ for every $x \in [0, \delta]$ gives
$$\frac{1}{n} \sum_{u \in B} m_u = \int_0^\delta \frac{|S_t|}{n}\,dt \le \int_0^\delta \mathbf{q}(U_t)\,dt = \sum_{c \in \mathcal{C}} \mathbf{q}(c)\,\rho_c = \frac{1}{n S} \sum_{u \in \mathcal{V}} W_u.$$
Multiplying by $nS > 0$ yields
$$S \sum_{u \in B} m_u \le \sum_{u \in \mathcal{V}} W_u. \tag{3}$$

### Step 4: Per-voter inequalities

Every quantity $\rho_c, m_u, M_u, W_u$ scales linearly with $\delta > 0$; normalizing by $\delta$, we assume without loss of generality that $\delta = 1$, so $\rho_c \in [0, 1]$, $\rho_a = 1$, and $\rho_b = 0$.

- **Case (A): $u \in A$ ($a \succ_u b$).** Since $\rho_b = 0$ and $\rho_c \le 1$ for all $c$,
  $$W_u = \sum_{c \neq b} s_{\mathrm{pos}_u(c)} \rho_c \le \sum_{c \neq b} s_{\mathrm{pos}_u(c)} = S - s_{\mathrm{pos}_u(b)} \le S - s_m = T,$$
  using monotonicity $s_{\mathrm{pos}_u(b)} \ge s_m$. Since $a \succ_u b$, we also have $M_u \ge \rho_a - \rho_b = 1$ (in fact $M_u = 1$). Because $T \ge 0$,
  $$W_u \le T M_u. \tag{4A}$$

- **Case (B): $u \in B$ ($b \succ_u a$).** Write $p := \mathrm{pos}_u(b)$, $P := \sum_{j=1}^{p-1} s_j$, and $M := M_u \in [0, 1]$.
  - Every candidate $c$ ranked strictly above $b$ ($c \succ_u b$) satisfies $\rho_c = \rho_c - \rho_b \le M$ as well as $\rho_c \le 1$, so $\rho_c \le \min(1, M)$.
  - Candidate $b$ has $\rho_b = 0$, and every candidate $c$ ranked strictly below $b$ has $\rho_c \le 1$.
  - Therefore
    $$W_u \le \min(1, M)\,P + \sum_{j=p+1}^m s_j = \min(1, M)\,P + (S - P - s_p).$$
  - Every candidate $c \in N_a(u)$ ($a \succcurlyeq_u c$) satisfies $1 - \rho_c = \rho_a - \rho_c \le M$, so $\rho_c \ge 1 - M$; since also $\rho_c \ge 0$, we obtain $m_u \ge \max(0, 1 - M)$.

  Note that $S - 1 = \sum_{j=2}^m s_j \ge 0$ (since $s_1 = 1$ and $s_j \ge 0$). We verify $W_u - (S - 1) m_u \le T M$ in two subcases:
  - **If $M \ge 1$** (i.e., $M = 1$): since $(S - 1) m_u \ge 0$ and $\min(1, M) = 1$,
    $$W_u - (S - 1) m_u \le W_u \le P + (S - P - s_p) = S - s_p \le S - s_m = T \le T M.$$
  - **If $0 \le M < 1$:** then $\min(1, M) = M$ and $\max(0, 1 - M) = 1 - M$, so
    $$W_u - (S - 1) m_u \le M P + (S - P - s_p) - (S - 1)(1 - M).$$
    Substituting $T = S - s_m$, the slack is
    $$\begin{aligned}
    T M - \bigl[M P + S - P - s_p - (S - 1)(1 - M)\bigr]
    &= (S - s_m)M - MP - S + P + s_p + S - SM - 1 + M \\
    &= M(1 - s_m - P) + P + s_p - 1.
    \end{aligned}$$
    - If $p = 1$, then $P = 0$ and $s_p = s_1 = 1$, so the slack equals $M(1 - s_m) \ge 0$ (since $M \ge 0$ and $s_m \le s_1 = 1$).
    - If $p \ge 2$, then $P = \sum_{j=1}^{p-1} s_j \ge s_1 = 1$, and rewriting the slack gives
      $$(P - 1)(1 - M) + (s_p - M s_m) \ge 0,$$
      since $P - 1 \ge 0$, $1 - M > 0$, and $s_p \ge s_m \ge M s_m \ge 0$.

  Hence in all cases,
  $$W_u - (S - 1) m_u \le T M_u. \tag{4B}$$

### Step 5: Combining the bounds

Subtract $(S - 1) \sum_{u \in B} m_u$ from (3) and apply (4A), (4B), and (2):
$$\sum_{u \in B} m_u = S \sum_{u \in B} m_u - (S - 1) \sum_{u \in B} m_u \le \sum_{u \in A} W_u + \sum_{u \in B} \bigl(W_u - (S - 1) m_u\bigr) \le T \sum_{u \in \mathcal{V}} M_u \le 2T\,\mathrm{SC}_d(b).$$
Substituting into (1) gives
$$\mathrm{SC}_d(a) \le \mathrm{SC}_d(b) + 2T\,\mathrm{SC}_d(b) = (1 + 2T)\,\mathrm{SC}_d(b). \qquad \blacksquare$$
