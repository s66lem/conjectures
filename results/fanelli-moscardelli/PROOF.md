# Disproof of the Fanelli–Moscardelli Stability Threshold Conjecture (ECAI 2025)

**Conjecture:** A. Fanelli and L. Moscardelli, *Approximately Stable Matching* (ECAI 2025, Section 5, `doi:10.3233/FAIA251234`; formalized open in `google-deepmind/formal-conjectures`, `FormalConjectures/Paper/ApproximatelyStableMatching.lean` as `FanelliMoscardelli.stability_threshold_tight`, issue #7848).

> **Conjecture (`stability_threshold_tight`):** There exists $N_0 \ge 3$ such that for every $N \ge N_0$,
> $$K(N) = \lceil N/2 \rceil = \lfloor (N + 1)/2 \rfloor.$$

**Main Result (Disproof):**
> **Theorem.** *For every integer $m \ge 3$ and $N = 2m + 1$, every complete strict preference profile on $N$ agents admits an $m$-stable matching. Consequently,*
> $$K(2m + 1) \le m < m + 1 = \lceil (2m + 1)/2 \rceil \qquad \text{for every } m \ge 3,$$
> *and `stability_threshold_tight` is **false**.*

The hypothesis $m \ge 3$ is sharp ($K(5) = 3$) and is used only in Section 7 ($|\mathrm{out}(z)| = m - 2 \ge 1$). Combined with DRAT-checked SAT upper bounds and explicit lower-bound witnesses, the exact threshold satisfies $K(7) = 3$, $K(8) = 3$, $K(9) = 4$, and $K(11) = 5$ (each strictly below $\lceil N/2 \rceil$). The proof is constructive and independently verified by [verify.py](verify.py).

---

## 0. Definitions and Stability Criterion

Following `FormalConjecturesForMathlib/Combinatorics/Roommates.lean` and Fanelli–Moscardelli (Section 2):
- Let $V$ be a set of $N = 2m + 1$ agents ($m \ge 3$). Each agent $i \in V$ has a strict 1-based ranking $\mathrm{rank}_i : V \to \{1, \dots, N\}$ (a bijection) with $\mathrm{rank}_i(i) = N$.
- A *matching* $M$ is an involution on $V$; fixed points ($M(i) = i$) are *single*. Write $\rho_i := \mathrm{rank}_i(M(i))$ (so $\rho_i = N$ if $i$ is single, and $\rho_i \le 2m$ if $i$ is matched).
- A pair $\{i, j\}$ ($i \ne j$, $M(i) \ne j$) **$k$-blocks** $M$ if
  $$\mathrm{rank}_i(j) + k \le \rho_i \quad \text{and} \quad \mathrm{rank}_j(i) + k \le \rho_j.$$
- $M$ is **$k$-stable** if it has no $k$-blocking pair, and $K(N)$ is the least positive integer $k$ such that every complete profile on $N$ agents admits a $k$-stable matching.

For each $v \in V$:
- $T_v := \{u \in V : \mathrm{rank}_v(u) \le m\}$ (note $|T_v| = m$ and $v \notin T_v$);
- $G = (V, E(G))$ is the **mutual-top-$m$ graph**: $uv \in E(G) \iff u \in T_v \text{ and } v \in T_u$, with $N(v) := \{u : uv \in E(G)\}$;
- $x_v \in V$ is $v$'s $(m+1)$-th choice ($\mathrm{rank}_v(x_v) = m + 1$), and $f(v) \in V$ is $v$'s first choice ($\mathrm{rank}_v(f(v)) = 1$).

For a matching $M$ with a single unmatched agent $u$, a matched agent $i \ne u$ is **content w.r.t. $j$** if $\rho_i \le \mathrm{rank}_i(j) + m - 1$. If $\rho_i \le m$ (e.g., $i$ is matched along a $G$-edge), then $i$ is content w.r.t. every agent (*fully content*).

**Lemma 1 (Stability criterion for near-perfect matchings).** *A matching $M$ on $N = 2m+1$ agents with exactly one single agent $u$ is $m$-stable if and only if:*
- **(a)** *every $G$-edge $\{i, j\} \notin M$ has an endpoint $i \ne u$ that is content w.r.t. $j$; and*
- **(b)** *$\rho_{x_u} \le \mathrm{rank}_{x_u}(u) + m - 1$ (which holds automatically whenever $\mathrm{rank}_{x_u}(u) \ge m + 1$, since $\rho_{x_u} \le 2m$).*

*Proof.* If $i, j$ are both matched, $\rho_i, \rho_j \le 2m$, so $\{i, j\}$ $m$-blocking forces $\mathrm{rank}_i(j) \le m$ and $\mathrm{rank}_j(i) \le m$, i.e., $\{i, j\} \in E(G)$; such an edge $m$-blocks iff neither endpoint is content w.r.t. the other. For $\{u, j\}$ with $j \ne u$, $u$'s side holds iff $\mathrm{rank}_u(j) + m \le 2m + 1 \iff \mathrm{rank}_u(j) \le m + 1$. If $\mathrm{rank}_u(j) \le m$ and $u \notin T_j$, then $\mathrm{rank}_j(u) + m \ge 2m + 1 > \rho_j$, so $\{u, j\}$ cannot block; if $u \in T_j$, then $\{u, j\} \in E(G)$ and non-blocking is exactly $j$ being content w.r.t. $u$ (condition (a)). If $\mathrm{rank}_u(j) = m + 1$, then $j = x_u$ and non-blocking is exactly condition (b). $\square$

---

## 1. Reduction to the Residual Case

Let $M_0$ be any maximal matching of $G$, and let $W := V \setminus V(M_0)$ be its uncovered set ($|W|$ is odd, hence $|W| \ge 1$). Extending $M_0$ by leaving one agent $u \in W$ single and pairing $W \setminus \{u\}$ always satisfies Lemma 1(a): every $G$-edge not in $M$ has an endpoint $i \in V(M_0)$ with $\rho_i \le m$.

Condition (b) can fail only if $x_u \in W$ (otherwise $x_u \in V(M_0)$ has $\rho_{x_u} \le m$), $r_u := \mathrm{rank}_{x_u}(u) \le m$, and $x_u$'s partner $v \in W \setminus \{u, x_u\}$ satisfies $\mathrm{rank}_{x_u}(v) \ge r_u + m$. Note that if $|W| = 1$, then $x_u \notin W$ (since $\mathrm{rank}_u(u) = N \ne m + 1$), so $M_0$ is already $m$-stable.

Suppose no choice of $u \in W$ and pairing of $W \setminus \{u\}$ is $m$-stable. Then for every $u \in W$: $x_u \in W \setminus \{u\}$, $r_u \le m$, and every $v \in W \setminus \{u, x_u\}$ satisfies $\mathrm{rank}_{x_u}(v) \ge r_u + m$. In particular $|W| \ge 3$, and $x$ has no 2-cycle on $W$ (if $x_u = w$ and $x_w = u$, then $r_w = \mathrm{rank}_u(w) \le m$, contradicting $\mathrm{rank}_u(x_u) = m + 1$). Thus $x_{x_u} \in W \setminus \{u, x_u\}$, yielding $m + 1 = \mathrm{rank}_{x_u}(x_{x_u}) \ge r_u + m$, so $r_u = 1$, i.e., $f(x_u) = u$. Therefore $W$ has **structure F**:
- $u \mapsto x_u$ is a permutation of $W$ (injective since $f(x_u) = u$) with no 1- or 2-cycles;
- $f(x_u) = u$ for every $u \in W$; and
- every $w \in W$ ranks every $v \in W \setminus \{f(w), w\}$ at position $\ge m + 1$.

**Exchange step.** If $W$ has structure F and some $w \in W$ has a $G$-neighbor $y \in V(M_0)$ with $z = M_0(y)$, form $M_1 = M_0 - yz + yw$ and extend $M_1$ to a maximal matching $M_1'$ of $G$. Because $W$ is $G$-independent, $z$ is the only newly uncovered vertex outside $W$, so at most one edge $zu$ ($u \in W \setminus \{w\}$) is added to reach $M_1'$. Set $u_0 := x^{-1}(w) \in W \setminus \{w\}$ and $u_1 := x^{-1}(u_0) \in W \setminus \{u_0, w\}$ (distinct since $x$ has no 1- or 2-cycles). The new uncovered set $W_1$ has odd size (hence $W_1 \ne \emptyset$). If no edge $zu$ is added, or if $zu$ is added with $u \ne u_0$, then $u_0 \in W_1$ has $x_{u_0} = w \notin W_1$; if $zu_0$ is added, then $u_1 \in W_1$ has $x_{u_1} = u_0 \notin W_1$. Thus $W_1$ lacks structure F, and $M_1'$ extends to an $m$-stable matching.

**Residual case.** Assuming no maximal matching of $G$ extends to an $m$-stable matching, every maximal matching of $G$ leaves uncovered precisely the set $I$ of $G$-isolated vertices, $I$ has structure F ($|I| \ge 3$ odd), and every maximal matching of $G[J]$ (where $J := V \setminus I$) is perfect. We record two immediate consequences:
- **(R1)** For every $w \in I$, $T_w \cap I = \{f(w)\}$, so $|T_w \cap J| = m - 1$; every $y \in T_w \cap J$ satisfies $\mathrm{rank}_y(w) \ge m + 1$ (since $I$ is $G$-isolated). Thus $n := |J| = 2m + 1 - |I|$ satisfies $m - 1 \le n \le 2m - 2$ (in particular $n \ge 2$ and $I \ne V$).
- **(R2)** $G[J]$ is *randomly matchable* (every maximal matching is perfect), so for every edge $uv$ of a component $C$ of $G[J]$, $C - u - v$ admits a perfect $G$-matching. By Sumner's characterization of randomly matchable graphs (*J. Graph Theory* 3 (1979), 183–186), every connected component of $G[J]$ is isomorphic to $K_{2r}$ ($r \ge 1$) or $K_{t,t}$ ($t \ge 2$). Let $J_2$ be the union of $K_2$ components ($b := |J_2|$) and $J_+ := J \setminus J_2$ ($a := |J_+|$); every vertex in $J_+$ has $\deg_G \ge 2$.

For each $y \in J$, let $C_y$ be its component in $G[J]$, and define:
$$d_y := \max_{u \in N(y)} \mathrm{rank}_y(u) \le m, \quad A_y := \{z \ne y : \mathrm{rank}_y(z) \le d_y + m - 1\}, \quad \varepsilon_y := |A_y \cap I|, \quad \beta_y := \min_{w \in I} \mathrm{rank}_y(w).$$
Since $d_y + m - 1 \le 2m - 1 < N$, we have $|A_y| = d_y + m - 1$.

---

## 2. Basic Matching Constructions

**Lemma B.** *Let $e, e' \in J$ lie in distinct components $C, C'$ of $G[J]$, and let $s \in N(e)$ and $t \in N(e')$ satisfy:*
- *(i) $\mathrm{rank}_e(e') \le \mathrm{rank}_e(s) + m - 1$,*
- *(ii) $\mathrm{rank}_{e'}(e) \le \mathrm{rank}_{e'}(t) + m - 1$.*

*For any $w \in I$, form a matching $M$ by leaving $s$ single, matching $e\text{–}e'$ and $t\text{–}w$, taking perfect $G$-matchings of $C - s - e$, $C' - e' - t$, and all other components of $G[J]$, and pairing $I \setminus \{w\}$ so that if $x_s \in I \setminus \{w\}$, then $x_s$ is paired with $f(x_s)$ (when $f(x_s) \ne w$) or with $x(x_s)$ (when $f(x_s) = w$). Then $M$ satisfies Lemma 1(a), and Lemma 1(b) holds unless $x_s \in \{e', t, w\}$. In particular, if $x_s \in I$, choosing $w \in I \setminus \{x_s, f(x_s)\}$ (possible since $|I| \ge 3$) makes $M$ $m$-stable.*

*Proof.* For (a): because $C \ne C'$ and $I$ is $G$-isolated, the only $G$-edges with no $G$-matched endpoint are $\{s, e\}$ (covered by $e$ via (i)) and $\{e', t\}$ (covered by $e'$ via (ii)). For (b): $x_s \ne e$ because $s \in N(e) \implies \mathrm{rank}_s(e) \le m$; if $x_s$ is $G$-matched then $\rho_{x_s} \le m$; if $x_s \in I \setminus \{w\}$ then either $\rho_{x_s} = 1$, or $f(x_s) = w$ and $x_s$ is paired with $x(x_s) \in I \setminus \{w, x_s\}$ (as $x$ has no 1- or 2-cycles on $I$, leaving an even remainder of size $|I| - 3$), giving $\rho_{x_s} = m + 1 \le \mathrm{rank}_{x_s}(s) + m - 1$ since $s \in J$ implies $s \ne w = f(x_s)$ and hence $\mathrm{rank}_{x_s}(s) \ge 2$. $\square$

In particular, whenever Lemma B (with optimal $w$ if $x_s \in I$) fails (b), we must have $x_s = o \in \{e', t\} \subseteq C'$ and $s \in T_o$.

**Lemma RB.** *Let $uy \in E(G)$ and $w \in I$ satisfy:*
- *(C1) $\mathrm{rank}_y(w) \le \mathrm{rank}_y(u) + m - 1$, and*
- *(C2) $x_u \ne w$, or $\mathrm{rank}_w(u) \ge m + 1$, or $\mathrm{rank}_w(y) \le \mathrm{rank}_w(u) + m - 1$.*

*Then leaving $u$ single, matching $y\text{–}w$, taking a perfect $G$-matching of $J - u - y$, and pairing $I \setminus \{w\}$ as in Lemma B gives an $m$-stable matching.*

*Proof.* Identical to Lemma B: $\{u, y\}$ is the only $G$-edge without a $G$-matched endpoint (covered by $y$ via C1), and (b) holds for $x_u = w$ by C2 and for $x_u \in I \setminus \{w\}$ as in Lemma B. $\square$

---

## 3. Consequence When Lemma RB Fails: Property `(*)`

Assume from now on that no triple $(u, y, w)$ satisfies Lemma RB.

**Property `(*)`.** *If $y \in J$ and $w \in I \cap A_y$, then $C_y = \{u, y\}$ is a $K_2$ component, $f(u) = y$, $x_u = w$, $\mathrm{rank}_w(u) \le m$, and $\mathrm{rank}_w(y) \ge \mathrm{rank}_w(u) + m$. In particular, $\varepsilon_y \le 1$ for all $y \in J$, and $\varepsilon_y = 0$ for all $y \in J_+$.*

*Proof.* Let $u \in N(y)$ be a worst $G$-neighbor of $y$ ($\mathrm{rank}_y(u) = d_y$). Since $w \in A_y$, (C1) holds for $(u, y, w)$, so (C2) fails: $x_u = w$, $\mathrm{rank}_w(u) \le m$, and $\mathrm{rank}_w(y) \ge \mathrm{rank}_w(u) + m \ge m + 1$. For the reversed triple $(y, u, w)$, (C2) holds (as $\mathrm{rank}_w(y) \ge m + 1$), so (C1) must fail: $m + 1 = \mathrm{rank}_u(w) \ge \mathrm{rank}_u(y) + m$, forcing $\mathrm{rank}_u(y) = 1$, i.e., $f(u) = y$. If $u$ had another $G$-neighbor $y' \ne y$, then $\mathrm{rank}_u(y') \ge 2$, so $\mathrm{rank}_u(w) = m + 1 \le \mathrm{rank}_u(y') + m - 1$ gives (C1) for $(y', u, w)$; then (C2) fails for $(y', u, w)$, forcing $\mathrm{rank}_w(u) \ge \mathrm{rank}_w(y') + m \ge m + 1$, contradicting $\mathrm{rank}_w(u) \le m$. Thus $\deg_G(u) = 1$ and $C_y = \{u, y\} \cong K_2$. Uniqueness of $x_u$ yields $\varepsilon_y \le 1$. $\square$

For $y \in J_2$, write $y'$ for its unique $G$-neighbor ($d_y = \mathrm{rank}_y(y')$). Let $K := \{z \in J_2 : \varepsilon_z = 1\}$, $\kappa := |K|$, and for $z \in K$ let $w_z$ be the unique agent in $A_z \cap I$; by `(*)`, $x_{z'} = w_z$ and $z' \in T_{w_z}$.

---

## 4. Good Arcs

A **good arc** $p \to q$ consists of $p, q \in J$ in distinct components with $q \in T_p$ and $p \in A_q$ (then $p \notin T_q$, so $\mathrm{rank}_q(p) \ge m + 1$). Put $Y_q(p) := \{y \in N(q) : \mathrm{rank}_q(y) \ge \mathrm{rank}_q(p) - m + 1\}$ (nonempty, as it contains a worst $G$-neighbor of $q$).

**Lemma GA.** *Let $p \to q$ be a good arc.*
1. *For any $y \in Y_q(p)$ and $u \in N(p)$, Lemma B with $(e, e', s, t) = (q, p, y, u)$ applies and fails only if $x_y = u$, $y \in T_u$, and $\beta_u \ge \mathrm{rank}_u(y) + m$ (choosing $w \in I$ minimizing $\mathrm{rank}_u(w)$ when $x_y = u \notin I$).*
2. *For any $u \in N(p)$ and $y \in Y_q(p)$, Lemma B with $(e, e', s, t) = (p, q, u, y)$ applies and fails only if ($x_u = q$, $u \in T_q$, $\mathrm{rank}_q(p) \ge \mathrm{rank}_q(u) + m$) or ($x_u = y$, $u \in T_y$, $\beta_y \ge \mathrm{rank}_y(u) + m$).*

*Consequently, if $\deg_G(p) \ge 2$, picking $u \in N(p) \setminus \{x_y\}$ in (1) gives an $m$-stable matching. If $\deg_G(p) = 1$ ($N(p) = \{u\}$) and both constructions fail for all $y \in Y_q(p)$, then:*
- *(G1) for all $y \in Y_q(p)$: $x_y = u$, $y \in T_u$, and $\beta_u \ge \mathrm{rank}_u(y) + m$;*
- *(G2) $x_u = q$, $u \in T_q$, and $\mathrm{rank}_q(u) \le \mathrm{rank}_q(p) - m$.*

*Proof.* In (1), (i) holds by $y \in Y_q(p)$ and (ii) holds since $\mathrm{rank}_p(q) \le m$; if $x_y = p$, then $\rho_p = \mathrm{rank}_p(q) \le m$, so (b) holds. In (2), (i) and (ii) hold symmetrically. When $\deg_G(p) = 1$ and (G1) holds, every $y \in Y_q(p)$ has $y \in T_u$ ($\mathrm{rank}_u(y) \le m < m + 1 = \mathrm{rank}_u(x_u)$), ruling out $x_u = y$ in (2) and forcing (G2). $\square$

**Lemma K2J.** *Any good arc $p \to q$ with $q \in J_+$ yields an $m$-stable matching.*

*Proof.* If $p \in J_+$, Lemma GA applies directly. Suppose $p \in J_2$ with partner $u = p'$, and assume all Lemma B constructions fail, so (G1)–(G2) hold for $p \to q$. By (G2), $u \in T_q$ and $\mathrm{rank}_u(q) = m + 1$. If $d_u \ge 2$, then $m + 1 \le d_u + m - 1$, making $q \to u$ a good arc with tail $q \in J_+$, which succeeds by Lemma GA. Hence $d_u = 1$, i.e., $f(u) = p$.

Now let $y \in Y_q(p) \subseteq C_q \subseteq J_+$, so $\deg_G(y) \ge 2$ and $d_y \ge 2$. By (G1), $y \in T_u$ and $x_y = u$, so $\mathrm{rank}_y(u) = m + 1 \le d_y + m - 1$. Thus $u \to y$ is a good arc with tail $u \in J_2$ (partner $p$), so (G1)–(G2) hold for $u \to y$ as well:
- (G2) for $u \to y$ gives $x_p = y$ and $\mathrm{rank}_y(p) \le \mathrm{rank}_y(u) - m = 1$, so $f(y) = p \notin N(y)$.
- Hence $Y_y(u) = \{z \in N(y) : \mathrm{rank}_y(z) \ge 2\} = N(y)$, and (G1) for $u \to y$ gives $x_{y_2} = p$ for every $y_2 \in N(y)$.
- Since $x_p = y$ is unique, $Y_q(p) = \{y\}$.
- Since $q \in N(y)$, we have $x_q = p$, so $\mathrm{rank}_q(p) = m + 1$ and $Y_q(p) = N(q) \setminus \{f(q)\}$.
- Yet (G2) for $p \to q$ gives $\mathrm{rank}_q(u) \le (m + 1) - m = 1$, i.e., $f(q) = u \notin N(q)$, so $Y_q(p) = N(q)$ has size $\deg_G(q) \ge 2$, contradicting $Y_q(p) = \{y\}$. $\square$

**Corollary S.** *If Lemma B applies with single $s \in J_+$, then an $m$-stable matching exists.*

*Proof.* Choosing $w \notin \{x_s, f(x_s)\}$ when $x_s \in I$, failure of (b) forces $x_s = o \in C' \ne C_s$ and $s \in T_o$. Since $s \in J_+$ has $d_s \ge 2$, $\mathrm{rank}_s(o) = m + 1 \le d_s + m - 1$, so $o \to s$ is a good arc into $J_+$ and Lemma K2J applies. $\square$

---

## 5. Mutual Pairs

A **mutual pair** is an unordered pair $\{e, e'\} \subseteq J$ in distinct components with $e' \in A_e$ and $e \in A_{e'}$. Then $U := \{s \in N(e) : \mathrm{rank}_e(s) \ge \mathrm{rank}_e(e') - m + 1\}$ and $Y := \{t \in N(e') : \mathrm{rank}_{e'}(t) \ge \mathrm{rank}_{e'}(e) - m + 1\}$ are nonempty, and Lemma B applies to $(e, e', s, t)$ for all $s \in U, t \in Y$.

- **Lemma MJ.** *If $\{e, e'\}$ is a mutual pair with $e \in J_+$, then $U \subseteq J_+$ and Corollary S yields an $m$-stable matching.*
- **Lemma D.** *Let $\{e, e'\} \subseteq J_2$ be a mutual pair with partners $s = e'$ and $t = (e')'$ (here $U = \{s\}, Y = \{t\}$). If Lemma B with single $s$ fails, then $x_s \in \{e', t\} = C_{e'}$. In particular, $e \notin K$ (since $e \in K$ implies $x_s = w_e \in I$ by `(*)`, in which case Lemma B succeeds).*

Consequently, if every Lemma B construction fails, all mutual partners of $e \in J_2$ lie in the single $K_2$ component $C_{x_{e'}}$: **each vertex lies in at most two mutual pairs.**

---

## 6. Counting Contradiction Outside the All-$K_2$ Case

Assume every construction in §§1–5 fails. By Lemma MJ, all mutual pairs lie in $J_2$; let $L$ be the number of mutual pairs.

For each $y \in J$, define $\alpha_y := |A_y \cap (J \setminus C_y)| = d_y + m - 1 - \varepsilon_y - |A_y \cap C_y|$. Since $|A_y \cap C_y| \le |C_y| - 1$ (with equality $= 1$ for $y \in J_2$), $\alpha_y \ge d_y + m - |C_y| - \varepsilon_y$. Let $P := \frac{1}{2} \sum_C |C|(n - |C|)$ be the number of unordered pairs in $J$ across distinct components. Each such pair contributes $2$ to $\sum_{y \in J} \alpha_y$ if it is mutual and at most $1$ otherwise, so
$$L \ge \sum_{y \in J} \alpha_y - P \ge \sum_C \left(\sum_{y \in C}(d_y + m - |C| - \varepsilon_y) - \frac{|C|(n - |C|)}{2}\right).$$

Using $\varepsilon_y = 0$ on $J_+$ and $n \le 2m - 2$ (so $2m - n \ge 2$), the contribution of each component $C$ is:
- **$C \cong K_2$:** $\sum_{y \in C}(d_y - \varepsilon_y) + (2m - 2 - n)$;
- **$C \cong K_{2r}$ ($r \ge 2$, $d_y \ge 2r - 1$):** $\ge r(2m - 2 - n) + 2r^2 \ge 2r = |C|$;
- **$C \cong K_{t,t}$ ($t \ge 2$, $d_y \ge t$):** $\ge t(2m - n) \ge 2t = |C|$.

Summing over all components gives
$$L \ge a + \sum_{z \in J_2}(d_z - \varepsilon_z) + \frac{b}{2}(2m - 2 - n) = a + \sum_{z \in J_2}(d_z - 1) + (b - \kappa) + \frac{b}{2}(2m - 2 - n). \tag{1}$$

For an upper bound, let $D := \{e' : e \in J_2 \text{ lies in a mutual pair}\} \subseteq J_2$. By Lemma D, every endpoint $e$ lies in at most $2$ mutual pairs and $e \notin K$ (hence $e' \notin K' := \{z' : z \in K\}$). Since $e \mapsto e'$ is a bijection on $J_2$, we obtain $2L \le 2|D|$ and $D \subseteq J_2 \setminus K'$, hence
$$L \le |D| \le b - \kappa. \tag{2}$$

Combining (1) and (2) yields
$$a + \sum_{z \in J_2}(d_z - 1) + \frac{b}{2}(2m - 2 - n) \le 0.$$
Every term is nonnegative, so:
1. $a = 0$, hence $J = J_2$ and $b = n \ge m - 1 > 0$;
2. $d_z = 1$ for every $z \in J$ (every $K_2$ component is a mutual first-choice pair);
3. $n = 2m - 2$, hence $|I| = 3$.

Since $d_z = 1$, $A_z = T_z$ for all $z \in J$, so a mutual pair in distinct components would be a $G$-edge — impossible. Therefore $L = 0$, and (1) forces $\kappa = b$: every $z \in J$ has a unique $I$-agent $w_z \in T_z \cap I$. Moreover, $\alpha_z = |T_z \cap (J \setminus \{z, z'\})| = m - 2$, so $\sum_{z \in J} \alpha_z = (2m - 2)(m - 2) = P$. Since no pair of non-partners in $J$ contributes $2$, every pair of non-partners contributes **exactly $1$** (a tournament on non-partners). Write $\mathrm{out}(z) := T_z \cap (J \setminus \{z, z'\})$; then $|\mathrm{out}(z)| = m - 2$.

---

## 7. Resolution of the All-$K_2$ Case ($m \ge 3$)

For each $z \in J$, define its color $c(z) := x_z \in I$. Applying `(*)` to $y = z'$ and $w = w_{z'} \in T_{z'} \cap I$ gives $c(z) = x_z = w_{z'}$, $z \in T_{c(z)}$, and $\mathrm{rank}_{c(z)}(z') \ge \mathrm{rank}_{c(z)}(z) + m > m$. Partners have distinct colors: if $c(z) = c(z') = q$, then both $z \in T_q$ and $z' \in T_q$, contradicting $\mathrm{rank}_q(z') > m$.

**Construction.** Fix $z \in J$ and $a \in \mathrm{out}(z)$ (so $z, z', a, a'$ are four distinct agents in $J$). Form $M$ by:
- leaving $z'$ single,
- matching $z\text{–}a$ and $a'\text{–}c(a)$ (note $c(a) = w_{a'} \in T_{a'}$),
- matching every other $K_2$ component as a $G$-edge, and
- pairing the two remaining agents of $I \setminus \{c(a)\}$.

Check Lemma 1:
- **(a):** The only $G$-edges without a $G$-matched endpoint are $\{z, z'\}$ ($z$ has $\rho_z = \mathrm{rank}_z(a) \le m$) and $\{a, a'\}$ ($a'$ has $\rho_{a'} = \mathrm{rank}_{a'}(w_{a'}) \le m = \mathrm{rank}_{a'}(a) + m - 1$).
- **(b):** The single is $z'$, with $x_{z'} = c(z') \in I$. If $c(z') \ne c(a)$, then $c(z')$ is paired with the unique other element of $I \setminus \{c(a)\}$. Since $|I| = 3$ and $x$ is a 3-cycle on $I$, this partner is either $f(c(z'))$ ($\rho_{c(z')} = 1$) or $x(c(z'))$ ($\rho_{c(z')} = m + 1 \le \mathrm{rank}_{c(z')}(z') + m - 1$ since $f(c(z')) = c(a) \in I \ne z'$, so $\mathrm{rank}_{c(z')}(z') \ge 2$).

Thus an $m$-stable matching exists unless $c(a) = c(z')$ for every $z \in J$ and every $a \in \mathrm{out}(z)$. Suppose toward a contradiction that this holds. Because $m \ge 3$, $|\mathrm{out}(z)| = m - 2 \ge 1$, so choose any $z \in J$ and $a \in \mathrm{out}(z)$. Consider the non-partner pair $\{z, a'\}$:
- If $a' \in \mathrm{out}(z)$, then $c(a') = c(z') = c(a)$, contradicting $c(a') \ne c(a)$.
- Otherwise, by the tournament property on non-partners, $z \in \mathrm{out}(a')$, so $c(z) = c((a')') = c(a) = c(z')$, contradicting $c(z) \ne c(z')$.

This contradiction completes the proof of the Theorem. $\square$
