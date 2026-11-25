# Disproof of Chen–Zwicker Conjecture 1 ($\mathrm{EF1}_{\mathrm{outer}}$ Spectrum of Connected Graphs)

We disprove **Conjecture 1** of Jiehua Chen and William S. Zwicker (`arXiv:2402.05884`; central conjecture of Nicolas Bousquet, Frank Connor, Agnès Totschnig, and Sébastien Zeitoun, *Fair Division of Graphs: Beyond Traceability*, `arXiv:2608.29902v1`), showing that an $8$-vertex connected graph $H$ has a non-contiguous `NO` region (`NO` at $k = 2$, `YES` at $k = 3$, `NO` at $k = 4$) across every standard valuation class from common binary additive up to arbitrary heterogeneous monotone valuations.

## 1. Verbatim Definitions (`arXiv:2608.29902`, §2)

Let $G = (V, E)$ be a connected simple graph and $N = \{1, \dots, k\}$ a set of $k$ agents.
- **Connected allocation:** A partition $A = (A_1, \dots, A_k)$ of $V$ into $k$ pairwise disjoint subsets (empty bundles allowed) such that every $A_j$ induces a connected subgraph of $G$ (with $\varnothing$ and singletons connected).
- **Valuations:** Each agent $i$ has a monotone valuation $v_i : \mathcal{C}(G) \to \mathbb{R}_{\ge 0}$ with $v_i(\varnothing) = 0$. Common binary additive valuations have $v_i(S) = \sum_{x \in S} w(x)$ with $w : V \to \{0, 1\}$ independent of $i$.
- **$\mathrm{EF1}_{\mathrm{outer}}$ (Definition 2):** An allocation $A$ is $\mathrm{EF1}_{\mathrm{outer}}$ if for all $i, j \in N$, either $A_j = \varnothing$ or there exists $x \in A_j$ such that $A_j \setminus \{x\}$ is connected and $v_i(A_i) \ge v_i(A_j \setminus \{x\})$.
- **$\mathrm{EF1}_{\mathrm{outer}}$ spectrum and Conjecture 1:** For a fixed graph $G$ and valuation class $\mathcal{V}$, the $k$-th entry of the spectrum is `YES` iff every $k$-agent instance on $G$ with valuations in $\mathcal{V}$ admits a connected $\mathrm{EF1}_{\mathrm{outer}}$ allocation. Conjecture 1 states that the spectrum of every connected graph has the form `YES* NO* YES^∞` (an initial `YES` run, a single contiguous possibly empty `NO` run, and an infinite `YES` tail).

## 2. Counterexample Graph $H$

Define the $8$-vertex connected graph $H = (V, E)$ on $V = \{u, w, a, b, c, \ell_a, \ell_b, \ell_c\}$ by taking $K_{2, 3}$ with sides $\{u, w\}$ and $\{a, b, c\}$ (the *hubs*) and attaching one pendant leaf to each hub:
$$E(H) = \{ua, ub, uc, wa, wb, wc, a\ell_a, b\ell_b, c\ell_c\}.$$
Define the common binary additive valuation $\beta$ by $\beta(a) = \beta(b) = \beta(c) = 1$ and $\beta(v) = 0$ for $v \in \{u, w, \ell_a, \ell_b, \ell_c\}$.

**Theorem 2.1.** Let $\mathcal{V}$ be any valuation class containing $\beta$ and contained in heterogeneous monotone valuations (in particular: common binary additive, common additive, common monotone, heterogeneous binary additive, heterogeneous additive, or heterogeneous monotone). Then the $\mathrm{EF1}_{\mathrm{outer}}$ spectrum of $H$ for $\mathcal{V}$ has:
- `NO` at $k = 2$,
- `YES` at $k = 3$,
- `NO` at $k = 4$.

In particular, Conjecture 1 is false for $\mathcal{V}$.

### Proof of `NO` at $k = 2$ (under $\beta$)

Suppose $(X, Y)$ is a connected $\mathrm{EF1}_{\mathrm{outer}}$ allocation for $2$ agents under $\beta$. Each leaf $\ell_h$ ($h \in \{a, b, c\}$) is adjacent only to $h$, so either $\{\ell_h\}$ is an entire bundle or $\ell_h$ belongs to the same bundle as $h$.
- If some bundle is $\{\ell_h\}$, it has value $0$, while the other bundle contains all three hubs (value $3$). Deleting a single vertex lowers its value by at most $1$, leaving value at least $2 > 0$, so the agent holding $\{\ell_h\}$ has $\mathrm{EF1}_{\mathrm{outer}}$ envy.
- Otherwise, every hub shares its bundle with its leaf. By pigeonhole, one bundle — say $X$ — contains at least two hubs. Since $X$ contains at least two hubs (and hence at least four vertices), for every hub $h \in X$, removing $h$ separates $\ell_h$ from the rest of $X$; thus no hub is an outer vertex of $X$. Every outer vertex $x$ of $X$ therefore has $\beta(x) = 0$, giving $\beta(X \setminus \{x\}) = \beta(X) \ge 2$, whereas $\beta(Y) = 3 - \beta(X) \le 1 < 2$, so the agent holding $Y$ envies $X$ up to any outer vertex. $\square$

### Proof of `NO` at $k = 4$ (under $\beta$)

Suppose $(A_1, A_2, A_3, A_4)$ is a connected $\mathrm{EF1}_{\mathrm{outer}}$ allocation for $4$ agents under $\beta$. Since $\beta(V) = 3 < 4$, some bundle $A_i$ has $\beta(A_i) = 0$. Avoiding $\mathrm{EF1}_{\mathrm{outer}}$ envy from agent $i$ toward every other bundle $A_j$ requires that every bundle $A_j$ contain at most one hub, and that if $A_j$ contains a hub $h$, then $h$ is an outer vertex of $A_j$.

Thus the three hubs $a, b, c$ lie in three distinct bundles $B_a, B_b, B_c$. In $H$, every neighbor of a hub $h$ lies in $I := \{u, w, \ell_a, \ell_b, \ell_c\}$, and $I$ is an independent set whose vertices have neighbors only in $\{a, b, c\}$. Therefore, inside $B_h$, every vertex of $B_h \cap I$ is adjacent only to $h$. Removing $h$ disconnects $B_h$ as soon as $|B_h \cap I| \ge 2$. Since $h$ must be outer in $B_h$, we have $|B_h \cap I| \le 1$ for each $h \in \{a, b, c\}$.

Consequently, $B_a \cup B_b \cup B_c$ absorbs at most $3$ vertices of the $5$-element independent set $I$, leaving at least $2$ vertices of $I$ outside $B_a \cup B_b \cup B_c$. Because $I$ is an independent set, these remaining vertices must occupy at least $2$ additional nonempty bundles, requiring at least $3 + 2 = 5 > 4$ nonempty bundles, a contradiction. $\square$

### Verification of `YES` at $k = 3$

- **Common binary additive:** All $2^8 = 256$ valuations $w : V \to \{0, 1\}$ admit a connected $\mathrm{EF1}_{\mathrm{outer}}$ allocation among the $66$ unordered connected $3$-partitions of $H$ (verified independently in Python and Lean 4).
- **Arbitrary heterogeneous monotone (hence every intermediate class):** Verified in exact rational arithmetic (Z3 `QF_LRA`, returning `unsat` for the nonexistence of an $\mathrm{EF1}_{\mathrm{outer}}$ allocation across all $66$ connected $3$-partitions, with an $18$-allocation unsat core) and formally verified in Lean 4.

## 3. Minimality and Higher-Order Family

- Exhaustive search over all connected graphs on $n \le 7$ vertices (all $853$ graphs on $n = 7$ and all smaller graphs) finds zero gaps under common binary additive valuations; on $n = 8$, exactly $4$ of the $11{,}117$ connected graphs exhibit a gap ($H$ plus $0, 1, 2,$ or $3$ edges among $\{a, b, c\}$), all with common binary spectrum `Y N Y N Y Y Y Y`.
- More generally, for $H_{s, m}$ ($K_{s, m}$ plus one pendant leaf on each vertex of the $m$-side), the same hand proofs show `NO` at $k \in [2, m - 1]$ and $k \in [m + 1, m + s - 1]$, while exhaustive computation confirms `YES` at $k = m$ for $(s, m) \in \{(2,3), (2,4), (3,3), (3,4), (4,4), (3,5), (5,4), (4,5)\}$.
