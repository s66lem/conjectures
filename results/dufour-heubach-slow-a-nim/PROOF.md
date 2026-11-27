# Disproof and Complete Corrected Characterization for Dufour–Heubach Conjecture 1 on Slow A-Nim

## Problem Statement

In *On the $\mathcal{P}$-positions of some infinite families of Slow $A$-Nim* (INTEGERS 26 (2026), Article #G3, Section 6; [arXiv:2404.06608v3](https://arxiv.org/abs/2404.06608), Conjecture 1 / `con:atleastk`), M. Dufour and S. Heubach study the impartial normal-play game $\mathrm{SN}(n, A)$ on $n$ stacks where a move picks $a \in A$ and removes one token from each of $a$ distinct nonempty stacks. For $A = \{k, k+1, \dots, n\}$, a position $p \in \mathbb{N}^n$ is *reduced* if $k \max_i p_i \le \sigma(p) := \sum_i p_i$, and its *reduction* $\tilde p$ chops all stacks at the largest $t \ge 0$ with $k t \le \sum_i \min(p_i, t)$.

Let $s = \sigma(p) \bmod (2k)$ and let $o$ be the number of odd stacks. Conjecture 1 states:

> For the game $\mathrm{SN}_{\tilde G}(n, A)$ with $A = \{k, k+1, \dots, n\}$, the set of $\mathcal{P}$-positions is given by
> $$\{(s, o) \mid s \equiv o \pmod 2,\; 0 \le s < k - 1,\; o \le s\} \;\cup\; \{(k - 1, o) \mid o \equiv n \pmod 2,\; 1 \le o \le k - 1\} \;\cup\; \{(s, o) \mid s \equiv o \pmod 2,\; k - 1 < s < 2k - 1,\; o \le 2(k - 1) - s\}.$$

## Main Results

### 1. Disproof of Conjecture 1

The middle set of Conjecture 1 contains two independent errors:

- **Parity error ($o \equiv n \pmod 2$):** At $n = 4$, $k = 2$ ($A = \{2, 3, 4\}$), the position $p = (0, 1, 2, 2)$ is reduced ($2 \cdot 2 \le 5$) and is a genuine $\mathcal{P}$-position (its three options up to symmetry—$(0, 0, 1, 2)$, $(0, 1, 1, 1)$, and $(0, 0, 1, 1)$—each move in one step to a terminal position). Yet $s = 5 \bmod 4 = 1 = k - 1$ and $o = 1 \not\equiv 4 = n \pmod 2$, so Conjecture 1 misclassifies $p$ as an $\mathcal{N}$-position.
- **Nonzero-odd error ($1 \le o$):** For every odd $k \ge 3$ and every $n \ge r := (3k - 1)/2$, the position with $r$ stacks of height $2$ and $n - r$ empty stacks is reduced ($2k \le 3k - 1$) and is a $\mathcal{P}$-position (by the mirror strategy for all-even positions), yet $s = (3k - 1) \bmod 2k = k - 1$ and $o = 0$, so Conjecture 1 misclassifies it as an $\mathcal{N}$-position (smallest instance: $(2, 2, 2, 2)$ at $n = 4, k = 3$).

### 2. Exact Corrected Characterization for All $(n, k, p)$

For any $q \in \mathbb{N}^n$, set $D(q) := \sum_{i=1}^n \lceil q_i / 2 \rceil$ and $E(q) := \sum_{i=1}^n \lfloor q_i / 2 \rfloor$.

**Theorem.** For every $n \ge 1$, every $k \ge 1$, and every position $p \in \mathbb{N}^n$ (reduced or not),
$$p \text{ is a } \mathcal{P}\text{-position of } \mathrm{SN}(n, \{k, \dots, n\}) \iff \left\lfloor \frac{D(\tilde p)}{k} \right\rfloor = \left\lfloor \frac{E(\tilde p)}{k} \right\rfloor.$$
For reduced positions $p$, this is equivalent to $s \le 2k - 2$ and $o \le \min(s, 2k - 2 - s)$, i.e., replacing the middle set of Conjecture 1 with $\{(k - 1, o) \mid 0 \le o \le k - 1\}$.

## Complete Proof

### Lemma 1 (Reduction Invariance)

Let $t(p) := \max \{ t \ge 0 : k t \le \sum_i \min(p_i, t) \}$ and $\tilde p_i := \min(p_i, t(p))$. By maximality of $t = t(p)$, setting $H := \{i : p_i > t\}$, we have $\sigma(\tilde p) + |H| < k(t + 1)$ and hence $|H| < k$. Also $t(p) = 0$ iff fewer than $k$ stacks are positive. For any legal move $q = p - e_S$ ($|S| \ge k$):
- Since $|H| + |S \setminus H| \ge |S| \ge k$, chopping $q$ at $t$ lowers the sum by at least $|S \setminus H| \ge k - |H| > \sigma(\tilde p) - k t$, so $t(q) < t(p)$.
- For every $s < t(p)$, $\min(q_i, s) = \min(\tilde p_i - \mathbf{1}_{i \in S}, s)$ for all $i$, so $\widetilde{p - e_S} = \widetilde{\tilde p - e_S}$.

### Lemma 2 (Even-Below-$t$ Lemma)

Suppose every stack of $q$ with $q_i \le t := t(q)$ is even. Then $\lfloor D(\tilde q) / k \rfloor = \lfloor E(\tilde q) / k \rfloor$.

*Proof.* If $t = 2r$ is even, every entry of $\tilde q$ is even, so $D(\tilde q) = E(\tilde q)$. If $t = 2r + 1$ is odd, the odd entries of $\tilde q$ are precisely $H = \{i : q_i > t\}$ (with $|H| < k$), so $D(\tilde q) = E(\tilde q) + |H|$ and $D(\tilde q) + E(\tilde q) = \sigma(\tilde q)$. From $k(2r + 1) \le \sigma(\tilde q)$ and $\sigma(\tilde q) + |H| < k(2r + 2)$, we get $2 D(\tilde q) = \sigma(\tilde q) + |H| < 2k(r + 1)$ and $2 E(\tilde q) = \sigma(\tilde q) - |H| \ge k(2r + 1) - |H| > 2 k r - 1$, hence $k r \le E(\tilde q) \le D(\tilde q) < k(r + 1)$.

### Step 1 ($\mathcal{P} \to \mathcal{N}$)

Let $p$ be reduced with $\lfloor D(p)/k \rfloor = \lfloor E(p)/k \rfloor = m$. Then $k m \le E(p) \le D(p) < k(m + 1)$, so $\sigma(p) = D(p) + E(p) \le 2 k m + 2k - 2$, whence $p_i \le 2m + 1$ and $\lfloor p_i / 2 \rfloor \le m$ for every $i$. Let $q = p - e_S$ ($|S| \ge k$) be any legal move. Since $\lfloor q_i / 2 \rfloor + \mathbf{1}_{i \in S} \le \lceil p_i / 2 \rceil$ for all $i$, summing gives $E(q) \le D(p) - |S| \le D(p) - k < k m$.

- If $q$ is reduced ($\tilde q = q$), then $\lceil q_i / 2 \rceil \ge \lfloor p_i / 2 \rfloor$ gives $D(q) \ge E(p) \ge k m > E(q)$, so $\lfloor D(q)/k \rfloor \ne \lfloor E(q)/k \rfloor$.
- If $q$ is not reduced, let $t = t(q)$, $H = \{i : q_i > t\}$ ($1 \le |H| < k$), and $c := \lceil t / 2 \rceil$. Pick $i_0 \in H$: $t + 1 \le q_{i_0} \le p_{i_0} \le 2m + 1 \implies t \le 2m \implies c \le m$.
  - For $i \notin H$, $\lceil \tilde q_i / 2 \rceil \ge \lfloor p_i / 2 \rfloor$; for $i \in H$, $\lceil \tilde q_i / 2 \rceil = c$ and $\lfloor p_i / 2 \rfloor \le m$. Summing yields
    $$D(\tilde q) \ge E(p) - |H|(m - c) \ge k m - |H|(m - c) = k c + (k - |H|)(m - c) \ge k c.$$
  - If $c = m$, then $E(\tilde q) \le E(q) < k m = k c$. If $c \le m - 1$, then $D(\tilde q) + E(\tilde q) + |H| < k(t + 1) \le k(2c + 1)$ minus the lower bound on $D(\tilde q)$ gives
    $$E(\tilde q) < 2 k c + (k - |H|) - k c - (k - |H|)(m - c) = k c - (k - |H|)(m - c - 1) \le k c.$$
  Hence $E(\tilde q) < k c \le D(\tilde q)$, so $\lfloor D(\tilde q)/k \rfloor \ne \lfloor E(\tilde q)/k \rfloor$.

### Step 2 ($\mathcal{N} \to \mathcal{P}$)

Let $p$ be reduced with $\lfloor D(p)/k \rfloor \ne \lfloor E(p)/k \rfloor$. Set $O := \{i : p_i \text{ odd}\}$.
- **Case 1 ($|O| \ge k$):** Play $S = O$. Every entry of $q = p - e_O$ is even, so Lemma 2 gives $\lfloor D(\tilde q)/k \rfloor = \lfloor E(\tilde q)/k \rfloor$.
- **Case 2 ($|O| < k$):** Let $m := \lfloor E(p)/k \rfloor$, so $k m \le E(p) < k(m + 1) \le D(p)$ and $p$ has at least $k$ positive stacks. Let $M := \max_i p_i$, $\mathrm{MaxS} := \{i : p_i = M\}$, and $S_0 := O \cup \mathrm{MaxS}$. For any $S \supseteq O$ of positive stacks, $D(p - e_S) = E(p)$ and $E(p - e_S) = E(p) - (|S| - |O|)$.
  - If $|S_0| \le k$: extend $S_0$ to $S$ of size $k$ among positive stacks. Then $\max(p - e_S) \le M - 1$, $p - e_S$ is reduced ($\sigma(p - e_S) = \sigma(p) - k \ge k(M - 1)$), $D(p - e_S) = E(p) \in [km, k(m+1))$, and $E(p - e_S) = D(p) - k \in [km, k(m+1))$.
  - If $|S_0| > k$: then $M = 2r$ is even (else $\mathrm{MaxS} \subseteq O$, contradicting $|O| < k$), and $k(2r) \le \sigma(p) < k(2m + 4) \implies r \le m + 1$.
    - If $r \le m$: choose $S = O$ plus $k - |O|$ stacks from $\mathrm{MaxS}$. Then $D(q) = E(p) \ge km$ and $E(q) = D(p) - k \ge km$, so $\sigma(q) \ge 2km \ge k(2r) = k M$, making $q$ reduced with $\lfloor D(q)/k \rfloor = \lfloor E(q)/k \rfloor = m$.
    - If $r = m + 1$: choose $S = S_0$ ($|S_0| > k$). If $q = p - e_{S_0}$ is reduced, then $\sigma(q) \ge k(2m + 1)$, so $E(q) = \sigma(q) - E(p) \ge k(2m + 1) - (k m + k - 1) = km + 1 > km$, giving $\lfloor D(q)/k \rfloor = \lfloor E(q)/k \rfloor = m$. If $q$ is not reduced, then $t(q) \le 2m$, and every stack of $q$ with height $\le 2m$ is even, so Lemma 2 gives $\lfloor D(\tilde q)/k \rfloor = \lfloor E(\tilde q)/k \rfloor$.

Strong induction on $\sigma(p)$ with Lemma 1 completes the proof of the theorem.

## Verification

- Lean 4 formalization: [DufourHeubachSlowANim.lean](file:///C:/Users/s6lem/.t3/projects/conjectures/lean/Conjectures/DufourHeubachSlowANim.lean)
- Standalone verifier: [verify.py](file:///C:/Users/s6lem/.t3/projects/conjectures/results/dufour-heubach-slow-a-nim/verify.py)
