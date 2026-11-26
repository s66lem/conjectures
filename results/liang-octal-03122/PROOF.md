# Proof of the Complete Resolution of Liang's Conjecture 4.1 (`arXiv:2611.29198v1`)

**Reference:** Kai Liang, *Quaternary games with infinite misère quotients*, [arXiv:2611.29198v1](https://arxiv.org/abs/2611.29198) (math.CO, 22 Nov 2026), Section 4.1, Conjecture 4.1.

## Rules and Notation

In the octal game $0.3122$, a position is a finite multiset of positive integer heaps. In a single move, a player selects one heap of size $h$ and either:
- removes the heap entirely if $h \in \{1, 2\}$, or
- replaces $h$ by $h - k$ for $k \in \{1, 3, 4\}$ whenever $h > k$.

Heaps never split. Under misère play, the empty position $\emptyset$ is an $\mathcal{N}$-position (the player about to move wins because the previous player took the last heap), and a nonempty position $X$ is a $\mathcal{P}$-position if and only if no option $Y$ of $X$ is a $\mathcal{P}$-position. Write $o(a, b, x, y) \in \{\mathcal{P}, \mathcal{N}\}$ for the misère outcome of the multiset $\{a, b, x, y\}$ (with $0$ denoting an absent heap).

---

## Theorem 1 (Disproof of the Literal Statement)

**Theorem 1.** *Without a lower bound on $x, y$, Conjecture 4.1 is false: $o(2, 2, 7, 2) = \mathcal{N}$ whereas $o(2, 2, 14, 2) = \mathcal{P}$, even though both pairs $(7, 2)$ and $(14, 2)$ have the same key $(0, 2, \mathrm{False})$.*

*Proof.* Direct finite evaluation of the misère recursion on positions of total heap sum at most $20$ (verified in `verify.py`) yields $o(2, 2, 7, 2) = \mathcal{N}$ and $o(2, 2, 14, 2) = \mathcal{P}$. Both have $x \equiv 0 \pmod 7$, $y \equiv 2 \pmod 7$, and $|x - y| \in \{5, 12\} > 4$. $\square$

---

## Theorem 2 (Proof of Conjecture 4.1 for All $x, y \ge 3$)

**Theorem 2.** *For all integers $x, y \ge 3$, the misère outcome $o(2, 2, x, y)$ in $0.3122$ depends only on $(x \bmod 7,\; y \bmod 7,\; [|x - y| \le 4])$. Explicitly, $o(2, 2, x, y) = \mathcal{P}$ if and only if $(x \bmod 7,\; y \bmod 7)$ lies in*
$$B = \{(1,1),(2,2),(3,3),(5,5),(6,6),(1,6),(6,1),(2,4),(4,2),(3,5),(5,3)\},$$
*together with $(0,0),(4,4)$ when $|x - y| \le 4$, or $(0,4),(4,0)$ when $|x - y| > 4$. All $98$ keys occur, and the threshold $x, y \ge 3$ is sharp.*

### Setup: Closed Family $\mathcal{F}$ and Reduction Operator $\Phi$

Let $\mathcal{F}$ be the set of positions with at most $4$ positive heaps, at most $2$ of which exceed $2$. Every move in $0.3122$ replaces a single heap $h$ by a strictly smaller heap $h' < h$ (or removes it), so $\mathcal{F}$ is closed under taking options. Represent every $X \in \mathcal{F}$ canonically as a $4$-tuple $(h_1, h_2, h_3, h_4)$ with
$$h_1 \ge h_2 \ge h_3 \ge h_4 \ge 0, \qquad h_3 \le 2, \qquad h_4 \le 2.$$
Fix thresholds $D = 13$, $G = 5$, $C = 8$ (note $C = 8 \le D + G = 18$). Define the reduction map $\rho(h_1, h_2)$ on pairs $h_1 \ge h_2 \ge 0$ in two stages:
1. **Stage $\rho_1$:** while $h_2 \ge D + 7 = 20$, replace $(h_1, h_2) \mapsto (h_1 - 7, h_2 - 7)$.
2. **Stage $\rho_2$:** then, while $h_1 - h_2 \ge G + 7 = 12$ and $h_1 \ge C + 7 = 15$, replace $(h_1, h_2) \mapsto (h_1 - 7, h_2)$.

After Stage $\rho_1$, $h_2 \le D + 6 = 19$. After Stage $\rho_2$, either $h_1 - h_2 \le G + 6 = 11$ (so $h_1 \le D + G + 12 = 30$) or $h_1 \le C + 6 = 14$. Hence every reduced tuple $(\tilde{h}_1, \tilde{h}_2, h_3, h_4)$ lies in the finite domain $h_1 \le 44$ ($5{,}853$ canonical positions). Define $\Phi(h_1, h_2, h_3, h_4) \in \{\mathcal{P}, \mathcal{N}\}$ to be the exact misère outcome $o(\tilde{h}_1, \tilde{h}_2, h_3, h_4)$ read from this finite table.

### Lemma 1 (Shift Invariance of $\Phi$)

1. **Diagonal shift:** If $h_2 \ge D + 7 = 20$, then $\Phi(h_1, h_2, h_3, h_4) = \Phi(h_1 - 7, h_2 - 7, h_3, h_4)$.
   *Proof.* Stage $\rho_1$ on $(h_1, h_2)$ takes one initial step to $(h_1 - 7, h_2 - 7)$, after which both reductions are identical. $\square$
2. **Top-heap shift:** If $h_1 - h_2 \ge G + 7 = 12$ and $h_1 \ge C + 7 = 15$, then $\Phi(h_1, h_2, h_3, h_4) = \Phi(h_1 - 7, h_2, h_3, h_4)$.
   *Proof.* Both $(h_1, h_2)$ and $(h_1 - 7, h_2)$ have the same second coordinate $h_2$, so Stage $\rho_1$ performs the exact same number $i = \max(0, \lfloor (h_2 - D)/7 \rfloor)$ of diagonal steps on both, producing $(h_1', h_2')$ and $(h_1' - 7, h_2')$ with $h_1' - h_2' = h_1 - h_2 \ge G + 7 = 12$. Moreover, either $i = 0$ (so $h_1' = h_1 \ge C + 7$) or $i \ge 1$ (so $h_2' \ge D = 13$ and $h_1' \ge h_2' + G + 7 \ge D + G + 7 \ge C + 7$). Therefore Stage $\rho_2$ on $(h_1', h_2')$ begins by subtracting $7$ from $h_1'$, landing directly on $(h_1' - 7, h_2')$. $\square$

### Lemma 2 (Translation of the Misère Recursion)

Say that $\Phi$ *satisfies the misère recursion at $X \in \mathcal{F}$* if $X = \emptyset$ and $\Phi(X) = \mathcal{N}$, or $X \ne \emptyset$ and $\Phi(X) = \mathcal{P} \iff \forall Y \in \mathrm{Opt}(X),\; \Phi(Y) = \mathcal{N}$.

1. **Diagonal translation:** If $h_2(X) \ge D + 11 = 24$, then $\Phi$ satisfies the misère recursion at $X$ if and only if it satisfies the misère recursion at $X' = (h_1 - 7, h_2 - 7, h_3, h_4)$.
   *Proof.* Since $h_1 \ge h_2 \ge 24 > 11$, neither of the two largest heaps can be removed in $X$ or $X'$, and subtracting $k \in \{1, 3, 4\}$ from either of the two largest heaps leaves both at least $20 > 2 \ge h_3 \ge h_4$. Thus every option $Y$ of $X$ satisfies $h_2(Y) \ge D + 7 = 20$, and the options of $X'$ are in bijection with those of $X$ via $Y \mapsto Y - (7, 7, 0, 0)$. By Lemma 1(1), $\Phi(X) = \Phi(X')$ and $\Phi(Y) = \Phi(Y - (7, 7, 0, 0))$ for every option $Y$. $\square$
2. **Top-heap translation:** If $h_2(X) < D + 11 = 24$, $h_1(X) - h_2(X) \ge G + 11 = 16$, and $h_1(X) \ge C + 11 = 19$, then $\Phi$ satisfies the misère recursion at $X$ if and only if it satisfies the misère recursion at $X' = (h_1 - 7, h_2, h_3, h_4)$.
   *Proof.* Since $h_1 \ge 19$ and $h_1 - h_2 \ge 16$, any move in $X$ or $X'$ lowers $h_1$ by at most $4$ (leaving $h_1 - 4 \ge 15$ and $(h_1 - 4) - h_2 \ge 12$, so $h_1$ strictly remains the largest heap and cannot be removed) or modifies one of $h_2, h_3, h_4$ (leaving $h_1$ unchanged and only increasing $h_1 - h_2$). Hence every option $Y$ of $X$ satisfies $h_1(Y) \ge C + 7 = 15$ and $h_1(Y) - h_2(Y) \ge G + 7 = 12$, and the options of $X'$ are in bijection with those of $X$ via $Y \mapsto Y - (7, 0, 0, 0)$. By Lemma 1(2), $\Phi(X) = \Phi(X')$ and $\Phi(Y) = \Phi(Y - (7, 0, 0, 0))$ for every option $Y$. $\square$

### Completion of the Proof of Theorem 2

Define the finite window
$$W = \{X \in \mathcal{F} : h_2(X) < 24 \text{ and } (h_1(X) - h_2(X) < 16 \text{ or } h_1(X) < 19)\}.$$
Every $X \in W$ has $h_1(X) \le 23 + 15 = 38 < 44$, and $|W| = 2{,}191$. The finite certificate in `verify.py` verifies directly that $\Phi$ satisfies the misère recursion at every $X \in W$. By Lemma 2 and induction on $h_1(X) + h_2(X)$ (since both translations strictly decrease $h_1 + h_2$), $\Phi$ satisfies the misère recursion at every $X \in \mathcal{F}$. Since $\Phi(\emptyset) = \mathcal{N}$, induction on $h_1 + h_2 + h_3 + h_4$ yields $\Phi(X) = o(X)$ for all $X \in \mathcal{F}$.

Finally, let $x, y \ge 3$; by symmetry assume $x \ge y \ge 3$, so the canonical form of $\{2, 2, x, y\}$ is $(x, y, 2, 2) \in \mathcal{F}$. Under Stage $\rho_1$, subtracting $(7, 7)$ preserves $x \bmod 7$, $y \bmod 7$, and $x - y$, while stopping at $y \ge D = 13 \ge 3$. Under Stage $\rho_2$, subtracting $(7, 0)$ preserves $x \bmod 7$ and $y \bmod 7$, requires $x - y \ge 12$, and leaves $x - y \ge G = 5 > 4$, so it also preserves the indicator $[|x - y| \le 4]$. Every pair $(x, y)$ with $x \ge y \ge 3$ therefore reduces with identical key to one of the $204$ reduced pairs $(\tilde{x}, \tilde{y})$ with $\tilde{x} \ge \tilde{y} \ge 3$. Exhaustive verification over all $204$ canonical pairs confirms that all $98$ keys appear and every pair matches the stated closed form without conflict. $\square$
