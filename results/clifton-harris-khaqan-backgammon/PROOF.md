# Resolution of Clifton–Harris–Khaqan Question 5.2 (`arXiv:2611.29890v1`)

## 1. Statement

Under the **backgammon parking scheme** of Clifton, Harris, and Khaqan ([arXiv:2611.29890v1](https://arxiv.org/abs/2611.29890v1), 23 Nov 2026), cars $1, \dots, n$ arrive sequentially at a row of $n$ parking spots with preference list $\alpha = (a_1, \dots, a_n) \in [n]^n$:
- If spot $a_i$ is unoccupied, car $i$ parks in spot $a_i$.
- If spot $a_i$ is already occupied by some car $j$, car $i$ takes spot $a_i$ and the displaced car $j$ moves to the leftmost unoccupied spot.

Write $\mathcal{O}_B(\alpha) = \pi = (\pi_1, \dots, \pi_n) \in S_n$ where car $\pi_s$ occupies spot $s$ after all $n$ cars have parked. Question 5.2 (§5) asks whether, for fixed $k \in \mathbb{N}$,
$$T(n, k) := \bigl|\mathcal{O}_B^{-1}\bigl(12\cdots k\, n(n-1)\cdots(k+1)\bigr)\bigr| \qquad (n \ge k)$$
can be expressed as a sum involving Motzkin numbers whose indices depend on $n$.

Let $m(x) = \sum_{n \ge 0} M_n x^n$ be the Motzkin generating function ($M_0 = 1$, $M_n = M_{n-1} + \sum_{i=0}^{n-2} M_i M_{n-2-i}$, equivalently $m = 1 + xm + x^2 m^2$), and let $B(r, i) = \frac{r - i + 1}{r + 1} \binom{r + i}{i}$ ($0 \le i \le r$) be Catalan's triangle, characterized recursively by $B(0, 0) = 1$ and $B(r, i) = \sum_{t=0}^{\min(i, r - 1)} B(r - 1, t)$ for $r \ge 1$.

**Theorem 1.** *For every integer $k \ge 1$,*
$$\sum_{n \ge k} T(n, k)\, x^n = x^k \sum_{i=0}^{k-1} B(k - 1, i)\, m(x)^{k + 1 - i}.$$
*Equivalently, for all integers $n \ge k \ge 1$,*
$$T(n, k) = \sum_{i=0}^{k-1} B(k - 1, i)\, M^{(k + 1 - i)}_{n - k}, \qquad M^{(r)}_N = \sum_{N_1 + \dots + N_r = N} M_{N_1} \cdots M_{N_r}.$$

Furthermore, because $x^2 m^2 = (1 - x)m - 1$, every power $x^k m^r$ reduces linearly to $a(x) m + b(x)$ with Laurent polynomials $a, b$, expressing $T(n, k)$ as a fixed signed linear combination of $M_{n + k}, \dots, M_{n - k + 1}$ for all $n \ge k$ (e.g. $T(n, 3) = M_{n+3} - 3M_{n+2} + 3M_{n+1} - 3M_n + 2M_{n-1} - 2M_{n-2}$ and $T(n, 4) = M_{n+4} - 4M_{n+3} + 6M_{n+2} - 7M_{n+1} + 7M_n - 7M_{n-1} + 5M_{n-2} - 5M_{n-3}$).

## 2. Proof

Two structural invariants of the backgammon process hold at every step:
- **(F1)** Once a spot is occupied, it remains occupied forever (a bump replaces its occupant and fills an additional free spot).
- **(F2)** A displaced car always moves to the leftmost unoccupied spot.

For a preference list $\alpha = (a_1, \dots, a_n)$, let $L(\alpha) = \max\{t \le n : a_1, \dots, a_t \text{ are pairwise distinct}\}$ be the length of its longest distinct prefix. Define the generating polynomial
$$P_\pi(y) = \sum_{\alpha \in \mathcal{O}_B^{-1}(\pi)} y^{L(\alpha)} \in \mathbb{Z}[y] \qquad (P_\emptyset(y) = 1),$$
and define the $\mathbb{Q}$-linear operator $\Phi : \mathbb{Q}[y] \to \mathbb{Q}[y]$ by $\Phi(y^j) = y + y^2 + \dots + y^{j + 1}$. For $\sigma \in S_{n-1}$, let $1 \oplus \sigma \in S_n$ denote the permutation $(1, \sigma_1 + 1, \dots, \sigma_{n-1} + 1)$.

**Lemma A (General car-$1$ reduction).** *For every $n \ge 1$ and every $\sigma \in S_{n-1}$,*
$$P_{1 \oplus \sigma}(y) = \Phi\bigl(P_\sigma(y)\bigr) = y P_\sigma(y) + \sum_{\alpha' \in \mathcal{O}_B^{-1}(\sigma)} \bigl(y + y^2 + \dots + y^{L(\alpha')}\bigr).$$

*Proof.* Partition $\mathcal{O}_B^{-1}(1 \oplus \sigma)$ according to whether $a_1 = 1$ or $a_1 \ne 1$.

*Case 1: $a_1 = 1$.* Car $1$ parks in spot $1$ at step $1$. If any later car chose spot $1$, car $1$ would be displaced to a spot $\ge 2$, and by (F1) spot $1$ would thereafter stay occupied by other cars, preventing car $1$ from ending in spot $1$. Hence $a_2, \dots, a_n \in \{2, \dots, n\}$, spot $1$ remains permanently occupied by car $1$, and the leftmost free spot always lies in $\{2, \dots, n\}$. Shifting spot indices down by $1$, $\alpha' = (a_2 - 1, \dots, a_n - 1)$ runs the backgammon process on $[n - 1]$ with outcome $\sigma$. Conversely, prepending $a_1 = 1$ to $(a'_1 + 1, \dots, a'_{n-1} + 1)$ for any $\alpha' \in \mathcal{O}_B^{-1}(\sigma)$ yields a valid list with $L(\alpha) = 1 + L(\alpha')$. This contributes $y P_\sigma(y)$.

*Case 2: $a_1 = p \in \{2, \dots, n\}$.* Car $1$ starts in spot $p \ne 1$ and ends in spot $1$, so it must enter spot $1$ via a bump. By (F1) and (F2), spot $1$ must remain unoccupied until that bump; while unoccupied, spot $1$ is the leftmost free spot. Therefore, no earlier car may choose spot $1$, and the very first bump of the entire process must displace car $1$ (any other bumped car would permanently occupy spot $1$). Let car $j \ge 2$ perform that first bump. Then:
- cars $2, \dots, j - 1$ choose pairwise distinct spots in $\{2, \dots, n\} \setminus \{p\}$;
- car $j$ chooses $a_j = p$, taking spot $p$ and sending car $1$ to spot $1$;
- thereafter, as in Case 1, no car chooses spot $1$, and cars $2, \dots, n$ experience the exact backgammon process on $\{2, \dots, n\}$ (since car $j$ lands in spot $p$ and immediately removes car $1$ from $\{2, \dots, n\}$, leaving the exact state as if cars $2, \dots, j$ had parked in empty spots $a_2, \dots, a_j$!).

Thus $\alpha' = (a_2 - 1, \dots, a_n - 1) \in \mathcal{O}_B^{-1}(\sigma)$, and setting $r = j - 1$, its first $r$ entries are pairwise distinct ($1 \le r \le L(\alpha')$) with $a_1 = a'_r + 1$. Conversely, given any $\alpha' \in \mathcal{O}_B^{-1}(\sigma)$ and any $1 \le r \le L(\alpha')$, setting $a_1 = a'_r + 1$ and $a_i = a'_{i-1} + 1$ ($2 \le i \le n$) defines the inverse map, and $a_1, \dots, a_r$ are pairwise distinct while $a_{r+1} = a_1$, so $L(\alpha) = r$. This contributes $\sum_{\alpha' \in \mathcal{O}_B^{-1}(\sigma)} \sum_{r=1}^{L(\alpha')} y^r$. Summing both cases yields $P_{1 \oplus \sigma} = \Phi(P_\sigma)$. $\square$

**Lemma B (Decreasing outcome $\delta_n = n(n - 1)\cdots 1$).** *For every $n \ge 2$,*
$$P_{\delta_n}(y) = y P_{\delta_{n-1}}(y) + P_{1 \oplus \delta_{n-2}}(y).$$

*Proof.* Car $1$ ends in spot $n$.

*Case 1: car $1$ is never displaced.* Then $a_1 = n$ and no later car chooses spot $n$. Spot $n$ stays occupied by car $1$, the leftmost free spot always lies in $[n - 1]$, and $\alpha' = (a_2, \dots, a_n) \in \mathcal{O}_B^{-1}(\delta_{n-1})$ with $L(\alpha) = 1 + L(\alpha')$. Conversely, every such $\alpha'$ arises, contributing $y P_{\delta_{n-1}}(y)$.

*Case 2: car $1$ is displaced.* By (F1), car $1$ could not return to spot $n$ if it started there and were bumped; hence it enters spot $n$ via a bump while spot $n$ is the leftmost free spot. This forces spots $1, \dots, n - 1$ to be completely full, so the bump occurs at step $n$: car $n$ takes car $1$'s spot $q$ and sends car $1$ to spot $n$. Since car $n$ ends in spot $1$ in $\delta_n$, we must have $q = 1$. Hence cars $1, \dots, n - 1$ never chose spot $n$ (by (F1)) and parked on $[n - 1]$ with outcome $(1, n - 1, \dots, 2) = 1 \oplus \delta_{n-2}$, followed by $a_n = 1$. Conversely, every $\alpha'' \in \mathcal{O}_B^{-1}(1 \oplus \delta_{n-2})$ followed by $a_n = 1$ produces $\delta_n$. Moreover, $L(\alpha) = L(\alpha'')$: if $L(\alpha'') < n - 1$ the first repeat already lies inside $\alpha''$, while if $L(\alpha'') = n - 1$ then $\alpha''$ is a permutation of $[n - 1]$, so $1$ already appears in $\alpha''$ and $a_n = 1$ repeats it. This contributes $P_{1 \oplus \delta_{n-2}}(y)$. $\square$

**Proposition 2 (Base bivariate generating function).** *Let $p(x) = x + x^2 m(x)$ (so $m = 1 / (1 - p)$). Then*
$$A_0(x, y) := \sum_{n \ge 0} P_{\delta_n}(y)\, x^n = \frac{1}{1 - y p(x)} = \sum_{j \ge 0} p(x)^j y^j.$$

*Proof.* By Lemmas A and B, the polynomials $a_n(y) = P_{\delta_n}(y)$ satisfy $a_0 = 1$, $a_1 = y$, and $a_n = y a_{n-1} + \Phi(a_{n-2})$ for $n \ge 2$, which determines $A_0(x, y)$ uniquely as the formal power series solution to $F = 1 + xy F + x^2 \Phi(F)$ (with $\Phi$ acting coefficientwise in $x$). Applying $\Phi$ termwise to $F = \sum_{j \ge 0} p^j y^j$ (well-defined $x$-adically since $[x^0] p = 0$) gives
$$\Phi(F) = \sum_{j \ge 0} p^j \left(y^{j+1} + \sum_{r=1}^{j} y^r\right) = \frac{y}{1 - yp} + \frac{yp}{(1 - yp)(1 - p)} = \frac{ym}{1 - yp}.$$
Since $p = x + x^2 m$, we have $1 + xy F + x^2 \Phi(F) = 1 + \frac{y(x + x^2 m)}{1 - yp} = 1 + \frac{yp}{1 - yp} = F$. Hence $A_0(x, y) = (1 - yp)^{-1}$. $\square$

**Lemma C (Catalan-triangle expansion).** *Define $c(k, j) = \Phi^k(y^j)|_{y=1}$ and $G_k(p) = \sum_{j \ge 0} c(k, j)\, p^j \in \mathbb{Z}[[p]]$. Then for every $k \ge 1$,*
$$G_k(p) = \sum_{i=0}^{k-1} B(k - 1, i)\, m^{k + 1 - i}, \qquad m = \frac{1}{1 - p}.$$

*Proof.* From $\Phi^k(y^j) = \Phi^{k-1}(\sum_{r=1}^{j+1} y^r)$, evaluating at $y = 1$ gives $c(0, j) = 1$ and $c(k, j) = \sum_{r=1}^{j+1} c(k - 1, r)$ for $k \ge 1$. Summing over $j \ge 0$:
$$G_k(p) = \sum_{j \ge 0} \sum_{r=1}^{j+1} c(k - 1, r)\, p^j = \sum_{r \ge 1} c(k - 1, r) \frac{p^{r - 1}}{1 - p} = \frac{m}{p}\bigl(G_{k-1}(p) - c(k - 1, 0)\bigr).$$
We prove the formula by induction on $k \ge 1$. For $k = 1$, $G_0 = m$ and $c(0, 0) = 1$, so $G_1 = \frac{m}{p}(m - 1) = m^2$ (since $m - 1 = pm$) and $B(0, 0) = 1$.

For $k \ge 2$, assume $G_{k-1} = Q(m) := \sum_{i=0}^{k-2} B(k - 2, i)\, m^{k - i}$. Since $m(0) = 1$, we have $c(k - 1, 0) = G_{k-1}(0) = Q(1)$. Dividing $m^{k - i} - 1 = (m - 1) \sum_{s=0}^{k - 1 - i} m^s$ term by term yields
$$Q(m) - Q(1) = (m - 1) \sum_{s=0}^{k - 1} \left(\sum_{t=0}^{\min(k - 1 - s,\, k - 2)} B(k - 2, t)\right) m^s = pm \sum_{j=0}^{k - 1} B(k - 1, j)\, m^{k - 1 - j},$$
where we set $j = k - 1 - s$ and applied the Catalan-triangle recurrence $B(k - 1, j) = \sum_{t=0}^{\min(j, k - 2)} B(k - 2, t)$. Multiplying by $m / p$ gives $G_k(p) = \sum_{j=0}^{k - 1} B(k - 1, j)\, m^{k + 1 - j}$. $\square$

*Proof of Theorem 1.* Since $\pi_k(n) = 1 \oplus \pi_{k-1}(n - 1)$ for $n \ge k \ge 1$, Lemma A gives $A_k(x, y) := \sum_{n \ge k} P_{\pi_k(n)}(y) x^n = x \Phi(A_{k-1}(x, y))$, hence $A_k(x, y) = x^k \Phi^k(A_0(x, y))$. Evaluating at $y = 1$ using Proposition 2 and Lemma C yields
$$\sum_{n \ge k} T(n, k)\, x^n = A_k(x, 1) = x^k \sum_{j \ge 0} c(k, j)\, p(x)^j = x^k G_k(p(x)) = x^k \sum_{i=0}^{k-1} B(k - 1, i)\, m(x)^{k + 1 - i}. \quad \square$$
