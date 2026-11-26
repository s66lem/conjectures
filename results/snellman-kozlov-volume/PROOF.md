# Complete Proof of Snellman's Normalized-Volume Monotonicity Conjecture (`arXiv:2611.26110v1`)

## 1. Statement and Setup

In [arXiv:2611.26110v1](https://arxiv.org/abs/2611.26110v1) (*Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*, 19 Nov 2026), Jan Snellman establishes via a staircase tiling (Theorem `thm-staircase`, Corollary `cor-rank2-volume`) and unimodular product equivalence (Proposition `prop-product-regime`) that the normalized volume $\mathrm{NV}(\mathrm{Koz}(n; 0, d))$ of the rank-two Kozlov polytope satisfies, for all integers $n \ge 1$ and $d \ge 0$:
$$\mathrm{NV}(\mathrm{Koz}(n; 0, d)) = \mathrm{NV}(\mathrm{Koz}(n)) \cdot T(n, \min(d, n - 1)),$$
where
$$\mathrm{NV}(\mathrm{Koz}(n)) = \prod_{k=2}^n \binom{n}{k}, \qquad T(n, d) = \sum_{j=1}^{n-d} t_d(j), \qquad t_d(j) = \binom{n-1+d}{d+j-1} \prod_{k=j+1}^{j+d} \binom{n}{k}$$
for $0 \le d \le n - 1$. (For $d \ge n - 1$, $\mathrm{Koz}(n; 0, d)$ is unimodularly equivalent to $\mathrm{Koz}(n)^2$, so its normalized volume is constant and equals $\binom{2n-2}{n-1}\mathrm{NV}(\mathrm{Koz}(n))^2$, which agrees with the $d = n - 1$ value of the formula.)

Snellman states the paper's sole conjecture (`conj-nv-monotone`):

> **Conjecture.** *$\mathrm{NV}(\mathrm{Koz}(n; 0, d))$ is weakly increasing in $d$.*

We prove this conjecture completely for all $n \ge 1$ and $d \ge 0$, together with a sharp quantitative lower bound and exact strictness characterization.

**Theorem 1.**
1. *For every integer $n \ge 2$ and every $0 \le d \le n - 2$,*
   $$T(n, d + 1) - T(n, d) \ge \left(\binom{n}{d} - 1\right) t_d(n - d) \ge 0.$$
2. *For every integer $n \ge 1$, $\mathrm{NV}(\mathrm{Koz}(n; 0, d))$ is weakly increasing in $d \ge 0$.*
3. *For $n \ge 2$ and $0 \le d \le n - 2$, one has the strict inequality $\mathrm{NV}(\mathrm{Koz}(n; 0, d + 1)) > \mathrm{NV}(\mathrm{Koz}(n; 0, d))$ except at the unique pair $(n, d) = (2, 0)$, where $\mathrm{NV}(\mathrm{Koz}(2; 0, 0)) = \mathrm{NV}(\mathrm{Koz}(2; 0, 1)) = 2$.*

## 2. Proof

Fix integers $n \ge 2$ and $0 \le d \le n - 2$. Since $\mathrm{NV}(\mathrm{Koz}(n)) > 0$ and $\mathrm{NV}(\mathrm{Koz}(n; 0, d))$ is constant for $d \ge n - 1$, it suffices to compare $T(n, d + 1)$ and $T(n, d)$ for $0 \le d \le n - 2$. (For $n = 1$, $\min(d, 0) = 0$ for all $d \ge 0$, so $\mathrm{NV}(\mathrm{Koz}(1; 0, d)) = 1$ is constant.)

### Lemma 2.1 (Termwise ratio and strict growth)
*For every $1 \le j \le n - d - 1$,*
$$(d + j)\, t_{d+1}(j) = (n + d) \binom{n}{j + d + 1} t_d(j).$$
*In particular, $t_{d+1}(j) > t_d(j)$ strictly for every $1 \le j \le n - d - 1$.*

*Proof.* By the absorption identity $(k + 1)\binom{m + 1}{k + 1} = (m + 1)\binom{m}{k}$ applied with $m = n - 1 + d$ and $k = d + j - 1$,
$$(d + j)\binom{n + d}{d + j} = (n + d)\binom{n - 1 + d}{d + j - 1}.$$
Moreover, the product factor in $t_{d+1}(j)$ has one extra top factor:
$$\prod_{k=j+1}^{j+d+1} \binom{n}{k} = \binom{n}{j + d + 1} \prod_{k=j+1}^{j+d} \binom{n}{k}.$$
Multiplying these two identities gives $(d + j)\, t_{d+1}(j) = (n + d)\binom{n}{j + d + 1} t_d(j)$. Since $1 \le j \le n - d - 1$, we have $j + d + 1 \le n$, so $\binom{n}{j + d + 1} \ge 1$, $n + d \ge d + j + 1 > d + j > 0$, and $t_d(j) > 0$. Dividing by $d + j$ gives $t_{d+1}(j) > t_d(j)$. $\square$

### Lemma 2.2 (Last-cell gain identity)
*For $n \ge 2$ and $0 \le d \le n - 2$,*
$$t_{d+1}(n - d - 1) = t_d(n - d - 1) + \binom{n}{d} t_d(n - d).$$

*Proof.* Setting $j = n - d - 1$ in Lemma 2.1 gives $d + j = n - 1$ and $j + d + 1 = n$, so $\binom{n}{n} = 1$ yields
$$(n - 1)\, t_{d+1}(n - d - 1) = (n + d)\, t_d(n - d - 1) = (n - 1)\, t_d(n - d - 1) + (d + 1)\, t_d(n - d - 1). \tag{1}$$
Next, compare $t_d(n - d - 1)$ with the dropped cell $t_d(n - d)$. By Pascal's absorption identity $(m - k)\binom{m}{k} = (k + 1)\binom{m}{k + 1}$ with $m = n - 1 + d$ and $k = n - 2$,
$$(d + 1)\binom{n - 1 + d}{n - 2} = (n - 1)\binom{n - 1 + d}{n - 1}.$$
For the binomial products, if $d = 0$ both products are empty ($1$) and $\binom{n}{0} = 1$; if $d \ge 1$,
$$\prod_{k=n-d}^{n-1} \binom{n}{k} = \binom{n}{n - d} \prod_{k=n-d+1}^{n-1} \binom{n}{k} = \binom{n}{d} \prod_{k=n-d+1}^{n} \binom{n}{k}$$
because $\binom{n}{n} = 1$ and $\binom{n}{n - d} = \binom{n}{d}$. Multiplying gives
$$(d + 1)\, t_d(n - d - 1) = (n - 1)\binom{n}{d} t_d(n - d). \tag{2}$$
Substituting (2) into (1) and dividing by $n - 1 > 0$ yields $t_{d+1}(n - d - 1) = t_d(n - d - 1) + \binom{n}{d} t_d(n - d)$. $\square$

### Completion of Proof of Theorem 1
Decompose the sums for $T(n, d + 1)$ and $T(n, d)$ by separating the last surviving cell $j = n - d - 1$ and the dropped cell $j = n - d$:
$$T(n, d + 1) - T(n, d) = \sum_{j=1}^{n-d-2} \bigl(t_{d+1}(j) - t_d(j)\bigr) + \bigl(t_{d+1}(n - d - 1) - t_d(n - d - 1) - t_d(n - d)\bigr).$$
By Lemma 2.1 every term in the sum over $1 \le j \le n - d - 2$ is nonnegative, and by Lemma 2.2 the trailing bracket equals $\bigl(\binom{n}{d} - 1\bigr) t_d(n - d)$. Since $\binom{n}{d} \ge 1$ and $t_d(n - d) > 0$, this proves Part (1) and hence weak monotonicity in Part (2).

For Part (3), suppose $n \ge 2$, $0 \le d \le n - 2$, and $(n, d) \ne (2, 0)$:
- If $d \ge 1$, then $1 \le d \le n - 2 < n$, so $\binom{n}{d} \ge n \ge 3 > 1$ and $t_d(n - d) > 0$, giving $T(n, d + 1) - T(n, d) \ge \bigl(\binom{n}{d} - 1\bigr) t_d(n - d) > 0$.
- If $d = 0$, then $n \ge 3$, so the sum over $1 \le j \le n - 2$ includes $j = 1$, where $j + d + 1 = 2 < n$, giving $t_1(1) > t_0(1)$ by Lemma 2.1, hence $T(n, 1) > T(n, 0)$.

Finally, at $(n, d) = (2, 0)$ we have $\mathrm{NV}(\mathrm{Koz}(2)) = \binom{2}{2} = 1$, $T(2, 0) = \binom{1}{0} + \binom{1}{1} = 2$, and $T(2, 1) = \binom{2}{1}\binom{2}{2} = 2$, so $\mathrm{NV}(\mathrm{Koz}(2; 0, 0)) = \mathrm{NV}(\mathrm{Koz}(2; 0, 1)) = 2$. $\square$

## 3. Boundary Consistency

- At $d = 0$ ($n \ge 1$): $T(n, 0) = \sum_{j=1}^n \binom{n-1}{j-1} = 2^{n-1}$, recovering $\mathrm{NV}(2\,\mathrm{Koz}(n)) = 2^{n-1}\mathrm{NV}(\mathrm{Koz}(n))$.
- At $d \ge n - 1$ ($n \ge 1$): $T(n, n - 1) = \binom{2n-2}{n-1}\prod_{k=2}^n \binom{n}{k} = \binom{2n-2}{n-1}\mathrm{NV}(\mathrm{Koz}(n))$, recovering $\mathrm{NV}(\mathrm{Koz}(n; 0, d)) = \binom{2n-2}{n-1}\mathrm{NV}(\mathrm{Koz}(n))^2$.
