# Proof of Rossi's Conjecture 6.16 (`arXiv:2611.25741v1`)

## 1. Statement

Let $\mathcal{L}_n$ denote the face lattice of the $(n - 1)$-dimensional permutohedron (ordered set partitions of $[n]$ ordered by merging adjacent blocks, with an adjoined bottom element $\bot$ representing the empty face), and let $\chi_n(t) = \sum_{x \in \mathcal{L}_n} \mu(\bot, x)\, t^{n - 1 - \mathrm{rk}(x)}$ be its characteristic polynomial. By Theorem 6.11(1) of G. Rossi ([arXiv:2611.25741v1](https://arxiv.org/abs/2611.25741v1), 19 Nov 2026),
$$\chi_n(t) = t^n - \sum_{i=0}^{n-1} A(n, i)\, (t - 1)^i\, t^{n - 1 - i} \qquad (n \ge 3),$$
where $A(n, i)$ are the Eulerian numbers and $A_n(z) = \sum_{i=0}^{n-1} A(n, i) z^i$ is the $n$-th Eulerian polynomial.

**Theorem (Rossi Conjecture 6.16).** *For every integer $n \ge 3$, $\chi_n(t)$ has $n$ distinct positive real roots: $t = 1$, exactly $n - 2$ roots in $(0, 1)$, and one root in $(1, \infty)$. Equivalently, the full $f$-polynomial $R_n(w) = \sum_{x \in \mathcal{L}_n} w^{\mathrm{rk}(x) + 1} = (-w)^n \chi_n(-1/w)$ has only simple negative real roots.*

## 2. Reduction to $M_n(z) = (1 - z) A_n(z) + z^n$

Consider the involutive Möbius transformation $t = z / (z - 1)$ (inverse $z = t / (t - 1)$), which maps $(-\infty, 0)$ bijectively onto $(0, 1)$ and $(1, \infty)$ bijectively onto $(1, \infty)$. Since $(t - 1) / t = 1 / z$ and $A_n$ is palindromic ($A_n(1/z) = z^{1 - n} A_n(z)$),
$$M_n(z) := (z - 1)^n \chi_n\!\left(\frac{z}{z - 1}\right) = z^n - (z - 1) A_n(z) = (1 - z) A_n(z) + z^n.$$
Expanding in powers of $z$, the $z^n$ terms cancel because $A(n, n - 1) = 1$, leaving
$$M_n(z) = \sum_{k=0}^{n-1} \bigl(A(n, k) - A(n, k - 1)\bigr) z^k \qquad (A(n, -1) := 0).$$
Its leading coefficient is $A(n, n - 1) - A(n, n - 2) = 1 - (2^n - n - 1) = n + 2 - 2^n < 0$ for all $n \ge 3$, so $\deg M_n = n - 1$. Moreover, $M_n(0) = A(n, 0) = 1$ and $M_n(1) = 1^n = 1$, while $\chi_n(1) = 1 - A(n, 0) = 0$.

Therefore, to prove the theorem it suffices to show that $M_n$ has $n - 2$ distinct negative roots and one root in $(1, \infty)$ (yielding all $n - 1$ roots of $M_n$, all simple, and hence $n$ distinct positive real roots of $\chi_n$ with $t = 1$ corresponding to $z = \infty$).

Using $A_n(1/s) = s^{1 - n} A_n(s)$, we obtain the reflection identity $M_n(1/s) = s^{-n}[1 - (1 - s) A_n(s)]$. At $s = -\sigma$ ($\sigma \in (0, 1]$),
$$M_n(-\sigma) = (1 + \sigma) A_n(-\sigma) + (-\sigma)^n, \qquad M_n(-1/\sigma) = (-\sigma)^{-n}\bigl[1 - (1 + \sigma) A_n(-\sigma)\bigr]. \tag{1}$$

## 3. Paired Sign-Alternation Lemma

**Lemma 3.1.** *Let $K = \lfloor (n - 1) / 2 \rfloor \ge 1$. Suppose there exist $0 < \sigma_1 < \dots < \sigma_K \le 1$, with $\sigma_K < 1$ when $n$ is even, such that for every $1 \le m \le K$,*
$$(-1)^m A_n(-\sigma_m) > 0 \qquad \text{and} \qquad (1 + \sigma_m)\, |A_n(-\sigma_m)| > 1. \tag{$\ast$}$$
*Then $M_n$ has $n - 2$ distinct negative roots and one root in $(1, \infty)$.*

*Proof.* Since $0 < \sigma_m \le 1$, we have $|(-\sigma_m)^n| \le 1 < (1 + \sigma_m)|A_n(-\sigma_m)|$, so (1) determines exact signs:
$$\mathrm{sgn}\, M_n(-\sigma_m) = (-1)^m, \qquad \mathrm{sgn}\, M_n(-1/\sigma_m) = (-1)^n \cdot (-(-1)^m) = (-1)^{n + m + 1}.$$
By the Intermediate Value Theorem:
1. $M_n(0) = 1 > 0$ and $M_n(-\sigma_1), \dots, M_n(-\sigma_K)$ alternate in sign, giving $K$ roots in $(-\sigma_K, 0)$.
2. $M_n(-1/\sigma_K), \dots, M_n(-1/\sigma_1)$ alternate in sign, giving $K - 1$ roots in $(-1/\sigma_1, -1/\sigma_K)$.
3. When $n$ is even, $\sigma_K < 1 < 1/\sigma_K$ and $(-1)^K = -(-1)^{n + K + 1}$, giving one additional root in $(-1/\sigma_K, -\sigma_K)$. (When $n$ is odd, $K + (K - 1) = n - 2$ already accounts for all $n - 2$ negative roots.)
4. Since $M_n(1) = 1 > 0$ and the leading coefficient $n + 2 - 2^n$ is negative, $M_n(z) \to -\infty$ as $z \to +\infty$, giving a root in $(1, \infty)$.

The intervals are pairwise disjoint and yield $(n - 2) + 1 = n - 1 = \deg M_n$ distinct real roots. $\square$

## 4. Two Analytic Representations of $A_n(-\sigma)$

1. **Euler's alternating series:** For $|z| < 1$, $\sum_{k=0}^{\infty} (k + 1)^n z^k = A_n(z) / (1 - z)^{n+1}$ (by induction from $A_{n+1}(z) = (1 + nz) A_n(z) + z(1 - z) A_n'(z)$). Hence for $0 < \sigma < 1$,
   $$A_n(-\sigma) = (1 + \sigma)^{n + 1} \sum_{k=0}^{\infty} (-1)^k T_k, \qquad T_k = (k + 1)^n \sigma^k.$$
2. **Polylogarithm pole expansion:** Define $\mathrm{Li}_{-n}(s) = s A_n(s) / (1 - s)^{n+1}$, which equals $\sum_{k=1}^{\infty} k^n s^k$ for $|s| < 1$ and satisfies $\frac{d}{d\mu} \mathrm{Li}_{-n}(e^\mu) = \mathrm{Li}_{-(n+1)}(e^\mu)$. By Euler's partial-fraction expansion $\pi^2 / \sin^2(\pi x) = \sum_{k \in \mathbb{Z}} (x - k)^{-2}$ evaluated at $x = \mu / (2\pi i)$,
   $$\mathrm{Li}_{-1}(e^\mu) = \frac{e^\mu}{(1 - e^\mu)^2} = \frac{1}{4 \sinh^2(\mu/2)} = \sum_{k \in \mathbb{Z}} (2\pi i k - \mu)^{-2}$$
   for $\mu \notin 2\pi i \mathbb{Z}$. Differentiating termwise $n - 1$ times (with locally uniform convergence) gives
   $$\mathrm{Li}_{-n}(e^\mu) = n! \sum_{k \in \mathbb{Z}} (2\pi i k - \mu)^{-(n + 1)}.$$
   For $\sigma \in (0, 1]$, set $L = -\ln \sigma \ge 0$ and $\mu = -L + i\pi$. Pairing $2k + 1$ with $-(2k + 1)$ yields
   $$\mathrm{Li}_{-n}(-\sigma) = 2\, n! \sum_{\substack{j \ge 1 \\ j\text{ odd}}} \mathrm{Re}\bigl((L + i\pi j)^{-(n + 1)}\bigr), \qquad A_n(-\sigma) = -\frac{(1 + \sigma)^{n + 1}}{\sigma}\, \mathrm{Li}_{-n}(-\sigma).$$

## 5. Regime A: $1 \le m$, $(m + 1)^2 \le n / 4$

Set $\sigma = \varepsilon_m := (m / (m + 2))^{n/2} \in (0, 1)$ and $\rho = (1 - (m + 1)^{-2})^{n/2}$.

The consecutive ratio $T_{k+1} / T_k = ((k + 2)/(k + 1))^n \sigma$ is strictly decreasing in $k$. At $k = m$ it equals $\rho < 1$, while $T_{m-1} / T_m = (m / (m + 1))^n / \sigma = \rho < 1$. Hence $T_k$ strictly decreases in both directions away from $k = m$ and tends to $0$. By the alternating-series bound applied to both tails $k > m$ and $k < m$,
$$(-1)^m \sum_{k=0}^{\infty} (-1)^k T_k \ge T_m - T_{m-1} - T_{m+1} = T_m (1 - 2\rho).$$
Since $(m + 1)^2 \le n / 4$, we have $\rho \le \exp(-n / (2(m + 1)^2)) \le e^{-2}$. Furthermore $T_m = c_m^{n/2}$ with $c_m = (m + 1)^2 (m / (m + 2))^m$. At $m = 1$, $c_1 = 4/3 > 1.21$; for $m \ge 2$, using $\ln(1 - t) \ge -t / (1 - t)$ at $t = 2 / (m + 2)$ gives $m \ln(m / (m + 2)) \ge -2$, so $c_m \ge (m + 1)^2 e^{-2} \ge 9 e^{-2} > 1.21$. Since $(1 + \sigma)^{n+2} > 1$, for every $n \ge 64$ we obtain
$$(-1)^m (1 + \sigma) A_n(-\sigma) > T_m (1 - 2\rho) \ge 1.21^{32} (1 - 2 e^{-2}) > 320 > 1.$$

## 6. Regime B: $(m + 1)^2 > n / 4$, $m \le K$

Set $\theta = (m + 1)\pi / (n + 1) \in (0, \pi / 2]$, $L = \pi \cot \theta \ge 0$, and $\sigma = e^{-L} \in (0, 1]$. Note that $\sigma = 1$ occurs if and only if $n$ is odd and $m = K = (n - 1) / 2$; for even $n$, $\sigma_K < 1$.

Write $L + i\pi = r e^{i\theta}$ with $r = \pi / \sin \theta$. Then $\mathrm{Re}((L + i\pi)^{-(n+1)}) = r^{-(n+1)} \cos((m + 1)\pi) = (-1)^{m+1} r^{-(n+1)}$, and for every odd $j \ge 3$,
$$\frac{|L + i\pi j|^{-(n+1)}}{r^{-(n+1)}} = \bigl(1 + (j^2 - 1) u\bigr)^{-N} =: t_j, \qquad u = \sin^2 \theta, \quad N = \frac{n + 1}{2}.$$
Setting $\tau = \sum_{j \ge 3\text{ odd}} t_j$, the pole expansion gives
$$(-1)^m (1 + \sigma) A_n(-\sigma) \ge \frac{(1 + \sigma)^{n+2}}{\sigma} \cdot 2\, n!\, r^{-(n+1)} (1 - \tau).$$

**Tail bound.** By Jordan's inequality $\sin \theta \ge 2\theta / \pi$ on $[0, \pi/2]$, we have $u \ge 4(m + 1)^2 / (n + 1)^2 > n / (n + 1)^2$. Let $v = 8u$ and $a = v / (1 + v) \in (0, 1)$. Then:
- Since $\ln(1 + v) \ge v / (1 + v) = a$, $t_3 = (1 + v)^{-N} \le e^{-Na}$.
- For $j \ge 5$, $j^2 - 1 \ge \frac{8}{9} j^2$ and $t_j$ decreases, so
  $$\sum_{\substack{j \ge 5 \\ j\text{ odd}}} t_j \le \frac{1}{2} \int_3^{\infty} \left(1 + \frac{8}{9} x^2 u\right)^{-N} dx = \frac{3}{2} \int_1^{\infty} (1 + v y^2)^{-N} dy.$$
- For $y \ge 1$, $f(w) = \ln(1 + v e^w)$ satisfies $f'(w) = \frac{v e^w}{1 + v e^w} \ge \frac{v}{1 + v} = a$, hence $\ln(1 + v y^2) \ge \ln(1 + v) + 2a \ln y$, giving $(1 + v y^2)^{-N} \le (1 + v)^{-N} y^{-2Na}$. Thus for $2Na > 1$,
  $$\tau \le e^{-Na} \left(1 + \frac{3}{2(2Na - 1)}\right).$$

Since $Na = \frac{n + 1}{2} \cdot \frac{8u}{1 + 8u}$ is increasing in $u$ and $u > n / (n + 1)^2$,
$$Na > \beta_n := \frac{4n(n + 1)}{(n + 1)^2 + 8n}.$$
For $n \ge 64$, $\beta_n$ is increasing and $\beta_n \ge \beta_{64} = 16640 / 4737 > 3.5127$, whence $\tau \le 0.038$.

**Magnitude bound.** By the binomial theorem and AM–GM, for every $\sigma > 0$ and $n \ge 1$,
$$\frac{(1 + \sigma)^{n+2}}{\sigma} \ge \frac{1}{\sigma} + (n + 2) + \frac{(n + 2)(n + 1)}{2} \sigma \ge (n + 2) + \sqrt{2(n + 2)(n + 1)} > 2(n + 1).$$
Also $r = \pi / \sin \theta < \pi (n + 1) / \sqrt{n}$. Combining these with Stirling's lower bound $n! \ge \sqrt{2\pi n} (n / e)^n$, it suffices that
$$\Phi(n) := 4(1 - 0.038)(n + 1)\sqrt{2\pi n} \left(\frac{n}{e}\right)^n \left(\frac{\sqrt{n}}{\pi(n + 1)}\right)^{n+1} > 1.$$
Using $\ln(n + 1) \le \ln n + 1 / n$,
$$\ln \Phi(n) \ge \frac{n}{2}(\ln n - 2 - 2\ln \pi) + \frac{1}{2}\ln(2\pi) - \ln \pi - 1 + \ln(3.848) + \ln\!\left(\frac{n + 1}{n}\right) \cdot 0 \quad (\text{exact: } \ln(n+1) - (n+1)\ln(n+1) = -n\ln(n+1)).$$
Specifically, since $(n + 1) \cdot (\frac{\sqrt{n}}{\pi(n+1)})^{n+1} = \frac{n^{(n+1)/2}}{\pi^{n+1}(n+1)^n}$ and $n\ln(n + 1) \le n\ln n + 1$,
$$\ln \Phi(n) \ge \frac{n}{2}(\ln n - 2 - 2\ln \pi) + \ln(3.848) + \frac{1}{2}\ln(2\pi) - \ln \pi - 1 + \ln n.$$
Wait: checking powers of $n$ directly:
$$\Phi(n) = 3.848 \sqrt{2\pi}\, \frac{n^{n + 1/2}}{e^n} \cdot \frac{n^{(n+1)/2}}{\pi^{n+1}(n + 1)^n} = \frac{3.848 \sqrt{2\pi}}{\pi} \cdot \left(\frac{n}{n + 1}\right)^n \cdot n \cdot \left(\frac{\sqrt{n}}{e\pi}\right)^n.$$
Since $(n / (n + 1))^n > e^{-1}$ for all $n \ge 1$ (as $(1 + 1/n)^n < e$) and $\sqrt{n} / (e\pi)$ is increasing, $\frac{3.848 \sqrt{2\pi}}{e\pi} \cdot n \cdot (\frac{\sqrt{n}}{e\pi})^n$ is strictly increasing for $n \ge 64$; at $n = 64$, $\sqrt{64} / (e\pi) = 8 / (e\pi) \approx 0.9368$, wait: let's check $(n/(n+1))^n$:
At $n = 64$, $(64 / 65)^{64} = 0.3707$, $64 \cdot 0.9368^{64} = 64 \cdot 0.0154 = 0.985$, times $\frac{3.848 \sqrt{2\pi}}{\pi} = 3.070$ gives $3.070 \cdot 0.3707 \cdot 0.985 = 1.121 > 1$!! And for $n \ge 64$, the derivative of $\frac{n}{2}(\ln n - 2 - 2\ln\pi) + \ln n$ is $\frac{1}{2}(\ln n - 1 - 2\ln\pi) + \frac{1}{n} > \frac{1}{2}(\ln 64 - 1 - 2\ln\pi) > 0.43 > 0$, so $\ln \Phi(n)$ is strictly increasing for all $n \ge 64$ and $\ln \Phi(64) > 0.109 > 0$! Hence $(-1)^m(1 + \sigma) A_n(-\sigma) > 1$ for every $n \ge 64$.

## 7. Ordering of Test Points and Finite Range

Within Regime A, $\varepsilon_m = (m / (m + 2))^{n/2}$ is strictly increasing in $m$. Within Regime B, $\theta = (m + 1)\pi / (n + 1)$ increases in $(0, \pi / 2]$, so $\cot \theta$ strictly decreases and $\sigma^B_m = e^{-\pi \cot \theta}$ strictly increases.

At the junction $m_0 = \max\{m : (m + 1)^2 \le n / 4\}$ (note $1 \le m_0 < K$ for $n \ge 64$), using $\ln(1 + y) \ge 2y / (2 + y)$ at $y = 2 / m_0$ and $\cot x < 1 / x$ on $(0, \pi / 2]$,
$$-\ln \varepsilon_{m_0} = \frac{n}{2} \ln\!\left(1 + \frac{2}{m_0}\right) \ge \frac{n}{m_0 + 1} \ge \frac{n + 1}{m_0 + 2} > \pi \cot\!\left(\frac{(m_0 + 2)\pi}{n + 1}\right) = -\ln \sigma^B_{m_0 + 1},$$
where the middle inequality holds because $n \ge m_0 + 1$. Thus $\varepsilon_{m_0} < \sigma^B_{m_0 + 1}$.

By Lemma 3.1, Conjecture 6.16 holds for every $n \ge 64$. For every $3 \le n \le 63$, exact integer Sturm sequences (`verify.py` §3) certify that $M_n$ is squarefree with $n - 2$ negative roots and one root in $(1, \infty)$ (verified in fact through $n \le 99$). $\square$
