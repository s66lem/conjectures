# Complete Proof of Conjecture 7.4 of Gil–Liang–Odetola–Weiner (`arXiv:2609.01562v1`)

## Conjecture Statement

In *Points of maximal traffic on a grid with obstruction* ([arXiv:2609.01562v1](https://arxiv.org/abs/2609.01562), Section 7), Juan Gil, Zhenni Liang, Ayodeji Odetola, and Michael Weiner study the maximum of the lattice-path traffic function $f_B$ on $\mathrm{Grid}(n) \setminus \{(0,0),(n,n)\}$ when a single obstruction $B = (a, n-a)$ lies on the antidiagonal $x+y=n$. For $n \ge 2$ and $1 \le a < n/2$, they define
$$D(n) := \frac{1}{n}\binom{2n-2}{n-1}, \qquad G(n,a) := \frac{n-2a+1}{n-a}\binom{n}{a}\binom{n-2}{a-1},$$
$$R_n(a) := \frac{G(n,a)}{D(n)}, \qquad \rho(n) := \max_{1 \le a < n/2} R_n(a).$$

By Propositions 7.1–7.2, Lemma 2.1, Theorem 5.1, and Section 6 of `arXiv:2609.01562v1`, for every $n \ge 9$ and every antidiagonal obstruction $B = (a, n-a)$ ($1 \le a < n/2$), one has $f_B(1,0) - f_B(1,1) = G(n,a) - D(n)$, so the maximum of $f_B$ is attained at $(1,1)$ and $(n-1,n-1)$ if and only if $R_n(a) < 1$ (the boundary cases $a \in \{0, n\}$ and midpoint $2a = n$ already attain their maxima at $(1,1)$ and $(n-1,n-1)$, and $n/2 < a \le n-1$ follows by reflection).

**Conjecture 7.4 (`arXiv:2609.01562v1`).** *For every $n \ge 496$ and every obstruction $B$ on the antidiagonal $x+y=n$, the maximum of $f_B$ is attained at $(1,1)$ and $(n-1,n-1)$. Equivalently, $\rho(n) < 1$ for all $n \ge 496$.*

The threshold $496$ is sharp: $R_{495}(240) \approx 1.0000240709 > 1$.

## Main Theorem

**Theorem 1.** *For every integer $n \ge 496$ and every integer $a$ with $1 \le a < n/2$, we have $R_n(a) < 1$ (equivalently $2(2n-1)a(n-2a+1)\binom{n}{a}^2 < n(n-1)\binom{2n}{n}$). Consequently, Conjecture 7.4 holds for all $n \ge 496$.*

## Proof

Asymptotically $\rho(n) \to \sqrt{8/(\pi e)} \approx 0.96788 < 1$. Our proof avoids Stirling's approximation, $\pi$, and Wallis limits, splitting into an elementary analytic bound for $n \ge 800$ and a unimodal peak certificate for $496 \le n \le 799$.

### Lemma 1 (Exact Refactorization)

For every $n \ge 2$ and $1 \le a < n/2$, let $m = \lfloor n/2 \rfloor$, $d = n - 2a \ge 1$, and $W(n) = \binom{n}{m}^2 / \binom{2n}{n}$. Then
$$R_n(a) = \frac{2(2n-1)\,a\,(n-2a+1)}{n(n-1)}\frac{\binom{n}{a}^2}{\binom{2n}{n}} = \frac{2n-1}{n-1}\cdot \frac{(n-d)(d+1)}{n}\cdot W(n)\cdot \left(\frac{\binom{n}{a}}{\binom{n}{m}}\right)^2.$$

*Proof.* By the binomial absorption identities $\binom{n-2}{a-1} = \frac{a(n-a)}{n(n-1)}\binom{n}{a}$ and $\binom{2n-2}{n-1} = \frac{n}{2(2n-1)}\binom{2n}{n}$, we obtain $G(n,a) = \frac{a(n-2a+1)}{n(n-1)}\binom{n}{a}^2$ and $D(n) = \frac{1}{2(2n-1)}\binom{2n}{n}$. Substituting $2a = n - d$ and multiplying and dividing by $\binom{n}{m}^2$ gives the second identity. $\square$

### Lemma 2 (Central Binomial Ratio Bound)

For every integer $n \ge 200$,
$$(n+1)\,W(n)^2 \le 201\,W(200)^2 < \frac{51}{40}.$$

*Proof.*
1. For even $n = 2m$ ($m \ge 1$), the recurrences $\binom{2m+2}{m+1} = \frac{2(2m+1)}{m+1}\binom{2m}{m}$ and $\binom{4m+4}{2m+2} = \frac{2(4m+3)(4m+1)}{(m+1)(2m+1)}\binom{4m}{2m}$ yield
   $$\frac{(2m+3)\,W(2m+2)^2}{(2m+1)\,W(2m)^2} = \frac{4(2m+3)(2m+1)^5}{(m+1)^2(4m+1)^2(4m+3)^2}.$$
   With $u = m - 1 \ge 0$, denominator minus numerator equals $32u^4 + 160u^3 + 281u^2 + 196u + 40 > 0$, so $(2m+1)W(2m)^2$ is strictly decreasing in $m \ge 1$.
2. For odd $n = 2m+1$ ($m \ge 0$), $\binom{2m+1}{m} = \frac{2m+1}{m+1}\binom{2m}{m}$ and $\binom{4m+2}{2m+1} = \frac{2(4m+1)}{2m+1}\binom{4m}{2m}$ give
   $$\frac{(2m+2)\,W(2m+1)^2}{(2m+1)\,W(2m)^2} = \frac{(2m+1)^5}{2(m+1)^3(4m+1)^2},$$
   whose denominator minus numerator is $32m^4 + 66m^3 + 46m^2 + 12m + 1 > 0$.
3. At $n = 200$, exact integer arithmetic confirms $40 \cdot 201 \cdot \binom{200}{100}^4 < 51 \cdot \binom{400}{200}^2$. $\square$

### Lemma 3 (Exponential Tail Bound)

For all $x \ge 0$, $\frac{1-x}{1+x} \le e^{-2x}$. Consequently, for every $n \ge 2$ and $1 \le a \le m = \lfloor n/2 \rfloor$ with $d = n - 2a$,
$$\left(\frac{\binom{n}{a}}{\binom{n}{m}}\right)^2 \le \exp\!\left(-\frac{d^2 - 1}{n + 1}\right).$$

*Proof.* Set $g(x) = (1+x)e^{-2x} - (1-x)$. Then $g(0) = 0$ and $g'(x) = 1 - (1+2x)e^{-2x} \ge 0$ for $x \ge 0$ since $1+2x \le e^{2x}$, so $g(x) \ge 0$. Applying this inductively to $k = m - a \ge 0$:
- For $n = 2m$ ($d = 2k$), $\frac{\binom{2m}{m-k}}{\binom{2m}{m}} = \prod_{j=1}^k \frac{1 - (2j-1)/(2m+1)}{1 + (2j-1)/(2m+1)} \le \exp\!\left(-\frac{2k^2}{2m+1}\right)$, whose square is $\exp\!\left(-\frac{d^2}{n+1}\right) \le \exp\!\left(-\frac{d^2-1}{n+1}\right)$.
- For $n = 2m+1$ ($d = 2k+1$), $\frac{\binom{2m+1}{m-k}}{\binom{2m+1}{m}} = \prod_{j=1}^k \frac{1 - 2j/(2m+2)}{1 + 2j/(2m+2)} \le \exp\!\left(-\frac{2k(k+1)}{2m+2}\right)$, whose square is $\exp\!\left(-\frac{d^2-1}{n+1}\right)$. $\square$

### Lemma 4 (Quadratic-Exponential Bound)

For every $t \in \mathbb{R}$ and every $\varepsilon > 0$,
$$\bigl(t + \varepsilon(1 - t^2)\bigr)e^{-t^2} \le e^{-1/2}\left(\frac{1}{\sqrt{2}} + \frac{\varepsilon}{2} + 2\varepsilon^2\right).$$

*Proof.* Put $c = \frac{1}{\sqrt{2}} + \frac{\varepsilon}{2} + 2\varepsilon^2 > 0$. Expanding directly gives
$$2c^2 - 2c\varepsilon - 4\varepsilon^2 = 1 + \left(4\sqrt{2} - \frac{9}{2}\right)\varepsilon^2 + 8\varepsilon^4 > 1,$$
so $4(c+\varepsilon)\bigl((c+\varepsilon)t^2 - t + (\frac{c}{2} - \varepsilon)\bigr) = (2(c+\varepsilon)t - 1)^2 + (2c^2 - 2c\varepsilon - 4\varepsilon^2 - 1) \ge 0$, whence $t + \varepsilon(1-t^2) \le c(t^2 + \frac{1}{2}) \le c\,e^{t^2 - 1/2}$. Multiplying by $e^{-t^2}$ finishes the lemma. $\square$

### Lemma 5 (All $n \ge 800$)

For $n \ge 800$ and $1 \le a < n/2$, put $d = n - 2a \ge 1$, $\varepsilon = (n+1)^{-1/2}$, and $t = d\varepsilon$. Then $\frac{(n-d)(d+1)}{n\sqrt{n+1}} < t + \varepsilon(1-t^2)$ (the difference is $\frac{d^2/(n+1) + d}{n\sqrt{n+1}} > 0$). Combining Lemmas 1–4 with $\frac{2n-1}{n-1} \le \frac{1599}{799}$, $\varepsilon^2 \le \frac{1}{801}$, $\varepsilon < \frac{1}{28}$, $e^{1/801} \le \frac{801}{800}$ (from $1 - \frac{1}{801} \le e^{-1/801}$), $e^{1/2} > \frac{211}{128}$ (from the 6-term Taylor sum $\frac{6331}{3840}$), and $\sqrt{2} > \frac{14142}{10000}$ gives
$$R_n(a)^2 < \left(\frac{1599}{799}\right)^2 \cdot \frac{51}{40} \cdot \left(\frac{801}{800}\right)^2 \cdot \left(\frac{128}{211}\right)^2 \cdot \left(\frac{10000}{14142} + \frac{1}{56} + \frac{2}{801}\right)^2 \approx 0.996967 < 1.$$
Thus $R_n(a) < 1$ for all $n \ge 800$ and all $1 \le a < n/2$. $\square$

### Lemma 6 (Unimodality and Finite Range $496 \le n \le 799$)

For fixed $n$ and $1 \le a < (n-1)/2$, let $F(n,a) = a(n-2a+1)\binom{n}{a}^2$. Since $(a+1)\binom{n}{a+1} = (n-a)\binom{n}{a}$,
$$F(n, a+1) \le F(n, a) \iff (n-2a-1)(n-a)^2 \le a(a+1)(n-2a+1).$$
Setting $d = n - 2a$, the identity $(d-3)(d+1) < (d-1)^2$ implies that this step inequality is monotone in $a$: once $F(n,a+1) \le F(n,a)$, it continues to hold for all larger $a < (n-1)/2$, and once $F(n,a) \le F(n,a+1)$, it holds for all smaller $a \ge 1$. Thus $F(n,a)$ is unimodal in $a$. Checking the single peak $a^*(n)$ for each $496 \le n \le 799$ (via the exact incremental binomial recurrence in Lean 4 and exhaustively over all $98{,}192$ pairs in `verify.py`) confirms $R_n(a) < 1$ throughout $[496, 799]$, with maximum $R_{497}(241) \approx 0.9999552841 < 1$. $\square$

## Formal Verification

The entire proof—including the exact paper ratio `R_paper n a = G_paper n a / D_paper n`, sharpness `1 < R_paper 495 240`, unimodality + certified 304-step kernel recurrence for $496 \le n < 800$, and Lemmas 1–5 for all $n \ge 800$—is formally verified in Lean 4 in [`lean/Conjectures/GilAntidiagonalTraffic.lean`](../../lean/Conjectures/GilAntidiagonalTraffic.lean) using only `[propext, Classical.choice, Quot.sound]`, with zero `sorry` and zero `native_decide`.
