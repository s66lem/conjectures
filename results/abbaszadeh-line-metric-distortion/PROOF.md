# Proof of the Line-Metric Distortion Conjecture of Abbaszadeh et al. (arXiv:2601.02095v1)

## Problem Statement

In *Metric Distortion with Preference Intensities* (arXiv:2601.02095v1, AAAI 2026), M. Abbaszadeh, A. Ansarifar, M. Latifian, and M. Seddighin study deterministic voting rules for elections with two alternatives $a_1, a_2$ in a metric space under mandatory preference-intensity elicitation with threshold $\alpha \in (0, 1]$. Each voter $i$ reports one of four types:

- $a_1 \succ a_2$: $d(i, a_2) \ge d(i, a_1) > \alpha\, d(i, a_2)$,
- $a_2 \succ a_1$: $d(i, a_1) \ge d(i, a_2) > \alpha\, d(i, a_1)$,
- $a_1 \gg a_2$: $d(i, a_1) \le \alpha\, d(i, a_2)$,
- $a_2 \gg a_1$: $d(i, a_2) \le \alpha\, d(i, a_1)$.

For a profile $E$ with type counts $n = (n_1, n_2, n_3, n_4)$, the worst-case distortion of alternative $c \in \{a_1, a_2\}$ on the $1$-Euclidean line is

$$\mathrm{dist}_\alpha(c, E) = \inf \left\{ t \ge 1 : \forall \text{ consistent } (a_1, a_2, x) \text{ in } \mathbb{R},\; \mathrm{SC}_x(c) \le t \min(\mathrm{SC}_x(a_1), \mathrm{SC}_x(a_2)) \right\},$$

where $\mathrm{SC}_x(a) = \sum_i |x_i - a|$. The rule $f^{\mathsf{tal}}_\alpha$ chooses the alternative with smaller worst-case distortion.

In Section 6, the authors conjecture:

> Considering elections with two alternatives and assuming that the metric is limited to the $1$-Euclidean space, we have
> $$\mathrm{dist}_\alpha(f^{\mathsf{tal}}_\alpha) = \max\!\left(\frac{3 - \alpha}{1 + \alpha},\, 2\alpha + 1\right).$$

## Main Theorem

**Theorem.** Fix $\alpha \in (0, 1]$ and set $M(\alpha) := \max\bigl(\frac{3 - \alpha}{1 + \alpha},\, 1 + 2\alpha\bigr)$. On two-alternative elections in $\mathbb{R}$ under mandatory elicitation:

1. For every profile $E$, $\min(\mathrm{dist}_\alpha(a_1, E), \mathrm{dist}_\alpha(a_2, E)) \le M(\alpha)$.
2. Every deterministic voting rule has worst-case distortion at least $M(\alpha)$, witnessed by the symmetric two-voter profiles $(a_1 \succ a_2, a_2 \succ a_1)$ for $\alpha < 1$ (distortion $\frac{3 - \alpha}{1 + \alpha}$) and $(a_1 \gg a_2, a_2 \gg a_1)$ for all $\alpha \in (0, 1]$ (distortion $1 + 2\alpha$).

Consequently, $\mathrm{dist}_\alpha(f^{\mathsf{tal}}_\alpha) = M(\alpha)$ and $f^{\mathsf{tal}}_\alpha$ is optimal among all deterministic rules.

## Complete Proof

### Step 1: Affine Normalization and Linearization

Fix $t \ge 1$. Because $\mathrm{SC}_x(a) \ge 0$, the condition $\mathrm{SC}_x(a_1) \le t \min(\mathrm{SC}_x(a_1), \mathrm{SC}_x(a_2))$ is equivalent to $\mathrm{SC}_x(a_1) \le t\,\mathrm{SC}_x(a_2)$. If $a_1 = a_2$, then $\mathrm{SC}_x(a_1) = \mathrm{SC}_x(a_2)$, so this holds trivially. Otherwise $s := a_2 - a_1 \ne 0$, and the affine rescaling $y_i := (x_i - a_1)/s$ maps $(a_1, a_2)$ to $(0, 1)$, preserves every preference predicate, and scales both social costs by $|s|^{-1}$. Thus $\mathrm{dist}_\alpha(a_1, E) \le t$ if and only if

$$\sum_{i=1}^N g_t(y_i) \le 0 \qquad \text{for every consistent } y \in \mathbb{R}^N \text{ with } (a_1, a_2) = (0, 1),$$

where $g_t(y) := |y| - t|y - 1|$.

### Step 2: Per-Agent Upper Bounds

Let $t \ge 1$ and $y \in \mathbb{R}$. Set $u_t := \frac{1 - t\alpha}{1 + \alpha}$ and, when $\alpha < 1$, $v_t := \frac{1 - t\alpha}{1 - \alpha}$.

1. **Type $a_1 \succ a_2$ ($|y| \le |y - 1|$):** By the triangle inequality, $1 \le |y| + |y - 1| \le 2|y - 1|$, so $|y - 1| \ge \frac{1}{2}$. Since $1 - t \le 0$,
   $$g_t(y) \le (1 - t)|y - 1| \le \frac{1 - t}{2}.$$
2. **Type $a_1 \gg a_2$ ($|y| \le \alpha|y - 1|$):** By the triangle inequality, $1 \le |y| + |y - 1| \le (1 + \alpha)|y - 1|$, so $|y - 1| \ge \frac{1}{1 + \alpha}$. Since $\alpha - t \le 0$,
   $$g_t(y) \le (\alpha - t)|y - 1| \le \frac{\alpha - t}{1 + \alpha}.$$
3. **Type $a_2 \gg a_1$:** By the triangle inequality, $|y| \le |y - 1| + 1$. Since $t \ge 1$,
   $$g_t(y) \le |y| - |y - 1| \le 1.$$
4. **Type $a_2 \succ a_1$ ($\alpha|y| < |y - 1| \le |y|$):**
   - If $\alpha = 1$, this condition is unsatisfiable.
   - If $\alpha < 1$ and $y \le 1$, then $|y - 1| \le |y|$ forces $y \ge 0$, so $\alpha y < 1 - y$, i.e., $y < \frac{1}{1 + \alpha}$. Since $1 + t > 0$,
     $$g_t(y) = y - t(1 - y) = (1 + t)y - t \le \frac{1 + t}{1 + \alpha} - t = u_t.$$
   - If $\alpha < 1$ and $y > 1$, then $\alpha y < y - 1$, i.e., $y > \frac{1}{1 - \alpha}$. Since $1 - t \le 0$,
     $$g_t(y) = y - t(y - 1) = (1 - t)y + t \le \frac{1 - t}{1 - \alpha} + t = v_t.$$
   Hence $g_t(y) \le \max(u_t, v_t)$.

### Step 3: Pairing Inequality and Upper Bound

For $\alpha \in (0, 1)$, define the two linear forms on $n = (n_1, n_2, n_3, n_4) \in \mathbb{R}_{\ge 0}^4$:

$$B_t^{(1)}(n) := \frac{1 - t}{2} n_1 + u_t n_2 + \frac{\alpha - t}{1 + \alpha} n_3 + n_4, \qquad B_t^{(2)}(n) := \frac{1 - t}{2} n_1 + v_t n_2 + \frac{\alpha - t}{1 + \alpha} n_3 + n_4.$$

By Step 2, $\sum_i g_t(y_i) \le \max(B_t^{(1)}(n), B_t^{(2)}(n))$ for every consistent normalized placement $y$. Thus $B_t^{(1)}(n) \le 0 \land B_t^{(2)}(n) \le 0$ implies $\mathrm{dist}_\alpha(a_1, E) \le t$. By swapping the labels of $a_1$ and $a_2$, letting $\sigma(n) := (n_2, n_1, n_4, n_3)$, $B_t^{(1)}(\sigma n) \le 0 \land B_t^{(2)}(\sigma n) \le 0$ implies $\mathrm{dist}_\alpha(a_2, E) \le t$.

Now set $t = M := M(\alpha)$. For every pair $(i, j) \in \{1, 2\}^2$, the sum $B_M^{(i)}(n) + B_M^{(j)}(\sigma n)$ has coefficients:

- on $n_3$ and $n_4$: $\frac{\alpha - M}{1 + \alpha} + 1 = \frac{1 + 2\alpha - M}{1 + \alpha} \le 0$, since $M \ge 1 + 2\alpha$;
- on $n_1$ and $n_2$: $\frac{1 - M}{2} + w$ with $w \in \{u_M, v_M\}$:
  - for $w = v_M$: $\frac{1 - M}{2} + \frac{1 - M\alpha}{1 - \alpha} = \frac{(3 - \alpha) - M(1 + \alpha)}{2(1 - \alpha)} \le 0$, since $M \ge \frac{3 - \alpha}{1 + \alpha}$;
  - for $w = u_M$: $\frac{1 - M}{2} + \frac{1 - M\alpha}{1 + \alpha} = \frac{(3 + \alpha) - M(1 + 3\alpha)}{2(1 + \alpha)} \le 0$, because
    $$(3 - \alpha)(1 + 3\alpha) - (3 + \alpha)(1 + \alpha) = 4\alpha(1 - \alpha) > 0,$$
    so $M \ge \frac{3 - \alpha}{1 + \alpha} > \frac{3 + \alpha}{1 + 3\alpha}$.

Since $n_1, n_2, n_3, n_4 \ge 0$, every paired sum $B_M^{(i)}(n) + B_M^{(j)}(\sigma n)$ is $\le 0$. Therefore it is impossible for $\max(B_M^{(1)}(n), B_M^{(2)}(n)) > 0$ and $\max(B_M^{(1)}(\sigma n), B_M^{(2)}(\sigma n)) > 0$ to hold simultaneously. Hence at least one alternative has distortion $\le M(\alpha)$.

When $\alpha = 1$, we have $M(1) = 3$. If the profile contains any voter of type $a_1 \succ a_2$ or $a_2 \succ a_1$, no consistent placement exists and both alternatives vacuously satisfy the bound. Otherwise $n_1 = n_2 = 0$, and Step 2 gives $\sum_i g_3(y_i) \le -n_3 + n_4$ for $a_1$ and $-n_4 + n_3$ for $a_2$; at least one of these is $\le 0$.

### Step 4: Tightness and Universal Lower Bound

1. **Intense profile $E_{\mathrm{int}} = (a_1 \gg a_2, a_2 \gg a_1)$ (all $\alpha \in (0, 1]$):**
   Place $a_1 = 0, a_2 = 1$ and $x = \bigl(\frac{\alpha}{1 + \alpha}, 1\bigr)$. Both preferences hold ($|x_1| = \alpha|x_1 - 1|$ and $|x_2 - 1| = 0 \le \alpha|x_2|$), while $\mathrm{SC}_x(0) = \frac{1 + 2\alpha}{1 + \alpha}$ and $\mathrm{SC}_x(1) = \frac{1}{1 + \alpha}$, giving ratio $1 + 2\alpha$. By symmetry, $\mathrm{dist}_\alpha(a_1, E_{\mathrm{int}}) = \mathrm{dist}_\alpha(a_2, E_{\mathrm{int}}) = 1 + 2\alpha$.

2. **Normal profile $E_{\mathrm{norm}} = (a_1 \succ a_2, a_2 \succ a_1)$ ($\alpha \in (0, 1)$):**
   For any $t < \frac{3 - \alpha}{1 + \alpha}$, set $\delta := \frac{(3 - \alpha) - t(1 + \alpha)}{2(1 - \alpha)} > 0$ and $\varepsilon := \frac{\delta}{2(|t| + 1)} > 0$. Place $a_1 = 0, a_2 = 1$ and $x = \bigl(\frac{1}{2}, \frac{1}{1 - \alpha} + \varepsilon\bigr)$. Both preferences strictly hold, $\mathrm{SC}_x(1) < \mathrm{SC}_x(0)$, and
   $$\mathrm{SC}_x(0) - t\,\mathrm{SC}_x(1) = \delta + (1 - t)\varepsilon \ge \delta - \frac{\delta}{2} = \frac{\delta}{2} > 0.$$
   Hence no $t < \frac{3 - \alpha}{1 + \alpha}$ bounds the distortion of $a_1$ (or, by symmetry, $a_2$). Combining with Step 2 at $t = \frac{3 - \alpha}{1 + \alpha}$ yields $\mathrm{dist}_\alpha(a_1, E_{\mathrm{norm}}) = \mathrm{dist}_\alpha(a_2, E_{\mathrm{norm}}) = \frac{3 - \alpha}{1 + \alpha}$.

Thus every deterministic voting rule suffers distortion at least $\max\bigl(\frac{3 - \alpha}{1 + \alpha}, 1 + 2\alpha\bigr) = M(\alpha)$ (at $\alpha = 1$, $M(1) = 3 = 1 + 2\cdot 1$ is already attained by $E_{\mathrm{int}}$), and $f^{\mathsf{tal}}_\alpha$ attains $M(\alpha)$ exactly.

## Verification

- Lean 4 formalization: [AbbaszadehLineMetricDistortion.lean](file:///C:/Users/s6lem/.t3/projects/conjectures/lean/Conjectures/AbbaszadehLineMetricDistortion.lean)
- Standalone rational-arithmetic verifier: [verify.py](file:///C:/Users/s6lem/.t3/projects/conjectures/results/abbaszadeh-line-metric-distortion/verify.py)
