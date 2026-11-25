# Chamber Uniqueness of Singer Golomb Rulers (`arXiv:2611.22656`)

We prove the **Singer Chamber-Uniqueness Conjecture** posed by Esther Notik (*Golomb rulers with real marks: the real and integer optima agree up to ten marks*, `arXiv:2611.22656`, November 2026, Section 7):

> *"For every prime power $m$, every Singer ruler is the only shortest point of its chamber."*

In fact, we prove a slightly stronger statement: for **every cyclic perfect difference set** $D \subset \mathbb{Z}/N\mathbb{Z}$ with at least two marks, cutting at its (unique) largest cyclic gap produces an integer Golomb ruler $x$ such that **every** anchored ruler $y$ in the real $1$-separated chamber of $x$ has every successive mark gap at least as large as the corresponding gap of $x$. Consequently, $x$ is the unique shortest point of its chamber, certified by an explicit full-rank integer dual weighting with no linear programming required.

---

## 1. Notation and Definitions

*(Notation comparison with `arXiv:2611.22656`: Notik writes $m$ for the prime power, $q = m^2 + m + 1$ for the modulus, and $n = m + 1$ for the number of marks, expressing chambers in gap coordinates $g_i = y_{i+1} - y_i$. Below we write $N$ for the general modulus of a cyclic perfect difference set on $n \ge 2$ marks — so $N = m^2 + m + 1$ and $n = m + 1$ for Singer sets — and work equivalently in mark coordinates $y = (y_1, \dots, y_n)$ anchored at $y_1 = 0$, which corresponds bijectively to gap coordinates via $g_i = y_{i+1} - y_i$.)*

Following Notik (`arXiv:2611.22656`, Definition 1 and Section 2):
- A **real ($1$-separated) Golomb ruler** on $n \ge 2$ marks is a vector $y = (y_1, \dots, y_n) \in \mathbb{R}^n$ with $0 = y_1 < y_2 < \dots < y_n$ such that:
  1. every positive pairwise difference satisfies $y_j - y_i \ge 1$ ($1 \le i < j \le n$), and
  2. every two distinct labeled positive differences satisfy $|(y_j - y_i) - (y_l - y_k)| \ge 1$.
- Given a real Golomb ruler $x$, order the $\binom{n}{2}$ index pairs $\{(i, j) : 1 \le i < j \le n\}$ by increasing value of $x_j - x_i$. Write $\Delta_r(y) := y_{j_r} - y_{i_r}$ for the labeled difference of rank $r \in \{1, \dots, \binom{n}{2}\}$, and put $\Delta_0(y) := 0$.
- The **closed chamber** of $x$ (anchored at $y_1 = 0$) consists of all $y \in \mathbb{R}^n$ with $y_1 = 0$ satisfying
  $$\Delta_r(y) - \Delta_{r-1}(y) \ge 1 \qquad \text{for all } 1 \le r \le \binom{n}{2}. \tag{1}$$
  *(This coincides with Notik's polyhedron $P_\sigma$ in gap coordinates: the consecutive-rank rows (1) are themselves rows of $P_\sigma$, and summing consecutive rows yields every non-consecutive separation inequality $\Delta_s(y) - \Delta_r(y) \ge s - r \ge 1$ for $s > r$, as well as $\Delta_r(y) \ge r \ge 1$.)*
- A subset $D \subset \mathbb{Z}/N\mathbb{Z}$ ($n = |D| \ge 2$) is a **cyclic perfect difference set** if every nonzero residue $r \in (\mathbb{Z}/N\mathbb{Z}) \setminus \{0\}$ has a unique representation $r = b - a$ with $a, b \in D$ ($a \neq b$). Every Singer difference set of prime-power order $m$ ($n = m + 1$ marks modulo $N = m^2 + m + 1$), together with every unit multiple $t \cdot D$ ($\gcd(t, N) = 1$) and translate $D + c$, is a cyclic perfect difference set.

---

## 2. Main Theorem and Proof

**Theorem.** *Let $D \subset \mathbb{Z}/N\mathbb{Z}$ be a cyclic perfect difference set with $n = |D| \ge 2$ marks. Let $G$ be the largest clockwise cyclic gap between consecutive marks of $D$ on $\mathbb{Z}/N\mathbb{Z}$. Cutting the cycle at $G$ and translating the following mark to $0$ yields a unique integer Golomb ruler $0 = x_1 < x_2 < \dots < x_n = L := N - G$ with successive gaps $h_i := x_{i+1} - x_i$ ($1 \le i \le n - 1$). Then:*
1. *$x$ is a real $1$-separated Golomb ruler lying in its own chamber;*
2. *for every anchored point $y = (0 = y_1, y_2, \dots, y_n)$ in the chamber of $x$, every successive gap satisfies*
   $$y_{i+1} - y_i \ge h_i \qquad (1 \le i \le n - 1);$$
3. *consequently $y_n \ge L$, with equality $y_n = L$ if and only if $y = x$.*

*In particular, for every prime power $m$, every Singer ruler (cut at its largest gap, for any unit multiplier and translate) is the unique shortest point of its chamber.*

### Proof

**Step 1 (Uniqueness of the largest cyclic gap).** Order $D$ cyclically as $a_1, a_2, \dots, a_n \in \mathbb{Z}/N\mathbb{Z}$ with clockwise cyclic gap lengths $g_1, \dots, g_n \in \{1, \dots, N - 1\}$ summing to $N$. Each cyclic gap $g_i$ is represented modulo $N$ by the oriented pair $(a_i, a_{i+1})$ (indices modulo $n$). Because $D$ is a cyclic perfect difference set, distinct oriented pairs represent distinct nonzero residues modulo $N$. Therefore $g_1, \dots, g_n$ are pairwise distinct. In particular, the largest cyclic gap $G := \max_i g_i$ is **unique**, and after cutting at $G$ and translating the following mark to $0$, the integer marks $0 = x_1 < x_2 < \dots < x_n = L := N - G$ have consecutive gaps
$$1 \le h_i := x_{i+1} - x_i < G \qquad (1 \le i \le n - 1), \qquad \sum_{i=1}^{n-1} h_i = L.$$
Moreover, all $\binom{n}{2}$ positive ordinary differences $x_j - x_i \in \{1, \dots, L\}$ ($1 \le i < j \le n$) are distinct, because they are distinct modulo $N$ (as $L < N$). Thus $x$ is an integer (hence real $1$-separated) Golomb ruler and lies in its own chamber.

**Step 2 (All integers $1, \dots, G - 1$ appear as positive differences).** Fix any integer $r$ with $1 \le r \le G - 1$. Since $r \not\equiv 0 \pmod N$ and $D$ is a cyclic perfect difference set, there exists a unique ordered pair of distinct marks $(x_a, x_b)$ such that $x_b - x_a \equiv r \pmod N$. Because $x_a, x_b \in [0, L]$ and $L < N$, the ordinary integer difference $x_b - x_a$ equals either $r$ or $r - N$. However,
$$|r - N| = N - r > N - G = L,$$
whereas $|x_b - x_a| \le L$. Hence $x_b - x_a = r > 0$, so $a < b$ and $r$ occurs as an ordinary positive difference of $x$.

Since all $\binom{n}{2}$ positive ordinary differences of $x$ are distinct positive integers and include every integer in $\{1, 2, \dots, G - 1\}$, those $G - 1$ differences occupy precisely the first $G - 1$ ranks of the difference ordering of $x$:
$$\Delta_r(x) = r \qquad \text{for every } 1 \le r \le G - 1.$$

**Step 3 (Gap dominance and uniqueness).** For each $1 \le i \le n - 1$, Step 1 gives $1 \le h_i \le G - 1$, so by Step 2 the consecutive-mark label $(i, i + 1)$ has exact rank $r = h_i$ in the difference ordering of $x$, i.e., $\Delta_{h_i}(y) = y_{i+1} - y_i$.

Now let $y$ be any point in the closed chamber of $x$ anchored at $y_1 = 0$. Summing the first $h_i$ consecutive chamber inequalities (1) gives
$$y_{i+1} - y_i = \Delta_{h_i}(y) = \sum_{r=1}^{h_i} \bigl(\Delta_r(y) - \Delta_{r-1}(y)\bigr) \ge \sum_{r=1}^{h_i} 1 = h_i \qquad (1 \le i \le n - 1). \tag{2}$$
Summing (2) over $i = 1, \dots, n - 1$ and using $y_1 = 0$ yields
$$y_n = \sum_{i=1}^{n-1} (y_{i+1} - y_i) \ge \sum_{i=1}^{n-1} h_i = L = x_n.$$
Equality $y_n = L$ forces equality in every single bound (2), i.e., $y_{i+1} - y_i = h_i = x_{i+1} - x_i$ for all $1 \le i \le n - 1$. Since $y_1 = 0 = x_1$, induction gives $y_i = x_i$ for every $i$, so $y = x$. $\blacksquare$

---

## 3. Explicit Full-Rank Integer Dual Certificate

Put $H := \max_{1 \le i \le n-1} h_i < G$. Assigning the rank-$r$ chamber inequality $\Delta_r(y) - \Delta_{r-1}(y) \ge 1$ the nonnegative integer dual weight
$$\lambda_r := \#\{1 \le i \le n - 1 : h_i \ge r\} \qquad (1 \le r \le H)$$
(and $\lambda_r = 0$ for $r > H$) gives an explicit LP dual certificate:
- Every supported row ($1 \le r \le H$) is tight at $x$ ($\Delta_r(x) - \Delta_{r-1}(x) = r - (r - 1) = 1$).
- The weighted sum of the left-hand sides telescopes identically to
  $$\sum_{r=1}^H \lambda_r \bigl(\Delta_r(y) - \Delta_{r-1}(y)\bigr) = \sum_{i=1}^{n-1} \sum_{r=1}^{h_i} \bigl(\Delta_r(y) - \Delta_{r-1}(y)\bigr) = \sum_{i=1}^{n-1} (y_{i+1} - y_i) = y_n - y_1.$$
- The weighted sum of the right-hand sides equals $\sum_{r=1}^H \lambda_r = \sum_{i=1}^{n-1} h_i = L$.
- Each coordinate-gap functional $y_{i+1} - y_i$ is a prefix sum of the supported rows, so the supported rows have full rank $n - 1$ on $\{y : y_1 = 0\}$.
