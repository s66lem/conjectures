# Proof of Manabe's Conjecture 57 (Admissible Angle Conjecture) and Extensions

This document gives a complete, self-contained proof of **Conjecture 57** of Hikaru Manabe, *Purely Periodic Three-move Subtraction Games* (`arXiv:2609.05358v2`), in a strictly stronger form, together with its full consequence for **Conjecture 52** and **Proposition 59**, an explicit cyclic-interval characterization of $\Theta_{c+b}$, and two partial period exclusions toward **Conjecture 56**.

## 1. Setup and Verbatim Definitions

Let $1 \le a < b < c$ be integers, $S = \{a, b, c\}$, $B = \{a, b\}$, $n = a + b$, $\delta = b - a$, $\eta = \lfloor \delta / a \rfloor$, $\varepsilon = \delta \bmod a$ ($0 \le \varepsilon < a$, so $\delta = \eta a + \varepsilon$), and $\rho = c \bmod n \in \{0, \dots, n - 1\}$.

The Sprague–Grundy nim-value sequence $\mathcal{G}_S : \mathbb{N} \to \mathbb{N}$ is defined recursively by
$$\mathcal{G}_S(x) = \mathrm{mex}\{\mathcal{G}_S(x - s) : s \in S,\ s \le x\},$$
and the set of $\mathrm{P}$-positions is $W = \mathcal{W}_0(S) = \{x \in \mathbb{N} : \mathcal{G}_S(x) = 0\}$. Equivalently (Manabe Lemma 4), $W$ is the unique subset of $\mathbb{N}$ that is *independent* ($x \in W \implies x - s \notin W$ for every $s \in S$ with $s \le x$) and *dominating* ($x \notin W \implies \exists s \in S$ with $s \le x$ and $x - s \in W$). Write $W_B = \mathcal{W}_0(B)$ for the base two-move game $B = \{a, b\}$.

A set $W \subseteq \mathbb{N}$ is **$P$-periodic** (purely periodic with period $P > 0$) if $x \in W \iff x + P \in W$ for all $x \ge 0$; similarly $\mathcal{G}_S$ is $P$-periodic if $\mathcal{G}_S(x + P) = \mathcal{G}_S(x)$ for all $x \ge 0$. Note that $P$-periodicity of $\mathcal{G}_S$ implies $P$-periodicity of $W$, and $P$ need not be the least period.

Reading residues modulo $n = a + b$ in $\{0, \dots, n - 1\}$:
- Base pattern: $\mathcal{Z} = W_B \cap [0, n)$.
- Gap set: $D = [a, b) \setminus \mathcal{Z}$.
- Arc $\Lambda$ (`arXiv:2609.05358v2`, formula (4)):
  $$\Lambda = \begin{cases} [(\eta + 1)a,\ (\eta + 1)a + \varepsilon), & \eta \text{ even}, \\ [\eta a + \varepsilon,\ (\eta + 1)a), & \eta \text{ odd}. \end{cases}$$
- Admissible angle sets (`arXiv:2609.05358v2`, Definition 19):
  - **(T0)** $\rho \in \Theta_{a+b} \iff \mathcal{Z} \cap (\mathcal{Z} + \rho) = \emptyset \pmod{n}$.
  - **(T1)** $\rho \in \Theta_{c+a} \iff \mathcal{Z} \cap [0, \delta) \cap (\mathcal{Z} + (\delta - \rho)) = \emptyset \pmod{n}$.
  - **(T2)** $\rho \in \Theta_{c+b} \iff (\rho + \Lambda) \cap \mathcal{Z} = \emptyset \text{ and } (\rho + D) \cap \Lambda = \emptyset \pmod{n}$.

All results in §§2–4 hold for **all** $1 \le a < b < c$ without assuming $a \ge 2$, $\gcd(a, b, c) = 1$, $c \neq a + b$, or minimality of $P$.

## 2. Base Pattern and First $c + b$ Positions

**Lemma 2.1 (Base facts F1–F4).**
1. **(F1)** $\mathcal{Z} = \{u \in [0, b) : \lfloor u / a \rfloor \text{ is even}\}$ and $W_B = \mathcal{Z} + n\mathbb{N}$.
2. **(F2)** For every $r \in \mathcal{Z}$, $(r + a) \bmod n \notin \mathcal{Z}$.
3. **(F3)** $\Lambda = [\delta, b) \setminus \mathcal{Z} = \{w \in [0, n) : w \notin \mathcal{Z} \text{ and } (w + a) \bmod n \notin \mathcal{Z}\} \subseteq D$.
4. **(F4)** Modulo $n$, $\Lambda + a \equiv [-\varepsilon, 0)$ if $\eta$ is even, and $\Lambda + a \equiv [-a, -\varepsilon)$ if $\eta$ is odd.

*Proof.*
(F1) Put $T = \{x \in \mathbb{N} : x \bmod n \in \mathcal{Z}'\}$ where $\mathcal{Z}' = \{u \in [0, b) : \lfloor u/a \rfloor \text{ even}\}$. For $x \in T$ with residue $u \in \mathcal{Z}'$: if $u \ge a$, $(x - a) \bmod n = u - a \in [0, b)$ has odd quotient $\lfloor u/a \rfloor - 1$, while if $u < a$ and $x \ge a$, $(x - a) \bmod n = u + b \in [b, n)$ lies outside $\mathcal{Z}'$; similarly if $x \ge b$, $(x - b) \bmod n = u + a$ either lies in $[b, n)$ or has odd quotient $\lfloor u/a \rfloor + 1$. Thus $T$ is $B$-independent. Conversely, if $x \notin T$ has residue $u$: if $u < b$, then $\lfloor u/a \rfloor$ is odd, so $x \ge u \ge a$ and $(x - a) \bmod n = u - a \in \mathcal{Z}'$; if $u \ge b$, then $x \ge u \ge b$ and $(x - b) \bmod n = u - b \in [0, a) \subseteq \mathcal{Z}'$. Thus $T$ is $B$-dominating, so $W_B = T$ and $\mathcal{Z} = \mathcal{Z}'$.

(F2) If $r \in \mathcal{Z}$, then $r < b$, so $r + a < n$ without wrap; either $r + a \ge b$ (outside $\mathcal{Z}$) or $r + a < b$ with odd quotient $\lfloor r/a \rfloor + 1$.

(F3) Since $\delta + a = b$ and $\delta = \eta a + \varepsilon$, we have $(\eta + 1)a + \varepsilon = b$. Thus $[\delta, b)$ splits into $[\eta a + \varepsilon, (\eta + 1)a)$ (quotient $\eta$) and $[(\eta + 1)a, b)$ (quotient $\eta + 1$), so $[\delta, b) \setminus \mathcal{Z}$ coincides verbatim with formula (4). Moreover, any $w \in [b, n)$ has $(w + a) \bmod n = w - b \in [0, a) \subseteq \mathcal{Z}$; any $w \in [0, \delta) \setminus \mathcal{Z}$ has odd quotient $\lfloor w/a \rfloor$ and $w + a < b$, so $(w + a) \bmod n = w + a \in \mathcal{Z}$; and any $w \in [\delta, b) \setminus \mathcal{Z}$ satisfies $b \le w + a < n$, so $(w + a) \bmod n = w + a \notin \mathcal{Z}$. Finally, $[0, a) \subseteq \mathcal{Z}$ gives $\Lambda \subseteq [a, b) \setminus \mathcal{Z} = D$.

(F4) Using $(\eta + 1)a + \varepsilon = b = n - a$, adding $a$ to formula (4) yields $[n - \varepsilon, n)$ when $\eta$ is even and $[n - a, n - \varepsilon)$ when $\eta$ is odd. $\square$

**Lemma 2.2 (Initial block L1–L2).**
1. **(L1)** $W \cap [0, c) = W_B \cap [0, c)$ and $W \cap [c, c + a) = \emptyset$.
2. **(L2)** For every $u \in [a, b)$,
   $$c + u \in W \iff u \in D \text{ and } (\rho + u + a) \bmod n \notin \mathcal{Z}.$$

*Proof.*
(L1) Below $c$ the available moves of $S$ and $B$ coincide, so $W \cap [0, c) = W_B \cap [0, c)$. For $x \in [c, c + a)$, we have $x - c \in [0, a) \subseteq \mathcal{Z} \subseteq W$, so $x \notin W$.

(L2) Write $x = c + u$ with $u \in [a, b)$. Then $x - c = u < c$, so $x - c \in W \iff u \in \mathcal{Z}$ by (L1); and $x - b = c + u - b \in [c - \delta, c)$, so by (L1) and (F1), $x - b \in W \iff (c + u - b) \bmod n \in \mathcal{Z} \iff (\rho + u + a) \bmod n \in \mathcal{Z}$.
If $u \in \mathcal{Z}$, then $x - c \in W$ forces $x \notin W$. If $u \notin \mathcal{Z}$, then $u \in D$, so $\lfloor u/a \rfloor$ is odd and hence $u - a \in \mathcal{Z} \subseteq W$; thus $x - a = c + (u - a)$ has the legal move $c$ to $u - a \in W$, forcing $x - a \notin W$. Therefore $x \in W \iff x - b \notin W \iff (\rho + u + a) \bmod n \notin \mathcal{Z}$. $\square$

## 3. Exact Periodicity Criteria for $P \in \{a + b, c + a, c + b\}$

**Lemma 3.1 (Join Lemma).** Let $P > c$ and $H = W \cap [0, P)$. Then $W$ is $P$-periodic if and only if no $h, h' \in H$ satisfy $h' - h \in \{P - a, P - b, P - c\}$.

*Proof.*
*Necessity:* If $W$ is $P$-periodic and $h, h' \in H$ satisfy $h' - h = P - s$ ($s \in S$), then $h + P \in W$ and $(h + P) - s = h' \in W$, contradicting independence of $W$.
*Sufficiency:* Put $T = H + P\mathbb{N}$. Since $H \subseteq W$, no two elements of $H$ differ by a move $s \in S$. Because $s \le c < P$, any move $s \in S$ between two elements of $T$ would produce either a difference $s$ within $H$ or a complementary difference $P - s$ within $H$, both excluded; thus $T$ is $S$-independent. For domination, any $x = r + kP \notin T$ ($0 \le r < P$) has $r \notin H = W \cap [0, P)$, so there exists $s \in S$ with $s \le r$ and $r - s \in H$, whence $x - s = (r - s) + kP \in T$. By uniqueness (Manabe Lemma 4), $W = T$. $\square$

**Theorem 3.2 (Period $a + b$, extending Lemma 54 / Prop. 55 to all $c > b$).** For all $1 \le a < b < c$,
$$W \text{ is } (a + b)\text{-periodic} \iff W = W_B \iff \rho \in \Theta_{a+b}.$$

*Proof.*
Suppose $W$ is $n$-periodic. For $x \in [0, n)$: if $x < c$, then $x \in W \iff x \in W_B$ by (L1); if $c \le x < n$, then since $c > b$ we have $x < n = a + b < c + a$, so $x \notin W$ by (L1) and $x \notin \mathcal{Z}$ since $\mathcal{Z} \subseteq [0, b) \subseteq [0, c)$. Hence $W \cap [0, n) = \mathcal{Z} = W_B \cap [0, n)$, and $n$-periodicity yields $W = W_B$.

Next, $W = W_B$ holds iff $W_B$ is $S$-independent (domination is inherited from $B \subset S$), i.e., iff there is no $x \ge c$ with $x \in W_B$ and $x - c \in W_B$. By (F1), such $x$ exists iff there exists $z \in \mathcal{Z}$ with $(z + \rho) \bmod n \in \mathcal{Z}$ (take $x = z + c$), which is the negation of (T0). Finally, $W = W_B$ is automatically $n$-periodic by (F1). $\square$

**Theorem 3.3 (Period $c + a$).** For all $1 \le a < b < c$,
$$W \text{ is } (c + a)\text{-periodic} \iff \rho \in \Theta_{c+a}.$$

*Proof.*
Apply Lemma 3.1 with $P = c + a > c$. Here $P - a = c$ and $P - c = a$ are already moves in $S$, so they cannot occur as differences inside $H = W \cap [0, c + a)$. Only $P - b = c - \delta > 0$ remains. By (L1), $H = W_B \cap [0, c)$. A pair $h, h' \in H$ with $h' = h + (c - \delta)$ satisfies $h = h' - (c - \delta) < \delta$ (so $h \in \mathcal{Z} \cap [0, \delta)$) and $h' \in [c - \delta, c) \cap W_B$ (so $z := h' \bmod n \in \mathcal{Z}$ satisfies $z + \delta \equiv h + \rho \pmod{n}$). Conversely, any $h \in \mathcal{Z} \cap [0, \delta)$ and $z \in \mathcal{Z}$ with $z + \delta \equiv h + \rho \pmod{n}$ satisfy $h' := h + (c - \delta) \in [0, c)$ and $h' \bmod n = z \in \mathcal{Z}$, hence $h, h' \in H$ with $h' - h = P - b$. Avoiding all such pairs is verbatim (T1). $\square$

Write **(N1)** for the condition $\forall u \in \Lambda,\ (\rho + u + a) \bmod n \in \mathcal{Z}$.

**Theorem 3.4 (Period $c + b$ and explicit form of $\Theta_{c+b}$).** For all $1 \le a < b < c$,
$$W \text{ is } (c + b)\text{-periodic} \iff \text{(N1)} \iff \rho \in \Theta_{c+b}.$$
Equivalently, $\rho \in \Theta_{c+b}$ iff
$$\begin{cases} (\rho - j) \bmod n \in \mathcal{Z} \text{ for all } 1 \le j \le \varepsilon, & \eta \text{ even}, \\ (\rho - j) \bmod n \in \mathcal{Z} \text{ for all } \varepsilon + 1 \le j \le a, & \eta \text{ odd}. \end{cases}$$

*Proof.*
*(i) $(c + b)$-periodicity $\iff$ (N1).* Apply Lemma 3.1 with $P = c + b > c$. Since $P - b = c$ and $P - c = b$ are moves in $S$, only $P - a = c + \delta$ remains. For $h, h' \in [0, c + b)$ with $h' = h + c + \delta$, we have $h < a$ and $h' \in [c + \delta, c + b)$. Since $[0, a) \subseteq \mathcal{Z} \subseteq H$, periodicity holds iff $W \cap [c + \delta, c + b) = \emptyset$. Writing $h' = c + u$ ($u \in [\delta, b)$): if $u < a$, then $c + u \notin W$ automatically by (L1); if $u \ge a$, then by (L2) we have $c + u \in W$ iff $u \in D$ and $(\rho + u + a) \bmod n \notin \mathcal{Z}$. Since $[\delta, b) \cap D = [\delta, b) \setminus \mathcal{Z} = \Lambda$ by (F3), $W \cap [c + \delta, c + b) = \emptyset$ is equivalent to (N1).

*(ii) Explicit form.* By (F4), as $u$ ranges over $\Lambda$, $(u + a) \bmod n$ ranges over $[- \varepsilon, 0) \bmod n$ ($\eta$ even) or $[-a, -\varepsilon) \bmod n$ ($\eta$ odd), so (N1) is identical to the displayed cyclic-interval condition.

*(iii) $\Theta_{c+b} \implies$ (N1).* Suppose $\lambda \in \Lambda$ has $(\rho + \lambda + a) \bmod n \notin \mathcal{Z}$. By the first clause of (T2), $w := (\rho + \lambda) \bmod n \notin \mathcal{Z}$. Since $(w + a) \bmod n = (\rho + \lambda + a) \bmod n \notin \mathcal{Z}$, (F3) gives $w \in \Lambda$. Because $\lambda \in \Lambda \subseteq D$ by (F3), this contradicts $(\rho + D) \cap \Lambda = \emptyset$.

*(iv) (N1) $\implies \Theta_{c+b}$.* First, if $\lambda \in \Lambda$ had $w := (\rho + \lambda) \bmod n \in \mathcal{Z}$, then (F2) would give $(\rho + \lambda + a) \bmod n = (w + a) \bmod n \notin \mathcal{Z}$, contradicting (N1). Thus $(\rho + \Lambda) \cap \mathcal{Z} = \emptyset$.

Second, suppose toward a contradiction that $d \in D$ satisfies $\lambda := (\rho + d) \bmod n \in \Lambda$. Write $d = q a + s$ with $q = \lfloor d / a \rfloor$ odd and $0 \le s < a$. Let $J = [1, \varepsilon]$ if $\eta$ is even, and $J = [\varepsilon + 1, a]$ if $\eta$ is odd; by (ii), (N1) states that $(\rho - j) \bmod n \in \mathcal{Z}$ for all $j \in J$.

- **Case $\eta$ even:** Since $\lambda \in \Lambda = [(\eta + 1)a, (\eta + 1)a + \varepsilon)$, we have $\varepsilon \ge 1$ and $\lambda = (\eta + 1)a + \lambda'$ with $0 \le \lambda' < \varepsilon$. Because $d < b = (\eta + 1)a + \varepsilon < (\eta + 2)a$, we have $q \le \eta + 1$. Set $2m = \eta + 1 - q$ (even, $0 \le 2m \le \eta$) and $t = \lambda' - s \in [1 - a, \varepsilon - 1]$. Then $\rho \equiv \lambda - d = 2ma + t \pmod{n}$. Pick $j = \max(1, t + 1)$; since $1 \le \varepsilon$ and $t \le \varepsilon - 1$, we have $j \in J$, and since $t \ge 1 - a$, we have $t < j \le t + a$.
- **Case $\eta$ odd:** Here $\lambda = \eta a + \varepsilon + \lambda'$ with $0 \le \lambda' < a - \varepsilon$. Since $d < b < (\eta + 2)a$ and $q$ is odd while $\eta + 1$ is even, $q \le \eta$. Set $2m = \eta - q$ (even, $0 \le 2m \le \eta - 1$) and $t = \varepsilon + \lambda' - s \in [\varepsilon + 1 - a, a - 1]$. Then $\rho \equiv \lambda - d = 2ma + t \pmod{n}$. Pick $j = \max(\varepsilon + 1, t + 1)$; since $\varepsilon < a$ and $t \le a - 1$, we have $j \in J$, and since $t \ge \varepsilon + 1 - a$, we have $t < j \le t + a$.

In both cases, $t - j \in [-a, -1]$, so $2ma + (t - j) \in [(2m - 1)a, 2ma)$. If $m = 0$, then $(\rho - j) \bmod n = n + (t - j) \in [b, n)$, which is disjoint from $\mathcal{Z}$. If $m \ge 1$, then $2m \le \eta$, so $0 \le (2m - 1)a \le 2ma + (t - j) < \eta a \le \delta < b$, whence $(\rho - j) \bmod n = 2ma + (t - j) \in [0, b)$ has odd quotient $2m - 1$, also outside $\mathcal{Z}$. This contradicts (N1) at $j \in J$. $\square$

## 4. Consequences for Conjectures 57, 52, and 56

**Corollary 4.1 (Proof of Manabe Conjecture 57, strengthened).** For all $1 \le a < b < c$, if $\mathcal{G}_S$ is purely periodic with period $a + b$ (resp. $c + a$, $c + b$) — not necessarily the least period, and without assuming $a \ge 2$, $\gcd(a, b, c) = 1$, or $c \neq a + b$ — then $\rho \in \Theta_{a+b}$ (resp. $\Theta_{c+a}$, $\Theta_{c+b}$).

*Proof.* $P$-periodicity of $\mathcal{G}_S$ implies $P$-periodicity of $W = \{x : \mathcal{G}_S(x) = 0\}$, so Theorems 3.2–3.4 apply directly. $\square$

**Corollary 4.2 (Equivalence of Conjectures 52 and 56 for all $c > b$).** Under the hypotheses of Conjecture 52 ($a \ge 2$, $\gcd(a, b, c) = 1$, $c \neq a + b$), Conjecture 52 holds if and only if Conjecture 56 holds, for **every** $c > b$ (removing the $c \ge 2(a + b)$ restriction in Manabe's Proposition 59).

*Proof.* If Conjecture 56 holds and $\mathcal{G}_S$ is purely periodic with least period $p$, then $p \in \{a + b, c + a, c + b\}$, so Corollary 4.1 gives $\rho \in \Theta_p \subseteq \Theta_{a+b} \cup \Theta_{c+a} \cup \Theta_{c+b}$; Manabe's Theorem 34 then yields the least-period formula. Conversely, Theorem 34 implies that Conjecture 52 gives $p \in \{a + b, c + a, c + b\}$. $\square$

**Proposition 4.3 (Partial period exclusions toward Conjecture 56).** Suppose $1 \le a < b < c$ and $W$ is purely periodic with period $p > 0$.
1. $p \notin (c - a, c + a)$.
2. If $c \ge p + n - \gcd(p, n)$, then $W$ is $n$-periodic and $\rho \in \Theta_{a+b}$ (extending Lemma 54 from $p \le n \le c/2$ to all $p \le c - n + \gcd(p, n)$, including $n \mid p$).

*Proof.*
(1) If $c - a < p < c$, then $r := c - p \in [0, a) \subseteq W$, so $c = r + p \in W$, contradicting (L1). If $c \le p < c + a$, then $0 \in W$ gives $p = 0 + p \in W$, again contradicting (L1).
(2) Put $g = \gcd(p, n)$. Since $g \le n$, we have $p \le p + n - g \le c$. On $[0, c)$, the indicator word of $W$ coincides with $W_B$ by (L1), so it has both periods $p$ and $n$. By the Fine–Wilf periodicity theorem, $W \cap [0, c)$ has period $g$. Because $p \le c$, the block $W \cap [0, p)$ is $g$-periodic; because $g \mid p$ and $W$ is $p$-periodic, repeating this block yields $W(x) = W(x \bmod p) = W((x \bmod p) \bmod g) = W(x \bmod g)$ for all $x \in \mathbb{N}$. Since $g \mid n$, $W$ is $n$-periodic, and Theorem 3.2 gives $\rho \in \Theta_{a+b}$. $\square$
