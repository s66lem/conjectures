# Proof of Karan Sharma's OEIS A401897 Conjecture (`a(n) ~ 48n / pi^2`)

**Target:** Conjecture in [OEIS A401897](https://oeis.org/A401897) (Karan Sharma, Nov 9, 2026; revision 10).

> **Name (verbatim):** "Number of Gaussian integers w with N(w) < N(z) that are visible from z, where z = a+b*i is the n-th nonzero Gaussian integer with 0 <= b <= a, ordered by norm and then by b."
> **Comment (verbatim):** "w is visible from z if no Gaussian integer lies strictly between them on the segment from z to w, i.e., gcd(Re(z-w), Im(z-w)) = 1. The points w checked include w = 0."
> **Conjecture (verbatim):** "Conjecture: a(n) ~ 48*n/Pi^2."

---

## Theorem

Let $(z_n)_{n \ge 1}$ enumerate all nonzero Gaussian integers $z = a + bi$ with $0 \le b \le a$, ordered first by norm $N(z) = a^2 + b^2$ and then by $b$, and let
$$a(n) := \#\{w \in \mathbb{Z}[i] : N(w) < N(z_n) \text{ and } \gcd(\mathrm{Re}(z_n - w), \mathrm{Im}(z_n - w)) = 1\}.$$
Then, with $N = N(z_n)$ and $R = \sqrt{N} \ge 1$:
1. **Uniform moving-viewpoint visibility bound:** For every nonzero $z \in \mathbb{Z}[i]$,
   $$\left|a(z) - \frac{6 N(z)}{\pi}\right| \le \pi \sqrt{N(z)}\bigl(2 + \sqrt{2} + \sqrt{2}\ln(2\sqrt{N(z)})\bigr).$$
2. **Rank–norm relation (accounting for norm ties):** For every $n \ge 1$,
   $$\left|n - \frac{\pi N(z_n)}{8}\right| \le 2\sqrt{N(z_n)}.$$
3. **Asymptotic resolution of A401897:**
   $$\lim_{n \to \infty} \frac{a(n)}{48n / \pi^2} = 1, \qquad a(n) = \frac{48n}{\pi^2}\left(1 + O\!\left(\frac{\log n}{\sqrt{n}}\right)\right).$$

---

## 1. Shifted Gauss Circle Lemma

**Lemma 1.** For every center $c \in \mathbb{R}^2$ and every radius $r > 0$, letting $D$ be either the open disk $\{x \in \mathbb{R}^2 : \|x - c\| < r\}$ or the closed disk $\{x \in \mathbb{R}^2 : \|x - c\| \le r\}$,
$$\bigl|\#(\mathbb{Z}^2 \cap D) - \pi r^2\bigr| \le \pi\left(\sqrt{2}\,r + \frac{1}{2}\right).$$

*Proof.* Associate to each lattice point $p \in \mathbb{Z}^2$ the closed unit square $Q(p) = p + [-\tfrac{1}{2}, \tfrac{1}{2}]^2$ of area $1$ and half-diagonal $1/\sqrt{2}$.
- **Upper bound:** The squares $Q(p)$ for $p \in \mathbb{Z}^2 \cap D$ have pairwise disjoint interiors and are contained in the disk of radius $r + 1/\sqrt{2}$ around $c$. Comparing areas gives $\#(\mathbb{Z}^2 \cap D) \le \pi(r + 1/\sqrt{2})^2 = \pi r^2 + \pi(\sqrt{2}\,r + \tfrac{1}{2})$.
- **Lower bound:** If $r \ge 1/\sqrt{2}$, every point $x$ with $\|x - c\| < r - 1/\sqrt{2}$ lies in $Q(p)$ for a nearest lattice point $p \in \mathbb{Z}^2$ with $\|p - x\| \le 1/\sqrt{2}$, so $\|p - c\| < r$ and $p \in D$. Comparing areas gives $\#(\mathbb{Z}^2 \cap D) \ge \pi(r - 1/\sqrt{2})^2 = \pi r^2 - \pi(\sqrt{2}\,r - \tfrac{1}{2}) \ge \pi r^2 - \pi(\sqrt{2}\,r + \tfrac{1}{2})$. If $0 < r < 1/\sqrt{2}$, then $\pi r^2 < \pi/2 < \pi(\sqrt{2}\,r + \tfrac{1}{2})$, so $\#(\mathbb{Z}^2 \cap D) \ge 0$ already gives the lower bound. $\square$

---

## 2. Uniform Moving-Viewpoint Visibility (Proposition A)

Fix any nonzero $z \in \mathbb{Z}^2$ with $N = \|z\|^2 \ge 1$ and $R = \sqrt{N} \ge 1$. Under the bijection $v = z - w$,
$$a(z) = \#\{v \in \mathbb{Z}^2 : \|v - z\| < R,\; \gcd(v_1, v_2) = 1\}.$$
Notice that $v = 0$ is excluded since $\|0 - z\| = R$ is not $< R$. Using the Möbius identity $\mathbf{1}[\gcd(v_1, v_2) = 1] = \sum_{d \mid \gcd(v_1, v_2)} \mu(d)$ for every nonzero $v \in \mathbb{Z}^2$,
$$a(z) = \sum_{d \ge 1} \mu(d)\, L(z, d), \qquad L(z, d) := \#\{u \in \mathbb{Z}^2 : \|du - z\| < R\}.$$
For any $u \in \mathbb{Z}^2$ counted in $L(z, d)$, we have $u \neq 0$ (since $\|0 - z\| = R$), hence $d \le \|du\| \le \|du - z\| + \|z\| < 2R$. Thus $L(z, d) = 0$ for all $d \ge 2R$, so the sum is finite over $1 \le d < 2R$.

Each $L(z, d)$ counts lattice points in the open disk of center $z/d$ and radius $R/d$. Applying Lemma 1 gives
$$L(z, d) = \frac{\pi N}{d^2} + E_d, \qquad |E_d| \le \pi\left(\frac{\sqrt{2}\,R}{d} + \frac{1}{2}\right).$$
Summing against $\mu(d)$ over $1 \le d < 2R$ and using $\sum_{d=1}^{\infty} \mu(d)/d^2 = 1/\zeta(2) = 6/\pi^2$:
1. **Tail of $\sum \mu(d)/d^2$:** Writing $M = \lceil 2R \rceil \ge 2$,
   $$\left|\sum_{d \ge M} \frac{\mu(d)}{d^2}\right| \le \sum_{d = M}^{\infty} \frac{1}{d(d - 1)} = \frac{1}{M - 1} \le \frac{1}{2R - 1} \le \frac{1}{R},$$
   contributing at most $\pi N / R = \pi R$ to $|a(z) - 6N/\pi|$.
2. **Error sum:** Using $|\mu(d)| \le 1$, $\sum_{1 \le d < 2R} 1/d \le 1 + \ln(2R)$, and $\#\{1 \le d < 2R\} \le 2R$:
   $$\sum_{1 \le d < 2R} |E_d| \le \pi\sqrt{2}\,R\bigl(1 + \ln(2R)\bigr) + \pi R.$$
Combining both estimates yields
$$\left|a(z) - \frac{6N}{\pi}\right| \le \pi R\bigl(2 + \sqrt{2} + \sqrt{2}\ln(2R)\bigr),$$
uniformly in the direction of $z$. $\square$

---

## 3. Wedge Symmetry and Rank–Norm Bound (Proposition B)

For $X > 0$, let $W(X) = \#\{(a, b) \in \mathbb{Z}^2 : 0 \le b \le a,\; 0 < a^2 + b^2 \le X\}$ and $P(X) = \#\{v \in \mathbb{Z}^2 \setminus \{0\} : \|v\|^2 \le X\}$, with $W^\circ(X), P^\circ(X)$ denoting the strict-inequality versions ($< X$).

**Lemma 2 (8-fold dihedral symmetry).** $8 W(X) = P(X) + \Lambda(X)$ with $0 \le \Lambda(X) \le 7\sqrt{X}$, and likewise $8 W^\circ(X) = P^\circ(X) + \Lambda^\circ(X)$ with $0 \le \Lambda^\circ(X) \le 7\sqrt{X}$.

*Proof.* The dihedral group $D_4$ of order $8$ preserves $\mathbb{Z}^2 \setminus \{0\}$ and norm, mapping the fundamental wedge $\{0 \le b \le a\}$ onto $8$ closed wedges covering $\mathbb{R}^2 \setminus \{0\}$. Every nonzero lattice point off the four symmetry lines $x = 0, y = 0, y = \pm x$ lies in exactly one wedge; every nonzero lattice point on those four lines lies in exactly two wedges. Hence $\Lambda(X)$ equals the number of nonzero lattice points of norm $\le X$ on the four lines:
$$0 \le \Lambda(X) = 4\lfloor\sqrt{X}\rfloor + 4\lfloor\sqrt{X/2}\rfloor \le (4 + 2\sqrt{2})\sqrt{X} < 7\sqrt{X},$$
and identically for the strict version. $\square$

Now let $z_n$ have norm $N = N(z_n) \ge 1$. Because the enumeration orders first by norm and then by $b$, regardless of ties at norm $N$ we have
$$W^\circ(N) + 1 \le n \le W(N).$$
Applying Lemma 2 and Lemma 1 (noting $P(N) = \#(\mathbb{Z}^2 \cap \overline{B}(0, \sqrt{N})) - 1$ and $P^\circ(N) = \#(\mathbb{Z}^2 \cap B(0, \sqrt{N})) - 1$):
$$n \le \frac{\pi N + \pi\sqrt{2}\sqrt{N} + \pi/2 - 1 + 7\sqrt{N}}{8} \le \frac{\pi N}{8} + 2\sqrt{N},$$
$$n \ge 1 + \frac{\pi N - \pi\sqrt{2}\sqrt{N} - \pi/2 - 1}{8} \ge \frac{\pi N}{8} - 2\sqrt{N},$$
since $(\pi\sqrt{2} + \pi/2 - 1 + 7)/8 < 1.51 < 2$ and $(\pi\sqrt{2} + \pi/2 - 7)/8 < 0 < 2$ for $N \ge 1$. Thus $|n - \pi N / 8| \le 2\sqrt{N}$. $\square$

---

## 4. Conclusion

As $n \to \infty$, we have $N = N(z_n) \to \infty$ (only finitely many lattice points lie in any bounded disk). Writing $a(n) = 6N/\pi + E_A$ and $n = \pi N / 8 + E_B$, Propositions A and B give
$$\frac{a(n)}{48n / \pi^2} = \frac{1 + \frac{\pi E_A}{6N}}{1 + \frac{8 E_B}{\pi N}},$$
where $|\pi E_A / (6N)| = O(\log N / \sqrt{N}) \to 0$ and $|8 E_B / (\pi N)| \le 16 / (\pi \sqrt{N}) \to 0$. Therefore $a(n) \sim 48n / \pi^2$ with explicit relative error $O(\log n / \sqrt{n})$. $\square$
