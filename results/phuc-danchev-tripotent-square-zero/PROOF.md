# Complete Resolution of Phuc–Danchev Problem 4.10

## 1. Problem Statement

Let $\mathcal{T}_d = \{T + N \in \mathrm{M}_d(\mathbb{F}_2) : T^3 = T,\; N^2 = 0\}$. Phuc and Danchev (`arXiv:2611.24594v2`, Section 4) proved that $\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d$ for $d \in \{1, 2, 4, 5\}$ and $\mathrm{M}_d(\mathbb{F}_2) \neq \mathcal{T}_d$ whenever $3 \mid d$, and posed:

> **Problem 4.10.** Determine all integers $d \ge 7$ with $3 \nmid d$ for which $\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d$. In particular, determine which orders $d = 8n + 4$, with $n \ge 2$ and $n \not\equiv 1 \pmod 3$, satisfy this equality.

**Theorem.** *For every integer $d \ge 7$ with $3 \nmid d$, $\mathrm{M}_d(\mathbb{F}_2) \neq \mathcal{T}_d$. In particular, no order $d = 8n + 4$ with $n \ge 1$ satisfies $\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d$. Consequently, $\mathrm{M}_d(\mathbb{F}_2) = \mathcal{T}_d$ if and only if $d \in \{1, 2, 4, 5\}$.*

## 2. Characteristic-2 Identities and Theorem 0

Let $F$ be a field of characteristic $2$ (so $x + x = 0$ and $-x = x$), and let $p(x) = x^3 + x^2 + 1 \in F[x]$. Notice the Bezout identity
$$(x^2 + 1)(x^3 + x) + (x^2 + x + 1)p(x) = 1,$$
so whenever $p(a) = 0$ in a ring $R$ of characteristic $2$, the element $a^3 + a$ is invertible with inverse $a^2 + 1$.

If $a = t + u$ in a characteristic-$2$ ring $R$ with $t^3 = t$ and $u^2 = 0$, then $t = a + u$, so $t^2 = a^2 + au + ua$, and expanding $0 = t^3 + t = (a^2 + au + ua)(a + u) + (a + u)$ yields
$$a^3 + a + a^2 u + a u a + u a^2 + u a u + u = 0. \tag{E1}$$
Multiplying (E1) on the right by $u$ and using $u^2 = 0$ gives
$$(a^3 + a)u + a u a u + u a^2 u = 0. \tag{E1u}$$

**Theorem 0 (Phuc–Danchev Theorem 3.1, $\lambda = 1$, self-contained proof).** *Let $R$ be a nonzero ring of characteristic $2$ and $a \in R$ with $p(a) = 0$. There do not exist $t, u \in R$ with $a = t + u$, $t^3 = t$, and $u^2 = 0$.*

*Proof.* Set $X = uau$, $Y = ua^2u$, and $Z = uauau$.
1. Multiplying (E1) on both sides by $u$ gives $ua^3u + Z + X = 0$. Since $a^3 = a^2 + 1$ and $u^2 = 0$, we have $ua^3u = ua^2u = Y$, so $Y = X + Z$.
2. Set $S = t^2 = a^2 + au + ua$. Since $t^3 = t$, we have $S^2 + S = t^4 + t^2 = 0$, so $u(S^2 + S)u = 0$. Expanding directly using $u^2 = 0$ gives $uSu = Y$ and $uS^2u = ua^4u + Yau + uaY$. Since $a^4 = a(a^2 + 1) = a^3 + a = a^2 + a + 1$, we have $ua^4u = Y + X$, whence $0 = (Y + X) + Yau + uaY + Y = X + Yau + uaY$, i.e., $X = Yau + uaY$.
3. Substituting $Y = X + Z$ gives $Yau = Xau + Zau = Z + uauauau = uaX + uaZ = uaY$, so $X = Yau + uaY = 0$.
4. Hence $Z = Xau = 0$ and $Y = X + Z = 0$. By (E1u), $(a^3 + a)u = aX + Y = 0$. Multiplying on the left by $a^2 + 1$ gives $u = 0$. Thus $a = t$, so $a^3 + a = 0$, yielding $1 = (a^2 + 1)(a^3 + a) = 0$, contradicting $R \neq 0$. $\square$

## 3. Lemma A (Sharp Rank Inequality)

**Lemma A.** *Let $V$ be a finite-dimensional vector space over a field $F$ of characteristic $2$, and let $a = t + u \in \mathrm{End}_F(V)$ with $t^3 = t$ and $u^2 = 0$. Set $e = p(a)$ and $K = \ker e$. Then*
$$K_1 := \{x \in K : e u x = e u a x = e u a^2 x = 0\} = 0,$$
*and consequently $\dim_F \ker p(a) \le 3 \cdot \mathrm{rank}\, p(a)$.*

*Proof.* Since $e$ is a polynomial in $a$, $e$ commutes with $a$ and $K$ is $a$-invariant.
1. **$a(K_1) \subseteq K_1$.** For $x \in K_1$, $ax \in K$, $eu(ax) = 0$, $eua(ax) = eua^2x = 0$, and since $a^3x = a^2x + x$ (as $ex = 0$), $eua^2(ax) = eu(a^2x + x) = eua^2x + eux = 0$.
2. **$u(K_1) \subseteq K_1$.** For $x \in K_1$, $ux \in K$ directly from $eux = 0$, and $eu(ux) = 0$ since $u^2 = 0$. Applying $e$ to (E1) evaluated at $x$ gives $euaux = 0$, because $e$ commutes with $a$ and $ex = eux = euax = eua^2x = 0$. Applying $e$ to (E1u) evaluated at $x$ gives $eua^2ux = (a^3 + a)eux + a(euaux) = 0$. Thus $ux \in K_1$.

Therefore $K_1$ is invariant under $a$, $u$, and $t = a + u$. Restricting to $K_1$ gives $p(a|_{K_1}) = 0$, $(t|_{K_1})^3 = t|_{K_1}$, and $(u|_{K_1})^2 = 0$ in $\mathrm{End}_F(K_1)$. By Theorem 0, $\mathrm{End}_F(K_1) = 0$, so $K_1 = 0$.

Consequently, the linear map $\Psi : K \to (\mathrm{im}\, e)^3$ defined by $\Psi(x) = (eux, euax, eua^2x)$ has kernel $K_1 = 0$, so $\dim_F K \le \dim_F (\mathrm{im}\, e)^3 = 3 \cdot \mathrm{rank}\, e$. $\square$

## 4. Lemma B (Rigidity of the Equality Case)

**Lemma B.** *Let $V = K \oplus U$ over a field $F$ of characteristic $2$ with $\dim_F K = 3 \dim_F U$, and let $a = a_1 \oplus B \in \mathrm{End}_F(V)$ where $p(a_1) = 0$ and $p(B) \in \mathrm{End}_F(U)$ is invertible. If $a = t + u$ with $t^3 = t$ and $u^2 = 0$, then $B^3 = B^2$.*

*Proof.* Write $u = \begin{pmatrix} u_{11} & u_{12} \\ u_{21} & c \end{pmatrix}$ relative to $V = K \oplus U$. Here $e = p(a) = 0 \oplus p(B)$ has $\ker e = K$, and since $p(B)$ is invertible, $eu a^j x = 0 \iff u_{21} a_1^j x = 0$ for all $x \in K$.

By Lemma A, the map $\Phi : K \to U^3$, $\Phi(x) = (u_{21}x, u_{21}a_1x, u_{21}a_1^2x)$, is injective. Since $\dim_F K = 3 \dim_F U = \dim_F U^3$, $\Phi$ is an isomorphism. Transporting $a_1$, $u_{21}$, and $u_{11}$ to $U^3$ via $\Phi$:
- $M := \Phi a_1 \Phi^{-1}$ acts by $M(x, y, z) = (y, z, x + z)$ (since $a_1^3 = a_1^2 + 1$).
- $u_{21} \Phi^{-1}(x, y, z) = x$.
- Write $N := \Phi u_{11} \Phi^{-1} : U^3 \to U^3$ in components as $N(x, y, z) = (N_1(x, y, z), N_2(x, y, z), N_3(x, y, z))$.

We determine $N_1, N_2, N_3$ explicitly:
1. **$N_1$:** The $U \leftarrow K$ block of $u^2 = 0$ is $u_{21} u_{11} + c u_{21} = 0$, i.e., $u_{21} u_{11} = c u_{21}$, so $N_1(x, y, z) = c x$.
2. **$N_2$:** The $U \leftarrow K$ block of (E1) is
   $$B^2 u_{21} + B u_{21} a_1 + u_{21} a_1^2 + u_{21} a_1 u_{11} + c B u_{21} + u_{21} = 0.$$
   Precomposing with $\Phi^{-1}$ gives $u_{21} a_1 u_{11} \Phi^{-1}(x, y, z) = N_2(x, y, z)$, so
   $$N_2(x, y, z) = (B^2 + cB + 1)x + By + z.$$
3. **$N_3$:** The $K \leftarrow K$ block of (E1) is
   $$a_1^3 + a_1 + a_1^2 u_{11} + a_1 u_{11} a_1 + u_{11} a_1^2 + u_{11} a_1 u_{11} + u_{12} B u_{21} + u_{11} = 0.$$
   Conjugating by $\Phi$ yields
   $$M^3 + M + M^2 N + M N M + N M^2 + N M N + (\Phi u_{12}) B \pi_1 + N = 0, \tag{KK}$$
   where $\pi_1(x, y, z) = x$ and the first coordinate of $\Phi u_{12}$ is $u_{21} u_{12} = c^2$ (from the $U \leftarrow U$ block of $u^2 = 0$). Taking the first coordinate of (KK) at $(x, y, z)$ gives:
   - $(M^3 + M)_1(x, y, z) = x + y + z$,
   - $(M^2 N)_1(x, y, z) = N_3(x, y, z)$,
   - $(M N M)_1(x, y, z) = N_2(y, z, x + z) = (B^2 + cB + 1)y + Bz + x + z$,
   - $(N M^2)_1(x, y, z) = c z$,
   - $(N M N)_1(x, y, z) = c N_2(x, y, z) = (c B^2 + c^2 B + c)x + c B y + c z$,
   - $((\Phi u_{12}) B \pi_1)_1(x, y, z) = c^2 B x$,
   - $N_1(x, y, z) = c x$.

   Summing these seven terms in characteristic $2$, every $x$, $y$, $z$, $c x$, $c z$, $c^2 B x$, $c B y$ term cancels, leaving
   $$N_3(x, y, z) + c B^2 x + B^2 y + B z = 0, \qquad\text{so}\qquad N_3(x, y, z) = c B^2 x + B^2 y + B z.$$
4. **Conclusion ($B^3 = B^2$):** Evaluate the third coordinate of (KK) at $(0, 0, w)$. Since $\pi_1(0, 0, w) = 0$, the $(\Phi u_{12}) B \pi_1$ term vanishes, and the remaining seven terms at $(0, 0, w)$ are:
   - $(M^3 + M)_3(0, 0, w) = w$,
   - $(M^2 N)_3(0, 0, w) = (N_1 + N_2 + N_3)(0, 0, w) = (1 + B)w$,
   - $(M N M)_3(0, 0, w) = (N_1 + N_3)(0, w, w) = (B^2 + B)w$,
   - $(N M^2)_3(0, 0, w) = N_3(w, w, w) = (cB^2 + B^2 + B)w$,
   - $(N M N)_3(0, 0, w) = N_3(w, Bw, cB^2w + Bw) = (cB^2 + B^3 + B^2)w$,
   - $N_3(0, 0, w) = Bw$.

   Summing in characteristic $2$:
   $$0 = \bigl(1 + (1 + B) + (B^2 + B) + (cB^2 + B^2 + B) + (cB^2 + B^3 + B^2) + B\bigr)w = (B^3 + B^2)w.$$
   Since $w \in U$ is arbitrary, $B^3 = B^2$. $\square$

## 5. Proof of the Main Theorem

Let $C = \begin{pmatrix} 0 & 0 & 1 \\ 1 & 0 & 0 \\ 0 & 1 & 1 \end{pmatrix} \in \mathrm{M}_3(\mathbb{F}_2)$, which satisfies $p(C) = C^3 + C^2 + I_3 = 0$. Every integer $d \ge 7$ with $3 \nmid d$ falls into one of three cases:

1. **$d = 3m + 1$ with $m \ge 2$:** Take $A = C^{\oplus m} \oplus [0] \in \mathrm{M}_d(\mathbb{F}_2)$. Then $p(A) = 0_{3m} \oplus [1]$, so $\dim \ker p(A) = 3m > 3 = 3 \cdot \mathrm{rank}\, p(A)$, ruling out $A \in \mathcal{T}_d$ by Lemma A.
2. **$d = 3m + 2$ with $m \ge 3$:** Take $A = C^{\oplus m} \oplus 0_2 \in \mathrm{M}_d(\mathbb{F}_2)$. Then $p(A) = 0_{3m} \oplus I_2$, so $\dim \ker p(A) = 3m > 6 = 3 \cdot \mathrm{rank}\, p(A)$, ruling out $A \in \mathcal{T}_d$ by Lemma A.
3. **$d = 8$:** Take $A = C \oplus C \oplus B \in \mathrm{M}_8(\mathbb{F}_2)$ where $B = \begin{pmatrix} 0 & 1 \\ 1 & 1 \end{pmatrix}$. Then $B^2 = B + I_2$ and $B^3 = I_2$, so $p(B) = B^3 + B^2 + I_2 = B^2$ is invertible (with inverse $B$) and $\dim \ker p(A) = 6 = 3 \cdot 2$. Since $B^3 = I_2 \neq B^2$, Lemma B rules out $A \in \mathcal{T}_8$.

Finally, for $d = 8n + 4$ with $n \ge 1$, we have $d \ge 12 > 7$: if $3 \mid d$ then $\mathrm{M}_d(\mathbb{F}_2) \neq \mathcal{T}_d$ by Theorem 0 (via $C^{\oplus (d/3)}$), and if $3 \nmid d$ then $\mathrm{M}_d(\mathbb{F}_2) \neq \mathcal{T}_d$ by Cases 1–2 above. $\square$
