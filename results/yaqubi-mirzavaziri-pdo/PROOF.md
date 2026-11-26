# Proof of Yaqubi–Mirzavaziri Conjecture 6.2 (`arXiv:2611.05623v1`)

**Source.** D. Yaqubi and M. Mirzavaziri, *Partitions with designated summands: $k$-tuples and their congruences*, [`arXiv:2611.05623v1`](https://arxiv.org/abs/2611.05623v1) (submitted 3 November 2026), Section 6, Conjecture 6.2.

**Theorem.** Let $f_m := \prod_{j \ge 1}(1 - q^{mj})$, $G(q) := \frac{f_4 f_6^2}{f_1 f_3 f_{12}}$, and $B_k(n) := [q^n] G(q)^k$. For every integer $k \ge 1$, let
$$e(k) := \begin{cases} 2 & \text{if } k \equiv 1 \pmod 8, \\ 3 & \text{if } k \equiv 6 \pmod 8, \\ v_2(B_k(3)) & \text{otherwise.} \end{cases}$$
Then $2^{e(k)} \mid B_k(4n+3)$ for every $n \ge 0$, and there exists $n \in \{0, 1\}$ such that $2^{e(k)+1} \nmid B_k(4n+3)$.

---

## 1. Finite Polynomial Jacobi Triple Product and Gauss Identities

Let $\varphi(q) := 1 + 2 \sum_{k \ge 1} q^{k^2}$ and $\psi(q) := \sum_{k \ge 0} q^{k(k+1)/2}$. For $N \ge 1$, define the polynomial in $z$ over $\mathbb{Z}[[q]]$
$$P_N(z) := \prod_{j=0}^{N-1} (1 + q^{2j+1} z)(z + q^{2j+1}) = \sum_{m=0}^{2N} a_{N,m}(q)\, z^m.$$
Each quadratic factor $(1 + q^{2j+1}z)(z + q^{2j+1}) = q^{2j+1} + (1 + q^{4j+2})z + q^{2j+1}z^2$ is palindromic of degree $2$, so by induction on $N$, $a_{N, 2N-m} = a_{N, m}$ for $0 \le m \le 2N$ and $a_{N, 2N} = q^{N^2}$.

Moreover, replacing $z$ by $q^2 z$ shifts each factor and gives the functional equation
$$(z + q^{2N-1}) P_N(q^2 z) = q^{2N-1}(1 + q^{2N+1} z) P_N(z).$$
Comparing the coefficient of $z^{N+k}$ ($1 \le k \le N$) and canceling $q^{2N-1}$ yields the recurrence
$$q^{2k-1}\bigl(1 - q^{2(N+1-k)}\bigr) a_{N, N+k-1} = \bigl(1 - q^{2(N+k)}\bigr) a_{N, N+k}.$$
Descending induction from $k = N$ down to $k = 0$ immediately yields, for every $0 \le k \le N$,
$$a_{N, N+k} \prod_{j=1}^{N+k} (1 - q^{2j}) \prod_{j=1}^{N-k} (1 - q^{2j}) = q^{k^2} \prod_{j=1}^{2N} (1 - q^{2j}).$$
For any fixed degree bound $d$ and $N \ge 2d + 2$:
- if $k \le d$, all three finite products agree with $f_2(q)$ modulo $q^{d+1}$, so canceling the unit $f_2(q)$ gives $a_{N, N+k} f_2(q) \equiv q^{k^2} \pmod{q^{d+1}}$;
- if $k > d$, then $k^2 > d$, so canceling the unit products on the left gives $a_{N, N+k} \equiv 0 \pmod{q^{d+1}}$.

**Identity (J2):** $f_2(q)\varphi(-q) = f_1(q)^2$.
Evaluating $P_N(-1)$ gives $(-1)^N P_N(-1) = \prod_{j=0}^{N-1} (1 - q^{2j+1})^2$, whose product with $f_2(q)^2$ agrees with $f_1(q)^2$ modulo $q^{d+1}$. On the other hand, using $a_{N, N-k} = a_{N, N+k}$,
$$(-1)^N P_N(-1) f_2(q) = \Bigl(a_{N,N} + 2\sum_{k=1}^N (-1)^k a_{N, N+k}\Bigr) f_2(q) \equiv 1 + 2\sum_{k=1}^d (-1)^k q^{k^2} \equiv \varphi(-q) \pmod{q^{d+1}}.$$
Multiplying by $f_2(q)$ gives $f_2(q)\varphi(-q) \equiv f_1(q)^2 \pmod{q^{d+1}}$ for all $d$.

**Identity (J1):** $f_1(q)\psi(q) = f_2(q)^2$.
Evaluating $P_N(q)$ gives $P_N(q) = 2 q^N (1 + q^{2N}) \prod_{j=1}^{N-1} (1 + q^{2j})^2$, so $P_N(q) f_2(q)^2 \equiv 2 q^N f_4(q)^2 \pmod{q^{N+m+1}}$ for $N = 4m+10$. Pairing $m = N + r$ with $m = N - (r+1)$ ($0 \le r < N$) using $a_{N, N-(r+1)} = a_{N, N+r+1}$ gives
$$P_N(q) f_2(q) \equiv 2 q^N \sum_{r=0}^{N-1} q^{r(r+1)} \equiv 2 q^N \psi(q^2) \pmod{q^{N+m+1}}.$$
Multiplying by $f_2(q)$ and extracting $[q^{N+m}]$ cancels $2$ and gives $f_2(q)\psi(q^2) = f_4(q)^2$, hence $f_1(q)\psi(q) = f_2(q)^2$.

---

## 2. Bijective Dissection of $\psi(q)\psi(q^3)$

**Lemma 2.1.** $\psi(q)\psi(q^3) = \varphi(q^6)\psi(q^4) + q\varphi(q^2)\psi(q^{12})$.

*Proof.* Fix $n \ge 0$. Since $T(a) = a(a+1)/2 \iff (2a+1)^2 = 8T(a)+1$, the coefficient $[q^n]\psi(q)\psi(q^3)$ counts pairs of positive odd integers $(x, y)$ with $x^2 + 3y^2 = 8n+4$. Similarly, $[q^n]\varphi(q^6)\psi(q^4)$ counts $(u, s) \in \mathbb{Z} \times (2\mathbb{N}+1)$ with $s^2 + 12u^2 = 2n+1$, and $[q^n]q\varphi(q^2)\psi(q^{12})$ counts $(v, t) \in \mathbb{Z} \times (2\mathbb{N}+1)$ with $4v^2 + 3t^2 = 2n+1$.

Given positive odd $(x, y)$ with $x^2 + 3y^2 = 8n+4$, choose the unique sign $\tilde{y} \in \{y, -y\}$ with $4 \mid (x - \tilde{y})$. Then $p := (x + 3\tilde{y})/4$ and $q' := (x - \tilde{y})/4$ are integers satisfying
$$p^2 + 3q'^2 = \frac{(x+3\tilde{y})^2 + 3(x-\tilde{y})^2}{16} = \frac{x^2 + 3y^2}{4} = 2n+1.$$
Hence exactly one of $p, q'$ is odd and the other is even:
- If $p$ is odd and $q'$ is even, send $(x, y) \mapsto (\mathrm{sgn}(p)\cdot q'/2,\, |p|)$ in the first set.
- If $p$ is even and $q'$ is odd, send $(x, y) \mapsto (\mathrm{sgn}(q')\cdot p/2,\, |q'|)$ in the second set.

The inverse maps $(u, s) \mapsto (|s + 6u|, |s - 2u|)$ and $(v, t) \mapsto (|2v + 3t|, |2v - t|)$ recover $(x, y)$ bijectively, because $(s+6u)-(s-2u) = 8u \equiv 0 \pmod 4$ and $(2v+3t)-(2v-t) = 4t \equiv 0 \pmod 4$. $\square$

---

## 3. Exact $2$-Dissection of $G$ and Congruences `(P1)`, `(P2)`, `(P3)`

By (J1) at $q$ and $q^3$ ($f_1\psi(q) = f_2^2$, $f_3\psi(q^3) = f_6^2$) and (J2) at $q^2$ ($f_4\varphi(-q^2) = f_2^2$), we obtain
$$G(q) = \frac{f_4 f_6^2}{f_1 f_3 f_{12}} = \frac{f_4 \psi(q)\psi(q^3)}{f_2^2 f_{12}} = \frac{\psi(q)\psi(q^3)}{\varphi(-q^2) f_{12}}.$$
Substituting Lemma 2.1 gives the exact $2$-dissection
$$G(q) = E_1(q^2) + q\, O_1(q^2), \qquad E_1(x) := \frac{\varphi(x^3)\psi(x^2)}{\varphi(-x)f_6(x)}, \quad O_1(x) := \frac{\varphi(x)\psi(x^6)}{\varphi(-x)f_6(x)}.$$
Write $\varphi(x) = 1 + 2S(x)$ where $S(x) := \sum_{k \ge 1} x^{k^2}$. Modulo $4$, $\varphi(-x) \equiv \varphi(x)$ and $\varphi(x)^2 = 1 + 4S(x) + 4S(x)^2 \equiv 1$, so $\varphi(-x)^{-1} \equiv \varphi(x) \pmod 4$. Put $a(y) := \psi(y)/f_3(y)$ and $b(y) := \psi(y^3)/f_3(y)$.

- **(P1) $4 \mid B_1(4n+3)$.** Modulo $4$, $O_1(x) \equiv \varphi(x)^2 \psi(x^6)/f_6(x) \equiv b(x^2)$ is purely even in $x$, so $B_1(4n+3) = [x^{2n+1}]O_1(x) \equiv 0 \pmod 4$.
- **(P2) $4 \mid B_2(4n+3)$.** Squaring gives $G(q)^2 = E_2(q^2) + 2q\, W_2(q^2)$ where $E_2(x) := E_1(x)^2 + x O_1(x)^2$ and $W_2(x) := E_1(x)O_1(x)$. Modulo $2$, $\varphi \equiv 1$ gives $W_2(x) \equiv a(x^2)b(x^2)$, which is purely even in $x$. Hence $B_2(4n+3) = 2[x^{2n+1}]W_2(x) \equiv 0 \pmod 4$.
- **(P3) $8 \mid B_{8s+6}(4n+3)$.** Write $G(q)^{8s+6} = (E_2(q^2) + 2q W_2(q^2))^{4s+3}$. In the binomial expansion, every term with $j \ge 3$ is divisible by $2^j \equiv 0 \pmod 8$, while $j = 0$ and $j = 2$ involve only even powers of $q$. Thus modulo $8$,
  $$B_{8s+6}(4n+3) \equiv 2(4s+3)\,[x^{2n+1}]\bigl(W_2(x) E_2(x)^{4s+2}\bigr) \pmod 8.$$
  It therefore suffices to show $[x^{2n+1}](W_2(x)E_2(x)^{4s+2}) \equiv 0 \pmod 4$. By the Frobenius congruence below, $E_2(x)^4 \equiv E_2(x^2)^2 \pmod 4$ is purely even, so it suffices to show $[x^{2n+1}](W_2(x)E_2(x)^2) \equiv 0 \pmod 4$. Modulo $4$, using $\varphi(-x)^{-1} \equiv \varphi(x)$ and $\varphi(x)^2 \equiv \varphi(x^3)^2 \equiv 1$:
  $$E_2(x) \equiv a(x^2)^2 + x b(x^2)^2, \qquad E_2(x)^2 \equiv a(x^2)^4 + x^2 b(x^2)^4 + 2x a(x^2)^2 b(x^2)^2,$$
  $$W_2(x) \equiv \bigl(1 + 2(S(x^3) + S(x))\bigr) a(x^2) b(x^2).$$
  The term $a(x^2)b(x^2)(a(x^2)^4 + x^2 b(x^2)^4)$ is purely even. The remaining terms carry a factor of $2$, so we reduce their inner factor modulo $2$. Since odd squares are $(2m+1)^2 = 8T(m)+1$, the odd-index part of $S(x) + S(x^3)$ is $x(\psi(x^8) + x^2\psi(x^{24}))$. Extracting $[x^{2n+1}]$ leaves $2[y^n]$ of
  $$\bigl(\psi(y^4) + y\psi(y^{12})\bigr)\, a(y)b(y)\bigl(a(y)^4 + y b(y)^4\bigr) + a(y)^3 b(y)^3 \pmod 2.$$
  Modulo $2$, Lemma 2.1 says $\psi(y)\psi(y^3) \equiv \psi(y^4) + y\psi(y^{12})$, and Frobenius gives $a(y)^4 + y b(y)^4 \equiv (\psi(y^4) + y\psi(y^{12}))/f_3(y)^4 \equiv \psi(y)\psi(y^3)/f_3(y)^4$. Substituting both into the display gives
  $$2\frac{(\psi(y)\psi(y^3))^3}{f_3(y)^6} \equiv 0 \pmod 2.$$
  Hence $4 \mid [x^{2n+1}](W_2 E_2^2)$ and $8 \mid B_{8s+6}(4n+3)$. $\square$

---

## 4. Frobenius Reductions, $B_k(3)$, and $B_k(7)$

**Lemma 4.1 (Frobenius).** For every $H \in \mathbb{Z}[[q]]$ and $j \ge 1$, $H(q)^{2^j} \equiv H(q^2)^{2^{j-1}} \pmod{2^j}$.

*Proof.* For $j = 1$, $H(q)^2 \equiv H(q^2) \pmod 2$ since cross terms cancel in pairs. If $A \equiv B \pmod{2^j}$, then $A^2 - B^2 = (A - B)((A - B) + 2B) \equiv 0 \pmod{2^{j+1}}$; induct on $j$. $\square$

**Lemma 4.2 (Uniform odd-index bound).** For every $k \ge 1$ and every $m \ge 0$, $2^{v_2(k)} \mid B_k(2m+1)$.

*Proof.* Write $k = 2^a r$ with $a = v_2(k)$. If $a = 0$ the claim is trivial. If $a \ge 1$, Lemma 4.1 gives $G^{2^a} \equiv G(q^2)^{2^{a-1}} \pmod{2^a}$, so $G^k \equiv G(q^2)^{2^{a-1} r} \pmod{2^a}$, whose odd-degree coefficients vanish. $\square$

**Lemma 4.3 (Residue reductions).** For all $n \ge 0$:
1. $k \equiv 1 \pmod 4 \implies 2 \mid B_k(4n+3)$;
2. $k \equiv 1 \pmod 8 \implies 4 \mid B_k(4n+3)$;
3. $k \equiv 2 \pmod 8 \implies 4 \mid B_k(4n+3)$.

*Proof.* By Lemma 4.1, $G^4 \equiv G(q^4) \pmod 2$ and $G^8 = (G^4)^2 \equiv (G(q^2)^2)^2 = G(q^2)^4 \equiv G(q^4)^2 \pmod 4$. Multiplying a series whose $(4j+3)$-coefficients vanish by any series in $q^4$ preserves vanishing of $(4n+3)$-coefficients. Apply (P1) for (1)–(2) and (P2) for (3). $\square$

**Lemma 4.4 (Exact formulas for $B_k(3)$ and $B_k(7)$).** Since $G(q) \equiv 1 + q + 2q^2 + 4q^3 + 5q^4 + 8q^5 + 12q^6 + 16q^7 \pmod{q^8}$ and $B_k(n) = \sum_{i=0}^n \binom{k}{i} [q^n](G - 1)^i$:
1. $6 B_k(3) = k(k+2)(k+7)$, and $B_k(3) > 0$ for $k \ge 1$;
2. $B_k(7) = 16\binom{k}{1} + 96\binom{k}{2} + 180\binom{k}{3} + 148\binom{k}{4} + 60\binom{k}{5} + 12\binom{k}{6} + \binom{k}{7}$.

**Lemma 4.5 (Exactness witnesses at $n = 1$).**
1. If $k \equiv 9 \pmod{16}$, then $B_k(7) \equiv 4 \pmod 8$, so $8 \nmid B_k(7)$.
2. If $k \equiv 14 \pmod{16}$, then $B_k(7) \equiv 8 \pmod{16}$, so $16 \nmid B_k(7)$.

*Proof.* By Vandermonde's identity $\binom{k+P}{i} = \binom{k}{i} + \sum_{j=1}^i \binom{P}{j}\binom{k}{i-j}$ for $i \le 7$:
- For $P = 32$, $8 \mid \binom{32}{j}$ for all $1 \le j \le 7$, so $B_k(7) \pmod 8$ has period $32$ in $k$. Direct evaluation gives $B_9(7) = 45\,972 \equiv 4 \pmod 8$ and $B_{25}(7) = 8\,109\,100 \equiv 4 \pmod 8$.
- For $P = 64$, $16 \mid \binom{64}{j}$ for all $1 \le j \le 7$, so $B_k(7) \pmod{16}$ has period $64$ in $k$. Direct evaluation gives $B_{14}(7) = 382\,216$, $B_{30}(7) = 22\,540\,440$, $B_{46}(7) = 275\,155\,624$, and $B_{62}(7) = 1\,707\,301\,688$, all congruent to $8 \pmod{16}$. $\square$

---

## 5. Completion of the Proof of Conjecture 6.2

From $1 + v_2(B_k(3)) = v_2(k) + v_2(k+2) + v_2(k+7)$ (Lemma 4.4(1)), we split on $k \pmod 8$:

- **$k \equiv 3, 7 \pmod 8$:** $v_2(k) = v_2(k+2) = 0$ and $v_2(k+7) = 1$, so $v_2(B_k(3)) = 0$. Trivially $2^0 \mid B_k(4n+3)$ and $2^1 \nmid B_k(3)$.
- **$k \equiv 5 \pmod 8$:** $v_2(B_k(3)) = 0 + 0 + 2 - 1 = 1$. Lemma 4.3(1) gives $2 \mid B_k(4n+3)$, and $n = 0$ gives $4 \nmid B_k(3)$.
- **$k \equiv 1 \pmod 8$:** Here $e(k) = 2$. Lemma 4.3(2) gives $4 \mid B_k(4n+3)$. If $k \equiv 1 \pmod{16}$, then $v_2(B_k(3)) = 0 + 0 + 3 - 1 = 2$ so $8 \nmid B_k(3)$; if $k \equiv 9 \pmod{16}$, Lemma 4.5(1) gives $8 \nmid B_k(7)$.
- **$k \equiv 2 \pmod 8$:** $v_2(B_k(3)) = 1 + 2 + 0 - 1 = 2$. Lemma 4.3(3) gives $4 \mid B_k(4n+3)$, and $n = 0$ gives $8 \nmid B_k(3)$.
- **$k \equiv 6 \pmod 8$:** Here $e(k) = 3$. Congruence (P3) gives $8 \mid B_k(4n+3)$. If $k \equiv 6 \pmod{16}$, then $v_2(B_k(3)) = 1 + 3 + 0 - 1 = 3$ so $16 \nmid B_k(3)$; if $k \equiv 14 \pmod{16}$, Lemma 4.5(2) gives $16 \nmid B_k(7)$.
- **$k \equiv 0, 4 \pmod 8$:** $v_2(k+2) = 1$ and $v_2(k+7) = 0$, so $v_2(B_k(3)) = v_2(k)$. Lemma 4.2 gives $2^{v_2(k)} \mid B_k(4n+3)$, and $n = 0$ gives $2^{v_2(k)+1} \nmid B_k(3)$.

This exhausts all integers $k \ge 1$ and completes the proof. $\square$
