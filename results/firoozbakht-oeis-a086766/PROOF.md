# Disproof of Firoozbakht's OEIS A086766 Conjecture

## 1. Statement of the Conjecture

For a positive integer $n$ with $d = \lfloor \log_{10} n \rfloor + 1$ decimal digits, let
$$f_n(r) := 10 n \sum_{i=0}^{r-1} 10^{d i} + 1 = 10 n \cdot \frac{10^{d r} - 1}{10^d - 1} + 1 \qquad (r \ge 1)$$
be the integer obtained by concatenating $n$ with itself $r$ times in base $10$, multiplying by $10$, and adding $1$. Sequence [OEIS A086766](https://oeis.org/A086766) defines $a(n)$ to be the least $r \ge 1$ such that $f_n(r)$ is prime, or $0$ if no such $r$ exists.

On January 7, 2015, Farideh Firoozbakht proved that $a(10^m) = 0$ for many $m \ge 2$ (including all $2 \le m \le 275$) and conjectured on OEIS A086766 (formalized as `OeisA86766.conjecture2` in `google-deepmind/formal-conjectures`):

> **Conjecture (Firoozbakht, 2015):** If $n > 0$ is not of the form $10^m$, then $a(n) \ne 0$.

We disprove this conjecture with an explicit infinite family (starting at $n = 1010$) and an algebraic family of **primitive** (non-periodic in base $10$) counterexamples of arbitrarily large digit length (including the $6$-digit witness $n = 104040$ and a $78$-digit witness).

---

## 2. Infinite Family Starting at $n = 1010$

**Theorem 1.** For every integer $k \ge 2$, let
$$n_k := 10 \cdot \frac{10^{2k} - 1}{99}.$$
Then $n_k$ has $2k$ decimal digits (consisting of $k$ copies of `10`), $n_k$ is not a power of $10$, and $f_{n_k}(r)$ is composite for every $r \ge 1$. Hence $a(n_k) = 0$.

**Proof.** Since $100 \equiv 1 \pmod{99}$, $99 \mid (10^{2k} - 1)$, so $n_k \in \mathbb{Z}$. Moreover $10^{2k-1} < \frac{10}{99}(10^{2k} - 1) < 10^{2k}$ for $k \ge 2$, so $n_k$ has exact digit length $d = 2k$ and strictly lies between $10^{2k-1}$ and $10^{2k}$, hence $n_k \ne 10^m$ for all $m \ge 0$.

For any $r \ge 1$,
$$f_{n_k}(r) = 10 n_k \cdot \frac{10^{2kr} - 1}{10^{2k} - 1} + 1 = \frac{100(10^{2kr} - 1)}{99} + 1 = \frac{10^{2(kr + 1)} - 1}{99} = \frac{(10^{kr + 1} - 1)(10^{kr + 1} + 1)}{99}.$$
Since $k \ge 2$ and $r \ge 1$, we have $kr + 1 \ge 3$ and $10^{kr + 1} \ge 1000$.
- If $kr$ is even, then $kr + 1$ is odd, so $10^{kr+1} \equiv 1 \pmod 9$ and $10^{kr+1} \equiv -1 \pmod{11}$. Thus $f_{n_k}(r) = \frac{10^{kr+1} - 1}{9} \cdot \frac{10^{kr+1} + 1}{11}$, a product of two integers $\ge \frac{999}{9} = 111 > 1$ and $\ge \frac{1001}{11} = 91 > 1$.
- If $kr$ is odd, then $kr + 1$ is even, so $99 \mid (10^{kr+1} - 1)$, and $f_{n_k}(r) = \frac{10^{kr+1} - 1}{99} \cdot (10^{kr+1} + 1)$, a product of two integers $\ge \frac{9999}{99} = 101 > 1$ and $\ge 10001 > 1$.

In both cases $f_{n_k}(r)$ is composite for every $r \ge 1$, so $a(n_k) = 0$. Setting $k = 2$ gives $n_2 = 1010$. $\square$

---

## 3. General Primitive Difference-of-Squares Family & Giant 78-Digit Witness

Even if one asks for **primitive** counterexamples (not equal to a shorter decimal string repeated $k$ times), infinitely many exist.

**Theorem 2.** Let $k \ge 1$, set $M := 10^{2k} - 1$, and suppose integers $n, c, e, g_{1,\mathrm{o}}, g_{2,\mathrm{o}}, g_{1,\mathrm{e}}, g_{2,\mathrm{e}}$ satisfy:
1. $10^{2k-1} < n < 10^{2k}$ (so $n$ has $2k$ decimal digits and is not a power of $10$),
2. $10 n = c^2$ and $c^2 - e^2 = M$ with $0 \le e < c$,
3. $g_{1,\mathrm{o}} g_{2,\mathrm{o}} = M$, $g_{1,\mathrm{o}} \mid (c \cdot 10^k - e)$, $g_{2,\mathrm{o}} \mid (c \cdot 10^k + e)$, with $g_{1,\mathrm{o}} < c \cdot 10^k - e$ and $g_{2,\mathrm{o}} < c \cdot 10^k + e$,
4. $g_{1,\mathrm{e}} g_{2,\mathrm{e}} = M$, $g_{1,\mathrm{e}} \mid (c - e)$, $g_{2,\mathrm{e}} \mid (c + e)$, with $g_{1,\mathrm{e}} < c \cdot 10^{2k} - e$ and $g_{2,\mathrm{e}} < c \cdot 10^{2k} + e$.

Then $f_n(r)$ is composite for every $r \ge 1$, and hence $a(n) = 0$.

**Proof.** Multiplying $f_n(r)$ by $M = 10^{2k} - 1$ and using $10 n = c^2$ and $c^2 - M = e^2$ gives
$$M \cdot f_n(r) = 10 n (10^{2kr} - 1) + M = c^2 \cdot 10^{2kr} - e^2 = \bigl(c \cdot 10^{kr} - e\bigr)\bigl(c \cdot 10^{kr} + e\bigr).$$
Since $10^{2k} \equiv 1 \pmod M$, we have $10^{2kj} \equiv 1 \pmod d$ for every divisor $d \mid M$ and every $j \ge 0$.
- If $r = 2j$ ($j \ge 1$), then $10^{kr} = 10^{2kj} \equiv 1 \pmod{g_{1,\mathrm{e}}, g_{2,\mathrm{e}}}$, so $g_{1,\mathrm{e}} \mid (c \cdot 10^{kr} - e)$ and $g_{2,\mathrm{e}} \mid (c \cdot 10^{kr} + e)$, with quotients strictly exceeding $1$ by (4) and $10^{kr} \ge 10^{2k}$.
- If $r = 2j + 1$ ($j \ge 0$), then $10^{kr} = 10^{2kj} \cdot 10^k \equiv 10^k \pmod{g_{1,\mathrm{o}}, g_{2,\mathrm{o}}}$, so $g_{1,\mathrm{o}} \mid (c \cdot 10^{kr} - e)$ and $g_{2,\mathrm{o}} \mid (c \cdot 10^{kr} + e)$, with quotients strictly exceeding $1$ by (3) and $10^{kr} \ge 10^k$.

Thus $f_n(r)$ is a product of two integers $> 1$ for every $r \ge 1$, so $a(n) = 0$. $\square$

### Explicit Primitive Instances

1. **Minimal $6$-digit primitive ($k = 3$):** $n = 104040$, $c = 1020$, $e = 201$, $(g_{1,\mathrm{o}}, g_{2,\mathrm{o}}) = (99, 10101)$, $(g_{1,\mathrm{e}}, g_{2,\mathrm{e}}) = (819, 1221)$.
2. **Giant $78$-digit primitive ($k = 39$):**
   - $n = 100558839880907801793259217884670002826017800775406752876641328923179557019040$,
   - $c = 1002790306499358826910734486514389551480$,
   - $e = 74755593831351630382001287234042424799$,
   - $(g_{1,\mathrm{o}}, g_{2,\mathrm{o}}) = (82858281,\; 12068799737711189060270270390958267647382160872972974179852946744091879)$,
   - $(g_{1,\mathrm{e}}, g_{2,\mathrm{e}}) = (928034712668007196528733199280347126681,\; 1077545900330710457292735773748431976279)$.
