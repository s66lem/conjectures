# Disproof of OEIS A108569 Parity Conjecture

## Conjecture Statement
- **Source:** Farideh Firoozbakht (OEIS [A108569](https://oeis.org/A108569), Jul 5, 2005); formalized as open in `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/108569.lean`).
- **Statement:** Let $A = \{n \in \mathbb{N}_{>0} : \varphi(n) = \varphi(n + \varphi(n))\}$, ordered as $a_0 < a_1 < a_2 < \dots$ with $a_0 = 1$. Conjecture: every term $a_k$ with $k > 0$ (i.e., every solution $n > 1$) is even.

## Verdict: DISPROVED

There exist odd solutions $n > 1$ — in fact, infinitely many.

### Explicit Counterexample
$$n = 5{,}095{,}354{,}107 = 3 \times 1033 \times 1{,}644{,}193$$

All three factors ($3$, $1033$, $1{,}644{,}193$) are prime and distinct, so $n > 1$ is odd and:
$$\varphi(n) = (3 - 1)(1033 - 1)(1{,}644{,}193 - 1) = 2 \times 1032 \times 1{,}644{,}192 = 3{,}393{,}612{,}288.$$

Adding $n$ and $\varphi(n)$:
$$n + \varphi(n) = 5{,}095{,}354{,}107 + 3{,}393{,}612{,}288 = 8{,}488{,}966{,}395 = 3 \times 5 \times 7 \times 13 \times 19 \times 327{,}317.$$

All six factors ($3, 5, 7, 13, 19, 327{,}317$) are prime and distinct, hence:
$$\varphi(n + \varphi(n)) = 2 \times 4 \times 6 \times 12 \times 18 \times 327{,}316 = 3{,}393{,}612{,}288 = \varphi(n).$$

Since $1 \in A$, $n \in A$, $1 < n$, and $A$ is infinite (containing $2^m$ for all $m \ge 2$), $n = a_k$ for $k = |\{x \in A : x < n\}| \ge 1$, directly refuting $\forall k > 0,\ \operatorname{Even}(a_k)$.

### Infinite Family of Odd Solutions
Since $3 \mid n$ and $3 \mid (n + \varphi(n))$, multiplying by $3^j$ ($j \ge 0$) scales both sides by $3^j$:
$$\varphi(3^j n) = 3^j \varphi(n) = 3^j \varphi(n + \varphi(n)) = \varphi(3^j(n + \varphi(n))) = \varphi(3^j n + \varphi(3^j n)).$$
Thus $n_j = 3^j \cdot 5{,}095{,}354{,}107$ ($j \ge 0$) is an infinite family of odd terms in A108569.

### How It Was Found
Setting $n = d p$ and $m = n + \varphi(n) = M q$ with odd $(d, M)$ and primes $p \nmid d$, $q \nmid M$ reduces $\varphi(n) = \varphi(m)$ and $m = n + \varphi(n)$ to the exact linear system with $B = \varphi(d)$, $D = \varphi(M)$, $g = \gcd(B, D)$, $b = B/g$, $e = D/g$, $k = (d+B)e - bM$:
$$t = \frac{M - d}{k}, \qquad p = 1 + e t, \qquad q = 1 + b t.$$
Taking $d = 3099 = 3 \cdot 1033$ and $M = 25935 = 3 \cdot 5 \cdot 7 \cdot 13 \cdot 19$ yields $k = 3$, $t = 7612$, $p = 1{,}644{,}193$, $q = 327{,}317$, both prime.

## Verification
Run [`verify.py`](verify.py) (uses exhaustive trial division for every prime factor and verifies $n$ plus $n_j$ for $j = 0 \dots 5$).
