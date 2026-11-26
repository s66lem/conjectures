# Proof of Mandal–Mohan Conjecture 1.19

## Problem Statement

Let $(F_i)_{i \ge 1}$ be the Fibonacci sequence ($F_1 = F_2 = 1$, $F_{i+2} = F_{i+1} + F_i$).
In *Integral Means of Fibonacci Numbers: Divisibility, Density, and Arithmetic Structure* (`arXiv:2611.32519v1`, 24 November 2026), Sagar Mandal and Mohan proved by a $2$-adic method (Theorem 1.18) that
$$H(n, k) := \frac{n^k}{\displaystyle\sum_{i=1}^n \frac{1}{F_i^k}}$$
is an integer for $k = 1$ if and only if $n \in \{1, 2\}$, and for $k = 2$ if and only if $n \in \{1, 2, 3\}$. Observing that their $2$-adic method does not extend to higher powers, they proposed:

> **Conjecture 1.19 (Mandal–Mohan, 2026).** Let $k \ge 3$. Then
> $$\frac{n^k}{\displaystyle\frac{1}{F_1^k} + \frac{1}{F_2^k} + \cdots + \frac{1}{F_n^k}} \in \mathbb{N}$$
> if and only if $n = 1, 2$.

## Main Theorem

**Theorem.** For all positive integers $n \ge 1$ and $k \ge 1$,
$$H(n, k) = \frac{n^k}{\sum_{i=1}^n F_i^{-k}} \in \mathbb{N} \iff n \in \{1, 2\} \text{ or } (n, k) = (3, 2).$$
In particular, Conjecture 1.19 holds for every $k \ge 3$, and the same short proof recovers Theorem 1.18 for $k = 1, 2$.

## Proof

Write $S_{n,k} := \sum_{i=1}^n F_i^{-k} > 0$. Then $H(n, k) \in \mathbb{N}$ if and only if there exists $m \in \mathbb{N}$ such that $m S_{n,k} = n^k$.

### 1. Isolated-index criterion

**Lemma 1.** *Suppose $n \ge 3$, $k \ge 1$, and there exists an index $q \in \{3, \dots, n\}$ such that:*
1. $\gcd(F_q, F_i) = 1$ *for every $1 \le i \le n$ with $i \ne q$, and*
2. $F_q \ge n$.

*Then $H(n, k) \notin \mathbb{N}$.*

*Proof.* Assume $m S_{n,k} = n^k$ for some $m \in \mathbb{N}$. Set
$$P := \prod_{\substack{1 \le i \le n \\ i \ne q}} F_i^k \in \mathbb{N}_{>0}, \qquad Q := \sum_{\substack{1 \le i \le n \\ i \ne q}} \frac{P}{F_i^k} \in \mathbb{N}.$$
Multiplying $m S_{n,k} = n^k$ by $F_q^k P$ clears all denominators and gives the exact natural-number identity
$$m \cdot (P + F_q^k Q) = n^k F_q^k P.$$
By hypothesis (1), $\gcd(F_q, F_i) = 1$ for every $i \ne q$, so $\gcd(F_q^k, P) = 1$, and therefore
$$\gcd(P + F_q^k Q,\; F_q^k) = \gcd(P, F_q^k) = 1.$$
Since $P + F_q^k Q$ divides $F_q^k \cdot (n^k P)$ and is coprime to $F_q^k$, Euclid's lemma yields
$$(P + F_q^k Q) \mid n^k P.$$
Because $n^k P > 0$, this forces $P + F_q^k Q \le n^k P$.

On the other hand, since $q \ge 3$, both $i = 1$ and $i = 2$ belong to $\{1, \dots, n\} \setminus \{q\}$, and $F_1 = F_2 = 1$, so
$$Q \ge \frac{P}{F_1^k} + \frac{P}{F_2^k} = 2P.$$
Using hypothesis (2), $F_q^k \ge n^k$, we obtain
$$P + F_q^k Q \ge P + 2 F_q^k P > 2 n^k P > n^k P,$$
contradicting $P + F_q^k Q \le n^k P$. $\square$

### 2. Cases $n = 5$ and $n \ge 7$ via Bertrand's postulate

**Lemma 2.** *If $q$ is a prime with $n/2 < q \le n$, then $\gcd(F_q, F_i) = 1$ for every $1 \le i \le n$ with $i \ne q$.*

*Proof.* By the strong divisibility property of the Fibonacci numbers, $\gcd(F_q, F_i) = F_{\gcd(q, i)}$. Since $q$ is prime, $\gcd(q, i) \in \{1, q\}$. If $\gcd(q, i) = q$, then $q \mid i$; since $1 \le i \le n < 2q$, this forces $i = q$, a contradiction. Hence $\gcd(q, i) = 1$ and $\gcd(F_q, F_i) = F_1 = 1$. $\square$

**Lemma 3.** *For every integer $m \ge 7$, $F_m \ge 2m - 1$.*

*Proof.* By strong induction on $m$: $F_7 = 13 \ge 13$ and $F_8 = 21 \ge 15$, and for $m \ge 9$,
$$F_m = F_{m-1} + F_{m-2} \ge (2m - 3) + (2m - 5) = 4m - 8 \ge 2m - 1. \qquad \square$$

Now apply Lemmas 1–3:
- **$n \ge 12$:** Since $\lfloor n/2 \rfloor \ge 6$, Bertrand's postulate guarantees a prime $q$ with $\lfloor n/2 \rfloor < q \le 2\lfloor n/2 \rfloor \le n$. Then $q \ge 7$ and $2q > n$, so Lemma 2 gives $\gcd(F_q, F_i) = 1$ for all $1 \le i \le n$, $i \ne q$, and Lemma 3 gives $F_q \ge 2q - 1 \ge n$. Lemma 1 yields $H(n, k) \notin \mathbb{N}$.
- **$7 \le n \le 11$:** Take $q = 7$. Then $q$ is prime, $2q = 14 > n$, and $F_7 = 13 > n$, so Lemmas 2 and 1 yield $H(n, k) \notin \mathbb{N}$.
- **$n = 5$:** Take $q = 5$. Then $q$ is prime, $2q = 10 > 5$, and $F_5 = 5 \ge 5$, so Lemmas 2 and 1 yield $H(5, k) \notin \mathbb{N}$.

### 3. Remaining small cases $n \in \{1, 2, 3, 4, 6\}$

- **$n = 6$:** Since $F_1 = F_2 = 1$, $F_3 = 2$, $F_4 = 3$, $F_5 = 5$, $F_6 = 8$,
  $$S_{6,k} = 2 + \frac{1}{2^k} + \frac{1}{3^k} + \frac{1}{5^k} + \frac{1}{8^k} = \frac{U_6}{120^k}, \qquad U_6 := 2 \cdot 120^k + 60^k + 40^k + 24^k + 15^k.$$
  For every $k \ge 1$: $2 \nmid U_6$ (only $15^k$ is odd), $3 \nmid U_6$ (only $40^k$ is not divisible by $3$), and $5 \nmid U_6$ (only $24^k$ is not divisible by $5$). Since $6^k \cdot 120^k$ has only prime factors $2, 3, 5$, we have $\gcd(U_6, 6^k \cdot 120^k) = 1$. If $m S_{6,k} = 6^k$, then $m U_6 = 6^k \cdot 120^k$, forcing $U_6 \mid 1$, impossible since $U_6 > 1$.

- **$n = 4$:** Similarly,
  $$S_{4,k} = 2 + \frac{1}{2^k} + \frac{1}{3^k} = \frac{U_4}{6^k}, \qquad U_4 := 2 \cdot 6^k + 3^k + 2^k.$$
  For every $k \ge 1$, $2 \nmid U_4$ (only $3^k$ is odd) and $3 \nmid U_4$ (only $2^k$ is not divisible by $3$), so $\gcd(U_4, 4^k \cdot 6^k) = 1$. Thus $m U_4 = 4^k \cdot 6^k$ forces $U_4 \mid 1$, impossible since $U_4 > 1$.

- **$n = 3$:** Here $S_{3,k} = 2 + 2^{-k} = (2^{k+1} + 1)/2^k$. If $m S_{3,k} = 3^k$, then $m(2^{k+1} + 1) = 3^k \cdot 2^k$. Since $\gcd(2^{k+1} + 1, 2^k) = 1$, we get $(2^{k+1} + 1) \mid 3^k$, so $2^{k+1} + 1 = 3^j$ for some $j \ge 0$.
  - If $j = 2t + 1$ is odd, then $3^j \equiv 3 \pmod 4$, whereas $2^{k+1} + 1 \equiv 1 \pmod 4$ (as $k \ge 1$), a contradiction.
  - If $j = 2t$ is even, then $t \ge 1$ (since $2^{k+1} + 1 \ge 5 > 1$) and
    $$(3^t - 1)(3^t + 1) = 3^{2t} - 1 = 2^{k+1}.$$
    Both $3^t - 1$ and $3^t + 1$ divide $2^{k+1}$, so $3^t - 1 = 2^a$ and $3^t + 1 = 2^b$ with $a < b$ and $2^b - 2^a = 2$. We cannot have $a = 0$ (which gives $3^t = 2$, impossible) nor $a \ge 2$ (which gives $4 \mid (2^b - 2^a) = 2$, impossible). Hence $a = 1$, giving $3^t - 1 = 2$, $t = 1$, $2^{k+1} = 8$, and $k = 2$.
  - Conversely, for $(n, k) = (3, 2)$, $S_{3,2} = 9/4$ and $H(3, 2) = 9/(9/4) = 4 \in \mathbb{N}$.

- **$n = 1, 2$:** Directly, $H(1, k) = 1 \in \mathbb{N}$ and $H(2, k) = 2^k / 2 = 2^{k-1} \in \mathbb{N}$ for every $k \ge 1$. $\square$

## Formal Verification

The entire proof above is formally verified in Lean 4 with zero `sorry`, zero custom axioms, and zero `native_decide` in `lean/Conjectures/MandalMohanFibonacciHarmonic.lean`:
- `MandalMohanFibonacciHarmonic.mandal_mohan_harmonic_iff`
- `MandalMohanFibonacciHarmonic.mandal_mohan_harmonic_den_iff`
- `MandalMohanFibonacciHarmonic.mandal_mohan_conjecture_1_19`
- `MandalMohanFibonacciHarmonic.mandal_mohan_conjecture_1_19_den`
