# Disproof of John M. Campbell's OEIS A189409 Squarefree Conjecture

## Problem Statement

For each $n \ge 0$, let $p_n\# = \prod_{k=0}^{n-1} p_k$ denote the $n$-th primorial (OEIS [A002110](https://oeis.org/A002110), with $p_0\# = 1$, $p_1\# = 2$, $p_2\# = 6$, etc.), and define the sequence
$$a(n) = (p_n\#)^2 + 1 \qquad (\text{OEIS } \text{A189409}).$$

In OEIS [A189409](https://oeis.org/A189409) (Apr 21, 2011) and `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/189409.lean`, `OeisA189409.conjecture_1`), John M. Campbell asked whether every term $a(n)$ is squarefree:
$$\forall n \in \mathbb{N}, \quad \text{Squarefree}(a(n)).$$

## Main Theorem

**Theorem 1 (Disproof and Exact Minimality).**
1. The term $a(9)$ is **not** squarefree:
   $$p_9\# = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 = 223{,}092{,}870,$$
   $$a(9) = 223{,}092{,}870^2 + 1 = 49{,}770{,}428{,}644{,}836{,}901 = 29^2 \cdot 53 \cdot 1{,}116{,}604{,}864{,}937.$$
   In particular, $29^2 = 841 \mid a(9)$, disproving Campbell's conjecture.
2. **Exact minimality:** Every earlier term $a(0), a(1), \dots, a(8)$ is squarefree, so $n = 9$ is the smallest counterexample.

## Proof

### Part 1: Divisibility by $29^2$

Observe modulo $29^2 = 841$ that:
$$p_9\# = 223{,}092{,}870 \equiv 800 \equiv -41 \pmod{841}.$$
Therefore
$$(p_9\#)^2 + 1 \equiv (-41)^2 + 1 = 1681 + 1 = 1682 = 2 \cdot 841 \equiv 0 \pmod{29^2}.$$
Explicitly, $a(9) = 29^2 \cdot 59{,}180{,}057{,}841{,}661 = 29^2 \cdot 53 \cdot 1{,}116{,}604{,}864{,}937$. Since $29 > 1$ is not a unit in $\mathbb{N}$ and $29^2 \mid a(9)$, $a(9)$ is not squarefree.

### Part 2: Exact Minimality ($0 \le n \le 8$)

The first nine terms factor completely into distinct primes as follows:

| $n$ | $p_n\#$ | $a(n) = (p_n\#)^2 + 1$ | Complete prime factorization | Lucas witness $a$ for large prime $q$ |
|---:|---:|---:|---|---|
| 0 | $1$ | $2$ | $2$ | trivial |
| 1 | $2$ | $5$ | $5$ | trivial |
| 2 | $6$ | $37$ | $37$ | trivial |
| 3 | $30$ | $901$ | $17 \cdot 53$ | trivial |
| 4 | $210$ | $44{,}101$ | $44{,}101$ | $a=6$; $q-1 = 2^2 \cdot 3^2 \cdot 5^2 \cdot 7^2$ |
| 5 | $2{,}310$ | $5{,}336{,}101$ | $5{,}336{,}101$ | $a=6$; $q-1 = 2^2 \cdot 3^2 \cdot 5^2 \cdot 7^2 \cdot 11^2$ |
| 6 | $30{,}030$ | $901{,}800{,}901$ | $73 \cdot 12{,}353{,}437$ | $a=6$; $q-1 = 2^2 \cdot 3^2 \cdot 409 \cdot 839$ |
| 7 | $510{,}510$ | $260{,}620{,}460{,}101$ | $1409 \cdot 184{,}968{,}389$ | $a=2$; $q-1 = 2^2 \cdot 11 \cdot 79 \cdot 127 \cdot 419$ |
| 8 | $9{,}699{,}690$ | $94{,}083{,}986{,}096{,}101$ | $94{,}083{,}986{,}096{,}101$ | $a=2$; $q-1 = (p_8\#)^2 = 2^2 \cdot 3^2 \cdots 19^2$ |

Notice that for each of the five large prime factors $q \in \{44{,}101,\ 5{,}336{,}101,\ 12{,}353{,}437,\ 184{,}968{,}389,\ 94{,}083{,}986{,}096{,}101\}$, every prime divisor of $q - 1$ is at most $839$. By Lucas's primality test (checking $a^{q-1} \equiv 1 \pmod q$ and $a^{(q-1)/r} \not\equiv 1 \pmod q$ for every prime $r \mid q - 1$), each $q$ is prime. Every term $a(n)$ for $0 \le n \le 8$ is either prime or a product of two distinct primes, hence squarefree. $\square$

## Remark on Higher Terms

For any prime $p$ and any $n$ with $p_k = p$ for some $k < n$, we have $p \mid p_n\#$, so $a(n) \equiv 1 \pmod p$; hence $p^2 \mid a(n)$ is only possible when $p \equiv 1 \pmod 4$ and $p > p_{n-1}$. An exhaustive modular scan across all $n \le 500$ and all primes $p \le 50{,}000$ reveals that $(n, p) = (9, 29)$ is the unique prime-square divisibility hit in that range.

## Formal Verification

Both the disproof (`disproof_conjecture_1`, `a_9_not_squarefree`) and exact minimality (`squarefree_lt_9`, `minimal_counterexample`) are formally verified in Lean 4 in [`lean/Conjectures/CampbellA189409.lean`](../../lean/Conjectures/CampbellA189409.lean) using only the standard axioms `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`).
