# Disproof of Runbo Li's Twin-Practical Conjecture 1.1 (`NNTDM` 32(3), 2026)

## 1. Conjecture Statement

A positive integer $n \ge 1$ is **practical** (OEIS A005153) if every integer $m$ with $1 \le m \le n$ can be expressed as a sum of distinct positive divisors of $n$.

In Section 1 of *On a conjecture involving twin practical numbers* (*Notes on Number Theory and Discrete Mathematics* **32**(3) (2026), 544–555, DOI `10.7546/nntdm.2026.32.3.544-555`), Runbo Li states:

> **Conjecture 1.1 (Li, 2026).** For any positive integer $C$, there are infinitely many practical numbers $q$ such that $q^C$ and $q^C + 2$ are also practical numbers.

The paper cites previous proofs for $C = 1$ (Margenstern, Melfi) and $C = 2, 4$ (Wang–Sun, `arXiv:1809.01532`), and proves the conjecture for all primes $7 \le C < 100$ (Theorem 1.2).

## 2. Main Theorem (Disproof for $30 \mid C$)

**Theorem 1.** *For every positive integer $q$, the integer $q^{30} + 2$ is not practical. Consequently, for every positive integer $C$ divisible by $30$, there is no positive integer $q$ such that $q^C + 2$ is practical, and Conjecture 1.1 is false.*

**Proof.** Fix $q \ge 1$ and set $n = q^{30} + 2$.

- **Case 1 ($q$ odd).** Then $n = q^{30} + 2 \ge 3$ is odd, so every positive divisor of $n$ is odd. In particular, the only positive divisor of $n$ that is at most $2$ is $1$, whose subset sums are at most $1 < 2$. Hence $2$ cannot be written as a sum of distinct divisors of $n$, so $n$ is not practical.

- **Case 2 ($q$ even).** Then $q \ge 2$, so $n \ge 2^{30} + 2 > 13$. We check $n$ modulo six small prime powers:
  - Modulo $4$: $2 \mid q \implies 4 \mid q^{30}$, so $n \equiv 2 \pmod{4}$ and $4 \nmid n$.
  - Modulo $9$: if $3 \mid q$, then $q^{30} \equiv 0 \pmod{9}$; otherwise $\gcd(q, 9) = 1$, and Euler's theorem gives $q^6 \equiv 1 \pmod{9}$, so $q^{30} = (q^6)^5 \equiv 1 \pmod{9}$. In all cases $n \in \{2, 3\} \pmod{9}$, so $9 \nmid n$.
  - Modulo $5$: $q^{30} = (q^4)^7 q^2 \equiv q^2 \in \{0, 1, 4\} \pmod{5}$ (for $5 \nmid q$, $q^4 \equiv 1 \pmod{5}$), so $n \in \{1, 2, 3\} \pmod{5}$ and $5 \nmid n$.
  - Modulo $7$: $q^{30} = (q^6)^5 \in \{0, 1\} \pmod{7}$, so $n \in \{2, 3\} \pmod{7}$ and $7 \nmid n$.
  - Modulo $11$: $q^{30} = (q^{10})^3 \in \{0, 1\} \pmod{11}$, so $n \in \{2, 3\} \pmod{11}$ and $11 \nmid n$.
  - Modulo $13$: $q^{30} = (q^{12})^2 q^6 \in \{0, 1, 12\} \pmod{13}$ (since $(q^6)^2 = q^{12} \equiv 1 \pmod{13}$ for $13 \nmid q$), so $n \in \{1, 2, 3\} \pmod{13}$ and $13 \nmid n$.

  Because $4 \nmid n$ rules out $4, 8, 12$, $5 \nmid n$ rules out $5, 10$, and $7, 9, 11, 13 \nmid n$, every positive divisor $d \mid n$ with $d \le 13$ must belong to $\{1, 2, 3, 6\}$. Any subset $S$ of divisors of $n$ summing to $13$ can only contain elements $\le 13$, hence $S \subseteq \{1, 2, 3, 6\}$, which forces
  $$\sum_{d \in S} d \le 1 + 2 + 3 + 6 = 12 < 13.$$
  Therefore $13 \le n$ is not a sum of distinct divisors of $n$, and $n$ is not practical.

Finally, if $C = 30 t$ with $t \ge 1$, then $q^C + 2 = (q^t)^{30} + 2$ is not practical for any $q \ge 1$. $\square$

## 3. Exact Characterization of the Local Obstruction

Why does this obstruction appear at $C = 30$? By the Stewart–Sierpiński characterization of practical numbers, an even integer $n$ with $4 \nmid n$ and $9 \nmid n$ satisfies $\sigma(2^{\nu_2(n)} 3^{\nu_3(n)}) \le \sigma(6) = 12$, so practicality requires a prime $p \le 13$ dividing $n$ (i.e., $p \in \{5, 7, 11, 13\}$).

**Theorem 2 (Sharpness).** *For every positive integer $C$, the condition*
$$\forall q \in 2\mathbb{N},\qquad 4 \nmid q^C + 2,\; 9 \nmid q^C + 2,\; 5 \nmid q^C + 2,\; 7 \nmid q^C + 2,\; 11 \nmid q^C + 2,\; 13 \nmid q^C + 2$$
*holds if and only if $30 \mid C$.*

**Proof.** The reverse direction follows from Theorem 1 (writing $q^{30t} = (q^t)^{30}$ with $2 \mid q^t$). Conversely, suppose the condition holds for $C \ge 1$:
- If $2 \nmid C$, then $C \equiv 1$ or $3 \pmod{4}$. Taking $q = 8$ when $C \equiv 1 \pmod{4}$ (since $8^4 \equiv 1 \pmod{5}$ and $8^1 + 2 = 10 \equiv 0 \pmod{5}$) or $q = 2$ when $C \equiv 3 \pmod{4}$ ($2^3 + 2 = 10 \equiv 0 \pmod{5}$) gives $5 \mid q^C + 2$, a contradiction. Thus $2 \mid C$.
- Now $C \equiv 0, 2, 4 \pmod{6}$. Taking $q = 4$ if $C \equiv 2 \pmod{6}$ ($4^2 + 2 = 18$) or $q = 2$ if $C \equiv 4 \pmod{6}$ ($2^4 + 2 = 18$) gives $9 \mid q^C + 2$ (as $2^6 \equiv 4^6 \equiv 1 \pmod{9}$). Thus $3 \mid C$.
- Now $C \equiv 0, 2, 4, 6, 8 \pmod{10}$. Since $q^{10} \equiv 1 \pmod{11}$ for $11 \nmid q$, the even witnesses $q = 8, 16, 2, 4$ satisfy $q^C + 2 \equiv 0 \pmod{11}$ for $C \equiv 2, 4, 6, 8 \pmod{10}$, respectively ($8^2 \equiv 16^4 \equiv 2^6 \equiv 4^8 \equiv 9 \pmod{11}$). Thus $5 \mid C$.

Hence $30 = \mathrm{lcm}(2, 3, 5) \mid C$. $\square$

For comparison, explicit small-exponent witnesses exist for every $C \in \{1, 2, 3, 4, 5, 6\}$: $(q, C) = (2, 1), (2, 2), (4, 3), (2, 4), (4, 5), (2, 6)$ all yield practical triples $(q, q^C, q^C + 2)$ (with $q^C + 2 \in \{4, 6, 66, 18, 1026, 66\}$, all verified in Lean 4).

## 4. Lean 4 Formalization

[`lean/Conjectures/LiTwinPractical.lean`](../../lean/Conjectures/LiTwinPractical.lean) formalizes Theorems 1 and 2, the empty-set consequence `li_conjecture_1_1_empty_of_dvd_thirty`, the refutation `li_conjecture_1_1_false`, and all six small-exponent positive witnesses `small_exponents_witnesses`, using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `sorry`, `admit`, or `native_decide`.
