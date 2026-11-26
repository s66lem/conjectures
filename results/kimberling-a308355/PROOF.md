# Exact Agreement Between OEIS A308355 and Row $n$ of A128628

**Sources.**
- [OEIS A308355](https://oeis.org/A308355) (*Limiting row sequence of the array A128628*, Clark Kimberling, May 2019): *"Conjecture: The length of maximal initial segment of this sequence that is identical to row $n$ of A128628 is $\mathrm{A025065}(n+1)$, for $n \ge 1$."*
- [OEIS A025065](https://oeis.org/A025065) (*Number of palindromic partitions of $n$*, Clark Kimberling, May 24, 2019): *"Conjecture: $a(n)$ is the length of maximal initial segment of $\mathrm{A308355}(n-1)$ that is identical to row $n$ of A128628, for $n \ge 2$."*

**Theorem.** For every integer $n \ge 1$, the row limit A308355 of A128628 exists, and the exact length of the maximal initial segment on which row $n$ of A128628 agrees with A308355 is $\mathrm{A025065}(n) = \sum_{r=0}^{\lfloor n/2 \rfloor} p(r)$. Consequently:
1. The corrected count $\mathrm{A025065}(n)$ (OEIS A025065 conjecture) holds for every $n \ge 1$.
2. The displayed conjecture on OEIS A308355 ($\mathrm{A025065}(n+1)$) holds if and only if $n$ is even, and fails for every odd $n = 2m+1 \ge 1$ by $p(m+1) > 0$.

---

## 1. Block Decomposition and Existence of the Row Limit

Write each integer partition of $n$ as a weakly decreasing tuple of positive integers, ordered in descending lexicographic order (OEIS A080577). Row $n$ of A128628 records the lengths (number of parts) of all partitions of $n$ in this order. Let $p(r)$ denote the number of partitions of $r$, with $p(0) = 1$ (the empty partition).

Group the partitions of $n \ge 1$ into consecutive blocks indexed by the remainder $r \in \{0, 1, \dots, n-1\}$ corresponding to largest part $n - r$. Because $n - r$ strictly decreases as $r$ increases, the blocks appear consecutively in descending lexicographic order. Removing the leading part $n - r$ from each partition in block $r$ leaves precisely the partitions of $r$ whose parts are at most $n - r$, still in descending lexicographic order. Thus block $r$ of row $n$ consists of $1 + \mathrm{len}(\tau)$ as $\tau$ ranges over partitions of $r$ with largest part at most $n - r$.

Whenever $2r \le n$ (equivalently, $r \le n - r$), every partition of $r$ automatically has all parts at most $r \le n - r$. Block $r$ of row $n$ therefore coincides with the unrestricted block
$$B(r) := \bigl(1 + \mathrm{len}(\tau) : \tau \vdash r \text{ in descending lex order}\bigr),$$
which has length $p(r) \ge 1$. For every $R \ge 0$ and every $n \ge \max(1, 2R)$, row $n$ begins with the concatenation $B(0) \Vert B(1) \Vert \cdots \Vert B(R)$ of length $\sum_{r=0}^R p(r) \ge R + 1$. Hence the row limit exists and equals the infinite concatenation $B(0) \Vert B(1) \Vert B(2) \Vert \cdots$, which is A308355.

---

## 2. Exact Maximal Common Prefix Length

Fix $n \ge 1$ and set $m := \lfloor n/2 \rfloor$ and $S(n) := \sum_{r=0}^m p(r)$. Since $2r \le n$ for every $0 \le r \le m$, row $n$ and A308355 agree on their first $S(n)$ entries (blocks $B(0)$ through $B(m)$).

- If $n \in \{1, 2\}$, then $m + 1 = n$, so row $n$ has total length $S(n)$ ($1$ for $n = 1$; $2$ for $n = 2$) and terminates immediately after block $m$. Hence the maximal common prefix has length exactly $S(n)$.
- If $n \ge 3$, then $m + 1 < n$, so row $n$ has a nonempty block for $r = m + 1$ starting at $0$-based index $S(n)$ (containing at least the all-$1$s tail $(1^{m+1})$ since $n - (m+1) \ge 1$). Every tail $\tau$ in block $m+1$ of row $n$ has sum $m+1$ and maximum part at most $n - (m+1) < m + 1$, so $\tau$ must have at least $2$ parts; thus the entry at index $S(n)$ in row $n$ is at least $3$. Meanwhile, the first partition of $m+1$ in descending lexicographic order is the single-part partition $(m+1)$, so the first entry of $B(m+1)$ at index $S(n)$ in A308355 is $1 + 1 = 2 \ne 3$.

Therefore row $n$ and A308355 agree at all indices $i < S(n)$ and disagree at index $S(n)$, so the exact maximal common prefix length is $S(n)$.

---

## 3. Palindromic Partitions Bijection

A partition $\lambda$ of $n$ can be arranged as a palindrome if and only if at most one part size occurs with odd multiplicity (proven by peeling off matching pairs from the outer ends of a palindrome).

Define a bijection between palindromic partitions $\lambda \vdash n$ and pairs $(r, \tau)$ with $0 \le r \le \lfloor n/2 \rfloor$ and $\tau \vdash r$:
- **Forward map:** Given a palindromic partition $\lambda \vdash n$, halve the multiplicity of every part size (keeping $\lfloor m_x(\lambda)/2 \rfloor$ copies of each part $x$) to obtain a partition $\tau$ of some $r \le \lfloor n/2 \rfloor$. At most one part size $c$ has odd multiplicity, and when it exists it equals $c = n - 2r > 0$.
- **Inverse map:** Given $0 \le r \le \lfloor n/2 \rfloor$ and $\tau \vdash r$, double every part multiplicity of $\tau$ and, if $c := n - 2r > 0$, insert one copy of $c$, sorting in weakly decreasing order. Every part other than $c$ has even multiplicity, so the resulting partition of $n$ is palindromic, and halving its multiplicities recovers $\tau$ exactly.

Hence $\mathrm{A025065}(n) = \sum_{r=0}^{\lfloor n/2 \rfloor} p(r) = S(n)$.

---

## 4. Disproof of the OEIS A308355 Conjecture for Every Odd $n \ge 1$

For even $n = 2m$, $\lfloor n/2 \rfloor = \lfloor (n+1)/2 \rfloor = m$, so $\mathrm{A025065}(n) = \mathrm{A025065}(n+1)$. For odd $n = 2m + 1$, $\lfloor (n+1)/2 \rfloor = m + 1$, so
$$\mathrm{A025065}(2m+2) = \mathrm{A025065}(2m+1) + p(m+1) > \mathrm{A025065}(2m+1).$$
Thus the OEIS A308355 conjecture fails for every odd $n \ge 1$:
- $n = 1$: row $1 = (1)$, limit starts $(1, 2, \dots)$, agreement is $1 = \mathrm{A025065}(1)$, while $\mathrm{A025065}(2) = 2$.
- $n = 3$: row $3 = (1, 2, 3)$, limit starts $(1, 2, 2, \dots)$, agreement is $2 = \mathrm{A025065}(3)$, while $\mathrm{A025065}(4) = 4$.
- $n = 5$: row $5 = (1, 2, 2, 3, 3, 4, 5)$, limit starts $(1, 2, 2, 3, 2, 3, 4, \dots)$, agreement is $4 = \mathrm{A025065}(5)$, while $\mathrm{A025065}(6) = 7$. $\square$
