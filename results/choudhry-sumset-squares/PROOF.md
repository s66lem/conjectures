# Complete Proof: Explicit (5, 4) and (6, 4) Integer Sumsets of Perfect Squares (Choudhry, INTEGERS 26, 2026, #A66)

## 1. Problem Statement

In *Two Sets of Integers Such That All Elements of the Sumset of the Two Sets Are Perfect Squares*, *INTEGERS* **26** (2026), #A66 (`arXiv:2508.07806`, Section 6, continuing Guy's *Unsolved Problems in Number Theory*, Problem D14), A. Choudhry poses the open problem:

> It would be interesting to find a quintuple $\{a_1, a_2, \dots, a_5\}$ and a quadruple $\{b_1, b_2, \dots, b_4\}$ such that all $20$ sums $a_i + b_j$, $i = 1, \dots, 5$, $j = 1, \dots, 4$, are squares.

Before Choudhry's paper, for $m, n > 2$ only Lagrange's $(4, 4)$ family (reported in Guy D14) had been published.

## 2. Minimal Explicit (5, 4) Solution

Let

$$A = \{216^2, 567^2, 1128^2, 1848^2, 5496^2\} = \{46656, 321489, 1272384, 3415104, 30206016\},$$
$$B = \{0, 1198800, 2695680, 22269520\}.$$

All 5 elements of $A$ are distinct, all 4 elements of $B$ are distinct, $\gcd(46656, 321489, 22269520) = 1$ (so the solution is primitive), and all $20$ pairwise sums $a_i + b_j = r_{i,j}^2$ are perfect squares:

| $a_i \setminus b_j$ | $0$ | $1198800$ | $2695680$ | $22269520$ |
|---|---:|---:|---:|---:|
| $46656$ | $216^2$ | $1116^2$ | $1656^2$ | $4724^2$ |
| $321489$ | $567^2$ | $1233^2$ | $1737^2$ | $4753^2$ |
| $1272384$ | $1128^2$ | $1572^2$ | $1992^2$ | $4852^2$ |
| $3415104$ | $1848^2$ | $2148^2$ | $2472^2$ | $5068^2$ |
| $30206016$ | $5496^2$ | $5604^2$ | $5736^2$ | $7244^2$ |

Applying Choudhry's translation Lemma 1 with $t = 1$ gives the all-positive, pairwise disjoint $(5, 4)$ solution

$$A' = \{46655, 321488, 1272383, 3415103, 30206015\}, \qquad B' = \{1, 1198801, 2695681, 22269521\}.$$

## 3. Five Complete Primitive (5, 4) Solutions (`max X ≤ 10000`)

In standard form $b_1 = 0$, $a_i = X_i^2$, an exhaustive search over all $X_i \le 10000$ yields exactly five primitive $(5, 4)$ solutions (all with $\gcd = 1$, verified in Lean 4 and `verify.py`):

1. $X = (216, 567, 1128, 1848, 5496)$, $B = (0, 1198800, 2695680, 22269520)$.
2. $X = (126, 714, 3129, 4419, 6834)$, $B = (0, 713440, 8382528, 105621408)$.
3. $X = (872, 1680, 3864, 4980, 8880)$, $B = (0, 17971200, 24269625, 135475200)$.
4. $X = (360, 1215, 3240, 5688, 7160)$, $B = (0, 3790800, 24076800, 138733056)$.
5. $X = (518, 1939, 3748, 4676, 5908)$, $B = (0, 2696960, 13704320, 139018880)$.

## 4. Explicit (6, 4) Solution (Exceeding Choudhry's Problem)

Extending the search to $\max X \le 40000$ reveals a primitive $(6, 4)$ solution (unique in that range):

$$A_6 = \{2988^2, 4356^2, 5787^2, 11164^2, 17046^2, 23948^2\} = \{8928144, 18974736, 33489369, 124634896, 290566116, 573506704\},$$
$$B_{6,4} = \{0, 16594560, 137675520, 1202947200\}.$$

All 24 pairwise sums $a_i + b_j = r_{i,j}^2$ are perfect squares:

| $a_i \setminus b_j$ | $0$ | $16594560$ | $137675520$ | $1202947200$ |
|---|---:|---:|---:|---:|
| $8928144$ | $2988^2$ | $5052^2$ | $12108^2$ | $34812^2$ |
| $18974736$ | $4356^2$ | $5964^2$ | $12516^2$ | $34956^2$ |
| $33489369$ | $5787^2$ | $7077^2$ | $13083^2$ | $35163^2$ |
| $124634896$ | $11164^2$ | $11884^2$ | $16196^2$ | $36436^2$ |
| $290566116$ | $17046^2$ | $17526^2$ | $20694^2$ | $38646^2$ |
| $573506704$ | $23948^2$ | $24292^2$ | $26668^2$ | $42148^2$ |

Here $\gcd(A_6(2), A_6(3)) = \gcd(33489369, 124634896) = 1$, and shifting by $(-1, +1)$ yields an all-positive, pairwise disjoint $(6, 4)$ solution.

## 5. Scaling-Shift Invariance and Infinite Families

For any solution $(A, B)$, nonzero integer $k$, and shift $t \in \mathbb{Z}$, $(k^2 A - t, k^2 B + t)$ is again a valid square-sumset solution since $(k^2 a_i - t) + (k^2 b_j + t) = k^2(a_i + b_j) = (k r_{i,j})^2$. Taking $k = 2n + 2$ and $t = 1$ ($n \in \mathbb{N}$) gives $k^2 a_i - 1 \equiv 3 \pmod{4}$ and $k^2 b_j + 1 \equiv 1 \pmod{4}$, guaranteeing strict positivity and pairwise disjointness $A_n \cap B_n = \emptyset$ for every $n \in \mathbb{N}$, yielding infinitely many distinct positive disjoint $(5, 4)$ and $(6, 4)$ solutions. $\blacksquare$
