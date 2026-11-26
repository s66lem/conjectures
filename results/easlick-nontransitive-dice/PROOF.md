# Proof of Conjecture 1 of Easlick (`arXiv:2610.40321v2`)

## Conjecture Statement

In *Computer-Assisted Results for $n$-Sided Non-Transitive Dice Taking Face Values in $[n]$* ([arXiv:2610.40321v2](https://arxiv.org/abs/2610.40321), November 2026), Terry Easlick defines the minimal-advantage directed graph $G_n = (V_n, E_n)$ on the set $V_n$ of all $\binom{2n-1}{n}$ non-standard $n$-sided dice with face values in $[n] = \{1, \dots, n\}$, represented as non-decreasing $n$-tuples $\mathbf{x} = (x_1, \dots, x_n)$ with $1 \le x_1 \le \cdots \le x_n \le n$.

Given two dice $D_{\mathbf{x}}, D_{\mathbf{y}} \in V_n$, define the strict-win count
$$W(\mathbf{x}, \mathbf{y}) := \sum_{i=1}^n \sum_{j=1}^n \mathbf{1}_{\{x_i > y_j\}}.$$
The smallest attainable winning probability strictly exceeding $1/2$ is $T(n)/n^2$, where
$$T(n) := \left\lfloor \frac{n^2}{2} \right\rfloor + 1 = \begin{cases} \frac{n^2}{2} + 1 & \text{if } n \text{ is even,} \\[4pt] \frac{n^2 + 1}{2} & \text{if } n \text{ is odd.} \end{cases}$$
A directed edge $D_{\mathbf{x}} \to D_{\mathbf{y}}$ lies in $G_n$ if and only if $W(\mathbf{x}, \mathbf{y}) = T(n)$. A simple directed cycle of length $L \ge 3$ in $G_n$ is a non-transitive cycle of length $L$ with uniform and minimal winning advantage.

Easlick proved computationally (Theorem 1) that $G_3, G_4, G_5$ are acyclic and that $G_6$ has maximum directed cycle length $6$ (attained by two unique $6$-cycles, interchanged by the face-reversal antiautomorphism). After finding cycles of length $n + 1$ for $7 \le n \le 12$, Easlick posed:

**Conjecture 1 (`arXiv:2610.40321v2`).** *$n = 6$ is the largest $n \ge 3$ such that the set of non-standard $n$-sided dice admits a non-transitive cycle of maximum length $n$ with uniform and minimal winning advantage.*

Combined with Easlick's Theorem 1 for $3 \le n \le 6$, establishing that $G_n$ contains a simple directed cycle of length at least $n + 1$ for every $n \ge 7$ implies that the maximum cycle length in $G_n$ strictly exceeds $n$ for all $n \ge 7$, thereby proving Conjecture 1.

## Main Result

**Theorem 1 (Proof of Easlick's Conjecture 1).** *For every integer $n \ge 7$, the directed graph $G_n$ contains a simple directed cycle of length at least $n + 1$. More precisely:*
1. *For every odd $n \ge 11$, $G_n$ contains an explicit simple directed cycle of length $3(n - 7) \ge n + 1$.*
2. *For every even $n \ge 16$, $G_n$ contains an explicit simple directed cycle of length $3(n - 10) \ge n + 1$.*
3. *For each $n \in \{7, 8, 9, 10, 12, 14\}$, $G_n$ contains an explicit simple directed cycle of length $n + 1$.*

*Combining Theorem 1 with Easlick's Theorem 1 (independently re-verified exhaustively for $n = 3, 4, 5, 6$), $n = 6$ is the unique integer $n \ge 3$ for which the maximum length of a non-transitive cycle in $G_n$ equals $n$.*

We also record the natural generalization of Easlick's Prollary 1: for every $n \ge 3$, the face-reversal map $f(x_1, \dots, x_n) = (n + 1 - x_n, \dots, n + 1 - x_1)$ is an involutive antiautomorphism of $G_n$.

## Proof

### The 3-Die Zipper Mechanism

Suppose three base templates $A(x), B(y), C(z) \in V_n$ each consist of $n - 1$ fixed base faces in $\{1, \dots, b - 1\}$ together with a single free top face $x, y, z \in \{b, b + 1, \dots, n\}$, such that:
- $A(x), B(y), C(z)$ have pairwise distinct base multisets (so $A(x) \ne B(y) \ne C(z) \ne A(x)$ for all $x, y, z$);
- $A(x) \to B(y)$ holds whenever $x > y$;
- $B(y) \to C(z)$ holds whenever $y \le z$;
- $C(z) \to A(x)$ holds whenever $z > x$.

Let $m = n - b - 1 \ge 1$. Consider the $3m$-vertex sequence indexed by $q = 0, 1, \dots, m - 1$:
$$D_{3q} = B\bigl(\text{if } q = 0 \text{ then } b \text{ else } b + m - q\bigr), \quad D_{3q+1} = C(b + m + 1 - q), \quad D_{3q+2} = A(b + m - q).$$
Check every vertex and edge:
- **Range:** All top faces lie in $\{b, \dots, b + m + 1\} = \{b, \dots, n\}$.
- **Distinctness:** The $A$-, $B$-, and $C$-blocks are pairwise disjoint by their base multisets. Within each block, the top face takes $m$ distinct values: $\{b, b + 1, \dots, b + m - 1\}$ for $B$, $\{b + 2, \dots, b + m + 1\}$ for $C$, and $\{b + 1, \dots, b + m\}$ for $A$. Hence all $3m$ dice are distinct.
- **Edges:**
  - $D_{3q} \to D_{3q+1}$: if $q = 0$, $b \le b + m + 1$; if $q \ge 1$, $b + m - q \le b + m + 1 - q$. Thus $B \to C$ holds for all $q$.
  - $D_{3q+1} \to D_{3q+2}$: $b + m + 1 - q > b + m - q$. Thus $C \to A$ holds for all $q$.
  - $D_{3q+2} \to D_{3(q+1)}$ (for $q < m - 1$): $b + m - q > b + m - (q + 1)$.
  - Wrap-around $D_{3m - 1} \to D_0$: $A(b + 1) \to B(b)$, since $b + 1 > b$.

Thus any such triple $(A, B, C)$ produces a simple directed cycle of length $3(n - b - 1)$ in $G_n$.

### Case 1: Odd $n = 2k + 1 \ge 11$ ($k \ge 5$)

Here $T(2k + 1) = 2k^2 + 2k + 1$. Set $b = 6$ and define for $6 \le x, y, z \le 2k + 1$:
$$A(x) = (1^k,\; 5^k,\; x), \qquad B(y) = (2^{k-1},\; 3^1,\; 4^k,\; y), \qquad C(z) = (2^1,\; 3^{2k-1},\; z).$$
Each die has length $2k + 1$, non-decreasing faces in $[2k + 1]$, and pairwise distinct base multisets ($1 \in A$ only; $4 \in B$ only). Direct counting gives:
- $W(A(x), B(y)) = k(2k) + 2k + \mathbf{1}_{\{x > y\}} = 2k^2 + 2k + \mathbf{1}_{\{x > y\}} = T(2k+1)$ whenever $x > y$.
- $W(B(y), C(z)) = 1 \cdot 1 + k(2k) + 2k + \mathbf{1}_{\{y > z\}} = 2k^2 + 2k + 1 + \mathbf{1}_{\{y > z\}} = T(2k+1)$ whenever $y \le z$.
- $W(C(z), A(x)) = (2k)k + 2k + \mathbf{1}_{\{z > x\}} = 2k^2 + 2k + \mathbf{1}_{\{z > x\}} = T(2k+1)$ whenever $z > x$.

By the 3-die zipper, $G_n$ has a simple directed cycle of length $3(n - 7)$. For all odd $n \ge 11$, $3(n - 7) \ge n + 1$ (with equality $12 = 11 + 1$ at $n = 11$).

### Case 2: Even $n = 2k \ge 16$ ($k \ge 8$)

Here $T(2k) = 2k^2 + 1$. Set $b = 9$ and define for $9 \le x, y, z \le 2k$:
$$A(x) = (1^{k-1},\; 5^1,\; 8^{k-1},\; x), \qquad B(y) = (2^{k-3},\; 3^2,\; 4^1,\; 7^{k-1},\; y), \qquad C(z) = (2^1,\; 3^{k-2},\; 6^k,\; z).$$
Each die has length $2k$, non-decreasing faces in $[2k]$, and pairwise distinct base multisets ($1 \in A$ only; $7 \in B$ only). Direct counting gives:
- $W(A(x), B(y)) = 1 \cdot k + (k - 1)(2k - 1) + (2k - 1) + \mathbf{1}_{\{x > y\}} = 2k^2 + \mathbf{1}_{\{x > y\}} = T(2k)$ whenever $x > y$.
- $W(B(y), C(z)) = 2 \cdot 1 + 1 \cdot (k - 1) + (k - 1)(2k - 1) + (2k - 1) + \mathbf{1}_{\{y > z\}} = 2k^2 + 1 + \mathbf{1}_{\{y > z\}} = T(2k)$ whenever $y \le z$.
- $W(C(z), A(x)) = 1 \cdot (k - 1) + (k - 2)(k - 1) + k \cdot k + (2k - 1) + \mathbf{1}_{\{z > x\}} = 2k^2 + \mathbf{1}_{\{z > x\}} = T(2k)$ whenever $z > x$.

By the 3-die zipper, $G_n$ has a simple directed cycle of length $3(n - 10)$. For all even $n \ge 16$, $3(n - 10) \ge n + 1$ (giving $18 \ge 17$ at $n = 16$).

### Case 3: Remaining Small Values $n \in \{7, 8, 9, 10, 12, 14\}$

- For $n = 14$ ($k = 7, T(14) = 99$), a 7-base zipper with $b = 8$ works directly:
  $$A_{14}(x) = (1^6, 4^1, 7^6, x), \qquad B_{14}(y) = (2^3, 3^4, 6^6, y), \qquad C_{14}(z) = (2^2, 3^4, 5^7, z),$$
  yielding a simple directed cycle of length $3(14 - 9) = 15 = 14 + 1$ in $G_{14}$.
- For $n \in \{7, 8, 9, 10, 12\}$, the explicit simple directed cycles of length $n + 1$ from Easlick (`Examplemmas 1–2`) are verified directly in both Lean 4 and `verify.py`.

This completes the proof of Conjecture 1 for all $n \ge 7$. $\square$

## Formal Verification

The entire $n \ge 7$ proof (together with `n6_has_cycle_6` and the general antiautomorphism; the $n \le 6$ upper bounds are Easlick's Theorem 1, independently re-verified exhaustively in `verify.py`) is formally verified in Lean 4 (Lean `v4.33.1` + Mathlib) in [`lean/Conjectures/EaslickNontransitiveDice.lean`](../../lean/Conjectures/EaslickNontransitiveDice.lean) with zero `sorry`, zero custom axioms, and zero `native_decide` (`[propext, Classical.choice, Quot.sound]` only):
- `wins_eq_card_pairs`, `minAdvTarget_gt_half`, `minAdvTarget_le_of_gt_half`
- `flipDie_involutive`, `flipDie_antiautomorphism`
- `odd_cycle_exists` (all odd $n \ge 11$, length $3(n - 7)$)
- `even_cycle_exists` (all even $n \ge 16$, length $3(n - 10)$)
- `cycle_7`, `cycle_8`, `cycle_9`, `cycle_10`, `cycle_12`, `cycle_14`, and `n6_has_cycle_6`
- `easlick_conjecture1` (every $n \ge 7$ admits a simple minimal-advantage cycle of length $\ge n + 1$)
