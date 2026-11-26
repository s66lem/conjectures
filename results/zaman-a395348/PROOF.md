# Proof of Rahid Zaman's OEIS A395348 Conjecture

## 1. Statement

Consider the standard square spiral on $\mathbb{Z}^2$ with labels $k \ge 0$ starting at $0 = (0, 0)$ (as in OEIS A308884 and A274641): ring $r \ge 1$ consists of the $8r$ cells with $\max(|x|, |y|) = r$, beginning at label $(2r - 1)^2$ and ordered along four edges of length $2r$ indexed by $e \in \{0, 1, 2, 3\}$ and offset $0 \le t \le 2r - 1$:

| Edge | $e$ | Coordinates $(x, y)$ | Label $k$ |
| :-: | :-: | :-: | :-: |
| East (E) | $0$ | $(r,\, 1 - r + t)$ | $(2r - 1)^2 + t$ |
| North (N) | $1$ | $(r - 1 - t,\, r)$ | $(2r - 1)^2 + 2r + t$ |
| West (W) | $2$ | $(-r,\, r - 1 - t)$ | $(2r - 1)^2 + 4r + t$ |
| South (S) | $3$ | $(1 - r + t,\, -r)$ | $(2r - 1)^2 + 6r + t$ |

Two players, Black and Red, alternate turns in rounds $n = 0, 1, 2, \dots$. On round $n$:
- Black places a queen at the smallest spiral label $a(n) \ge 0$ whose cell $(x, y)$ is unoccupied and not attacked by any existing Red queen (i.e. shares none of $x$, $y$, $x + y$, $x - y$ with any previously placed Red queen).
- Red then places a queen at the smallest spiral label $b(n) \ge 0$ whose cell $(x, y)$ is unoccupied and not attacked by any existing Black queen (including Black's $n$-th queen).

The sequence $a(n)$ is [OEIS A395348](https://oeis.org/A395348) (with companion Red sequence [OEIS A395349](https://oeis.org/A395349)). On November 18, 2026, Rahid Zaman conjectured:

> **Conjecture (Zaman, OEIS A395348).** *For every integer $n \ge 2$,*
> $$a(n + 4) = a(n) + 8n + 34.$$

We prove this conjecture by determining the exact closed-form coordinates of both players' queens for every round $n \ge 0$.

**Theorem 1.** *Let $B(n)$ and $R(n)$ denote the coordinates of the $n$-th Black and Red queens. For $0 \le n \le 3$,*
$$B(0) = (0, 0),\quad B(1) = (1, 1),\quad B(2) = (-2, 0),\quad B(3) = (3, 1),$$
$$R(0) = (2, -1),\quad R(1) = (-1, 2),\quad R(2) = (-1, -2),\quad R(3) = (2, 3).$$
*For every $h \ge 0$ and $j \in \{0, 1, 2, 3\}$, writing $n = 4h + 4 + j$:*
- *$j = 0$ ($r = 2h + 3$): $B(n) = (-r, 1)$, $R(n) = (2, -r)$.*
- *$j = 1$ ($r = 2h + 4$): $B(n) = (r, 0)$, $R(n) = (-1, r)$.*
- *$j = 2$ ($r = 2h + 4$): $B(n) = (-r, 0)$, $R(n) = (-1, -r)$.*
- *$j = 3$ ($r = 2h + 5$): $B(n) = (r, 1)$, $R(n) = (2, r)$.*

*Consequently, $a(n + 4) = a(n) + 8n + 34$ for every integer $n \ge 2$.*

## 2. Proof

### Step 1: Monotonicity of Each Color's Labels

For any fixed color (Black or Red), the set of occupied cells and the set of opponent-attacked cells are monotone increasing from turn to turn. When a player places a queen at label $k^*$, every label $k < k^*$ is already occupied or attacked by the opponent, and $k^*$ itself becomes occupied. Therefore, on that player's next turn, no label $\le k^*$ can be legal: it suffices to verify that every label strictly between the player's previous placement and the predicted target is attacked by an existing opposing queen, and that the predicted target itself is neither occupied nor attacked by any existing opposing queen.

### Step 2: Base Rounds $0 \le n \le 7$

Direct greedy evaluation of rounds $0 \le n \le 7$ (sixteen placements, all within ring $r \le 5$, label $\le 93$) confirms the table of Theorem 1:

| $n$ | Black $B(n)$ | $a(n)$ | Red $R(n)$ | $b(n)$ |
| :-: | :-: | :-: | :-: | :-: |
| $0$ | $(0, 0)$ | $0$ | $(2, -1)$ | $9$ |
| $1$ | $(1, 1)$ | $2$ | $(-1, 2)$ | $15$ |
| $2$ | $(-2, 0)$ | $18$ | $(-1, -2)$ | $21$ |
| $3$ | $(3, 1)$ | $28$ | $(2, 3)$ | $31$ |
| $4$ | $(-3, 1)$ | $38$ | $(2, -3)$ | $47$ |
| $5$ | $(4, 0)$ | $52$ | $(-1, 4)$ | $61$ |
| $6$ | $(-4, 0)$ | $68$ | $(-1, -4)$ | $75$ |
| $7$ | $(5, 1)$ | $86$ | $(2, 5)$ | $93$ |

### Step 3: Exact Line-Set Invariants for Every Block $h \ge 1$

For any integer $h \ge 1$, let $\mathcal{B}_h = \{B(i) : 0 \le i \le 4h + 3\}$ and $\mathcal{R}_h = \{R(i) : 0 \le i \le 4h + 3\}$ be the predicted sets of queens placed through round $4h + 3$. For a finite set $S \subset \mathbb{Z}^2$, denote its four projected line sets by
$$X(S) = \{x : (x, y) \in S\},\quad Y(S) = \{y : (x, y) \in S\},\quad D_+(S) = \{x + y : (x, y) \in S\},\quad D_-(S) = \{x - y : (x, y) \in S\}.$$

**Lemma 2.1 (Line-Set Invariants).** *For every $h \ge 1$:*
1. $X(\mathcal{B}_h) = [-(2h + 2),\, 2h + 3] \setminus \{-1, 2\}$, $Y(\mathcal{B}_h) = \{0, 1\}$,
   $D_+(\mathcal{B}_h) = \{2m : -(h + 1) \le m \le h + 2\}$, and
   $D_-(\mathcal{B}_h) = \{2m : -(h + 1) \le m \le h + 1\}$.
2. $X(\mathcal{R}_h) = \{-1, 2\}$, $Y(\mathcal{R}_h) = [-(2h + 2),\, 2h + 3] \setminus \{0, 1\}$,
   $D_+(\mathcal{R}_h) = \{2m + 1 : -(h + 2) \le m \le h + 2\}$, and
   $D_-(\mathcal{R}_h) = \{2m + 1 : -(h + 2) \le m \le h + 1\}$.

*Proof.* For $h = 1$, direct enumeration of the eight points of $\mathcal{B}_1$ and eight points of $\mathcal{R}_1$ from Step 2 gives:
- $X(\mathcal{B}_1) = \{-4, -3, -2, 0, 1, 3, 4, 5\} = [-4, 5] \setminus \{-1, 2\}$, $Y(\mathcal{B}_1) = \{0, 1\}$, $D_+(\mathcal{B}_1) = \{-4, -2, 0, 2, 4, 6\}$, $D_-(\mathcal{B}_1) = \{-4, -2, 0, 2, 4\}$.
- $X(\mathcal{R}_1) = \{-1, 2\}$, $Y(\mathcal{R}_1) = \{-4, -3, -2, -1, 2, 3, 4, 5\} = [-4, 5] \setminus \{0, 1\}$, $D_+(\mathcal{R}_1) = \{-5, -3, -1, 1, 3, 5, 7\}$, $D_-(\mathcal{R}_1) = \{-5, -3, -1, 1, 3, 5\}$.

Advancing from $h$ to $h + 1$ adds the four Black queens $(-(2h+3), 1)$, $(2h+4, 0)$, $(-(2h+4), 0)$, $(2h+5, 1)$, whose line values are:
- $x \in \{-(2h+3), 2h+4, -(2h+4), 2h+5\}$, extending $X(\mathcal{B}_h)$ to $[-(2h+4), 2h+5] \setminus \{-1, 2\}$;
- $y \in \{0, 1\}$, preserving $Y(\mathcal{B}_h) = \{0, 1\}$;
- $x + y \in \{-(2h+2), 2h+4, -(2h+4), 2h+6\}$, extending $D_+(\mathcal{B}_h)$ by $\{-(2h+4), 2h+6\}$;
- $x - y \in \{-(2h+4), 2h+4, -(2h+4), 2h+4\}$, extending $D_-(\mathcal{B}_h)$ by $\{-(2h+4), 2h+4\}$.

Similarly, the four new Red queens $(2, -(2h+3))$, $(-1, 2h+4)$, $(-1, -(2h+4))$, $(2, 2h+5)$ have:
- $x \in \{-1, 2\}$, preserving $X(\mathcal{R}_h) = \{-1, 2\}$;
- $y \in \{-(2h+3), 2h+4, -(2h+4), 2h+5\}$, extending $Y(\mathcal{R}_h)$ to $[-(2h+4), 2h+5] \setminus \{0, 1\}$;
- $x + y \in \{-(2h+1), 2h+3, -(2h+5), 2h+7\}$, extending $D_+(\mathcal{R}_h)$ by $\{-(2h+5), 2h+7\}$;
- $x - y \in \{2h+5, -(2h+5), 2h+3, -(2h+3)\}$, extending $D_-(\mathcal{R}_h)$ by $\{-(2h+5), 2h+5\}$. $\square$

In particular, **every Black queen has $x + y$ and $x - y$ even, whereas every Red queen has $x + y$ and $x - y$ odd**.

### Step 4: Inductive Verification of Block $h \ge 1$

Assume Theorem 1 holds through round $4h + 3$ ($h \ge 1$). We verify each of the eight turns of block $h$ in chronological order. By Step 1, on each turn it suffices to check that (a) every spiral cell strictly between the player's previous placement and predicted target shares $x$, $y$, $x + y$, or $x - y$ with an already-placed opposing queen, and (b) the predicted target is unoccupied and shares none of the four line values with any existing opposing queen. Note that every predicted target lies strictly after all previously placed queens of the same color and has strictly larger $\max(|x|, |y|)$ or strictly larger spiral label than all previously placed queens of the other color, except when both lie on the same ring — in every case, $X(\mathcal{B}_h)$ and $Y(\mathcal{B}_h)$ vs. $X(\mathcal{R}_h)$ and $Y(\mathcal{R}_h)$ are completely disjoint from the opposing color's target (since $y \in \{0, 1\}$ for Black and $y \notin \{0, 1\}$ for Red), so no predicted target is ever already occupied.

1. **Black, $j = 0$ ($r = 2h + 3$):** Previous Black $(r, 1)$, target $(-r, 1)$. Existing Red set is $\mathcal{R}_h$.
   - *Gap:* cells on ring $r$ from $(r, 2)$ through $(r, r)$ (E), all of N ($y = r$), and $(-r, r - 1)$ down to $(-r, 2)$ (W). Every gap cell satisfies $2 \le y \le r = 2h + 3$, so $y \in Y(\mathcal{R}_h)$.
   - *Target $(-r, 1)$:* $x = -(2h + 3) \notin \{-1, 2\} = X(\mathcal{R}_h)$, $y = 1 \notin Y(\mathcal{R}_h)$, and $x \pm y$ are even while $D_\pm(\mathcal{R}_h)$ contain only odd integers. Legal.

2. **Red, $j = 0$ ($r = 2h + 3$):** Previous Red $(2, r)$, target $(2, -r)$. Existing Black set is $\mathcal{B}_h \cup \{(-r, 1)\}$, so $X = [-r, r] \setminus \{-1, 2\}$, $Y = \{0, 1\}$, $D_+ = 2[-(h+1), h+2]$, $D_- = 2[-(h+2), h+1]$.
   - *Gap:* N edge with $-r \le x \le 1$ ($y = r$), all of W ($x = -r$), and S edge with $-(r - 1) \le x \le 1$ ($y = -r$). Every cell with $x \ne -1$ satisfies $x \in [-r, r] \setminus \{-1, 2\} = X$. The only two remaining gap cells are $(-1, r)$ (attacked via $x + y = r - 1 = 2h + 2 \in D_+$) and $(-1, -r)$ (attacked via $x - y = r - 1 = 2h + 2 \in D_-$).
   - *Target $(2, -r)$:* $x = 2 \notin X$, $y = -r \notin \{0, 1\} = Y$, and $x \pm y$ are odd while $D_\pm$ contain only even integers. Legal.

3. **Black, $j = 1$ ($r = 2h + 4$):** Previous Black $(-(r - 1), 1)$, target $(r, 0)$. Existing Red set is $\mathcal{R}_h \cup \{(2, -(r - 1))\}$, so $X = \{-1, 2\}$, $Y = [-(r - 1), r - 1] \setminus \{0, 1\}$, $D_+ = 2[-(h+2), h+2] + 1$, $D_- = 2[-(h+2), h+2] + 1$.
   - *Gap:* on ring $r - 1$, W edge with $-(r - 1) \le y \le 0$ ($x = -(r - 1)$) and all of S ($y = -(r - 1)$); on ring $r$, E edge with $-(r - 1) \le y \le -1$ ($x = r$). Every cell with $y \ne 0$ satisfies $y \in [-(r - 1), -1] \subset Y$. The sole remaining cell is $(-(r - 1), 0)$, which has $x + y = -(r - 1) = -(2h + 3) \in D_+$.
   - *Target $(r, 0)$:* $x = r \notin \{-1, 2\}$, $y = 0 \notin Y$, and $x \pm y$ are even. Legal.

4. **Red, $j = 1$ ($r = 2h + 4$):** Previous Red $(2, -(r - 1))$, target $(-1, r)$. Existing Black set adds $(r, 0)$ to turn 2, giving $X = [-(r - 1), r] \setminus \{-1, 2\}$, $Y = \{0, 1\}$, $D_+ = 2[-(h+1), h+2]$, $D_- = 2[-(h+2), h+2]$.
   - *Gap:* on ring $r - 1$, S edge with $3 \le x \le r - 1$; on ring $r$, all of E ($x = r$) and N edge with $0 \le x \le r - 1$ ($y = r$). Every cell with $x \ne 2$ lies in $X$. Since $(2, -(r - 1))$ is the previous Red queen, the sole remaining gap cell with $x = 2$ is $(2, r)$, which has $x - y = -(r - 2) = -(2h + 2) \in D_-$.
   - *Target $(-1, r)$:* $x = -1 \notin X$, $y = r \notin \{0, 1\}$, and $x \pm y$ are odd. Legal.

5. **Black, $j = 2$ ($r = 2h + 4$):** Previous Black $(r, 0)$, target $(-r, 0)$. Existing Red set adds $(-1, r)$ to turn 3, giving $X = \{-1, 2\}$, $Y = [-(r - 1), r] \setminus \{0, 1\}$, $D_+ = 2[-(h+2), h+2] + 1$, $D_- = 2[-(h+3), h+2] + 1$.
   - *Gap:* on ring $r$, E edge with $1 \le y \le r$, all of N ($y = r$), and W edge with $1 \le y \le r - 1$. Every cell with $y \ne 1$ satisfies $2 \le y \le r$, so $y \in Y$. The only two remaining gap cells are $(r, 1)$ (with $x + y = r + 1 = 2h + 5 \in D_+$) and $(-r, 1)$ (with $x + y = -(r - 1) = -(2h + 3) \in D_+$).
   - *Target $(-r, 0)$:* $x = -r \notin \{-1, 2\}$, $y = 0 \notin Y$, and $x \pm y$ are even. Legal.

6. **Red, $j = 2$ ($r = 2h + 4$):** Previous Red $(-1, r)$, target $(-1, -r)$. Existing Black set adds $(-r, 0)$ to turn 4, giving $X = [-r, r] \setminus \{-1, 2\}$, $Y = \{0, 1\}$, $D_+ = 2[-(h+2), h+2]$, $D_- = 2[-(h+2), h+2]$.
   - *Gap:* on ring $r$, N edge with $-r \le x \le -2$, all of W ($x = -r$), and S edge with $-(r - 1) \le x \le -2$. Every gap cell has $x \in [-r, -2] \subset X$.
   - *Target $(-1, -r)$:* $x = -1 \notin X$, $y = -r \notin \{0, 1\}$, and $x \pm y$ are odd. Legal.

7. **Black, $j = 3$ ($r = 2h + 5$):** Previous Black $(-(r - 1), 0)$, target $(r, 1)$. Existing Red set adds $(-1, -(r - 1))$ to turn 5, giving $X = \{-1, 2\}$, $Y = [-(r - 1), r - 1] \setminus \{0, 1\}$, $D_+ = 2[-(h+3), h+2] + 1$, $D_- = 2[-(h+3), h+2] + 1$.
   - *Gap:* on ring $r - 1$, W edge with $-(r - 1) \le y \le -1$ and all of S ($y = -(r - 1)$); on ring $r$, E edge with $-(r - 1) \le y \le 0$. Every cell with $y \ne 0$ satisfies $y \in [-(r - 1), -1] \subset Y$. The sole remaining gap cell is $(r, 0)$, which has $x + y = r = 2h + 5 \in D_+$.
   - *Target $(r, 1)$:* $x = r \notin \{-1, 2\}$, $y = 1 \notin Y$, and $x \pm y$ are even. Legal.

8. **Red, $j = 3$ ($r = 2h + 5$):** Previous Red $(-1, -(r - 1))$, target $(2, r)$. Existing Black set adds $(r, 1)$ to turn 6, giving $X = [-(r - 1), r] \setminus \{-1, 2\}$, $Y = \{0, 1\}$, $D_+ = 2[-(h+2), h+3]$, $D_- = 2[-(h+2), h+2]$.
   - *Gap:* on ring $r - 1$, S edge with $0 \le x \le r - 1$ ($y = -(r - 1)$); on ring $r$, all of E ($x = r$) and N edge with $3 \le x \le r - 1$. Every cell with $x \ne 2$ lies in $X$. The sole remaining gap cell is $(2, -(r - 1))$, which has $x + y = -(r - 3) = -(2h + 2) \in D_+$.
   - *Target $(2, r)$:* $x = 2 \notin X$, $y = r \notin \{0, 1\}$, and $x \pm y$ are odd. Legal.

This completes the induction on $h \ge 1$ and proves the coordinate table of Theorem 1 for all $n \ge 0$.

### Step 5: Derivation of Zaman's Recurrence

Substituting the Black coordinates for $n = 4h + 4 + j$ ($h \ge 0$) into the spiral label formula $k = (2r - 1)^2 + 2re + t$:
- $j = 0$ ($r = 2h + 3$, W edge $e = 2$, $t = r - 2$): $a(n) = (2r - 1)^2 + 4r + (r - 2) = 4r^2 + r - 1$.
- $j = 1$ ($r = 2h + 4$, E edge $e = 0$, $t = r - 1$): $a(n) = (2r - 1)^2 + (r - 1) = 4r^2 - 3r$.
- $j = 2$ ($r = 2h + 4$, W edge $e = 2$, $t = r - 1$): $a(n) = (2r - 1)^2 + 4r + (r - 1) = 4r^2 + r$.
- $j = 3$ ($r = 2h + 5$, E edge $e = 0$, $t = r$): $a(n) = (2r - 1)^2 + r = 4r^2 - 3r + 1$.

For any $n = 4h + 4 + j \ge 4$, advancing $n \mapsto n + 4$ replaces $r$ by $r + 2$, giving:
- $j = 0$: $4(r + 2)^2 + (r + 2) - 1 - (4r^2 + r - 1) = 16r + 18 = 16(2h + 3) + 18 = 32h + 66 = 8(4h + 4) + 34 = 8n + 34$.
- $j = 1$: $4(r + 2)^2 - 3(r + 2) - (4r^2 - 3r) = 16r + 10 = 16(2h + 4) + 10 = 32h + 74 = 8(4h + 5) + 34 = 8n + 34$.
- $j = 2$: $4(r + 2)^2 + (r + 2) - (4r^2 + r) = 16r + 18 = 16(2h + 4) + 18 = 32h + 82 = 8(4h + 6) + 34 = 8n + 34$.
- $j = 3$: $4(r + 2)^2 - 3(r + 2) + 1 - (4r^2 - 3r + 1) = 16r + 10 = 16(2h + 5) + 10 = 32h + 90 = 8(4h + 7) + 34 = 8n + 34$.

Finally, for $n = 2$ and $n = 3$, Step 2 yields:
$$a(6) = 68 = 18 + 8 \cdot 2 + 34 = a(2) + 8 \cdot 2 + 34, \qquad a(7) = 86 = 28 + 8 \cdot 3 + 34 = a(3) + 8 \cdot 3 + 34.$$
Thus $a(n + 4) = a(n) + 8n + 34$ for every integer $n \ge 2$. $\square$
