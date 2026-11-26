# Disproof of Talmage's Monotonicity Conjecture for Muñiz's List Reversal

## 1. Problem Statement and Rules

Let $L = (x_1, \dots, x_\ell)$ be a finite sequence of pairwise distinct positive integers with maximum $n = \max(L)$. In Muñiz's list reversal game (Talmage, `arXiv:2611.25115v1`, Section 1), a single legal move on a state $s$ either:

- **combines** two adjacent entries $a, b$ into their sum $a + b$, or
- **splits** one entry $x$ into two adjacent positive integers $a, b$ with $a + b = x$,

subject to the invariant that after every move, all entries of the list remain pairwise distinct integers in $\{1, \dots, n\}$, where $n$ is the maximum of the *initial* list. A list $L$ is **reversible** if some finite sequence of legal moves transforms $L$ into its reverse $L^{\mathrm{rev}} = (x_\ell, \dots, x_1)$.

In the Discussion section of `arXiv:2611.25115v1`, Talmage states:

> "The irreversible lists found by computer search in [Appendix A] suggest a conjecture that reversibility is monotonic in $n$, in the sense that replacing the maximum value $n$ in an irreversible list with $n+1$ (leaving the rest of the list unchanged) must yield an irreversible list. No counterexamples to the conjecture are presently known, but it is not clear if that is an artifact of only having data on short lists."

Let $\mathrm{bump}(L)$ denote the list obtained from $L$ by replacing its unique maximum entry $n$ with $n + 1$.

## 2. Theorem

**Theorem.** *Reversibility under Muñiz's list reversal game is not monotonic in the maximum entry $n$ in either direction:*
1. *$(2, 6)$ is irreversible, whereas $\mathrm{bump}(2, 6) = (2, 7)$ is reversible.*
2. *$(1, 3, 7, 4)$ is reversible, whereas $\mathrm{bump}(1, 3, 7, 4) = (1, 3, 8, 4)$ is irreversible.*

Note that Part 1 disproves the conjecture verbatim (which also conflicts with Talmage's own Corollary that only finitely many irreversible lists of each length exist), while Part 2 disproves the charitable converse ("reversible lists remain reversible when the maximum is incremented by $1$").

## 3. Proof

### 3.1. $(2, 6)$ is irreversible ($n = 6$)

Consider the $7$-element set of states of sum $8$:
$$S_{2,6} = \bigl\{(2, 6),\; (2, 1, 5),\; (2, 5, 1),\; (3, 5),\; (1, 2, 5),\; (3, 1, 4),\; (3, 4, 1)\bigr\}.$$

We list every legal move from every state in $S_{2,6}$ under upper bound $n = 6$:

| State | Legal combines ($\le 6$, distinct) | Legal splits (distinct positive) | Image |
|---|---|---|---|
| $(2, 6)$ | none ($2+6=8>6$) | $6 \to (1,5), (5,1)$ ($2=1+1$ repeats; $6=2+4,3+3$ collide/repeat) | $(2,1,5), (2,5,1)$ |
| $(2, 1, 5)$ | $2+1=3 \to (3,5)$; $1+5=6 \to (2,6)$ | none ($5=1+4,2+3$ collide with $1,2$) | $(3,5), (2,6)$ |
| $(2, 5, 1)$ | $5+1=6 \to (2,6)$ ($2+5=7>6$) | none ($5=1+4,2+3$ collide with $1,2$) | $(2,6)$ |
| $(3, 5)$ | none ($3+5=8>6$) | $3 \to (1,2),(2,1)$; $5 \to (1,4),(4,1)$ ($5=2+3$ collides with $3$) | $(1,2,5), (2,1,5), (3,1,4), (3,4,1)$ |
| $(1, 2, 5)$ | $1+2=3 \to (3,5)$ ($2+5=7>6$) | none ($5=1+4,2+3$ collide with $1,2$) | $(3,5)$ |
| $(3, 1, 4)$ | $3+1=4$ collides; $1+4=5 \to (3,5)$ | none ($3=1+2, 4=1+3$ collide with $1,3$; $4=2+2$ repeats) | $(3,5)$ |
| $(3, 4, 1)$ | $3+4=7>6$; $4+1=5 \to (3,5)$ | none ($3=1+2, 4=1+3$ collide with $1,3$; $4=2+2$ repeats) | $(3,5)$ |

Every legal move from any state in $S_{2,6}$ lands in $S_{2,6}$. Since $(2, 6) \in S_{2,6}$ and $(6, 2) \notin S_{2,6}$, no sequence of legal moves reverses $(2, 6)$.

### 3.2. $(2, 7)$ is reversible ($n = 7$)

The following $4$-move sequence reverses $(2, 7)$ with all intermediate entries distinct and in $\{1, \dots, 7\}$:
$$(2, 7) \xrightarrow{\text{split } 7=1+6} (2, 1, 6) \xrightarrow{\text{combine } 2+1=3} (3, 6) \xrightarrow{\text{split } 6=4+2} (3, 4, 2) \xrightarrow{\text{combine } 3+4=7} (7, 2).$$

### 3.3. $(1, 3, 7, 4)$ is reversible ($n = 7$)

The following $18$-move sequence reverses $(1, 3, 7, 4)$ with all intermediate entries distinct and in $\{1, \dots, 7\}$:
1. $(1, 3, 7, 4) \to (1, 3, 5, 2, 4)$ (split $7 = 5 + 2$)
2. $(1, 3, 5, 2, 4) \to (1, 3, 5, 6)$ (combine $2 + 4 = 6$)
3. $(1, 3, 5, 6) \to (4, 5, 6)$ (combine $1 + 3 = 4$)
4. $(4, 5, 6) \to (3, 1, 5, 6)$ (split $4 = 3 + 1$)
5. $(3, 1, 5, 6) \to (3, 1, 5, 2, 4)$ (split $6 = 2 + 4$)
6. $(3, 1, 5, 2, 4) \to (3, 6, 2, 4)$ (combine $1 + 5 = 6$)
7. $(3, 6, 2, 4) \to (3, 5, 1, 2, 4)$ (split $6 = 5 + 1$)
8. $(3, 5, 1, 2, 4) \to (3, 5, 1, 6)$ (combine $2 + 4 = 6$)
9. $(3, 5, 1, 6) \to (3, 5, 7)$ (combine $1 + 6 = 7$)
10. $(3, 5, 7) \to (1, 2, 5, 7)$ (split $3 = 1 + 2$)
11. $(1, 2, 5, 7) \to (1, 2, 5, 3, 4)$ (split $7 = 3 + 4$)
12. $(1, 2, 5, 3, 4) \to (1, 7, 3, 4)$ (combine $2 + 5 = 7$)
13. $(1, 7, 3, 4) \to (1, 5, 2, 3, 4)$ (split $7 = 5 + 2$)
14. $(1, 5, 2, 3, 4) \to (6, 2, 3, 4)$ (combine $1 + 5 = 6$)
15. $(6, 2, 3, 4) \to (6, 5, 4)$ (combine $2 + 3 = 5$)
16. $(6, 5, 4) \to (6, 5, 3, 1)$ (split $4 = 3 + 1$)
17. $(6, 5, 3, 1) \to (4, 2, 5, 3, 1)$ (split $6 = 4 + 2$)
18. $(4, 2, 5, 3, 1) \to (4, 7, 3, 1)$ (combine $2 + 5 = 7$).

### 3.4. $(1, 3, 8, 4)$ is irreversible ($n = 8$)

Consider the $5$-element set of states of sum $16$:
$$S_{1,3,8,4} = \bigl\{(1, 3, 8, 4),\; (1, 3, 2, 6, 4),\; (1, 3, 6, 2, 4),\; (1, 5, 6, 4),\; (1, 2, 3, 6, 4)\bigr\}.$$

We check every legal move from every state in $S_{1,3,8,4}$ under upper bound $n = 8$:

- **$(1, 3, 8, 4)$:** Combines: $1+3=4$ collides; $3+8=11>8$; $8+4=12>8$. Splits: $3=1+2$ and $4=1+3$ collide with $1$ (and $4=2+2$ repeats); for $8$, the partitions $1+7$ and $3+5$ collide with $1, 3$ and $4+4$ repeats, leaving only $8 \to (2, 6)$ and $(6, 2)$, giving $(1, 3, 2, 6, 4)$ and $(1, 3, 6, 2, 4)$.
- **$(1, 3, 2, 6, 4)$:** Combines: $1+3=4$ collides; $3+2=5 \to (1, 5, 6, 4)$; $2+6=8 \to (1, 3, 8, 4)$; $6+4=10>8$. Splits: $2, 3, 4$ have no collision-free split; for $6$, $1+5$ collides with $1$, $2+4$ collides with $2, 4$, and $3+3$ repeats.
- **$(1, 3, 6, 2, 4)$:** Combines: $1+3=4$ collides; $3+6=9>8$; $6+2=8 \to (1, 3, 8, 4)$; $2+4=6$ collides. Splits: none (same entry set as $(1, 3, 2, 6, 4)$).
- **$(1, 5, 6, 4)$:** Combines: $1+5=6$ collides; $5+6=11>8$; $6+4=10>8$. Splits: $4=1+3$ collides with $1$; $6=1+5, 2+4, 3+3$ collide/repeat; for $5$, $1+4$ collides with $1, 4$, leaving only $5 \to (2, 3)$ and $(3, 2)$, giving $(1, 2, 3, 6, 4)$ and $(1, 3, 2, 6, 4)$.
- **$(1, 2, 3, 6, 4)$:** Combines: $1+2=3$ collides; $2+3=5 \to (1, 5, 6, 4)$; $3+6=9>8$; $6+4=10>8$. Splits: none (same entry set as $(1, 3, 2, 6, 4)$).

Thus $S_{1,3,8,4}$ is closed under all legal moves. Since $(1, 3, 8, 4) \in S_{1,3,8,4}$ and $(4, 8, 3, 1) \notin S_{1,3,8,4}$, the list $(1, 3, 8, 4)$ is irreversible. $\square$
