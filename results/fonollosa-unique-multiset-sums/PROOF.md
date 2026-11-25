# Resolution of Fonollosa's Problem 4: Exact Minimum Order and Classification for Unique Multiset Sums in Finite Abelian Groups

## Problem Statement

Let $G$ be a finite abelian group (written additively), and let $n \ge 1$. A family $A = (a_0, \dots, a_{n-1}) \in G^n$ has **unique multiset sums** (is *valid*) if the only nonnegative integer multiplicity vector $m = (m_0, \dots, m_{n-1}) \in \mathbb{N}^n$ satisfying
$$\sum_{i=0}^{n-1} m_i = n \qquad \text{and} \qquad \sum_{i=0}^{n-1} m_i a_i = \sum_{i=0}^{n-1} a_i$$
is the all-ones vector $m_0 = \dots = m_{n-1} = 1$.

In *Minimum modulus for the unique multiset-sum problem* ([arXiv:2607.08366v2](https://arxiv.org/abs/2607.08366), §8, Problem 4) and its companion *Ryser, Glynn, and the discrete Fourier transform: orthogonal schemes for the permanent* ([arXiv:2607.09949v2](https://arxiv.org/abs/2607.09949), Remark 1), José A. R. Fonollosa introduced orthogonal DFT permanent evaluators indexed by valid families in finite abelian groups $G$. Using Nisan–Wigderson partial derivatives, he proved $|G| \ge \binom{2n}{n}/2^n \sim 2^n/\sqrt{\pi n}$, proved optimality of $2^{n-1}$ within elementary abelian $2$-groups, checked $n \le 6$ exhaustively, and left open as **Problem 4** whether $2^{n-1}$ is the minimum order over **all** finite abelian groups for every $n \ge 1$.

## Main Theorem

**Theorem 1 (Resolution of Problem 4, Uniqueness of Glynn's Scheme, and Sharpened Cyclic Bound).**
Let $G$ be a finite abelian group and let $n \ge 1$.
1. **Exact minimum order:** If $G$ admits a valid family $A = (a_0, \dots, a_{n-1})$, then
   $$|G| \ge 2^{n-1},$$
   and this bound is attained for every $n \ge 1$ by $G = (\mathbb{Z}/2\mathbb{Z})^{n-1}$ with $a_0 = 0$ and $a_1, \dots, a_{n-1}$ the standard basis.
2. **Complete equality classification:** Equality $|G| = 2^{n-1}$ holds **if and only if** $G \cong (\mathbb{Z}/2\mathbb{Z})^{n-1}$ is an elementary abelian $2$-group of rank $n - 1$ and $A$ is an affine basis of $G$ (i.e., after translating $a_0$ to $0$, the map $(\mathbb{Z}/2\mathbb{Z})^{n-1} \to G$, $(\varepsilon_i) \mapsto \sum_{i=1}^{n-1} \varepsilon_i (a_i - a_0)$, is a group isomorphism).
3. **Disjoint nonzero doubles and sharpened cyclic bound:** After translating $a_0$ to $0$, the $2^{n-1}$ subset sums of $\{a_1, \dots, a_{n-1}\}$ are pairwise distinct and disjoint from the set of nonzero doubles $\{2a_i : 0 \le i < n\} \setminus \{0\}$, so
   $$|G| \ge 2^{n-1} + \bigl|\{2(a_i - a_0) : 0 \le i < n\} \setminus \{0\}\bigr|.$$
   In particular, for every cyclic group $G = \mathbb{Z}/N\mathbb{Z}$ ($N \ge 1$) admitting a valid size-$n$ set,
   $$N \ge 2^{n-1} + \left\lceil \frac{n}{\gcd(2, N)} \right\rceil - 1 = 2^{n-1} + \left\lfloor \frac{n - 1}{\gcd(2, N)} \right\rfloor.$$

## Proof

Translating every entry $a_i \mapsto a_i - c$ preserves validity, because $\sum_i m_i(a_i - c) = \sum_i (a_i - c)$ whenever $\sum_i m_i = n$ and $\sum_i m_i a_i = \sum_i a_i$. Translate so that $a_0 = 0$.

**Lemma 1 (Uniqueness at subset targets).** *For every $S \subseteq \{0, \dots, n-1\}$, if $m \in \mathbb{N}^n$ satisfies $\sum_i m_i = |S|$ and $\sum_i m_i a_i = \sum_{i \in S} a_i$, then $m_i = \mathbf{1}_{i \in S}$ for all $i$.*

*Proof.* Define $m'_i = m_i + \mathbf{1}_{i \notin S}$. Then $\sum_i m'_i = |S| + (n - |S|) = n$ and $\sum_i m'_i a_i = \sum_{i \in S} a_i + \sum_{i \notin S} a_i = \sum_i a_i$. By validity of $A$, $m'_i = 1$ for all $i$, so $m_i = \mathbf{1}_{i \in S}$. In particular (taking $|S| = 1$), the entries $a_0, \dots, a_{n-1}$ are pairwise distinct. $\square$

**Lemma 2 (Distinct subset sums).** *The $2^{n-1}$ subset sums $\sum_{i \in S} a_i$ for $S \subseteq \{1, \dots, n-1\}$ are pairwise distinct.*

*Proof.* Suppose $S, T \subseteq \{1, \dots, n-1\}$ satisfy $\sum_{i \in S} a_i = \sum_{i \in T} a_i$. Without loss of generality $|S| \le |T|$. Pad $S$ with $|T| - |S|$ copies of the anchor index $0$ (where $a_0 = 0$) to obtain a multiplicity vector $m$ with $\sum_i m_i = |T|$ and $\sum_i m_i a_i = \sum_{i \in S} a_i = \sum_{i \in T} a_i$. By Lemma 1, $m_i = \mathbf{1}_{i \in T}$ for every $i$. Since $0 \notin T$, we get $m_0 = |T| - |S| = 0$ and $S = T$. $\square$

Let $U = \{\sum_{i \in S} a_i : S \subseteq \{1, \dots, n-1\}\}$. Lemma 2 immediately gives $|G| \ge |U| = 2^{n-1}$.

**Lemma 3 (Disjointness of nonzero doubles).** *For every $i \in \{0, \dots, n-1\}$ with $2a_i \ne 0$, we have $2a_i \notin U$.*

*Proof.* Suppose $2a_i = \sum_{j \in S} a_j$ for some $S \subseteq \{1, \dots, n-1\}$. Since $2a_i \ne 0$, we have $i \ne 0$ and $S \ne \emptyset$ (so $|S| \ge 1$). Take the multiplicity vector $m$ with $2$ copies of index $i$ and $|S| - 1$ copies of index $0$. Then $\sum_j m_j = |S| + 1 = |S \cup \{0\}|$ and $\sum_j m_j a_j = 2a_i = \sum_{j \in S \cup \{0\}} a_j$. Lemma 1 forces $m_i \in \{0, 1\}$, contradicting $m_i = 2$. $\square$

Setting $D = \{2a_i : 0 \le i < n\} \setminus \{0\}$, Lemmas 2 and 3 yield $U \cap D = \emptyset$ and hence
$$|G| \ge |U| + |D| = 2^{n-1} + |D|.$$
In the cyclic group $G = \mathbb{Z}/N\mathbb{Z}$ ($N \ge 1$), multiplication by $2$ has kernel of size $g = \gcd(2, N) \in \{1, 2\}$, so the image $I = \{2a_i : 0 \le i < n\}$ (which contains $0 = 2a_0$) satisfies $n \le g |I|$, hence $|D| = |I| - 1 \ge \lceil n/g \rceil - 1 = \lfloor (n-1)/g \rfloor$.

**Proof of Equality Classification.**
Suppose $|G| = 2^{n-1}$. Then $U = G$, so $D = \emptyset$ by Lemma 3; thus $2a_i = 0$ for all $i$. Since every $g \in G = U$ is a sum of elements among $a_1, \dots, a_{n-1}$, we have $2g = 0$ for all $g \in G$. Therefore the map
$$\varphi : (\mathbb{Z}/2\mathbb{Z})^{n-1} \to G, \qquad (\varepsilon_1, \dots, \varepsilon_{n-1}) \mapsto \sum_{i=1}^{n-1} \varepsilon_i a_i$$
is a well-defined group homomorphism. By Lemma 2, $\varphi$ is injective; since both finite groups have cardinality $2^{n-1}$, $\varphi$ is an additive group isomorphism sending the $i$-th standard basis vector to $a_i = a_i^{\text{orig}} - a_0^{\text{orig}}$.

Conversely, let $G = (\mathbb{Z}/2\mathbb{Z})^{n-1}$ with $a_0 = 0$ and $a_i = e_i$ ($1 \le i \le n-1$). If $\sum_{i=0}^{n-1} m_i = n$ and $\sum_{i=0}^{n-1} m_i a_i = (1, \dots, 1)$, then each $m_i$ ($1 \le i \le n-1$) is odd, hence $m_i \ge 1$. If any $m_j \ge 3$, then $\sum_{i=1}^{n-1} m_i \ge (n - 2) + 3 = n + 1 > n$, a contradiction. Thus $m_1 = \dots = m_{n-1} = 1$, and $\sum_{i=0}^{n-1} m_i = n$ forces $m_0 = 1$. Translating preserves validity, so every affine basis is valid. $\square$

## Relation to Waring Rank

Over $\mathbb{C}$, character orthogonality for a valid family $A = (a_0, \dots, a_{n-1})$ with $t = \sum_i a_i$ yields
$$x_0 \cdots x_{n-1} = \frac{1}{n!\,|G|} \sum_{\chi \in \widehat{G}} \overline{\chi(t)} \left(\sum_{i=0}^{n-1} \chi(a_i) x_i\right)^n.$$
Thus the numerical lower bound $|G| \ge 2^{n-1}$ alone also follows from the Waring rank $\mathrm{rk}_{\mathbb{C}}(x_0 \cdots x_{n-1}) = 2^{n-1}$ (Carlini, Catalisano, and Geramita, *J. Algebra* 2012, Corollary 3.3). The elementary combinatorial proof above works purely inside $G$ without complex characters or algebraic geometry, and yields both the complete equality classification ($G \cong (\mathbb{Z}/2\mathbb{Z})^{n-1}$ with an affine basis) and the strengthened cyclic bound $N \ge 2^{n-1} + \lfloor (n-1)/\gcd(2, N) \rfloor$.

## Formal Verification

All claims of Theorem 1 are formally verified in Lean 4 in [`lean/Conjectures/FonollosaUniqueMultisetSums.lean`](../../lean/Conjectures/FonollosaUniqueMultisetSums.lean) using only the standard axioms `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`).
