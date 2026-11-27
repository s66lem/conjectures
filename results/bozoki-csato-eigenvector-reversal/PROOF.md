# Full Rank Reversal Between Right and Inverse Left Eigenvectors for Four Alternatives

## Problem Statement

In *Theoretical properties of the eigenvector method* ([arXiv:2603.24274](https://arxiv.org/abs/2603.24274), math.OC, March 2026), S. Bozóki and L. Csató review Example 5 (a $5 \times 5$ pairwise comparison matrix whose right Perron eigenvector $w^R$ and inverse left Perron eigenvector $w^{-L}$ induce strictly opposite rankings) and pose the following open question (Section *Right–left asymmetry*):

> It remains an open question whether an analogous example exists for four alternatives. In addition, Example 5 calls for finding a class of pairwise comparison matrices for which the right and inverse left eigenvectors lead to a reversed order of the alternatives.

A *pairwise comparison matrix* (PCM) is an entrywise-positive matrix $A \in \mathbb{R}_{>0}^{n \times n}$ satisfying $a_{ij} a_{ji} = 1$ for all $i, j$. Its right Perron eigenvector $w^R > 0$ satisfies $A w^R = \lambda_{\max} w^R$, and its inverse left Perron eigenvector $w^{-L} > 0$ has entries $(w^{-L})_i = 1 / v_i$, where $v^T A = \lambda_{\max} v^T$ with $v > 0$.

## Main Results

### Theorem 1 (Characterization of the Full-Reversal Class)

Let $A \in \mathbb{R}_{>0}^{n \times n}$ be a PCM with positive right eigenvector $w$ and positive left eigenvector $v$ at eigenvalue $\lambda$. Define the diagonally rescaled matrix $B = D_w^{-1} A D_w$ (entries $b_{ij} = a_{ij} w_j / w_i$) and the entrywise product $u = v \circ w$ ($u_i = v_i w_i$). Then:

1. $B$ is a PCM with constant row sums $\sum_j b_{ij} = \lambda$ and positive left eigenvector $u$ ($u^T B = \lambda u^T$).
2. $w$ is strictly decreasing and $v^{-1}$ is strictly increasing if and only if $u$ is strictly decreasing and
   $$\frac{u_j}{u_i} < \frac{w_j}{w_i} < 1 \qquad \text{for all } 1 \le i < j \le n.$$
3. Conversely, for any constant-row-sum PCM $B$ with strictly decreasing positive left eigenvector $u$ and any positive vector $w$ satisfying $u_j / u_i < w_j / w_i < 1$ for all $i < j$, the matrix $A = D_w B D_w^{-1}$ is a PCM whose right and inverse left Perron eigenvectors induce strictly opposite rankings.

### Theorem 2 (Explicit 4×4 Rational Witness)

The $4 \times 4$ rational pairwise comparison matrix

$$A_4 = \begin{pmatrix}
1 & \frac{34}{11} & \frac{17}{48} & \frac{34}{33} \\
\frac{11}{34} & 1 & \frac{77}{32} & 2 \\
\frac{48}{17} & \frac{32}{77} & 1 & \frac{64}{77} \\
\frac{33}{34} & \frac{1}{2} & \frac{77}{64} & 1
\end{pmatrix}$$

has exact Perron eigenvalue $\lambda_{\max} = 5$, right Perron eigenvector $w = (34, 33, 32, 22)^T$ (inducing the strict order $1 \succ 2 \succ 3 \succ 4$), and left Perron eigenvector $v = \bigl(\frac{42}{17}, \frac{27}{11}, \frac{77}{32}, \frac{26}{11}\bigr)^T$, whose entrywise reciprocal $v^{-1} = \bigl(\frac{17}{42}, \frac{11}{27}, \frac{32}{77}, \frac{11}{26}\bigr)^T$ satisfies $\frac{17}{42} < \frac{11}{27} < \frac{32}{77} < \frac{11}{26}$, inducing the strictly opposite order $4 \succ 3 \succ 2 \succ 1$.

### Theorem 3 (Sharpness at $n = 3$)

For every $3 \times 3$ PCM $A$, setting $q = (a_{12} a_{23} / a_{13})^{1/3} > 0$, the vector $w_0 = (a_{13} q,\; a_{23} / q,\; 1)^T$ satisfies both $A w_0 = (1 + q + q^{-1}) w_0$ and $(w_0^{-1})^T A = (1 + q + q^{-1}) (w_0^{-1})^T$. By positive eigenvector uniqueness, $w^R$ and $w^{-L}$ are always positively proportional for $n = 3$, so $n = 4$ is the exact minimum dimension for full (or any) rank reversal.

## Self-Contained Proof

### Lemma (Uniqueness of Positive Eigenvectors)

Let $M \in \mathbb{R}_{>0}^{n \times n}$ ($n \ge 1$) have positive eigenvectors $M w = \lambda w$ and $v^T M = \lambda v^T$. If $M x = \mu x$ with $x > 0$, then $\mu = \lambda$ and $x = t w$ for some $t > 0$.

*Proof.* Taking the dot product with $v$ gives $\mu (v^T x) = v^T M x = \lambda (v^T x)$; since $v^T x > 0$, we have $\mu = \lambda$. Moreover $\lambda > 0$ from $M w = \lambda w > 0$. Set $t := \min_i (x_i / w_i) > 0$ and $z := x - t w \ge 0$, with $z_k = 0$ at a minimizer $k$ and $M z = \lambda z$. If $z \ne 0$, then since $M > 0$ we get $0 < (M z)_k = \lambda z_k = 0$, a contradiction. Thus $z = 0$ and $x = t w$. Applying the same argument to $M^T$ yields left-eigenvector uniqueness.

### Construction and Verification of $A_4$

Start from the constant-row-sum $4 \times 4$ PCM

$$B = \begin{pmatrix}
1 & 3 & \frac{1}{3} & \frac{2}{3} \\
\frac{1}{3} & 1 & \frac{7}{3} & \frac{4}{3} \\
3 & \frac{3}{7} & 1 & \frac{4}{7} \\
\frac{3}{2} & \frac{3}{4} & \frac{7}{4} & 1
\end{pmatrix},$$

whose rows each sum to $5$ and whose left eigenvector at eigenvalue $5$ is $u = (84, 81, 77, 52)^T$. Choosing $w = (34, 33, 32, 22)^T$ satisfies
$$\frac{81}{84} < \frac{33}{34} < 1, \qquad \frac{77}{81} < \frac{32}{33} < 1, \qquad \frac{52}{77} < \frac{22}{32} < 1.$$
By Theorem 1, $A_4 = D_w B D_w^{-1}$ has right eigenvector $w$, left eigenvector $v = u / w = \bigl(\frac{42}{17}, \frac{27}{11}, \frac{77}{32}, \frac{26}{11}\bigr)^T$, and eigenvalue $5$. By the Lemma, every positive right/left eigenvector of $A_4$ is a positive multiple of $w$ or $v$, giving full rank reversal independent of normalization.

## Verification

- Lean 4 formalization: [BozokiCsatoEigenvectorReversal.lean](file:///C:/Users/s6lem/.t3/projects/conjectures/lean/Conjectures/BozokiCsatoEigenvectorReversal.lean)
- Standalone verifier: [verify.py](file:///C:/Users/s6lem/.t3/projects/conjectures/results/bozoki-csato-eigenvector-reversal/verify.py)
