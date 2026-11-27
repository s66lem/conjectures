# Disproof of Hart–Rowley Conjecture 1.3 (`arXiv:2502.00777v1`, *Archiv der Mathematik* 2026)

## 1. Conjecture Statement

In Section 1 of *A note on involution prefixes in Coxeter groups* (`arXiv:2502.00777v1`, published in *Archiv der Mathematik* 2026), S. B. Hart and P. J. Rowley define, for a Coxeter group $(W, R)$ with Coxeter length $\ell$:
- $u \in W$ is a **prefix** of $w \in W$ if $\ell(u) + \ell(u^{-1} w) = \ell(w)$ (equivalently, some reduced expression for $u$ extends to a reduced expression for $w$).
- $\mathrm{ipref}(w) = \{u \in W : u \text{ is a prefix of } w \text{ and } o(u) = 2\}$ is the set of involution prefixes of $w$, and $A(w) \subseteq \mathrm{ipref}(w)$ is the subset of maximal Coxeter length.
- $W$ has the **ancestor property** if $|A(w)| = 1$ for every $w \in W \setminus \{1\}$, in which case the unique element $a(w) \in A(w)$ is the **ancestor** of $w$.
- **Conjecture 1.2 (Ancestor Conjecture):** Every finite Coxeter group has the ancestor property. *(Recently proved unconditionally for all Coxeter groups by C. Gaetz and Y. Gao, `arXiv:2610.22857`.)*
- When $W$ has the ancestor property, every $w \in W$ has a unique greedy **ancestor decomposition** $w = a_1 a_2 \cdots a_k$ with $a_i = a(a_i \cdots a_k)$ for $1 \le i \le k$; its **involution length** is $\ell_{\mathrm{inv}}(w) = k$ (with $\ell_{\mathrm{inv}}(1) = 0$).

> **Conjecture 1.3 (Hart–Rowley).** Suppose Conjecture 1.2 holds, and let $W$ be a finite Coxeter group. For each $w \in W$, the involution length of $w$ is at most the rank of $W$.

*(Section 3 of `arXiv:2502.00777v1` states that Conjectures 1.2 and 1.3 were verified in Magma for $F_4, E_6, H_3, H_4$; we show this computational claim is false for Conjecture 1.3 under the paper's definitions.)*

## 2. Main Counterexample in $H_3$ (Rank 3, Order 120)

Let $W = H_3$ with simple reflections $r_1, r_2, r_3$ and Coxeter matrix
$$m(r_1, r_2) = 3, \qquad m(r_2, r_3) = 5, \qquad m(r_1, r_3) = 2.$$
Consider the length-$7$ element
$$w_1 = r_2 r_3 r_1 r_2 r_3 r_2 r_1 = r_2 r_1 r_3 r_2 r_3 r_2 r_1.$$

1. **Right weak order interval $[1, w_1]$:** The prefixes of $w_1$ are the $9$ elements
   $$1,\quad r_2,\quad r_2 r_1,\quad r_2 r_3,\quad r_2 r_3 r_1,\quad r_2 r_3 r_1 r_2,\quad r_2 r_3 r_1 r_2 r_3,\quad r_2 r_3 r_1 r_2 r_3 r_2,\quad w_1.$$
   Among these $9$ elements, only $r_2$ (length $1$) and $a_1 = r_2 r_3 r_1 r_2$ (length $4$, an involution since $a_1^{-1} = r_2 r_1 r_3 r_2 = r_2 r_3 r_1 r_2 = a_1$) have order $2$. Hence $a(w_1) = a_1$.
2. **Remaining Coxeter element:** Removing $a_1$ leaves
   $$a_1^{-1} w_1 = r_3 r_2 r_1,$$
   a Coxeter element of length $3 = 7 - 4$. Its prefixes are $1, r_3, r_3 r_2, r_3 r_2 r_1$. Since $o(r_3 r_2) = 5 \neq 2$ and $o(r_3 r_2 r_1) = 10 \neq 2$, the unique involution prefix is $a_2 = r_3$.
3. **Final two steps:** Next, $a_2^{-1}(r_3 r_2 r_1) = r_2 r_1$ has prefixes $1, r_2, r_2 r_1$; since $o(r_2 r_1) = 3 \neq 2$, its ancestor is $a_3 = r_2$. Finally $a_3^{-1}(r_2 r_1) = r_1$ is an involution, so $a_4 = r_1$.

Therefore, the exact ancestor decomposition of $w_1$ is
$$w_1 = (r_2 r_3 r_1 r_2)(r_3)(r_2)(r_1), \qquad \ell_{\mathrm{inv}}(w_1) = 4 > 3 = \mathrm{rank}(H_3).$$

A second independent length-$7$ witness in $H_3$ is
$$w_2 = r_2 r_3 r_2 r_3 r_1 r_2 r_3 = (r_2 r_3 r_2)(r_3 r_1)(r_2)(r_3), \qquad \ell_{\mathrm{inv}}(w_2) = 4 > 3.$$

Moreover, direct verification over all $119$ non-identity elements of $H_3$ confirms that Conjecture 1.2 (the ancestor property) holds unconditionally for $H_3$, with $\max_{w \in H_3} \ell_{\mathrm{inv}}(w) = 4$.

## 3. Additional Counterexamples in Exceptional Crystallographic and Non-Crystallographic Types

Exact computation (`verify.py`) and parabolic inheritance ($\ell_{\mathrm{inv}, W}(w) = \ell_{\mathrm{inv}, W_J}(w)$ for every standard parabolic subgroup $W_J \le W$, because every prefix of $w \in W_J$ lies in $W_J$ with unchanged Coxeter length) show that Conjecture 1.3 fails in $H_3$, $F_4$, $E_6$, and $E_7$:

| Type | Rank | $|W|$ | Counterexample $w$ & ancestor decomposition | $\max \ell_{\mathrm{inv}}$ |
|---|---|---|---|---|
| $H_3$ | $3$ | $120$ | $r_2 r_3 r_1 r_2 r_3 r_2 r_1 = (r_2 r_3 r_1 r_2)(r_3)(r_2)(r_1)$ | **$4 > 3$** |
| $F_4$ | $4$ | $1{,}152$ | $r_3 r_4 r_1 r_2 r_3 r_2 r_1 = (r_3 r_1)(r_4 r_2)(r_3)(r_2)(r_1)$ | **$5 > 4$** |
| $E_6$ | $6$ | $51{,}840$ | $r_3 r_2 r_4 r_5 r_6 r_1 r_3 r_4 r_5 r_2 r_4 r_3 r_1 = (r_3 r_2)(r_4 r_1)(r_5 r_3)(r_6 r_4)(r_5 r_2)(r_4)(r_3)(r_1)$ | **$8 > 6$** |
| $E_7$ | $7$ | $2{,}903{,}040$ | inherits $E_6$ ($8 > 7$) | **$\ge 8 > 7$** |

## 4. Lean 4 Formalization Architecture

In [`lean/Conjectures/HartRowleyCoxeterInvolutionLength.lean`](../../lean/Conjectures/HartRowleyCoxeterInvolutionLength.lean), we formalize the refutation over Mathlib's abstract `CoxeterSystem CoxeterMatrix.H₃ W` (zero concrete-group shortcuts, zero custom axioms, zero `native_decide`):
1. Lift `CoxeterMatrix.H₃` via `cs.lift` to a homomorphism `rootRep cs : W →* Equiv.Perm (Fin 30)` on the $30$ roots of $H_3$.
2. Establish `invCount (rootRep cs w) ≤ cs.length w` for all $w \in W$ from the single-root flip property of simple reflections.
3. Certify right multiplication on $120$ canonical reduced words via a reflection-verified braid/cancellation rewriter (`applyCert_sound`), proving surjectivity of `Fin 120 → W` by `cs.simple_induction_right`; injectivity follows from strict monotonicity of the sorted $3$-simple-root action keys (`rootKey`, `sorted_strictMono_aux`).
4. Deduce exact Coxeter lengths `cs.length (cs.wordProd (canonWord k)) = (canonWord k).length`, verify Conjecture 1.2 (`H3_hasAncestorProperty`) for all $119$ non-identity elements, and prove `HasInvolutionLength cs w₁ 4` and `HasInvolutionLength cs w₂ 4` (`4 > 3 = Fintype.card (Fin 3)`).
