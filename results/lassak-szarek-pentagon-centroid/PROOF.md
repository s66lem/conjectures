# Disproof of Lassak–Szarek's Centroid Banach–Mazur Distance Conjecture for a Pentagon and a Triangle

## Problem Statement

Let $C, D \subset \mathbb{R}^2$ be planar convex bodies with centroids $\mathrm{cen}(C), \mathrm{cen}(D)$, where $\mathrm{cen}(K) = \frac{1}{\mathrm{area}(K)} \int_K x \, dx$. In *Banach–Mazur distance and related methods of comparing convex bodies* (`arXiv:2611.21947v1`, November 2026), M. Lassak and S. J. Szarek define the *centroid Banach–Mazur distance*
$$d_{\mathrm{BM}}^{\mathrm{cen}}(C, D) = \inf_{a,\, h_\lambda} \bigl\{\lambda > 0 : C \subset a(D) \subset h_\lambda(C) \text{ and } \mathrm{cen}(C) = \mathrm{cen}(a(D)) = \mathrm{cen}(h_\lambda(C))\bigr\},$$
where $a : \mathbb{R}^2 \to \mathbb{R}^2$ ranges over invertible affine transformations and $h_\lambda : \mathbb{R}^2 \to \mathbb{R}^2$ ranges over homotheties of ratio $\lambda > 0$.

For an affine-regular pentagon $F$ and a triangle $T$, Lassak (2024) established the upper bound
$$d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \le \eta := \frac{7 - \sqrt{5}}{2} \approx 2.381966.$$
Lassak and Szarek conjectured that this bound is optimal and posed the explicit open problem:
> **Problem.** Is $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) = \eta$?

We prove that the answer is **no**:
$$d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \le \frac{1 + \cos 24^\circ}{\cos 36^\circ} \approx 2.365272 < \frac{19}{8} = 2.375 < \eta.$$

## 1. Affine Invariance

If $\Phi, \Psi : \mathbb{R}^2 \to \mathbb{R}^2$ are invertible affine transformations, then $\mathrm{cen}(\Phi(K)) = \Phi(\mathrm{cen}(K))$ for every convex body $K$, and $\Phi \circ h_\lambda \circ \Phi^{-1}$ is a homothety of the same ratio $\lambda$ whenever $h_\lambda$ is. Consequently, $d_{\mathrm{BM}}^{\mathrm{cen}}(\Phi(C), \Psi(D)) = d_{\mathrm{BM}}^{\mathrm{cen}}(C, D)$, so it suffices to verify the upper bound for one convenient affine-regular pentagon and one nondegenerate triangle.

## 2. Closed-Form Construction ($\lambda^* = \frac{1 + \cos 24^\circ}{\cos 36^\circ} \approx 2.365272$)

Let $F = \mathrm{conv}\{u_{72^\circ k} : k = 0, 1, 2, 3, 4\}$ be the regular pentagon of circumradius $1$ centred at the origin, where $u_\theta = (\cos \theta, \sin \theta)$. By $5$-fold rotational symmetry, $\mathrm{cen}(F) = 0$. The edge normals of $F$ lie at angles $\nu_k = 36^\circ + 72^\circ k$, and the support function in direction $\nu_k$ is $\cos 36^\circ$, so the Minkowski gauge of $F$ is
$$g_F(\rho u_\phi) = \max_{0 \le k \le 4} \frac{\rho \cos(\phi - \nu_k)}{\cos 36^\circ}.$$

Let $E = \mathrm{conv}\{r u_{48^\circ}, r u_{168^\circ}, r u_{288^\circ}\}$ be the equilateral triangle centred at $0$ with circumradius
$$r = \frac{\cos 36^\circ}{\cos 12^\circ}.$$
Then $\mathrm{cen}(E) = 0$. We verify the two inclusions:

1. **$E \subset F$:**
   - For $\phi = 48^\circ$, the closest edge normal of $F$ is $\nu_0 = 36^\circ$ ($|\phi - \nu_0| = 12^\circ$), so $g_F(r u_{48^\circ}) = r \cos 12^\circ / \cos 36^\circ = 1$.
   - For $\phi = 168^\circ$, the closest edge normal is $\nu_2 = 180^\circ$ ($|\phi - \nu_2| = 12^\circ$), so $g_F(r u_{168^\circ}) = r \cos 12^\circ / \cos 36^\circ = 1$.
   - For $\phi = 288^\circ$, the closest edge normals are $\nu_3 = 252^\circ$ and $\nu_4 = 324^\circ$ ($|\phi - \nu| = 36^\circ$), so $g_F(r u_{288^\circ}) = r \cos 36^\circ / \cos 36^\circ = r = \cos 36^\circ / \cos 12^\circ < 1$.
   Since every vertex of $E$ has $g_F \le 1$, convexity gives $E \subset F$.

2. **$F \subset \lambda^* E$:** The inradius of $E$ is $r/2$, and its three outward edge normals lie at $\mu \in \{108^\circ, 228^\circ, 348^\circ\}$, so the Minkowski gauge of $E$ is
   $$g_E(u_\psi) = \max_{\mu \in \{108^\circ, 228^\circ, 348^\circ\}} \frac{2 \cos(\psi - \mu)}{r}.$$
   Evaluating on the five vertices $u_{72^\circ k}$ of $F$:
   - $\psi = 0^\circ$: closest normal is $348^\circ$ (angular distance $12^\circ$), giving $g_E(u_{0^\circ}) = \frac{2 \cos 12^\circ}{r}$.
   - $\psi = 72^\circ$: closest normal is $108^\circ$ (distance $36^\circ$), giving $g_E(u_{72^\circ}) = \frac{2 \cos 36^\circ}{r}$.
   - $\psi = 144^\circ$: closest normal is $108^\circ$ (distance $36^\circ$), giving $g_E(u_{144^\circ}) = \frac{2 \cos 36^\circ}{r}$.
   - $\psi = 216^\circ$: closest normal is $228^\circ$ (distance $12^\circ$), giving $g_E(u_{216^\circ}) = \frac{2 \cos 12^\circ}{r}$.
   - $\psi = 288^\circ$: closest normals are $228^\circ$ and $348^\circ$ (distance $60^\circ$), giving $g_E(u_{288^\circ}) = \frac{1}{r}$.
   The maximum over all five vertices is attained at $k = 0$ and $k = 3$:
   $$\lambda^* := \frac{2 \cos 12^\circ}{r} = \frac{2 \cos^2 12^\circ}{\cos 36^\circ} = \frac{1 + \cos 24^\circ}{\cos 36^\circ} \approx 2.365272.$$
   Hence $F \subset \lambda^* E$.

Setting $a(T) := \lambda^* E$ (an invertible affine image of any triangle $T$) and $h_{\lambda^*}(x) := \lambda^* x$, we obtain
$$F \subset a(T) \subset h_{\lambda^*}(F) \quad \text{and} \quad \mathrm{cen}(F) = \mathrm{cen}(a(T)) = \mathrm{cen}(h_{\lambda^*}(F)) = 0.$$
Therefore $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \le \lambda^* \approx 2.365272 < \eta \approx 2.381966$.

## 3. Exact $\mathbb{Q}(\sqrt{5})$ Certificate ($\lambda = 19/8 = 2.375 < \eta$)

To obtain a completely elementary, purely algebraic certificate over $\mathbb{Q}(\sqrt{5})$ (used in our Lean 4 formalization), apply the invertible linear transformation $L(x, y) = (x,\, y / \sin 72^\circ)$ to the regular pentagon $F$. Using $\cos 72^\circ = c := \frac{\sqrt{5} - 1}{4}$, $\cos 144^\circ = -\frac{\varphi}{2}$ where $\varphi := \frac{1 + \sqrt{5}}{2}$, and $\sin 144^\circ / \sin 72^\circ = 2\cos 72^\circ = \frac{1}{\varphi} = \frac{\sqrt{5} - 1}{2}$, the image $F' = L(F)$ is the affine-regular pentagon with vertices
$$P_0 = (1, 0),\quad P_1 = (c, 1),\quad P_2 = \left(-\frac{\varphi}{2}, \frac{1}{\varphi}\right),\quad P_3 = \left(-\frac{\varphi}{2}, -\frac{1}{\varphi}\right),\quad P_4 = (c, -1).$$

### Lemma 3.1 ($\mathrm{cen}(F') = 0$)
The linear map $A(x, y) = \bigl(cx - (1 - c^2)y,\; x + cy\bigr)$ satisfies $\det A = c^2 + (1 - c^2) = 1$ and maps $P_k \mapsto P_{(k+1)\bmod 5}$ for all $k \in \{0,1,2,3,4\}$. Hence $A(F') = F'$, and since $A$ is volume-preserving, $A(\mathrm{cen}(F')) = \mathrm{cen}(A(F')) = \mathrm{cen}(F')$. Because $\det(A - I) = (c - 1)^2 + (1 - c^2) = 2(1 - c) = \frac{5 - \sqrt{5}}{2} \ne 0$, the unique fixed point of $A$ is $0$, so $\mathrm{cen}(F') = 0$.

### Lemma 3.2 (Rational Triangle Certificate)
Consider the nondegenerate triangle $T_0 = \mathrm{conv}\{v_0, v_1, v_2\}$ with rational vertices
$$v_0 = \left(\frac{112}{200}, \frac{127}{200}\right),\qquad v_1 = \left(-\frac{161}{200}, \frac{35}{200}\right),\qquad v_2 = \left(\frac{49}{200}, -\frac{162}{200}\right).$$
Then $v_0 + v_1 + v_2 = (0, 0)$, so $\mathrm{cen}(T_0) = \frac{1}{3}(v_0 + v_1 + v_2) = (0, 0)$, and $\det(v_1 - v_0, v_2 - v_0) = \frac{73101}{40000} > 0$.

1. **$T_0 \subset F'$:** Each vertex $v_j$ is an explicit convex combination of three vertices of $F'$:
   - $v_0 = \left(\frac{497}{800} - \frac{459}{4000}\sqrt{5}\right) P_0 + \left(\frac{381}{800} + \frac{283}{4000}\sqrt{5}\right) P_1 + \left(-\frac{39}{400} + \frac{11}{250}\sqrt{5}\right) P_2$,
   - $v_1 = \left(-\frac{161}{200} + \frac{361}{1000}\sqrt{5}\right) P_0 + \left(\frac{757}{800} - \frac{547}{4000}\sqrt{5}\right) P_2 + \left(\frac{687}{800} - \frac{897}{4000}\sqrt{5}\right) P_3$,
   - $v_2 = \left(\frac{21}{50} - \frac{127}{1000}\sqrt{5}\right) P_0 + \left(-\frac{11}{400} + \frac{151}{2000}\sqrt{5}\right) P_3 + \left(\frac{243}{400} + \frac{103}{2000}\sqrt{5}\right) P_4$.
   Every triple of coefficients sums to $1$ and each coefficient is strictly positive (verified by comparing squares since $2.236 < \sqrt{5} < 2.237$). By convexity of $F'$, $T_0 \subset F'$.

2. **$F' \subset \frac{19}{8} T_0$:** Every vertex $P_k$ of $F'$ is an explicit convex combination of $\frac{19}{8} v_0, \frac{19}{8} v_1, \frac{19}{8} v_2$ with denominator $D = 1{,}388{,}919 = 19 \cdot 73{,}101$:
   - $P_0$: $\frac{1}{462973}(259391,\; 191,\; 203391)$,
   - $P_1$: $\frac{1}{D}\bigl(720173 + 78800\sqrt{5},\; 679373 - 115600\sqrt{5},\; -10627 + 36800\sqrt{5}\bigr)$,
   - $P_2$: $\frac{1}{D}\bigl(216173 + 89200\sqrt{5},\; 528173 + 166000\sqrt{5},\; 644573 - 255200\sqrt{5}\bigr)$,
   - $P_3$: $\frac{1}{D}\bigl(552173 - 246800\sqrt{5},\; 628973 + 65200\sqrt{5},\; 207773 + 181600\sqrt{5}\bigr)$,
   - $P_4$: $\frac{1}{D}\bigl(48173 + 78800\sqrt{5},\; 477773 - 115600\sqrt{5},\; 862973 + 36800\sqrt{5}\bigr)$.
   Every triple sums to $1$ and every entry is strictly positive (in particular, $36800^2 \cdot 5 = 6{,}771{,}200{,}000 > 112{,}933{,}129 = 10627^2$ and $644573^2 > 5 \cdot 255200^2$). Hence $F' \subset \frac{19}{8} T_0$.

3. **Strict inequality $\frac{19}{8} < \eta$:**
   $$\frac{19}{8} < \frac{7 - \sqrt{5}}{2} \iff \sqrt{5} < \frac{9}{4} \iff 5 < \frac{81}{16} \iff 80 < 81.$$

Setting $a(T) = \frac{19}{8} T_0$ and $h_{19/8}(x) = \frac{19}{8} x$ yields $F' \subset a(T) \subset h_{19/8}(F')$ with $\mathrm{cen}(F') = \mathrm{cen}(a(T)) = \mathrm{cen}(h_{19/8}(F')) = 0$. Therefore
$$d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) = d_{\mathrm{BM}}^{\mathrm{cen}}(F', T) \le \frac{19}{8} < \eta,$$
refuting $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) = \eta$. $\square$

### Remark on the Sharp Value
Numerical minimization of $\max_k g_\Delta(P_k) \cdot \max_j g_F(v_j)$ over all triangles $\Delta$ with $\mathrm{cen}(\Delta) = 0$ consistently converges to $\lambda^* = \frac{1 + \cos 24^\circ}{\cos 36^\circ} \approx 2.36527226$, attained by the rotated equilateral triangle $E$ of Section 2. Determining whether $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) = \lambda^*$ remains open.
