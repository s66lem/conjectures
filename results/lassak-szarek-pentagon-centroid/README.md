# Disproof of Lassak–Szarek's Conjecture on the Centroid Banach–Mazur Distance Between a Pentagon and a Triangle (`arXiv:2611.21947v1`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24572740.svg)](https://doi.org/10.5281/zenodo.24572740)

**Problem:** Problem in the section *"Centroid Banach–Mazur distance"* of M. Lassak and S. J. Szarek, *Banach–Mazur distance and related methods of comparing convex bodies*, [arXiv:2611.21947v1](https://arxiv.org/abs/2611.21947) (November 2026).

**Status:** **DISPROVED** (answer is **NO**, formally verified in **Lean 4**):
- For every affine-regular pentagon $F$ and every nondegenerate triangle $T$,
  $$d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \le \frac{1 + \cos 24^\circ}{\cos 36^\circ} = \frac{2 \cos^2 12^\circ}{\cos 36^\circ} \approx 2.365272 < \frac{19}{8} = 2.375 < \eta := \frac{7 - \sqrt{5}}{2} \approx 2.381966.$$
- In particular, $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \ne \eta$, refuting the conjectured optimality of Lassak's bound $\eta$.

## Statement (Verbatim)

> Another result from [L 24c] is that if $F$ is an affine-regular pentagon, then $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \le \frac{7 - \sqrt{5}}{2} =: \eta \approx 2.382$. ... We conjecture that this bound is optimal.
>
> **Problem.** Is $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) = \eta$?

Here the centroid Banach–Mazur distance is defined by
$$d_{\mathrm{BM}}^{\mathrm{cen}}(C, D) = \inf_{a, h_\lambda} \bigl\{\lambda > 0 : C \subset a(D) \subset h_\lambda(C) \text{ and } \mathrm{cen}(C) = \mathrm{cen}(a(D)) = \mathrm{cen}(h_\lambda(C))\bigr\},$$
where $a$ is an invertible affine transformation and $h_\lambda$ is a homothety of ratio $\lambda > 0$.

## Summary of Disproof

1. **Analytic rotated equilateral triangle ($\lambda^* \approx 2.365272$):** Let $F$ be the regular pentagon with vertices $(\cos 72^\circ k, \sin 72^\circ k)$ ($k = 0, \dots, 4$, centroid $0$), and let $E$ be the equilateral triangle centred at $0$ with vertices at polar angles $48^\circ, 168^\circ, 288^\circ$ and circumradius $r = \cos 36^\circ / \cos 12^\circ$. Evaluating the Minkowski gauges directly shows $E \subset F$ (with the $48^\circ$ and $168^\circ$ vertices on $\partial F$) and $F \subset \lambda^* E$ with
   $$\lambda^* = \frac{2\cos^2 12^\circ}{\cos 36^\circ} = \frac{1 + \cos 24^\circ}{\cos 36^\circ} \approx 2.365272 < \eta.$$
   Setting $a(T) = \lambda^* E$ gives $F \subset a(T) \subset \lambda^* F$ with common centroid $0$.
2. **Exact $\mathbb{Q}(\sqrt{5})$ rational certificate ($\lambda = 19/8 = 2.375 < \eta$, formalized in Lean 4):** Applying the linear map $L(x, y) = (x, y / \sin 72^\circ)$ sends $F$ to the affine-regular pentagon $F'$ with vertices in $\mathbb{Q}(\sqrt{5})$:
   $$P_0 = (1, 0),\quad P_1 = (c, 1),\quad P_2 = (-\tfrac{\varphi}{2}, \tfrac{1}{\varphi}),\quad P_3 = (-\tfrac{\varphi}{2}, -\tfrac{1}{\varphi}),\quad P_4 = (c, -1),$$
   where $c = (\sqrt{5} - 1)/4$ and $\varphi = (1 + \sqrt{5})/2$. Taking the rational-vertex triangle
   $$T_0 = \mathrm{conv}\!\left\{\left(\tfrac{112}{200}, \tfrac{127}{200}\right), \left(-\tfrac{161}{200}, \tfrac{35}{200}\right), \left(\tfrac{49}{200}, -\tfrac{162}{200}\right)\right\},$$
   whose vertices sum to $0$, exact barycentric weights in $\mathbb{Q}(\sqrt{5})$ prove $T_0 \subset F'$ and $F' \subset \frac{19}{8} T_0$. Since $\mathrm{cen}(F') = 0$ (forced by the determinant-$1$ cyclic permutation matrix $A = \bigl(\begin{smallmatrix}c & c^2 - 1 \\ 1 & c\end{smallmatrix}\bigr)$ with $\det(A - I) \ne 0$) and $\mathrm{cen}(T_0) = 0$, we obtain $d_{\mathrm{BM}}^{\mathrm{cen}}(F, T) \le \frac{19}{8} < \frac{7 - \sqrt{5}}{2}$ (equivalently $\sqrt{5} < \frac{9}{4}$, i.e. $80 < 81$).

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical disproof (both exact $\mathbb{Q}(\sqrt{5})$ certificate and closed-form rotated equilateral bound).
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone stdlib-only exact $\mathbb{Q}(\sqrt{5})$ verifier (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint ([DOI: 10.5281/zenodo.24572740](https://doi.org/10.5281/zenodo.24572740)).
- [LassakSzarekPentagonCentroid.lean](../../lean/Conjectures/LassakSzarekPentagonCentroid.lean) — Complete Lean 4 formalization.
