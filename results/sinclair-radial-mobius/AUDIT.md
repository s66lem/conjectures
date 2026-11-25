# Verification & Audit Log — Sinclair Conjecture C (`arXiv:2608.18519`)

## Source & Definition Audit

Checked verbatim against Thomas Sinclair, *The radial derivative on the graded Möbius algebra* (`arXiv:2608.18519`, §§1–3, 5):

- **Simple matroid $M$ of rank $r$ on $E$ ($|E| = n$):** Lattice of flats $\mathcal{L}(M) = \bigsqcup_{j=0}^r \mathcal{L}_j(M)$ with ordered atom-basis count $\beta_x = \mathrm{rk}(x)! \cdot \#\{\text{bases of } M|x\}$ and layer vectors $v_j = \sum_{x \in \mathcal{L}_j(M)} \beta_x e_x$.
- **Coordinate lowering operators (§2, Proposition 2.2):** $L_a^\beta(e_y) = \sum_{x \lessdot y,\, x \vee a = y} (\beta_x / \beta_y) e_x$.
- **Radial derivative (§2, Proposition 2.3):** $U^\beta = \sum_{a \in E} L_a^\beta$, $K(e_y) = \mathrm{rk}(y) e_y$, $S(e_x) = (n - |x|) e_x$, and $D_\beta = S^{-1} U^\beta K$ on proper flats, satisfying $D_\beta(v_j) = j v_{j-1}$.
- **Cyclic module and grading (§1, §3):** Graded by operator word length $k$: $\mathcal{C}_0(M) = \mathbb{Q} v_r$ and $\mathcal{C}_{k+1}(M) = D_\beta(\mathcal{C}_k(M)) + \sum_{a \in E} L_a^\beta(\mathcal{C}_k(M)) \subseteq \mathbb{Q}\mathcal{L}_{r-k}(M)$, with $h_k^\beta(M) = \dim_{\mathbb{Q}} \mathcal{C}_k(M)$ and $\delta_k(M) = h_k^\beta(M) - h_k^0(M)$.
- **Conjecture C (§1):** Front-loading $\delta_k(M) \ge \delta_{r-k}(M)$ (equivalently $h_k^\beta(M) \ge h_{r-k}^\beta(M)$ since $H^0$ is palindromic) for all $k \le r/2$.

## Cross-Model Adversarial Referee Audit

- **Discoverer:** Claude Opus 5.5.
- **Independent Adversarial Referee:** GPT-6.2 Astra (`Verdict: ACCEPT`).
- Independently implemented the flat lattice, $\beta_x$, $L_a^\beta$, $D_\beta$, and exact rational span computation from `arXiv:2608.18519` without consulting Opus's code.
- Confirmed exact calibration against the paper's own published examples: $M(K_5)$ (Example 3.2, $H^0 = (1, 10, 20, 10, 1)$, $H_\beta = (1, 10, 20, 10, 1)$), $U_{3,6}$, $U_{4,7}$, and Theorem D ($t = 6$).
- Independently confirmed $M(K_{1,1,4} + \{2,3\})$ is simple of rank $5$ on $10$ elements with $H^0 = (1, 10, 27, 27, 10, 1)$ and $H_\beta = (1, 11, 31, 32, 10, 1)$, giving $h_2^\beta = 31 < 32 = h_3^\beta$ (and noting that even reversing the vector fails at $k = 1$, $10 < 11$).
- Independently verified $G_m = K_{1,1,m} + \{2,3\}$ for $m = 4, 5, 6, 7$ and confirmed that $K_{1,1,m}$ itself has $H_\beta = H^0$.

## Independent Python 3 Verification

`python3 -O results/sinclair-radial-mobius/verify.py` (stdlib `fractions.Fraction` only):

- Reproduces Example 3.2 ($M(K_5)$) and verifies $D_\beta(v_j) = j v_{j-1}$ on every layer for every matroid tested.
- Verifies exact rational $H^0$ and $H_\beta$ for $G_4, G_5, G_6, G_7$, the symmetric baseline $K_{1,1,4}$, and the $12$-element non-graphic binary counterexample.

## Lean 4 Formal Verification

File: [`lean/Conjectures/SinclairRadialMobius.lean`](../../lean/Conjectures/SinclairRadialMobius.lean) (1,070 lines, Lean `v4.33.1` + Mathlib).

- Formalizes `SimpleMatroid` via rank-function axioms, `IsFlat` / `Flat`, closure `cl`, ordered atom-basis counts `beta`, cover relation `Covers`, coordinate lowering operators `L_beta`, radial derivative `D_beta = S_inv ∘ U_beta ∘ K_op`, cyclic module `C_mod`, and exact dimension `h_beta` over `ℚ`.
- Exports `M_G4_rank : M_G4.rank = 5`, `M_G4_h2_le`, `M_G4_h3_ge`, exact `M_G4_h2 : h_beta M_G4 2 = 31`, `M_G4_h3 : h_beta M_G4 3 = 32`, and `not_sinclair_conjecture_C`.
- Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero warnings.
- `lake build Conjectures.SinclairRadialMobius` succeeded cleanly (1,650 jobs, 29s); `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all exported theorems.
