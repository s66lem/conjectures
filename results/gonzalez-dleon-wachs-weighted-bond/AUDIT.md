# Audit Log: Disproof of González D'León–Wachs Conjecture 4.13(2) (`arXiv:2608.08692v2`)

## 1. Source & Definition Audit

- **Source:** Rafael S. González D'León and Michelle L. Wachs, *Weighted bond posets and a new chromatic symmetric function*, `arXiv:2608.08692v2` (2026).
- **Conjecture 4.13(2) (verbatim):** Let $G$ be a graph with $n$ vertices and $k$ connected components. If $H$ is a subgraph of $G$ with $n$ vertices and $k$ connected components, then $(-1)^{n-k}(\mu_G(t) - \mu_H(t))$ is real-rooted.
- **Definition fidelity:** Both `verify.py` and `lean/Conjectures/WachsWeightedBond.lean` construct the weighted bond poset $\mathcal{W}\Pi_G$ directly from the verbatim definition (connected induced-subgraph blocks $B$ with $0 \le w(B) < |B|$, ordered by refinement with merge-weight increment $0 \le w(B) - \sum_{A \subseteq B} w(A) < |\{A : A \subseteq B\}|$) and compute $\mu_G(t) = \sum_{\boldsymbol{\pi} \in \mathrm{Max}(\mathcal{W}\Pi_G)} \mu(\hat{0}, \boldsymbol{\pi}) t^{w(\boldsymbol{\pi})}$ via the poset Möbius function (`IncidenceAlgebra.mu ℤ ⊥ a` in Lean 4).

## 2. Computational Verification (`verify.py`)

- Ran `python -O results/gonzalez-dleon-wachs-weighted-bond/verify.py` (Python 3 stdlib only, `-O`-safe `require()` checks):
  - Independently computed $\mu_{K_3}, \mu_{P_3}, \mu_{\mathrm{House}}, \mu_{C_5}$ from the full weighted bond poset and cross-checked against recurrence (3.1).
  - Verified $H = P_3 \sqcup C_5 \subseteq K_3 \sqcup \mathrm{House} = G$ on $8$ vertices with $2$ connected components each, exact difference $P(t) = 8 + 82t + 271t^2 + 396t^3 + 271t^4 + 82t^5 + 8t^6$, reciprocal cubic $Q(s) = 8s^3 + 82s^2 + 247s + 232$, $\gamma$-polynomial $\Gamma(u) = 2u^3 + 15u^2 + 34u + 8$, and discriminant $\Delta = -22{,}364 < 0$ (Sturm count: $2$ real roots of $6$).
  - Checked the non-trivial $2$-component chorded-cycle family through $m = 10$ ($n = 14$).
  - Result: `PASS` (exit 0).

## 3. Lean 4 Formalization Audit (`lean/Conjectures/WachsWeightedBond.lean`)

- **Toolchain:** Lean `v4.33.1` + Mathlib `v4.33.1`.
- **Hygiene audit:** Zero occurrences of `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `implemented_by` (`decide +kernel` only, kernel-checked).
- **Verified exports under `WachsWeightedBond`:**
  - Verbatim poset & product formula: `WPi`, `WPi.bot_blocks`, `μ_sum`, `μ_edgeless`.
  - Exact component polynomials from `WPi`: `μ_K3`, `μ_P3`, `μ_House`, `μ_C5`.
  - Graph properties: `K3_connected`, `P3_connected`, `House_connected`, `C5_connected`, `H_le_G`, `G_components`, `H_components`, `HWithIsolates_le_GWithIsolates`, `GWithIsolates_components`, `HWithIsolates_components`.
  - Algebraic non-real-rootedness: `signed_μ_difference`, `signed_μ_difference_with_isolates`, `P_has_nonreal_root`, `P_not_splits`.
  - Main disproof theorems: `conjecture_4_13_2_counterexample` ($n = 8, k = 2$) and `conjecture_4_13_2_infinite_family` ($n = 8 + r, k = 2 + r$ for all $r \in \mathbb{N}$).
- **Axiom check (`#print axioms`):**
  - `WachsWeightedBond.conjecture_4_13_2_counterexample`: `[propext, Classical.choice, Quot.sound]`
  - `WachsWeightedBond.conjecture_4_13_2_infinite_family`: `[propext, Classical.choice, Quot.sound]`
- **Build check:** `cd lean && lake build Conjectures.WachsWeightedBond` and `lake env lean Conjectures\WachsWeightedBond.lean` passed with exit code 0 and zero warnings.

## 4. Scope Caveats Verified

- Exhaustive check of all $12{,}346$ graphs and $18.1\text{M}$ subgraph pairs with $n \le 8$ confirms $n = 8$ is minimal and all three counterexamples at $n = 8$ are disconnected.
- Both the connected restriction ($k = 1$) and single-edge-deletion case ($H = G - e$) of Conjecture 4.13(2) remain open, as do Conjectures 4.12, 4.13(1), 4.15, 4.16, 6.21, and 7.3.
