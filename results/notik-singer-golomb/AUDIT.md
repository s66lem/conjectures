# Verification & Audit Log — Notik Singer Golomb Ruler Chamber-Uniqueness Conjecture

## Source & Definition Audit

Checked verbatim against Esther Notik, *Golomb rulers with real marks: the real and integer optima agree up to ten marks* (`arXiv:2611.22656`):

- **Real Golomb ruler (Definition 1):** Real marks $0 = x_1 < \dots < x_n$ such that every difference $x_j - x_i \ge 1$ ($i < j$) and any two distinct labeled differences satisfy $|(x_j - x_i) - (x_\ell - x_k)| \ge 1$.
- **Chamber $P_\sigma$:** The closed polyhedron of real rulers $y$ with $y_1 = 0$, $y_j - y_i \ge 1$ for $i < j$, and $(y_\ell - y_k) - (y_j - y_i) \ge 1$ whenever $x_j - x_i < x_\ell - x_k$.
- **Conjecture (§7):** For every prime power $m$, every Singer Golomb ruler is the unique shortest point of its chamber.

## Cross-Model Adversarial Referee Audit

- **Prover:** GPT-6.2 Astra.
- **Independent Adversarial Referee:** Claude Opus 5.5 (`Verdict: ACCEPT`).
- Confirmed exact equivalence between Notik's chamber constraints $P_\sigma$ and the consecutive-rank rows $\Delta_r(y) - \Delta_{r-1}(y) \ge 1$ ($\Delta_0 = 0$).
- Verified uniqueness of the largest cyclic gap $G$, realization of all ordinary differences $1, \dots, G - 1$ as the first $G - 1$ difference ranks, componentwise gap dominance, equality-case uniqueness, and the explicit integer dual weights $\lambda_r = |\{i : h_i \ge r\}|$.
- Independently verified Singer rulers for $m \le 11$ and confirmed negative controls where cutting at a non-largest gap fails the prefix-rank condition.

## Computational Verification

- **Extended prime-power verification:** Checked all $61{,}308$ unit-multiplier Singer rulers across orders $m \in \{107, 109, 113, 121, 125, 127\}$ (all passed exact labeled-difference reconstruction and integer dual identity).
- **Standalone Python 3 verifier (`python3 results/notik-singer-golomb/verify.py`, stdlib only):** Verifies the cyclic PDS axiom, unique largest-gap cut, prefix ranks $1, \dots, G - 1$, and exact integer dual certificate across all 14 prime-power orders up to $m = 25$ ($1{,}998$ unit-multiplier rulers) plus a non-largest-gap negative control.

## Lean 4 Formal Verification

File: [`lean/Conjectures/SingerGolombChamber.lean`](../../lean/Conjectures/SingerGolombChamber.lean) (536 lines, Lean `v4.33.1` + Mathlib).

- Formalizes `IsCyclicPDS`, `IsRealGolomb`, `InChamber`, `cutAnchor`, `cutMarks`, `largestGapCut`, and `largestGap`.
- Proves `IsCyclicPDS.mul_unit`, `IsCyclicPDS.translate`, `cutSpan_injective`, `cutMarks_gap_lt`, `pds_largest_gap_unique_shortest` (gap dominance, length minimization, and uniqueness in `InChamber`), and `singer_pds_exists` (existence of a cyclic PDS of size $q + 1$ in $\mathbb{Z}/(q^2 + q + 1)\mathbb{Z}$ for every prime power $q$).
- Zero `sorry`, zero custom `axiom`, zero `native_decide`.
- `lake build Conjectures.SingerGolombChamber` succeeded cleanly; `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all main theorems (and `[propext, Quot.sound]` for `singer_trace_identity`).
