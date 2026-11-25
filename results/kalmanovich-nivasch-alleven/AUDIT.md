# Verification & Audit Log — Kalmanovich–Nivasch Conjecture 9.1

## Source & Definition Audit

Checked verbatim against Daniel Kalmanovich and Gabriel Nivasch, *All-even sets in $\mathbb{R}^2$ and $\mathbb{R}^3$* (`arXiv:2610.38864`):

- **Planar all-even set (§1):** A nonempty finite set $S \subset \mathbb{R}^2$ such that for every nonzero direction $u \in \mathbb{R}^2$, the number of distinct projections $m_S(u) = |\{\langle p, u \rangle : p \in S\}|$ is even.
- **Monotone contagion (§5):** Starting from $U_0 = T \subseteq S$, repeatedly add $y \in S \setminus U$ whenever there exist $x, p, q \in U$ with $p \ne q$ such that the secant $xy$ is parallel to $pq$. $T$ is a *monotonically contagious triangle* if $|T| = 3$ and the closure equals $S$.
- **Regular $n$-gon parallel-chord lemma (§6):** On the regular $n$-gon $P_n$, chords $p_i p_j$ and $p_k p_\ell$ ($i \ne j$, $k \ne \ell$) are parallel if and only if $i + j \equiv k + \ell \pmod n$.
- **Conjecture 9.1:** Every planar all-even set has a monotonically contagious triangle.

## Cross-Model Adversarial Referee Audit

- **Prover:** GPT-6.2 Astra.
- **Independent Adversarial Referee:** Claude Opus 5.5 (`Verdict: ACCEPT on both parts`).
- Verified all definitions against `arXiv:2610.38864`, verified the parallel-chord characterization numerically on 200,000 chord pairs with zero mismatches, verified all-evenness across all 210 chord-sum classes, verified all $\binom{36}{3} = 7{,}140$ triangles exhaustively (max closure size $28$), confirmed Property $\mathcal{C}$ and height-rigidity (rank $33$), and verified the infinite seed-number family $S_k$.

## Independent Python 3 Verification

`python3 results/kalmanovich-nivasch-alleven/verify.py` (stdlib only):

- Confirms $|S| = 36$, $A \cap B = \emptyset$, and $m_S(s) \in \{22, 26, 32, 34, 36\}$ for every $s \in \mathbb{Z}/210\mathbb{Z}$.
- Confirms every one of the $7{,}140$ triangles in $S$ has monotone closure of size at most $28$, contained in one of the six closed proper subsets $A \cup (B \cap (c + 15G))$ or $B \cup (A \cap (c + 6G))$.
- Confirms height-rigidity ($\mathrm{rank}_{\mathbb{F}_{211}} = 33 = |S| - 3$) and Property $\mathcal{C}$.
- Confirms the infinite family $S_k$ for small $k$.

## Lean 4 Formal Verification

File: [`lean/Conjectures/KalmanovichNivaschAllEven.lean`](../../lean/Conjectures/KalmanovichNivaschAllEven.lean) (385 lines, Lean `v4.33.1` + Mathlib).

- Formalizes genuine real Euclidean points `Pt := ℝ × ℝ`, inner product `dot`, 2D determinant `det2`, `IsAllEven`, `InMonoClosure`, `IsMonoClosed`, and `IsMonoContagious`.
- Proves `pt210_injective`, `S36_card : S36.card = 36`, `det2_chord_eq_zero_iff`, `dot_eq_iff_sum_eq`, `S36_isAllEven`, `S36_no_mono_contagious_triangle`, and `not_conjecture_9_1`.
- Zero `sorry`, zero custom `axiom`, zero `native_decide`.
- `lake build Conjectures.KalmanovichNivaschAllEven` succeeded cleanly; `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all three main theorems.
