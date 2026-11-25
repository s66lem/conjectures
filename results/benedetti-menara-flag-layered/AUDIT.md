# Verification & Audit Log — Benedetti–Menara Conjecture 7.1 ($r = 2$)

## Source & Definition Audit

Checked verbatim against Bruno Benedetti and Giuliamaria Menara, *Diameter bounds for complexes that are close to flag or close to normal* (`arXiv:2611.08071`, §§2 and 7):

- **$1$-layered family of $r$-sets (§2):** A set of $r$-subsets of an $m$-set partitioned into nonempty disjoint layers $L_0, \dots, L_N$ such that for every nonempty $S$, $\{t : \exists F \in L_t,\, S \subseteq F\}$ is an interval.
- **Flagness (§7):** No $(r + 1)$-clique in the graph of co-occurring pairs; at $r = 2$, this is precisely triangle-freeness of the simple graph $G = (V, E)$, with neither connectivity nor proper edge labeling assumed.
- **Conjecture 7.1 (§7):** Every flag $1$-layered family of $r$-subsets of an $m$-set has at most $m - r + 1$ layers. Section 7 explicitly notes: *"The conjecture is trivial for $r = 1$, and open for $r = 2$, that is, for triangle-free graphs, where the Larman–Barnette bound only gives $2m - 3$ layers (Theorem 2.1)."*

## Cross-Model Adversarial Referee Audit

- **Prover:** Claude Opus 5.5.
- **Independent Adversarial Referee:** GPT-6.2 Astra (`REVISE` on initial draft for omitting the $a = 0, b = s$ closed-walk shortening case — immediately repaired and verified in both prose and Lean 4; `ACCEPT` on both higher-rank consequences: halved Larman–Barnette bound $2^{r-2}(m - r) + 1$ and unconditional Lemma 7.2 / Main Theorem E(a) at $p = r - 2$ / $p = d - 2$).
- Independently checked all four cases of Claim 1, both cases of Claim 2, the complete five-case walk-to-simple-path reduction (including $a = 0, b = s$ for $s = 2$ and $s \ge 3$), down-closure interval preservation, and the induction step.
- Independently enumerated all $13{,}017$ nonempty triangle-free $1$-layered families on a $5$-element ground set (maximum layers $= 4$, with $1{,}210$ attaining equality on their used vertices).

## Independent Python 3 Verification

`python3 results/benedetti-menara-flag-layered/verify.py` (stdlib only):

- Exhaustively enumerates all $13{,}017$ nonempty triangle-free $1$-layered families on $\{0, 1, 2, 3, 4\}$, confirming max layers $= 4$ and $1{,}210$ tight families.
- Verifies tight path families for $m = 2 \dots 20$, the $K_4$ non-flag control ($4$ layers on $4$ vertices), explicit $c \ge 1$ non-monotone-path witnesses ($m = 7, 8$), and $10{,}000$ randomly grown families.

## Lean 4 Formal Verification

File: [`lean/Conjectures/FlagLayeredR2.lean`](../../lean/Conjectures/FlagLayeredR2.lean) (668 lines, Lean `v4.33.1` + Mathlib).

- Formalizes both the `SimpleGraph` interval-labeling formulation (`triangle_free_interval_layers_le`, `triangle_free_interval_layers_le_active`, `monotone_path_vertex_bound`, `monotone_walk_active_bound`) and the verbatim `Finset (Finset V)` family formulation (`FlagOneLayered`, `flag_one_layered_r2_le`), plus tightness (`path_attains_bound`).
- Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero warnings.
- `lake build Conjectures.FlagLayeredR2` succeeded cleanly (776 jobs, 6.6s); `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all six exported theorems.
