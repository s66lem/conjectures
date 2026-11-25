# Verification & Audit Log — Chen–Zwicker Conjecture 1 (`arXiv:2402.05884` & `arXiv:2608.29902`)

## Source & Definition Audit

Checked verbatim against Jiehua Chen and William S. Zwicker (`arXiv:2402.05884`) and Nicolas Bousquet, Frank Connor, Agnès Totschnig, and Sébastien Zeitoun, *Fair Division of Graphs: Beyond Traceability* (`arXiv:2608.29902v1`, §§1–2):

- **Connected allocation (§2):** Partition $A = (A_1, \dots, A_k)$ of $V(G)$ into $k$ pairwise disjoint connected subsets; empty bundles are explicitly permitted (Definition 2 handles $A_j = \varnothing$, and singletons reduce to $\varnothing$ which is connected).
- **$\mathrm{EF1}_{\mathrm{outer}}$ (Definition 2):** For all agents $i, j$, either $A_j = \varnothing$ or there exists $x \in A_j$ with $A_j \setminus \{x\}$ connected and $v_i(A_i) \ge v_i(A_j \setminus \{x\})$.
- **Conjecture 1 (§1):** For a fixed valuation class, the $\mathrm{EF1}_{\mathrm{outer}}$ spectrum of any connected graph has the form `YES* NO* YES^∞` (an initial `YES` run, a single contiguous possibly empty `NO` run, and an infinite `YES` tail).

## Cross-Model Adversarial Audit

- **Discoverer:** Claude Opus 5.5 (discovered the minimal $8$-vertex counterexample $H = K_{2,3} + 3\text{ pendant leaves}$, proved `NO` at $k = 2$ and $k = 4$, verified `YES` at $k = 3$ exhaustively for binary and via Z3 `QF_LRA` for heterogeneous monotone valuations, and checked minimality across all connected graphs on $n \le 8$ vertices).
- **Independent Cross-Model Auditor:** Gemini 4 Neon (independently checked verbatim definitions against `arXiv:2608.29902v1`, verified both hand proofs for $k = 2$ and $k = 4$, and wrote a from-scratch Python 3 verifier enumerating all $15$, $66$, and $151$ unordered connected partitions of $H$ for $k = 2, 3, 4$, confirming `NO` for $\beta$ at $k = 2, 4$ and `YES` for all $256$ common binary valuations at $k = 3$ across all four $8$-vertex gap graphs).

## Independent Python 3 Verification

`python3 -O results/chen-zwicker-ef1-outer/verify.py` (stdlib only, `-O`-safe):

- Confirms $H$ and all three hub-edge variants ($H + \{a,b\}$, $H + \{a,b\},\{b,c\}$, $H + K_3$) are connected and have exact common-binary $\mathrm{EF1}_{\mathrm{outer}}$ spectrum `Y N Y N Y Y Y Y`.

## Lean 4 Formal Verification

File: [`lean/Conjectures/ChenZwickerEF1Outer.lean`](../../lean/Conjectures/ChenZwickerEF1Outer.lean) (8,854 lines, Lean `v4.33.1` + Mathlib).

- Formalizes `H : SimpleGraph (Fin 8)`, `H_connected`, `IsConnectedBundle` (with `isConnectedBundle_iff_connected` proving equivalence to Mathlib's `(G.induce S).Connected` for nonempty `S`), `IsConnectedAllocation`, `IsMonotoneVal`, `commonBinaryVal`, and verbatim `IsEF1Outer`.
- Proves `H_no_k2` and `H_no_k4` for `e ∘ beta` into any linear order (covering $\mathbb{N}$ and $\mathbb{R}$), **`H_yes_k3_hetero_monotone`** for EVERY linear order $\alpha$ and EVERY triple of heterogeneous monotone valuations $v_1, v_2, v_3$ (via $54$ acceptance propositions over the $18$-allocation core, $294$ monotone-chain clauses, and a $195$-node case split), `H_yes_k3_common_binary`, `spectrum_gap`, and **`not_chen_zwicker_conjecture_1`** covering common binary additive, common additive, common monotone, heterogeneous additive, and heterogeneous monotone real-valued valuation classes simultaneously.
- Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero warnings.
- `lake build Conjectures.ChenZwickerEF1Outer` succeeded cleanly (26s); `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all eight exported theorems.
