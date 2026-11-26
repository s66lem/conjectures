# Independent Adversarial Audit — Palacios et al. Tree Hitting-Time Index Conjecture (`arXiv:2611.34295v1`)

**Verdict:** **PASS** (0 blocking defects).

**Auditor:** Independent cross-model audit (`claude-sonnet-5-5`, read-only scope), November 26, 2026.

## Summary of Checks

1. **Lean 4 build & axiom hygiene:**
   - `lake build Conjectures.PalaciosHittingTimeTrees` succeeded (8706 jobs) with 0 errors and 0 warnings (`LEAN_NUM_THREADS=1`).
   - `#print axioms` on all 10 headline theorems (`hitTime_satisfies_first_step`, `first_step_unique`, `GraftConfig.graft_isTree`, `GraftConfig.graft_leafCount`, `GraftConfig.graft_htIndex_strict_lt`, `exists_graftConfig_of_deg_ge_three`, `isTree_iso_pathGraph_of_deg_le_two`, `palacios_tree_hitting_time_le`, `palacios_tree_hitting_time_strict_lt`, `palacios_tree_hitting_time_eq_iff`) returned only `[propext, Classical.choice, Quot.sound]`.
   - Zero occurrences of `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, or `elab` in `lean/Conjectures/PalaciosHittingTimeTrees.lean`.
   - `lean/Conjectures.lean` imports `Conjectures.PalaciosHittingTimeTrees`.
2. **Statement & definition fidelity:**
   - Verified directly against the live `arXiv:2611.34295v1` PDF (25 Nov 2026, only version): $HT(G) = \sum_{i < j} \max(E_i T_j, E_j T_i)$ on simple connected undirected graphs, with the conjecture stated in §3 that $P_n$ maximizes $HT(T)$ among trees.
   - Confirmed `twoHT` equals twice the unordered pair sum, `htIndex = twoHT / 2` with evenness proved (`two_mul_htIndex`), `hitTime` uniquely solves the first-step equations (`first_step_unique`), `pathGraph` is consecutive-index adjacency, and `IsTree` enforces nonemptiness. Zero factor-of-2, off-by-one, or vacuity mismatches.
3. **Python verifier & manuscript:**
   - `python -O -W error results/palacios-hitting-time-trees/verify.py` exited 0 (`ALL CHECKS PASSED: 1904 algebraic triples, 280 graft graphs, all 1441 labeled trees of orders 2..6`).
   - `paper.tex` uses `\author{Salem Levinstein}` without `\thanks`; `.md` files contain zero `\operatorname`.
4. **Openness & concurrent-work note:**
   - At audit time, `arXiv:2611.34295v1` has no update and Zenodo has 0 matching records (verified via Zenodo API by both arXiv ID and topic keywords).
   - A concurrent independent Lean 4 proof was announced the same day in an open GitHub issue (`the-omega-institute/trureturing#34417`, created 2026-11-26T10:19Z, unpublished / no merged PR at publication time). As noted in the repository README, priority is not asserted; this package presents our independent proof and Lean 4 formalization.
5. **Polish items applied:**
   - Updated `paper.tex` to cite `§3` (without an unverified page number) and added the reference to Palacios–Petojević (Ref. [14] of `arXiv:2611.34295v1`); recompiled `paper.pdf` with 0 TeX warnings.
