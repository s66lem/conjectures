# Independent Adversarial Audit — Li–Nešetřil–Yang Problems 3.5 & 3.6 (`arXiv:2611.33681v1`)

**Verdict:** **PASS** (0 blocking defects).

**Auditor:** Independent cross-model audit (`claude-sonnet-5-5`, read-only scope), November 26, 2026.

## Summary of Checks

1. **Lean 4 build & axiom hygiene:**
   - `lake build Conjectures.LiNesetrilYangWcol` succeeded with 0 errors and 0 warnings (`LEAN_NUM_THREADS=1`).
   - `#print axioms` on all 10 headline theorems (`exists_topological_order`, `forest_wcolPlus_eq_one`, `forest_colPlus_eq_one`, `forest_wcolPlusGraph_eq_one`, `wcolGraph_mono`, `pathGraph_isAcyclic`, `dirPath_halving_lower`, `pathGraph_wcol_ge`, `no_uniform_weak_bound`, `p4_disproves_prob35_prob36`) returned only `[propext, Classical.choice, Quot.sound]`.
   - Zero occurrences of `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, or `elab` in `lean/Conjectures/LiNesetrilYangWcol.lean`.
   - `lean/Conjectures.lean` imports `Conjectures.LiNesetrilYangWcol`.
2. **Statement & definition fidelity:**
   - Verified verbatim against live `arXiv:2611.33681v1` (25 Nov 2026, latest version): directed $(k, +)$ and $(k, -)$ weak/strong reachability directions, self-inclusion in $W^{k,\pm}$, min-over-$\sigma$ / max-over-$y$, max-over-orientations for undirected graphs, and exact wording of Problems 3.5 and 3.6.
   - Confirmed Lean's use of walks is equivalent to paths for weak reachability (shortest walk is a path, and lower-bound witnesses are explicit paths).
3. **Openness verification:**
   - `arXiv:2611.33681v1` is the latest version with Problems 3.5 and 3.6 open.
   - Verified 0 matching issues/PRs on `the-omega-institute/trureturing` and 0 matching Zenodo records (checked by arXiv ID and topic keywords).
4. **Python verifier & manuscript:**
   - `python -O -W error results/li-nesetril-yang-wcol/verify.py` exited 0 (`ALL CHECKS PASSED`, 65,988 oriented forests checked); stdlib-only, using `require()`.
   - `README.md` and `PROOF.md` contain zero `\operatorname`, clearly mark the $k = 1$ positive remark as outside Lean scope, and `paper.tex` uses `\author{Salem Levinstein}` without `\thanks`.
   - Created this `AUDIT.md` (resolving the `README.md` link).
