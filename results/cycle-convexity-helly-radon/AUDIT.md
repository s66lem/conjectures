# Independent Adversarial Audit — Result #61 (Disproof of the Cycle Convexity Helly–Radon Conjecture)

- **Auditor:** `claude-sonnet-5-5` (independent read-only cross-model adversarial review)
- **Date:** 2026-11-27
- **Target:** R. S. Nair, B. S. Anand, Ullas Chandran S. V., J. R. Nascimento, A. Anil, *Computing the Helly Number, Radon Number and Rank in Cycle Convexity*, `arXiv:2609.34236v1`, Section 5 ("Conclusion"), Conjecture 1
- **Lean file:** [`lean/Conjectures/CycleConvexityHellyRadon.lean`](../../lean/Conjectures/CycleConvexityHellyRadon.lean)

## Audit Summary

| Check | Result | Details |
|---|---|---|
| 1. Build & typecheck | **PASS** | Temp copy with `#print axioms` appended for all 31 public lemmas and theorems compiled cleanly on `bishop` (`rc=0`, `51.3 s`, 18 threads); `0` errors, `0` warnings, `0` info messages beyond axiom output. |
| 2. Axioms | **PASS** | Every public lemma and theorem depends only on `[propext, Classical.choice, Quot.sound]` (with 4 elementary lemmas printing zero axioms). |
| 3. Forbidden tokens | **PASS** | Case-sensitive grep across the entire file (comments and docstrings included) for `sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, `local instance`: **0 hits**. |
| 4. Specification audit | **PASS** | `cycleInterval`, `IsCycleConvex`, `cycleHull`, `IsHellyIndep`, `IsRadonIndep`, `hellyNumber`, and `radonNumber` match Section 2 of `arXiv:2609.34236v1` verbatim (`IsCycle` excludes length-1 and length-2 walks; `IsRadonIndep` quantifies over nonempty disjoint bipartitions); `G16` is verified simple, undirected, connected, 16 vertices, 36 edges; general Levi inequality `hellyNumber_le_radonNumber` and non-vacuous counterexample `hellyNumber G16 = 5 < 6 = radonNumber G16` verified cleanly. |
| 5. Artifacts & verification | **PASS** | `python -O -W error results/cycle-convexity-helly-radon/verify.py` exits `0` (`ALL CHECKS PASSED`, exhaustive over all `65,536` subsets and all `11,440` 7-sets, `0` `assert` statements); `0` `\operatorname` in `.md`; `PROOF.md`, `README.md`, `paper.tex`, and `paper.pdf` are fully consistent. |
