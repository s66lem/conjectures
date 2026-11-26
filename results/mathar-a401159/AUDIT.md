# Independent Adversarial Audit — R. J. Mathar's OEIS A401159 Conjectures

**Verdict:** **PASS** (0 blocking defects).

**Auditor:** Independent cross-model audit (`claude-sonnet-5-5`, read-only scope), November 26, 2026.

## Summary of Checks

1. **Lean 4 build & axiom hygiene:**
   - `lake build Conjectures.MatharA401159` succeeded (8706 jobs) with 0 errors and 0 warnings (`LEAN_NUM_THREADS=1`).
   - `#print axioms` on `validMatrixCount_of_le`, `validMatrixCount_succ`, `mathar_A401159_conj1`, `mathar_A401159_conj2_nat`, and `mathar_A401159_conj2_rat` returned only `[propext, Classical.choice, Quot.sound]`.
   - Zero occurrences of `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, or `elab` in `lean/Conjectures/MatharA401159.lean`.
   - `lean/Conjectures.lean` imports `Conjectures.MatharA401159`.
2. **Statement & definition fidelity:**
   - Verified verbatim against live OEIS A401159 (offset `1,1`, approved November 18, 2026): $T(n, 2) = \mathrm{A086601}(n)$ and $T(n, 3) = 1 + n + \frac{11}{4}n^2 + \frac{13}{8}n^3 + \frac{1}{8}n^4 + \frac{3}{8}n^5 + \frac{1}{8}n^6$, along with OEIS A086601 and A000124 definitions.
   - Confirmed `IsValidMatrix` enforces row sum $\le k$ and column sum $\le k$, matching all published `%S`/`%T`/`%U` triangle entries ($n \le 9, m \le 3$), and that the Lean theorems quantify over all $n \in \mathbb{N}$ (covering $n \ge 1$).
3. **Mathematical rigor:**
   - Independently verified the column-support `Equiv`, the $m \le k$ automatic row-sum case, the $m = k + 1$ empty-intersection Möbius inversion factorization $N(J)^{k+1}$, handling of $j > n$ via $\binom{n}{j} = 0$, and the exact $k = 2$ sextic expansion including $n = 0$ boundary terms.
4. **Python verifier & manuscript:**
   - `python -O -W error results/mathar-a401159/verify.py` exited 0 (`OK`), stdlib-only, using `require()` rather than `assert`.
   - Confirmed `README.md`, `PROOF.md`, `paper.tex` (`\author{Salem Levinstein}`, no `\thanks`), and `MatharA401159.lean` agree on all statements and metadata.
   - Created this `AUDIT.md` to resolve the `README.md` link.
