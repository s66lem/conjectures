# Independent Adversarial Audit — Takuto Nakai's OEIS A400474 Conjecture

**Verdict:** **PASS** (0 blocking defects).

**Auditor:** Independent cross-model audit (`claude-sonnet-5-5`, read-only scope), November 26, 2026.

## Summary of Checks

1. **Lean 4 build & axiom hygiene:**
   - `lake build Conjectures.NakaiA400474` succeeded with 0 errors and 0 warnings (`LEAN_NUM_THREADS=1`).
   - `#print axioms` on `nakai_A400474_combinatorial`, `nakai_A400474_upper`, `nakai_A400474_attained`, `balanced_eq_conjectured`, `excl_bal_le`, and `admissibleCount_eq_sub_excl` returned only `[propext, Classical.choice, Quot.sound]`.
   - Zero occurrences of `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, or `elab` in `lean/Conjectures/NakaiA400474.lean`.
   - `lean/Conjectures.lean` imports `Conjectures.NakaiA400474`.
2. **Statement & definition fidelity:**
   - Verified verbatim against live OEIS A400474 (`%F` line: $c = 6, -3, 4, 3, 0, -5$, offset $3$, verified for $n \le 1000$; `%C` comment matches the same angle-triple bijection and endpoint limits $\max(A, \pi - z)$ and $\min(\pi, 2\pi - z - B)$).
   - Confirmed `angleTripleSet`, `admissibleCount`, `conjecturedFormula`, `angleTriples_card_eq_admissibleCount`, and `exists_real_angles_of_floors` faithfully formalize the real-angle floor reduction and combinatorial maximization. The Euclidean inscribed-angle bijection is proved in `PROOF.md` and `paper.tex` and clearly noted as outside Lean scope.
3. **Mathematical rigor:**
   - Independently checked Lemma 2.1 (all endpoint cases including $\pi - z - B \le 0$, IVT, and two-circle uniqueness), floor-sum bound $p + q + r \ge n - 2$, pairwise disjointness of the three exclusion sets, $D_n(s)$ formula, the $n \ge 16$ transfer gap ($p - q \ge 6 \implies D_n(q + 1) - D_n(p) \le -2$), all six residue identities $\bmod 6$, and the $n = 3 \dots 15$ prefix matching OEIS `%S`.
4. **Python verifier & manuscript:**
   - `python -O -W error results/nakai-a400474/verify.py` exited 0 (`ALL CHECKS PASSED`), stdlib-only (`math`), using `require()` rather than `assert`.
   - `paper.tex` uses `\author{Salem Levinstein}` without `\thanks` and aligns with `README.md`, `PROOF.md`, and Lean scope.
5. **Polish items applied:**
   - Created this `AUDIT.md` (resolving the `README.md` link).
   - Clarified the `README.md` status line to explicitly specify `(real-angle floor reduction and combinatorial maximization)`.
   - Cleaned up draft comments in `NakaiA400474.lean` (`card_unrestrictedSet`) and dead variable assignments in `verify.py`.
