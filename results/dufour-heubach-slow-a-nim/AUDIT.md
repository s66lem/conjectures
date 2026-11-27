# Independent Adversarial Audit — Result #59 (Dufour–Heubach Slow A-Nim)

- **Auditor:** Independent cross-model read-only audit (`claude-sonnet-5-5`, effort `medium`)
- **Target:** [`lean/Conjectures/DufourHeubachSlowANim.lean`](../../lean/Conjectures/DufourHeubachSlowANim.lean) and companion package in [`results/dufour-heubach-slow-a-nim/`](./)
- **Date:** 2026-11-26
- **Verdict:** **PASS** (5/5 checks passed)

## Audit Checks

1. **Build & Typecheck — PASS:** Independent `lake env lean` run on an out-of-repo temporary copy (`LEAN_NUM_THREADS=1`, no `-j`, gated by `gpu_lock` `ram` slot) exited `0` with `0` errors, `0` warnings, and `0` info messages (aside from the auditor's 7 appended `#print axioms` commands).
2. **Axioms — PASS:** All 7 public theorems (`step_P_to_N`, `step_N_to_P`, `isP_iff_div_eq`, `div_eq_iff_correctedSO`, `isP_iff_correctedSO_of_reduced`, `conjecture1_false_parity`, `conjecture1_false_infinite_family`) depend exclusively on `[propext, Classical.choice, Quot.sound]`.
3. **Forbidden Tokens — PASS:** Case-sensitive scan across the entire Lean file (including comments and docstrings) returned `0` hits for all 11 forbidden tokens (`sorry`, `admit`, `axiom `, `opaque `, `unsafe`, `implemented_by`, `extern`, `native_decide`, `partial `, `set_option`, `local instance`).
4. **Adversarial Specification Audit — PASS:** Verified exact fidelity to Dufour–Heubach (INTEGERS 26 (2026) #G3, Section 6 / `arXiv:2404.06608v3`, `con:atleastk`):
   - `IsP` defines normal-play P-positions of Slow $A$-Nim with $A = \{k, \dots, n\}$ by well-founded recursion on `total p` via `move_total_lt`.
   - `Conjecture1Pred` matches the three printed clauses ($S_1$, $S_2$, $S_3$) of Conjecture 1 verbatim, with safe natural-number inequalities (`o + s ≤ 2 * (k - 1)`).
   - `IsReduced`, `redHeight`, and `reduction` match the paper's Theorem 4 and Lemma 3.
   - Both disproof theorems (`conjecture1_false_parity` at $n = 4, k = 2, p = (0,1,2,2)$ and `conjecture1_false_infinite_family` for all odd $k \ge 3$ and $n \ge (3k-1)/2$) are non-vacuous conjunctions of `IsReduced`, `IsP`, and `¬ Conjecture1Pred`.
   - `isP_iff_div_eq` and `isP_iff_correctedSO_of_reduced` prove the complete corrected characterization for all positions (reduced and non-reduced) directly on plain Slow $A$-Nim.
5. **Cross-Document Consistency & Companion Verifier — PASS:** `python -O -W error verify.py` exited `0` and printed `ALL CHECKS PASSED` (identifying 199 Conjecture 1 failures and confirming exact agreement between plain and playable-reduced P-positions for $n \le 6$). The Lean file, `PROOF.md`, `paper.tex`, and `README.md` are mutually consistent.
