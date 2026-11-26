# Independent Adversarial Audit — Rahid Zaman's OEIS A395348 Conjecture

**Verdict:** **PASS** (0 blocking defects).

**Auditor:** Independent cross-model audit (`claude-sonnet-5-5`, read-only scope), November 26, 2026.

## Summary of Checks

1. **Lean 4 build & axiom hygiene:**
   - `lake build Conjectures.ZamanA395348` succeeded with 0 errors and 0 warnings (`LEAN_NUM_THREADS=1`).
   - `#print axioms` on `isGreedyGame_pred`, `zaman_A395348_recurrence`, and `predBlackLabel_recurrence` returned only `[propext, Classical.choice, Quot.sound]`; `isGreedyGame_unique` uses only `[propext, Quot.sound]`.
   - Zero occurrences of `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, or `elab` in `lean/Conjectures/ZamanA395348.lean`.
   - `lean/Conjectures.lean` imports `Conjectures.ZamanA395348`.
2. **Statement & definition fidelity:**
   - Verified verbatim against live OEIS A395348 (conjecture by Rahid Zaman, November 18, 2026: $a(n + 4) = a(n) + 8n + 34$ for $n \ge 2$).
   - Independently compared `predBlackLabel` and `predRedLabel` against all $20\,000$ b-file terms of both OEIS A395348 and OEIS A395349: 0 mismatches.
   - Confirmed `IsGreedyGame` faithfully reproduces the exact Black-then-Red turn order (with Red's attack check including Black's $n$-th queen), spiral coordinate function `spiralXY`, and base rounds $0 \le n \le 7$.
3. **Mathematical rigor:**
   - Audited all base-round checks (rounds $0$–$7$), gap lemmas for every block turn, uniqueness, and recurrence derivations in Lean 4, and checked the `PROOF.md` line-set invariants at $h = 1$ by hand.
4. **Python verifier & manuscript:**
   - `python -I -O -W error results/zaman-a395348/verify.py` exited 0; stdlib-only and uses `require()` rather than `assert`.
   - `paper.tex` uses `\author{Salem Levinstein}` without `\thanks`.
5. **Polish items applied:**
   - Updated base-round label bound from `120` to `93` in `README.md`, `PROOF.md`, and `paper.tex`.
   - Clarified the non-occupation sentence in `paper.tex` (disjoint Black/Red $y$-sets plus strictly increasing same-color labels) and aligned Section 3's formal-verification statement strictly with the Lean-proved theorems (`Theorem 1`, uniqueness, and recurrence); recompiled `paper.pdf` with 0 TeX warnings.
