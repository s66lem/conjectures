# Independent Adversarial Audit — Campbell OEIS A189409 Disproof

## Audit Summary

- **Auditor:** Codex (`gpt-6-luna`, independent read-only cross-model review) + independent Lean 4 kernel & axiom audit.
- **Outcome:** All mathematical, arithmetic, formalization, and verifier checks passed. One wording inaccuracy caught during the audit (stating "verbatim" where the standalone Mathlib module defines `kthPrimorial` directly instead of importing `FormalConjecturesUtil`'s `Nat.kthPrimorial`) was corrected across `CampbellA189409.lean` and `paper.tex`.

## Verified Checklist

1. **Mathematical equivalence to OEIS A189409 / `FormalConjectures/OEIS/189409.lean`:** Confirmed `kthPrimorial n = ∏ k ∈ Finset.range n, Nat.nth Nat.Prime k` and `a n = (kthPrimorial n)^2 + 1` match `a 0 = 2, a 1 = 5, ..., a 9 = 49770428644836901`.
2. **Disproof at `n = 9`:** Confirmed $p_9\# = 223{,}092{,}870$, $a(9) = 49{,}770{,}428{,}644{,}836{,}901 = 29^2 \cdot 53 \cdot 1{,}116{,}604{,}864{,}937$, so $29^2 \mid a(9)$ and $\neg \text{Squarefree}(a(9))$.
3. **Exact minimality (`n < 9`):** Confirmed `a(0)..a(8)` are all squarefree, with all large prime factors certified via deterministic Lucas primality witnesses in the Lean kernel (zero `native_decide`).
4. **Forbidden-shortcut audit:** Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `unsafe`/`implemented_by`.
5. **Lean 4 kernel & axiom audit:** `lake build Conjectures.CampbellA189409` and `lake env lean Conjectures.lean` exit 0; `#print axioms` on `a_9_not_squarefree`, `disproof_conjecture_1`, `a_9_factorization`, `squarefree_lt_9`, and `minimal_counterexample` report strictly `[propext, Classical.choice, Quot.sound]`.
6. **Independent Python verifier:** `python -O verify.py` exits 0 with all checks active under `-O`.
