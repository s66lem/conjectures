# Audit Record — Fonollosa Problem 4 (`arXiv:2607.08366v2`)

## Summary

- **Verdict:** **PASS** (after docstring provenance fix below)
- **Independent Auditor:** Codex (`gpt-6-luna`, read-only adversarial audit)
- **Date:** 2026-11-25

## Audit Findings & Resolution

1. **Statement & Mathematical Soundness:** Passed. `Valid` matches Fonollosa's unique multiset-sum condition (`arXiv:2607.08366v2`, §8 Problem 4; `arXiv:2607.09949v2`, Remark 1). All edge cases (`n = 1`, `N` even/odd, `A.Nonempty`, anchor translation, equivalence of `(A.card - 1) / Nat.gcd 2 N` and `⌈n / gcd(2, N)⌉ - 1`) verified sound.
2. **Forbidden Lean Constructs:** Passed. Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `unsafe`/`implemented_by`.
3. **Provenance Wording Fix (Addressed):** The initial audit flagged the docstring on `IsValidMod` for claiming "Verbatim predicate from `FormalConjectures/Arxiv/2607.08366/MinModulus.lean`" without that external file in the workspace. Softened to "Standalone cyclic residue-set validity predicate corresponding to `FormalConjectures/Arxiv/2607.08366/MinModulus.lean`" and rebuilt Lean 4 cleanly.
4. **Attribution:** Passed. Explicitly credits Carlini–Catalisano–Geramita (*J. Algebra* 2012, Corollary 3.3) for the complex Waring rank bound $\mathrm{rk}_{\mathbb{C}}(x_0 \cdots x_{n-1}) = 2^{n-1}$ and distinguishes our elementary proof, equality classification, and cyclic strengthening from Fonollosa's prior Nisan–Wigderson bound and elementary-2-group result.
5. **Independent Python Verifier:** `python -O -W error results/fonollosa-unique-multiset-sums/verify.py` passed (`19,523` anchored sets across all finite abelian groups of order $\le 16$, `3,550` valid, `690` cyclic, `872` hitting $|G| = 2^{n-1}$ all elementary abelian $2$-groups; construction checked for $n = 1\dots 8$; stdlib-only, `-O`-safe `require()`, `0.065 s`).
6. **Document Hygiene:** Passed. Zero `\operatorname` in Markdown; `paper.pdf` compiles via `tectonic` with zero warnings; author attribution `Salem Levinstein` (no `\thanks`).

## Lean 4 Kernel Axiom Check

Verified under `leanprover/lean4:v4.33.1` + Mathlib `v4.33.1`:

```text
'FonollosaUniqueMultisetSums.order_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FonollosaUniqueMultisetSums.order_lower_bound_with_doubles' depends on axioms: [propext, Classical.choice, Quot.sound]
'FonollosaUniqueMultisetSums.two_nsmul_eq_zero_of_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'FonollosaUniqueMultisetSums.equality_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
'FonollosaUniqueMultisetSums.valid_at_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FonollosaUniqueMultisetSums.cyclic_modulus_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```
