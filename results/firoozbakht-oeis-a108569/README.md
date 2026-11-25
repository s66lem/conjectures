# Firoozbakht’s OEIS A108569 parity conjecture

Complete proposed disproof of Farideh Firoozbakht’s 2005 conjecture on [OEIS A108569](https://oeis.org/A108569) (also listed open in `google-deepmind/formal-conjectures`, `FormalConjectures/OEIS/108569.lean`), which asserted that every solution n > 1 to φ(n) = φ(n + φ(n)) is even. The odd integer n = 5,095,354,107 = 3 × 1,033 × 1,644,193 satisfies φ(n) = 3,393,612,288 = φ(n + φ(n)), and multiplying by 3ʲ for any j ≥ 0 yields an infinite family of odd counterexamples.

- [Complete disproof](PROOF.md)
- [Lean 4 formalization](../../lean/Conjectures/FiroozbakhtA108569.lean) (`FiroozbakhtA108569.disproof_oeis_a108569`, `infinite_odd_family`)
- [Exact verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

Run `python3 verify.py` with Python 3 (standard library only), or `cd ../../lean && lake build Conjectures.FiroozbakhtA108569` to check the Lean 4 proof (v4.33.1 + Mathlib, zero `sorry`, standard axioms only). The result is internally reviewed and Lean-verified, but externally unrefereed; priority is not asserted.
