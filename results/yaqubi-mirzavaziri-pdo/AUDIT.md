# Independent Adversarial Audit — Result #28

**Target:** Conjecture 6.2 of D. Yaqubi and M. Mirzavaziri, *Partitions with designated summands: $k$-tuples and their congruences* ([arXiv:2611.05623v1](https://arxiv.org/abs/2611.05623v1), 3 Nov 2026).  
**Auditor:** Independent read-only cross-model audit (`claude-sonnet-5-5`, effort `medium`).  
**Date:** November 26, 2026  
**Verdict:** **PASS** (zero mathematical or Lean 4 correctness defects; all polish items resolved).

## Checks Verified

1. **Lean 4 Build & Axiom Audit**
   - `lake build Conjectures.YaqubiMirzavaziriPDO` succeeded cleanly with 0 errors and 0 warnings.
   - `#print axioms` on `yaqubi_mirzavaziri_conjecture_6_2`, `gauss_J1`, `gauss_J2`, `psi_mul_psi3`, `cong_P1`, `cong_P2`, `cong_P3`, `dvd_B_odd`, `six_mul_B_three`, `B_seven_formula`, and `conjExp_explicit` reported only `[propext, Classical.choice, Quot.sound]`.
   - Grep for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, and `elab` returned zero matches.
   - Imported in `lean/Conjectures.lean`.

2. **Mathematical & Statement Fidelity**
   - Verified directly against the PDF text of `arXiv:2611.05623v1`: generating function $G(q) = f_4 f_6^2 / (f_1 f_3 f_{12})$, $B_k(n) = [q^n] G(q)^k$, and Conjecture 6.2 (largest power of $2$ dividing all $B_k(4n+3)$ is $2^{v_2(B_k(3))}$ except $2^2$ for $k \equiv 1 \pmod 8$ and $2^3$ for $k \equiv 6 \pmod 8$).
   - Verified full quantifier coverage (`1 ≤ k`, `∀ n : ℕ`, both divisibility `2^(conjExp k) ∣ B k (4*n+3)` and exactness `∃ n, ¬ 2^(conjExp k + 1) ∣ B k (4*n+3)`), including both exceptional classes $k \equiv 9 \pmod{16}$ and $k \equiv 14 \pmod{16}$ using $n = 1$ ($B_k(7)$).
   - Verified `invOfUnit` with unit constant `1` is sound via `constantCoeff_f`.

3. **Independent Verification Script**
   - `python -O -W error results/yaqubi-mirzavaziri-pdo/verify.py` passed in 0.37 s (stdlib-only, `-O`-safe `require()`, cross-checks eta quotient against the combinatorial $\mathrm{PDO}(n)$ product, Gauss identities, $\psi(q)\psi(q^3)$ dissection, $2$-dissection, $B_k(3)$ and $B_k(7)$ certificates, and Conjecture 6.2 for $k \le 160$, $4n+3 < 200$).

4. **Polish Items Addressed**
   - Removed literal backticks around `(P1)`--`(P3)` in the section heading of `paper.tex` and recompiled `paper.pdf` with 0 TeX warnings.
   - Clarified "self-contained modulo Mathlib's pentagonal number theorem" in `README.md` and `paper.tex`, and explicitly noted that Lean defines $G$ via the paper's eta quotient while `verify.py` cross-checks the combinatorial $\mathrm{PDO}_k(n)$ product.
   - Added this `AUDIT.md` file resolving the link in `README.md`.
