import Mathlib

/-!
# Proof of Rossi's Conjecture 6.16 (`arXiv:2611.25741v1`)

Reference: G. Rossi, "Characteristic polynomials of hyperplane arrangements and face lattices
of permutohedra", arXiv:2611.25741v1 (19 Nov 2026), Conjecture 6.16 and Theorem 6.11(1).

For `n ≥ 3`, the characteristic polynomial of the face lattice of the `(n - 1)`-dimensional
permutohedron is
`χ_n(t) = t^n - ∑_{i=0}^{n-1} A(n, i) (t - 1)^i t^(n - 1 - i)`,
where `A(n, i)` are the Eulerian numbers.

We formally prove:
1. **Main Theorem (`rossi_conjecture_6_16`):** For every integer `n ≥ 3`, `χ_n(t)` has `n`
   distinct positive real roots: `t = 1`, exactly `n - 2` roots in `(0, 1)`, and one root
   in `(1, ∞)`. In particular, `χ_n` splits into `n` distinct linear factors over `ℝ`.
2. **Full `f`-polynomial Corollary (`rossi_full_f_polynomial_real_rooted`):** Equivalently,
   the full `f`-polynomial `R_n(w) = 1 + w * ∑_{i=0}^{n-1} A(n, i) (1 + w)^i = (-w)^n χ_n(-1/w)`
   has `n` distinct strictly negative real roots.
-/

namespace RossiPermutohedronRealRoots

open Finset Polynomial Real Complex Filter Topology
open scoped BigOperators UpperHalfPlane

/-! ### Section 1: Eulerian numbers, `χ_n(t)`, `M_n(z)`, and `R_n(w)` -/

/-- Eulerian numbers `A(n, k)` (`n ≥ 1`, `0 ≤ k < n`): number of permutations of `n` elements
with `k` descents. -/
def eulerian : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, k => if k = 0 then 1 else 0
  | _n + 2, 0 => 1
  | n + 2, k + 1 => (k + 2) * eulerian (n + 1) (k + 1) + (n + 1 - k) * eulerian (n + 1) k

private lemma eulerian_zero_right {n : ℕ} (hn : 1 ≤ n) : eulerian n 0 = 1 := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => rfl
    | succ _ => rfl

private lemma eulerian_eq_zero_of_ge : ∀ {n k : ℕ}, 1 ≤ n → n ≤ k → eulerian n k = 0 := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro k _ hk
      simp [eulerian, show k ≠ 0 by omega]
    | succ n =>
      intro k _ hk
      cases k with
      | zero => omega
      | succ k =>
        simp only [eulerian]
        have h1 : eulerian (n + 1) (k + 1) = 0 := ih (by omega) (by omega)
        have h2 : n + 1 - k = 0 := by omega
        rw [h1, h2, mul_zero, zero_mul, add_zero]

private lemma eulerian_succ_succ (n k : ℕ) :
    eulerian (n + 2) (k + 1) =
      (k + 2) * eulerian (n + 1) (k + 1) + (n + 1 - k) * eulerian (n + 1) k := rfl

private lemma eulerian_symm : ∀ {n k : ℕ}, 1 ≤ n → k < n → eulerian n (n - 1 - k) = eulerian n k := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro k _ hk
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    | succ n =>
      intro k _ hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.add_sub_cancel, Nat.sub_zero, eulerian_zero_right (by omega)]
        rw [eulerian_succ_succ]
        have h1 : eulerian (n + 1) (n + 1) = 0 := eulerian_eq_zero_of_ge (by omega) le_rfl
        have h2 : eulerian (n + 1) n = 1 := by
          have h := ih (k := 0) (by omega) (by omega)
          rw [Nat.add_sub_cancel, Nat.sub_zero, eulerian_zero_right (by omega)] at h
          exact h
        rw [h1, h2]; omega
      · by_cases hklast : k = n + 1
        · subst hklast
          have hsub : n + 2 - 1 - (n + 1) = 0 := by omega
          rw [hsub, eulerian_zero_right (by omega), eulerian_succ_succ]
          have h1 : eulerian (n + 1) (n + 1) = 0 := eulerian_eq_zero_of_ge (by omega) le_rfl
          have h2 : eulerian (n + 1) n = 1 := by
            have h := ih (k := 0) (by omega) (by omega)
            rw [Nat.add_sub_cancel, Nat.sub_zero, eulerian_zero_right (by omega)] at h
            exact h
          rw [h1, h2]; omega
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          obtain ⟨m, hm⟩ : ∃ m, n + 1 - (k' + 1) = m + 1 := ⟨n - k' - 1, by omega⟩
          have hsub : n + 2 - 1 - (k' + 1) = m + 1 := by omega
          rw [hsub, eulerian_succ_succ, eulerian_succ_succ]
          have h1 : eulerian (n + 1) (m + 1) = eulerian (n + 1) k' := by
            have := ih (k := k') (by omega) (by omega)
            rwa [show n + 1 - 1 - k' = m + 1 by omega] at this
          have h2 : eulerian (n + 1) m = eulerian (n + 1) (k' + 1) := by
            have := ih (k := k' + 1) (by omega) (by omega)
            rwa [show n + 1 - 1 - (k' + 1) = m by omega] at this
          rw [h1, h2]
          have hc1 : m + 2 = n + 1 - k' := by omega
          have hc2 : n + 1 - m = k' + 2 := by omega
          rw [hc1, hc2, add_comm]

private lemma eulerian_last {n : ℕ} (hn : 1 ≤ n) : eulerian n (n - 1) = 1 := by
  have := eulerian_symm (n := n) (k := 0) hn (by omega)
  simpa [eulerian_zero_right hn] using this

private lemma eulerian_one_right : ∀ {n : ℕ}, 2 ≤ n → eulerian n 1 + n + 1 = 2 ^ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    cases n with
    | zero => intro h; omega
    | succ n =>
      intro _
      cases n with
      | zero => decide
      | succ n =>
        rw [show (1 : ℕ) = 0 + 1 from rfl, eulerian_succ_succ, eulerian_zero_right (by omega)]
        simp only [Nat.zero_add]
        have hprev := ih (by omega)
        have hpow : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
        rw [show n + 1 + 1 = n + 2 by omega] at hprev
        rw [show n + 1 + 1 + 1 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega]
        omega

private lemma eulerian_penultimate {n : ℕ} (hn : 2 ≤ n) :
    eulerian n (n - 2) + n + 1 = 2 ^ n := by
  have hsym := eulerian_symm (n := n) (k := 1) (by omega) (by omega)
  rw [show n - 1 - 1 = n - 2 by omega] at hsym
  rw [hsym]
  exact eulerian_one_right hn

/-- The `n`-th Eulerian polynomial `A_n(z) = ∑_{i=0}^{n-1} A(n, i) z^i ∈ ℝ[X]`. -/
noncomputable def eulerianPoly (n : ℕ) : Polynomial ℝ :=
  ∑ i ∈ range n, C (eulerian n i : ℝ) * X ^ i

/-- The characteristic polynomial `χ_n(t)` of the face lattice of the `(n - 1)`-permutohedron
(Rossi Theorem 6.11(1)). -/
noncomputable def charPoly (n : ℕ) : Polynomial ℝ :=
  X ^ n - ∑ i ∈ range n, C (eulerian n i : ℝ) * (X - 1) ^ i * X ^ (n - 1 - i)

/-- The Möbius-transformed polynomial `M_n(z) = (1 - z) A_n(z) + z^n = (z - 1)^n χ_n(z / (z - 1))`. -/
noncomputable def Mpoly (n : ℕ) : Polynomial ℝ :=
  (1 - X) * eulerianPoly n + X ^ n

/-- The full `f`-polynomial `R_n(w) = 1 + w ∑_{i=0}^{n-1} A(n, i) (1 + w)^i = (-w)^n χ_n(-1/w)`. -/
noncomputable def fullFPoly (n : ℕ) : Polynomial ℝ :=
  1 + X * ∑ i ∈ range n, C (eulerian n i : ℝ) * (1 + X) ^ i

private lemma coeff_eulerianPoly (n k : ℕ) :
    (eulerianPoly n).coeff k = if k < n then (eulerian n k : ℝ) else 0 := by
  unfold eulerianPoly
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k < n
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hik), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hk) h
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private lemma coeff_eulerianPoly_eq {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (eulerianPoly n).coeff k = (eulerian n k : ℝ) := by
  rw [coeff_eulerianPoly]
  split_ifs with hk
  · rfl
  · rw [eulerian_eq_zero_of_ge hn (by omega), Nat.cast_zero]

/-- Derivative recurrence for Eulerian polynomials:
`A_{n+1}(X) = (1 + n X) A_n(X) + X (1 - X) A_n'(X)` for `n ≥ 1`. -/
private lemma eulerianPoly_succ {n : ℕ} (hn : 1 ≤ n) :
    eulerianPoly (n + 1) =
      (1 + C (n : ℝ) * X) * eulerianPoly n + X * (1 - X) * derivative (eulerianPoly n) := by
  apply Polynomial.ext
  intro k
  rw [coeff_eulerianPoly_eq (by omega)]
  have hdecomp : (1 + C (n : ℝ) * X) * eulerianPoly n + X * (1 - X) * derivative (eulerianPoly n) =
      eulerianPoly n + C (n : ℝ) * (X * eulerianPoly n) + X * derivative (eulerianPoly n) -
        X * (X * derivative (eulerianPoly n)) := by ring
  rw [hdecomp, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul_zero,
      coeff_eulerianPoly_eq hn 0, eulerian_zero_right hn, eulerian_zero_right (by omega)]
    ring
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative, coeff_eulerianPoly_eq hn (k + 1), coeff_eulerianPoly_eq hn k]
    by_cases hkn : k < n
    · have hrec : eulerian (n + 1) (k + 1) =
          (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact eulerian_succ_succ m k
      rw [hrec]
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub (by omega)
      cases k with
      | zero =>
        rw [Polynomial.coeff_X_mul_zero]
        push_cast [hcast]
        ring
      | succ k =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, coeff_eulerianPoly_eq hn (k + 1)]
        push_cast [hcast]
        ring
    · have h1 : eulerian (n + 1) (k + 1) = 0 := eulerian_eq_zero_of_ge (by omega) (by omega)
      have h2 : eulerian n (k + 1) = 0 := eulerian_eq_zero_of_ge hn (by omega)
      have h3 : eulerian n k = 0 := eulerian_eq_zero_of_ge hn (by omega)
      rw [h1, h2, h3]
      cases k with
      | zero => omega
      | succ k =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, coeff_eulerianPoly_eq hn (k + 1), h3]
        simp

private lemma eulerianPoly_palindromic {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : s ≠ 0) :
    s ^ (n - 1) * (eulerianPoly n).eval s⁻¹ = (eulerianPoly n).eval s := by
  unfold eulerianPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_nbij (fun i => n - 1 - i) ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
  · intro i₁ hi₁ i₂ hi₂ hEq
    simp only [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
    dsimp only at hEq; omega
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_range] at hj
    exact ⟨n - 1 - j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [eulerian_symm hn hi, inv_pow]
    have hpow : s ^ (n - 1) = s ^ i * s ^ (n - 1 - i) := by
      rw [← pow_add, show i + (n - 1 - i) = n - 1 by omega]
    rw [hpow]
    field_simp [hs]

private lemma Mpoly_eval_eq_charPoly {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : z ≠ 1) :
    (Mpoly n).eval z = (z - 1) ^ n * (charPoly n).eval (z / (z - 1)) := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  unfold Mpoly charPoly eulerianPoly
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finsetSum, Polynomial.eval_C]
  conv_rhs => rw [mul_sub, Finset.mul_sum]
  have h1 : (z - 1) ^ n * (z / (z - 1)) ^ n = z ^ n := by rw [div_pow]; field_simp [hz1]
  rw [h1]
  have h2 : ∑ i ∈ range n,
      (z - 1) ^ n * ((eulerian n i : ℝ) * (z / (z - 1) - 1) ^ i * (z / (z - 1)) ^ (n - 1 - i)) =
      (z - 1) * ∑ i ∈ range n, (eulerian n i : ℝ) * z ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_nbij (fun i => n - 1 - i) ?_ ?_ ?_ ?_
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intro i₁ hi₁ i₂ hi₂ hEq
      simp only [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
      dsimp only at hEq; omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_range] at hj
      exact ⟨n - 1 - j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [eulerian_symm hn hi]
      have hfrac : z / (z - 1) - 1 = 1 / (z - 1) := by field_simp [hz1]; ring
      rw [hfrac]
      have hpow : (z - 1) ^ n = (z - 1) * (z - 1) ^ i * (z - 1) ^ (n - 1 - i) := by
        rw [← pow_succ', ← pow_add, show i + 1 + (n - 1 - i) = n by omega]
      rw [hpow, div_pow, div_pow, one_pow]
      field_simp [hz1]
  rw [h2]
  ring

private lemma charPoly_eval_one {n : ℕ} (hn : 1 ≤ n) : (charPoly n).eval 1 = 0 := by
  unfold charPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one,
    sub_self]
  rw [Finset.sum_eq_single 0]
  · simp [eulerian_zero_right hn]
  · intro i _ hi0
    rw [zero_pow hi0, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma Mpoly_eval_zero {n : ℕ} (hn : 1 ≤ n) : (Mpoly n).eval 0 = 1 := by
  unfold Mpoly eulerianPoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, sub_zero, one_mul, zero_pow (by omega : n ≠ 0), add_zero,
    Polynomial.eval_finsetSum, Polynomial.eval_C, Polynomial.eval_pow]
  rw [Finset.sum_eq_single 0]
  · simp [eulerian_zero_right hn]
  · intro i _ hi0; rw [zero_pow hi0, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma Mpoly_eval_one {n : ℕ} : (Mpoly n).eval 1 = 1 := by
  simp [Mpoly]

private lemma Mpoly_reflection {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : s ≠ 0) :
    (Mpoly n).eval s⁻¹ = s⁻¹ ^ n * (1 - (1 - s) * (eulerianPoly n).eval s) := by
  unfold Mpoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow]
  have hpal := eulerianPoly_palindromic hn hs
  have hsn : s ^ n = s * s ^ (n - 1) := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
  have heval : (eulerianPoly n).eval s⁻¹ = (eulerianPoly n).eval s / s ^ (n - 1) := by
    rw [eq_div_iff (pow_ne_zero _ hs), mul_comm]; exact hpal
  rw [heval, inv_pow, hsn]
  field_simp [hs]
  ring

private lemma coeff_Mpoly_eq_zero_of_ge {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ k) :
    (Mpoly n).coeff k = 0 := by
  unfold Mpoly
  have hexp : (1 - X) * eulerianPoly n + X ^ n = eulerianPoly n - X * eulerianPoly n + X ^ n := by ring
  rw [hexp, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  cases k with
  | zero => omega
  | succ k =>
    rw [Polynomial.coeff_X_mul, coeff_eulerianPoly_eq hn (k + 1), coeff_eulerianPoly_eq hn k]
    by_cases hkn : k + 1 = n
    · rw [if_pos hkn, eulerian_eq_zero_of_ge hn (by omega),
        show k = n - 1 by omega, eulerian_last hn]
      simp
    · rw [if_neg hkn, eulerian_eq_zero_of_ge hn (by omega),
        eulerian_eq_zero_of_ge hn (by omega)]
      simp

private lemma coeff_Mpoly_top {n : ℕ} (hn : 3 ≤ n) :
    (Mpoly n).coeff (n - 1) = (n : ℝ) + 2 - 2 ^ n := by
  unfold Mpoly
  have hexp : (1 - X) * eulerianPoly n + X ^ n = eulerianPoly n - X * eulerianPoly n + X ^ n := by ring
  rw [hexp, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega),
    add_zero]
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
  rw [hm, Polynomial.coeff_X_mul, coeff_eulerianPoly_eq (by omega),
    coeff_eulerianPoly_eq (by omega), ← hm, eulerian_last (by omega)]
  have hpen := eulerian_penultimate (n := n) (by omega)
  have hm_eq : m = n - 2 := by omega
  rw [hm_eq, Nat.cast_one]
  have hpenR : (eulerian n (n - 2) : ℝ) + (n : ℝ) + 1 = 2 ^ n := by exact_mod_cast hpen
  linarith

private lemma two_pow_gt_add_two {n : ℕ} (hn : 3 ≤ n) : (n : ℝ) + 2 < 2 ^ n := by
  have hnat : n + 2 < 2 ^ n := by
    induction n with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => omega
      | succ n =>
        cases n with
        | zero => omega
        | succ n =>
          cases n with
          | zero => decide
          | succ n =>
            have hprev := ih (by omega)
            have : 2 ^ (n + 4) = 2 * 2 ^ (n + 3) := by ring
            omega
  exact_mod_cast hnat

private lemma Mpoly_natDegree {n : ℕ} (hn : 3 ≤ n) : (Mpoly n).natDegree = n - 1 := by
  have hne : (Mpoly n).coeff (n - 1) ≠ 0 := by
    rw [coeff_Mpoly_top hn]
    have := two_pow_gt_add_two hn
    linarith
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact coeff_Mpoly_eq_zero_of_ge (by omega) (by omega)
  · exact Polynomial.le_natDegree_of_ne_zero hne

private lemma Mpoly_leadingCoeff_neg {n : ℕ} (hn : 3 ≤ n) : (Mpoly n).leadingCoeff < 0 := by
  rw [Polynomial.leadingCoeff, Mpoly_natDegree hn, coeff_Mpoly_top hn]
  linarith [two_pow_gt_add_two hn]

private lemma charPoly_natDegree {n : ℕ} (hn : 1 ≤ n) : (charPoly n).natDegree = n := by
  unfold charPoly
  have hsum_deg : (∑ i ∈ range n, C (eulerian n i : ℝ) * (X - 1) ^ i * X ^ (n - 1 - i)).natDegree < n := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_lt]
    refine ⟨by omega, fun i hi => ?_⟩
    rw [Finset.mem_range] at hi
    calc
      (C (eulerian n i : ℝ) * (X - 1) ^ i * X ^ (n - 1 - i)).natDegree
          ≤ (C (eulerian n i : ℝ) * (X - 1) ^ i).natDegree + (X ^ (n - 1 - i) : Polynomial ℝ).natDegree :=
            Polynomial.natDegree_mul_le
      _ ≤ (C (eulerian n i : ℝ)).natDegree + ((X - 1) ^ i : Polynomial ℝ).natDegree +
            (X ^ (n - 1 - i) : Polynomial ℝ).natDegree := by
            gcongr; exact Polynomial.natDegree_mul_le
      _ ≤ 0 + i + (n - 1 - i) := by
            rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
            have hsub : ((X - 1 : Polynomial ℝ) ^ i).natDegree ≤ i := by
              calc
                ((X - 1 : Polynomial ℝ) ^ i).natDegree ≤ i * (X - 1 : Polynomial ℝ).natDegree :=
                  Polynomial.natDegree_pow_le
                _ ≤ i * 1 := by
                  gcongr
                  exact Polynomial.natDegree_sub_le X 1 |>.trans (by simp)
                _ = i := mul_one i
            omega
      _ < n := by omega
  have hlt : (∑ i ∈ range n, C (eulerian n i : ℝ) * (X - 1) ^ i * X ^ (n - 1 - i)).natDegree <
      (X ^ n : Polynomial ℝ).natDegree := by
    rwa [Polynomial.natDegree_X_pow]
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]

private lemma charPoly_ne_zero {n : ℕ} (hn : 1 ≤ n) : charPoly n ≠ 0 := by
  intro h0
  have := charPoly_natDegree hn
  rw [h0, Polynomial.natDegree_zero] at this
  omega

private lemma fullFPoly_eval_eq_charPoly {n : ℕ} {w : ℝ} (hw : w ≠ 0) :
    (fullFPoly n).eval w = (-w) ^ n * (charPoly n).eval (-1 / w) := by
  unfold fullFPoly charPoly
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finsetSum, Polynomial.eval_C]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  have h1 : (-w) ^ n * (-1 / w) ^ n = 1 := by
    rw [← mul_pow]; field_simp [hw]; simp
  rw [h1]
  have h2 : -∑ i ∈ range n, (-w) ^ n * ((eulerian n i : ℝ) * (-1 / w - 1) ^ i * (-1 / w) ^ (n - 1 - i)) =
      ∑ i ∈ range n, w * ((eulerian n i : ℝ) * (1 + w) ^ i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hfrac : -1 / w - 1 = -(1 + w) / w := by field_simp [hw]; ring
    rw [hfrac]
    have hpow : (-w) ^ n = (-w) * (-w) ^ i * (-w) ^ (n - 1 - i) := by
      rw [← pow_succ', ← pow_add, show i + 1 + (n - 1 - i) = n by omega]
    rw [hpow]
    have ha : (-w) ^ i * (-(1 + w) / w) ^ i = (1 + w) ^ i := by
      rw [← mul_pow]; congr 1; field_simp [hw]
    have hb : (-w) ^ (n - 1 - i) * (-1 / w) ^ (n - 1 - i) = 1 := by
      rw [← mul_pow]; field_simp [hw]; simp
    calc
      -((-w) * (-w) ^ i * (-w) ^ (n - 1 - i) * ((eulerian n i : ℝ) * (-(1 + w) / w) ^ i * (-1 / w) ^ (n - 1 - i)))
          = w * (eulerian n i : ℝ) * ((-w) ^ i * (-(1 + w) / w) ^ i) *
              ((-w) ^ (n - 1 - i) * (-1 / w) ^ (n - 1 - i)) := by ring
      _ = w * ((eulerian n i : ℝ) * (1 + w) ^ i) := by rw [ha, hb]; ring
  linarith

private lemma fullFPoly_natDegree {n : ℕ} (hn : 1 ≤ n) : (fullFPoly n).natDegree = n := by
  have h1X : (1 + X : Polynomial ℝ) = X + C (1 : ℝ) := by rw [add_comm, Polynomial.C_1]
  have hdeg_pow : ∀ k : ℕ, ((1 + X : Polynomial ℝ) ^ k).natDegree = k := by
    intro k
    rw [h1X, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  have hsum_coeff_top : (∑ i ∈ range n, C (eulerian n i : ℝ) * (1 + X) ^ i).coeff (n - 1) = 1 := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (n - 1)]
    · rw [Polynomial.coeff_C_mul, eulerian_last hn, Nat.cast_one, one_mul]
      have hmonic : ((1 + X : Polynomial ℝ) ^ (n - 1)).Monic := by
        rw [h1X]; exact (Polynomial.monic_X_add_C 1).pow (n - 1)
      simpa [Polynomial.Monic, Polynomial.leadingCoeff, hdeg_pow (n - 1)] using hmonic
    · intro i hi hne
      rw [Finset.mem_range] at hi
      rw [Polynomial.coeff_C_mul]
      have hdeg : ((1 + X : Polynomial ℝ) ^ i).natDegree < n - 1 := by
        rw [hdeg_pow i]; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hsum_deg : (∑ i ∈ range n, C (eulerian n i : ℝ) * (1 + X) ^ i).natDegree = n - 1 := by
    apply le_antisymm
    · refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun i hi => ?_⟩
      rw [Finset.mem_range] at hi
      dsimp only [Function.comp_apply]
      calc
        (C (eulerian n i : ℝ) * (1 + X) ^ i).natDegree
            ≤ (C (eulerian n i : ℝ)).natDegree + ((1 + X : Polynomial ℝ) ^ i).natDegree :=
              Polynomial.natDegree_mul_le
        _ ≤ n - 1 := by rw [Polynomial.natDegree_C, zero_add, hdeg_pow i]; omega
    · exact Polynomial.le_natDegree_of_ne_zero (by rw [hsum_coeff_top]; exact one_ne_zero)
  have hsum_ne : (∑ i ∈ range n, C (eulerian n i : ℝ) * (1 + X) ^ i) ≠ 0 := by
    intro h0; rw [h0, Polynomial.coeff_zero] at hsum_coeff_top; exact zero_ne_one hsum_coeff_top
  unfold fullFPoly
  have hdeg_mul : (X * ∑ i ∈ range n, C (eulerian n i : ℝ) * (1 + X) ^ i).natDegree = n := by
    rw [Polynomial.natDegree_X_mul hsum_ne, hsum_deg]; omega
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hdeg_mul
  · rw [Polynomial.natDegree_one, hdeg_mul]; omega

/-! ### Section 2: Paired Sign-Alternation Lemma (Lemma 3.1) -/

private lemma exists_root_of_mul_neg {P : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (hneg : P.eval a * P.eval b < 0) : ∃ x ∈ Set.Ioo a b, P.IsRoot x := by
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) := P.continuous.continuousOn
  rcases mul_neg_iff.mp hneg with ⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩
  · have hmem : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := ⟨hb_neg, ha_pos⟩
    obtain ⟨x, hx, hPx⟩ := intermediate_value_Ioo' hab.le hcont hmem
    exact ⟨x, hx, hPx⟩
  · have hmem : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := ⟨ha_neg, hb_pos⟩
    obtain ⟨x, hx, hPx⟩ := intermediate_value_Ioo hab.le hcont hmem
    exact ⟨x, hx, hPx⟩

private lemma exists_roots_of_alternating {P : Polynomial ℝ} {m : ℕ} (pts : Fin (m + 1) → ℝ)
    (hmono : StrictMono pts)
    (halt : ∀ i : Fin m, P.eval (pts i.castSucc) * P.eval (pts i.succ) < 0) :
    ∃ S : Finset ℝ, S.card = m ∧ ∀ x ∈ S, P.IsRoot x ∧ pts 0 < x ∧ x < pts (Fin.last m) := by
  have hex : ∀ i : Fin m, ∃ x ∈ Set.Ioo (pts i.castSucc) (pts i.succ), P.IsRoot x := fun i =>
    exists_root_of_mul_neg (hmono Fin.castSucc_lt_succ) (halt i)
  choose r hr_mem hr_root using hex
  have hr_mono : StrictMono r := by
    intro i j hij
    have hle : pts i.succ ≤ pts j.castSucc :=
      hmono.monotone (show i.succ.val ≤ j.castSucc.val by have : i.val < j.val := hij; simp; omega)
    exact ((hr_mem i).2.trans_le hle).trans (hr_mem j).1
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hr_mono.injective, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    refine ⟨hr_root i, ?_, ?_⟩
    · exact lt_of_le_of_lt (hmono.monotone (Fin.zero_le i.castSucc)) (hr_mem i).1
    · exact lt_of_lt_of_le (hr_mem i).2 (hmono.monotone (Fin.le_last i.succ))

private lemma exists_Mpoly_root_gt_one {n : ℕ} (hn : 3 ≤ n) :
    ∃ z : ℝ, 1 < z ∧ (Mpoly n).IsRoot z := by
  have hdeg : 0 < (Mpoly n).natDegree := by rw [Mpoly_natDegree hn]; omega
  have hlc : (Mpoly n).leadingCoeff < 0 := Mpoly_leadingCoeff_neg hn
  -- Since `leadingCoeff < 0` and `natDegree > 0`, `M_n(x) → -∞` as `x → +∞`!
  have htend : Tendsto (fun x : ℝ => (Mpoly n).eval x) atTop atBot := by
    have hpos : Tendsto (fun x : ℝ => (-(Mpoly n)).eval x) atTop atTop :=
      Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _
        (by
          rw [Polynomial.degree_neg, Polynomial.degree_eq_natDegree (by intro h; rw [h] at hdeg; simp at hdeg)]
          exact_mod_cast hdeg)
        (by rw [Polynomial.leadingCoeff_neg]; linarith)
    have hneg : Tendsto (fun x : ℝ => -((-(Mpoly n)).eval x)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hpos
    simpa using hneg
  obtain ⟨R, hR1, hRneg⟩ : ∃ R : ℝ, 1 < R ∧ (Mpoly n).eval R < 0 := by
    have hev1 : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
    have hev2 : ∀ᶠ x : ℝ in atTop, (Mpoly n).eval x < 0 := htend.eventually (eventually_lt_atBot 0)
    obtain ⟨R, h1, h2⟩ := (hev1.and hev2).exists
    exact ⟨R, h1, h2⟩
  have hmul : (Mpoly n).eval 1 * (Mpoly n).eval R < 0 := by
    rw [Mpoly_eval_one, one_mul]; exact hRneg
  obtain ⟨z, hz, hroot⟩ := exists_root_of_mul_neg hR1 hmul
  exact ⟨z, hz.1, hroot⟩

/-- **Lemma 3.1 (Paired Sign-Alternation Lemma):**
Given `n ≥ 3`, `K = (n - 1) / 2`, and strictly increasing test points `0 < σ 0 < ... < σ (K-1) ≤ 1`
(with `σ (K - 1) < 1` when `Even n`) satisfying `(-1)^(j+1) * (1 + σ j) * A_n(-σ j) > 1` for
every `j : Fin K`, `χ_n(t)` has `n` distinct positive real roots: `1`, `n - 2` in `(0, 1)`,
and `1` in `(1, ∞)`. -/
theorem paired_sign_alternation {n : ℕ} (hn : 3 ≤ n)
    (σ : Fin ((n - 1) / 2) → ℝ)
    (hσ_pos : ∀ j, 0 < σ j)
    (hσ_mono : StrictMono σ)
    (hσ_le : ∀ j, σ j ≤ 1)
    (hσ_even_lt : Even n → ∀ j, σ j < 1)
    (hcond : ∀ j : Fin ((n - 1) / 2),
      (-1 : ℝ) ^ (j.val + 1) * ((1 + σ j) * (eulerianPoly n).eval (-σ j)) > 1) :
    ∃ S : Finset ℝ, S.card = n ∧
      (∀ t ∈ S, (charPoly n).IsRoot t) ∧
      (1 : ℝ) ∈ S ∧
      (S.filter (fun t => 0 < t ∧ t < 1)).card = n - 2 ∧
      (S.filter (fun t => 1 < t)).card = 1 := by
  let K := (n - 1) / 2
  have hK_pos : 0 < K := by omega
  have hM_neg : ∀ j : Fin ((n - 1) / 2), 0 < (-1 : ℝ) ^ (j.val + 1) * (Mpoly n).eval (-σ j) := by
    intro j
    have h1 := hcond j
    have hM : (Mpoly n).eval (-σ j) = (1 + σ j) * (eulerianPoly n).eval (-σ j) + (-σ j) ^ n := by
      simp [Mpoly]
    rw [hM, mul_add]
    have hpow : |(-1 : ℝ) ^ (j.val + 1) * (-σ j) ^ n| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_neg,
        abs_of_pos (hσ_pos j)]
      exact pow_le_one₀ (hσ_pos j).le (hσ_le j)
    linarith [(abs_le.mp hpow).1]
  have hM_inv : ∀ j : Fin ((n - 1) / 2), 0 < (-1 : ℝ) ^ (n + j.val + 2) * (Mpoly n).eval (-(σ j)⁻¹) := by
    intro j
    have h1 := hcond j
    have hne : -σ j ≠ 0 := neg_ne_zero.mpr (hσ_pos j).ne'
    have hrefl := Mpoly_reflection (by omega : 1 ≤ n) hne
    rw [inv_neg] at hrefl
    rw [hrefl]
    have hpow_eq : (-(σ j)⁻¹) ^ n = (-1 : ℝ) ^ n * (σ j)⁻¹ ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [hpow_eq, sub_neg_eq_add]
    have hpos_pow : 0 < (σ j)⁻¹ ^ n := pow_pos (inv_pos.mpr (hσ_pos j)) n
    have hsign : (-1 : ℝ) ^ (n + j.val + 2) * ((-1 : ℝ) ^ n * (σ j)⁻¹ ^ n *
        (1 - (1 + σ j) * (eulerianPoly n).eval (-σ j))) =
        (σ j)⁻¹ ^ n * ((-1 : ℝ) ^ (j.val + 1) * ((1 + σ j) * (eulerianPoly n).eval (-σ j)) -
          (-1 : ℝ) ^ (j.val + 1)) := by
      have h2n : (-1 : ℝ) ^ (n + j.val + 2) * (-1 : ℝ) ^ n = -((-1 : ℝ) ^ (j.val + 1)) := by
        rw [← pow_add, show n + j.val + 2 + n = 2 * n + (j.val + 2) by omega, pow_add,
          pow_mul, neg_one_sq, one_pow, one_mul, pow_succ]; ring
      calc
        (-1 : ℝ) ^ (n + j.val + 2) * ((-1 : ℝ) ^ n * (σ j)⁻¹ ^ n *
            (1 - (1 + σ j) * (eulerianPoly n).eval (-σ j)))
            = (σ j)⁻¹ ^ n * (((-1 : ℝ) ^ (n + j.val + 2) * (-1 : ℝ) ^ n) *
                (1 - (1 + σ j) * (eulerianPoly n).eval (-σ j))) := by ring
        _ = (σ j)⁻¹ ^ n * ((-1 : ℝ) ^ (j.val + 1) * ((1 + σ j) * (eulerianPoly n).eval (-σ j)) -
              (-1 : ℝ) ^ (j.val + 1)) := by rw [h2n]; ring
    rw [hsign]
    refine mul_pos hpos_pow ?_
    have hle1 : (-1 : ℝ) ^ (j.val + 1) ≤ 1 := by
      rcases Nat.even_or_odd (j.val + 1) with he | ho
      · rw [he.neg_one_pow]
      · rw [ho.neg_one_pow]; linarith
    linarith
  have hneg_roots : ∃ T : Finset ℝ, T.card = n - 2 ∧ ∀ z ∈ T, (Mpoly n).IsRoot z ∧ z < 0 := by
    let L := n - 2 - K
    have hLK : L + K = n - 2 := by omega
    have hL_le : L ≤ K := by omega
    have hL_odd : ¬ Even n → L + 1 = K := by
      intro ho
      have hodd : Odd n := Nat.not_even_iff_odd.mp ho
      rcases hodd with ⟨r, hr⟩; omega
    let pts : Fin ((n - 2) + 1) → ℝ := fun i =>
      if h1 : i.val < L then -(σ ⟨i.val, by omega⟩)⁻¹
      else if h2 : i.val < n - 2 then -σ ⟨n - 3 - i.val, by omega⟩
      else 0
    have hpts_last : pts (Fin.last (n - 2)) = 0 := by
      simp [pts, show ¬ n - 2 < L by omega]
    have hpts_mono : StrictMono pts := by
      intro a b hab
      have hab_val : a.val < b.val := hab
      simp only [pts]
      by_cases ha1 : a.val < L
      · rw [dif_pos ha1]
        by_cases hb1 : b.val < L
        · rw [dif_pos hb1]
          have hlt : σ ⟨a.val, by omega⟩ < σ ⟨b.val, by omega⟩ :=
            hσ_mono (show (⟨a.val, by omega⟩ : Fin ((n - 1) / 2)) < ⟨b.val, by omega⟩ from hab_val)
          exact neg_lt_neg (inv_strictAnti₀ (hσ_pos _) hlt)
        · rw [dif_neg hb1]
          by_cases hb2 : b.val < n - 2
          · rw [dif_pos hb2]
            have ha_lt_one : σ ⟨a.val, by omega⟩ < 1 := by
              by_cases he : Even n
              · exact hσ_even_lt he _
              · have hlt_K : a.val < K - 1 := by have := hL_odd he; omega
                exact lt_of_lt_of_le (hσ_mono (show (⟨a.val, by omega⟩ : Fin ((n - 1) / 2)) <
                  ⟨K - 1, by omega⟩ from hlt_K)) (hσ_le _)
            have h1_lt : 1 < (σ ⟨a.val, by omega⟩)⁻¹ := (one_lt_inv₀ (hσ_pos _)).mpr ha_lt_one
            linarith [hσ_le ⟨n - 3 - b.val, by omega⟩]
          · rw [dif_neg hb2]
            exact neg_lt_zero.mpr (inv_pos.mpr (hσ_pos _))
      · rw [dif_neg ha1]
        have hb1 : ¬ b.val < L := by omega
        rw [dif_neg hb1]
        by_cases ha2 : a.val < n - 2
        · rw [dif_pos ha2]
          by_cases hb2 : b.val < n - 2
          · rw [dif_pos hb2]
            have hlt : σ ⟨n - 3 - b.val, by omega⟩ < σ ⟨n - 3 - a.val, by omega⟩ :=
              hσ_mono (Fin.mk_lt_mk.mpr (by omega))
            linarith
          · rw [dif_neg hb2]
            exact neg_lt_zero.mpr (hσ_pos _)
        · exfalso; have := b.isLt; omega
    have hpts_sign : ∀ i : Fin ((n - 2) + 1),
        0 < (-1 : ℝ) ^ (n - 2 - i.val) * (Mpoly n).eval (pts i) := by
      intro i
      simp only [pts]
      by_cases h1 : i.val < L
      · rw [dif_pos h1]
        have hinv := hM_inv ⟨i.val, by omega⟩
        have hpar : (-1 : ℝ) ^ (n - 2 - i.val) = (-1 : ℝ) ^ (n + i.val + 2) := by
          have hev : Even ((n + i.val + 2) - (n - 2 - i.val)) := ⟨i.val + 2, by omega⟩
          rw [show n + i.val + 2 = (n - 2 - i.val) + ((n + i.val + 2) - (n - 2 - i.val)) by omega,
            pow_add, hev.neg_one_pow, mul_one]
        rwa [hpar]
      · rw [dif_neg h1]
        by_cases h2 : i.val < n - 2
        · rw [dif_pos h2]
          have hneg := hM_neg ⟨n - 3 - i.val, by omega⟩
          rwa [show n - 3 - i.val + 1 = n - 2 - i.val by omega] at hneg
        · rw [dif_neg h2]
          have hi_eq : i.val = n - 2 := by have := i.isLt; omega
          rw [hi_eq, Nat.sub_self, pow_zero, one_mul, Mpoly_eval_zero (by omega)]
          exact zero_lt_one
    have halt : ∀ i : Fin (n - 2),
        (Mpoly n).eval (pts i.castSucc) * (Mpoly n).eval (pts i.succ) < 0 := by
      intro i
      have ha := hpts_sign i.castSucc
      have hb := hpts_sign i.succ
      have hprod := mul_pos ha hb
      have hexp : (-1 : ℝ) ^ (n - 2 - i.castSucc.val) * (-1 : ℝ) ^ (n - 2 - i.succ.val) = -1 := by
        rw [← pow_add]
        have hodd : Odd ((n - 2 - i.val) + (n - 2 - (i.val + 1))) :=
          ⟨n - 3 - i.val, by have := i.isLt; omega⟩
        simpa using hodd.neg_one_pow
      nlinarith
    obtain ⟨T, hTcard, hTprop⟩ := exists_roots_of_alternating pts hpts_mono halt
    refine ⟨T, hTcard, fun z hz => ⟨(hTprop z hz).1, ?_⟩⟩
    have := (hTprop z hz).2.2
    rwa [hpts_last] at this
  obtain ⟨T, hTcard, hTprop⟩ := hneg_roots
  obtain ⟨zpos, hzpos_gt, hzpos_root⟩ := exists_Mpoly_root_gt_one hn
  let f : ℝ → ℝ := fun z => z / (z - 1)
  have hf_inj : ∀ z₁ z₂ : ℝ, z₁ ≠ 1 → z₂ ≠ 1 → f z₁ = f z₂ → z₁ = z₂ := by
    intro z₁ z₂ h1 h2 hEq
    dsimp [f] at hEq
    have h1' : z₁ - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h2' : z₂ - 1 ≠ 0 := sub_ne_zero.mpr h2
    rw [div_eq_div_iff h1' h2'] at hEq
    linarith
  have hf_root : ∀ z : ℝ, z ≠ 1 → (Mpoly n).IsRoot z → (charPoly n).IsRoot (f z) := by
    intro z hz hroot
    have h := Mpoly_eval_eq_charPoly (by omega : 1 ≤ n) hz
    rw [Polynomial.IsRoot.def] at hroot ⊢
    rw [hroot] at h
    have hpow : (z - 1) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hz)
    exact (mul_eq_zero.mp h.symm).resolve_left hpow
  have hf_neg : ∀ z : ℝ, z < 0 → 0 < f z ∧ f z < 1 := by
    intro z hz
    dsimp [f]
    have hden : z - 1 < 0 := by linarith
    constructor
    · exact div_pos_of_neg_of_neg hz hden
    · rw [div_lt_one_of_neg hden]; linarith
  have hf_gt1 : 1 < f zpos := by
    dsimp [f]
    rw [one_lt_div (by linarith : 0 < zpos - 1)]
    linarith
  let S0 : Finset ℝ := T.image f
  have hS0_card : S0.card = n - 2 := by
    rw [Finset.card_image_of_injOn, hTcard]
    intro z₁ hz₁ z₂ hz₂ hEq
    exact hf_inj z₁ z₂ (by linarith [(hTprop z₁ hz₁).2]) (by linarith [(hTprop z₂ hz₂).2]) hEq
  have hS0_bounds : ∀ t ∈ S0, 0 < t ∧ t < 1 := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    exact hf_neg z (hTprop z hz).2
  let S : Finset ℝ := insert 1 (insert (f zpos) S0)
  have h1_not_in_S0 : (1 : ℝ) ∉ S0 := fun h => lt_irrefl 1 (hS0_bounds 1 h).2
  have hfpos_not_in_S0 : f zpos ∉ S0 := fun h => by have := (hS0_bounds (f zpos) h).2; linarith
  have h1_ne_fpos : (1 : ℝ) ≠ f zpos := ne_of_lt hf_gt1
  refine ⟨S, ?_, ?_, Finset.mem_insert_self 1 _, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [h1_ne_fpos, h1_not_in_S0]),
      Finset.card_insert_of_notMem hfpos_not_in_S0, hS0_card]; omega
  · intro t ht
    simp only [S, Finset.mem_insert] at ht
    rcases ht with rfl | rfl | ht0
    · exact charPoly_eval_one (by omega)
    · exact hf_root zpos (ne_of_gt hzpos_gt) hzpos_root
    · rcases Finset.mem_image.mp ht0 with ⟨z, hz, rfl⟩
      exact hf_root z (by linarith [(hTprop z hz).2]) (hTprop z hz).1
  · have hfilt : S.filter (fun t => 0 < t ∧ t < 1) = S0 := by
      ext t
      simp only [S, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | rfl | ht0, h0, h1⟩
        · linarith
        · linarith
        · exact ht0
      · intro ht0
        exact ⟨Or.inr (Or.inr ht0), hS0_bounds t ht0⟩
    rw [hfilt, hS0_card]
  · have hfilt : S.filter (fun t => 1 < t) = {f zpos} := by
      ext t
      simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | ht0, h1⟩
        · linarith
        · rfl
        · linarith [(hS0_bounds t ht0).2]
      · rintro rfl
        exact ⟨Or.inr (Or.inl rfl), hf_gt1⟩
    rw [hfilt, Finset.card_singleton]

/-! ### Section 3: Euler's Alternating Series & Regime A -/

private lemma summable_nat_pow_mul_pow (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ => ((k + 1 : ℝ) ^ n) * r ^ k := by
  by_cases hr_zero : r = 0
  · subst hr_zero
    refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    rw [Finset.mem_singleton] at hk; rw [zero_pow hk, mul_zero]
  · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
    set ρ : ℝ := (r + 1) / 2 with hρ_def
    have hρ_pos : 0 < ρ := by linarith
    have hρ_lt1 : ρ < 1 := by linarith
    have hratio : r / ρ < 1 := (div_lt_one hρ_pos).mpr (by linarith)
    have htend : Tendsto (fun k : ℕ => ((k + 1 : ℝ) ^ n) * (r / ρ) ^ k) atTop (nhds 0) := by
      have h0 : Tendsto (fun k : ℕ => ((k : ℝ) ^ n) * (r / ρ) ^ k) atTop (nhds 0) :=
        tendsto_pow_const_mul_const_pow_of_abs_lt_one n
          (by rw [abs_of_pos (div_pos hr_pos hρ_pos)]; exact hratio)
      have h1 : Tendsto (fun k : ℕ => ((k + 1 : ℝ) ^ n) * (r / ρ) ^ (k + 1)) atTop (nhds 0) :=
        (h0.comp (tendsto_add_atTop_nat 1)).congr fun k => by simp [Nat.cast_add, Nat.cast_one]
      have h2 := h1.div_const (r / ρ)
      rw [zero_div] at h2
      refine h2.congr fun k => ?_
      have hne : r / ρ ≠ 0 := ne_of_gt (div_pos hr_pos hρ_pos)
      rw [pow_succ]; field_simp [hne]
    refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hρ_pos.le hρ_lt1) ?_
    filter_upwards [htend.eventually (ge_mem_nhds zero_lt_one)] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmul : ((k + 1 : ℝ) ^ n) * r ^ k = (((k + 1 : ℝ) ^ n) * (r / ρ) ^ k) * ρ ^ k := by
      rw [div_pow]; field_simp [hρ_pos.ne']
    rw [hmul]
    exact mul_le_of_le_one_left (pow_nonneg hρ_pos.le k) hk

/-- Euler's series for Eulerian polynomials: for `n ≥ 1` and `|z| < 1`,
`∑_{k=0}^∞ (k + 1)^n z^k = A_n(z) / (1 - z)^(n + 1)`. -/
private lemma hasSum_eulerian_series :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {z : ℝ}, |z| < 1 →
      HasSum (fun k : ℕ => ((k + 1 : ℝ) ^ n) * z ^ k) ((eulerianPoly n).eval z / (1 - z) ^ (n + 1)) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro _ z hz
      set r : ℝ := (|z| + 1) / 2 with hr_def
      have hr0 : 0 ≤ r := by linarith [abs_nonneg z]
      have hr1 : r < 1 := by linarith
      have hr_pos : 0 < r := by linarith [abs_nonneg z]
      have hz_in : z ∈ Set.Ioo (-r) r := by
        rw [Set.mem_Ioo]; exact abs_lt.mp (by linarith)
      have hderiv_tsum : HasDerivAt (fun x : ℝ => ∑' k : ℕ, x ^ (k + 1))
          (∑' k : ℕ, ((k + 1 : ℝ) ^ 1) * z ^ k) z :=
        hasDerivAt_tsum_of_isPreconnected
          (g := fun k (x : ℝ) => x ^ (k + 1))
          (g' := fun k (x : ℝ) => ((k + 1 : ℝ) ^ 1) * x ^ k)
          (u := fun k : ℕ => ((k + 1 : ℝ) ^ 1) * r ^ k)
          (t := Set.Ioo (-r) r)
          (summable_nat_pow_mul_pow 1 hr0 hr1) isOpen_Ioo isPreconnected_Ioo
          (fun k x _ => by simpa [pow_one] using hasDerivAt_pow (k + 1) x)
          (fun k x hx => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_pow]
            gcongr; exact abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
          (y₀ := 0) (by rw [Set.mem_Ioo]; constructor <;> linarith)
          (by
            have : (fun k : ℕ => (0 : ℝ) ^ (k + 1)) = 0 := by funext k; simp
            rw [this]; exact summable_zero) hz_in
      have hEqOn : ∀ x ∈ Set.Ioo (-r) r, (∑' k : ℕ, x ^ (k + 1)) = x / (1 - x) := by
        intro x hx
        have hx1 : |x| < 1 := lt_trans (abs_lt.mpr ⟨hx.1, hx.2⟩) hr1
        have hgeom := hasSum_geometric_of_abs_lt_one hx1
        have hmul : HasSum (fun k : ℕ => x * x ^ k) (x * (1 - x)⁻¹) := hgeom.mul_left x
        simpa [pow_succ', div_eq_mul_inv] using hmul.tsum_eq
      have hderiv_rat : HasDerivAt (fun x : ℝ => x / (1 - x)) (1 / (1 - z) ^ 2) z := by
        have h1z : 1 - z ≠ 0 := by linarith [(abs_lt.mp hz).2]
        have hd := (hasDerivAt_id z).fun_div ((hasDerivAt_const z (1 : ℝ)).fun_sub (hasDerivAt_id z)) h1z
        exact hd.congr_deriv (by dsimp only [id_eq]; ring)
      have hderiv_tsum2 : HasDerivAt (fun x : ℝ => ∑' k : ℕ, x ^ (k + 1)) (1 / (1 - z) ^ 2) z :=
        hderiv_rat.congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hz_in) hEqOn)
      have htsum_eq : (∑' k : ℕ, ((k + 1 : ℝ) ^ 1) * z ^ k) = 1 / (1 - z) ^ 2 :=
        hderiv_tsum.unique hderiv_tsum2
      have hsum : Summable fun k : ℕ => ((k + 1 : ℝ) ^ 1) * z ^ k := by
        refine Summable.of_norm_bounded (summable_nat_pow_mul_pow 1 (abs_nonneg z) hz) fun k => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_pow]
      have hA1 : (eulerianPoly 1).eval z = 1 := by simp [eulerianPoly, eulerian]
      rw [hA1, ← htsum_eq]
      exact hsum.hasSum
    | succ m =>
      intro _ z hz
      set n := m + 1
      have hn : 1 ≤ n := by omega
      set r : ℝ := (|z| + 1) / 2 with hr_def
      have hr0 : 0 ≤ r := by linarith [abs_nonneg z]
      have hr1 : r < 1 := by linarith
      have hr_pos : 0 < r := by linarith [abs_nonneg z]
      have hz_in : z ∈ Set.Ioo (-r) r := by
        rw [Set.mem_Ioo]; exact abs_lt.mp (by linarith)
      have hderiv_tsum : HasDerivAt (fun x : ℝ => ∑' k : ℕ, ((k + 1 : ℝ) ^ n) * x ^ (k + 1))
          (∑' k : ℕ, ((k + 1 : ℝ) ^ (n + 1)) * z ^ k) z :=
        hasDerivAt_tsum_of_isPreconnected
          (g := fun k (x : ℝ) => ((k + 1 : ℝ) ^ n) * x ^ (k + 1))
          (g' := fun k (x : ℝ) => ((k + 1 : ℝ) ^ (n + 1)) * x ^ k)
          (u := fun k : ℕ => ((k + 1 : ℝ) ^ (n + 1)) * r ^ k)
          (t := Set.Ioo (-r) r)
          (summable_nat_pow_mul_pow (n + 1) hr0 hr1) isOpen_Ioo isPreconnected_Ioo
          (fun k x _ => by
            have hd := (hasDerivAt_pow (k + 1) x).const_mul ((k + 1 : ℝ) ^ n)
            exact hd.congr_deriv (by rw [pow_succ]; push_cast; ring))
          (fun k x hx => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_pow]
            gcongr; exact abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
          (y₀ := 0) (by rw [Set.mem_Ioo]; constructor <;> linarith)
          (by
            have : (fun k : ℕ => ((k + 1 : ℝ) ^ n) * (0 : ℝ) ^ (k + 1)) = 0 := by funext k; simp
            rw [this]; exact summable_zero) hz_in
      have hEqOn : ∀ x ∈ Set.Ioo (-r) r,
          (∑' k : ℕ, ((k + 1 : ℝ) ^ n) * x ^ (k + 1)) =
            x * (eulerianPoly n).eval x / (1 - x) ^ (n + 1) := by
        intro x hx
        have hx1 : |x| < 1 := lt_trans (abs_lt.mpr ⟨hx.1, hx.2⟩) hr1
        have hprev := (ih hn hx1).mul_left x
        have hrewrite : (fun k : ℕ => x * (((k + 1 : ℝ) ^ n) * x ^ k)) =
            (fun k : ℕ => ((k + 1 : ℝ) ^ n) * x ^ (k + 1)) := by
          funext k; rw [pow_succ']; ring
        rw [hrewrite] at hprev
        simpa [mul_div_assoc] using hprev.tsum_eq
      have hderiv_rat : HasDerivAt
          (fun x : ℝ => x * (eulerianPoly n).eval x / (1 - x) ^ (n + 1))
          ((eulerianPoly (n + 1)).eval z / (1 - z) ^ (n + 2)) z := by
        have h1z : 1 - z ≠ 0 := by linarith [(abs_lt.mp hz).2]
        have hd_num : HasDerivAt (fun x : ℝ => x * (eulerianPoly n).eval x)
            (1 * (eulerianPoly n).eval z + z * (derivative (eulerianPoly n)).eval z) z :=
          (hasDerivAt_id z).fun_mul (Polynomial.hasDerivAt (eulerianPoly n) z)
        have hd_den : HasDerivAt (fun x : ℝ => (1 - x) ^ (n + 1))
            (-((n + 1 : ℝ) * (1 - z) ^ n)) z := by
          have hd1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
            simpa using (hasDerivAt_const z (1 : ℝ)).fun_sub (hasDerivAt_id z)
          have hd2 := hd1.pow (n + 1)
          exact hd2.congr_deriv (by push_cast; ring)
        have hd_quo := hd_num.fun_div hd_den (pow_ne_zero (n + 1) h1z)
        refine hd_quo.congr_deriv ?_
        rw [eulerianPoly_succ hn]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_sub,
          Polynomial.eval_C, Polynomial.eval_X]
        field_simp [h1z]
        ring
      have hderiv_tsum2 : HasDerivAt (fun x : ℝ => ∑' k : ℕ, ((k + 1 : ℝ) ^ n) * x ^ (k + 1))
          ((eulerianPoly (n + 1)).eval z / (1 - z) ^ (n + 2)) z :=
        hderiv_rat.congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hz_in) hEqOn)
      have htsum_eq : (∑' k : ℕ, ((k + 1 : ℝ) ^ (n + 1)) * z ^ k) =
          (eulerianPoly (n + 1)).eval z / (1 - z) ^ (n + 2) :=
        hderiv_tsum.unique hderiv_tsum2
      have hsum : Summable fun k : ℕ => ((k + 1 : ℝ) ^ (n + 1)) * z ^ k := by
        refine Summable.of_norm_bounded (summable_nat_pow_mul_pow (n + 1) (abs_nonneg z) hz) fun k => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_pow]
      rw [← htsum_eq]
      exact hsum.hasSum

/-- Finite alternating sum lower bound for non-decreasing nonnegative sequence:
`(-1)^m ∑_{k < m} (-1)^k T k ≥ -T (m - 1)` for `m ≥ 1`. -/
private lemma alternating_left_bound {T : ℕ → ℝ} :
    ∀ {m : ℕ}, 1 ≤ m → (∀ k < m, 0 ≤ T k) → (∀ k, k + 1 < m → T k ≤ T (k + 1)) →
      -T (m - 1) ≤ (-1 : ℝ) ^ m * ∑ k ∈ range m, (-1 : ℝ) ^ k * T k := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hnonneg hinc
    match m with
    | 0 => omega
    | 1 =>
      simp
    | 2 =>
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, one_mul, pow_one, neg_one_mul]
      have : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [this, one_mul]
      linarith [hnonneg 0 (by omega)]
    | m + 3 =>
      -- Peel off the top two terms `m + 1` and `m + 2`!
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hprev := ih (m + 1) (by omega) (by omega) (fun k hk => hnonneg k (by omega))
        (fun k hk => hinc k (by omega))
      have hpow1 : (-1 : ℝ) ^ (m + 3) = (-1 : ℝ) ^ (m + 1) := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]; norm_num
      have hpow2 : (-1 : ℝ) ^ (m + 3) * (-1 : ℝ) ^ (m + 1) = 1 := by
        rw [← pow_add, show m + 3 + (m + 1) = 2 * (m + 2) by omega, pow_mul]; norm_num
      have hpow3 : (-1 : ℝ) ^ (m + 3) * (-1 : ℝ) ^ (m + 2) = -1 := by
        rw [← pow_add, show m + 3 + (m + 2) = 2 * (m + 2) + 1 by omega, pow_succ, pow_mul]; norm_num
      have hstep : T m ≤ T (m + 1) := hinc m (by omega)
      have hcalc : (-1 : ℝ) ^ (m + 3) *
          ((∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * T k) + (-1 : ℝ) ^ (m + 1) * T (m + 1) +
            (-1 : ℝ) ^ (m + 2) * T (m + 2)) =
          (-1 : ℝ) ^ (m + 1) * (∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * T k) + T (m + 1) - T (m + 2) := by
        rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, hpow2, hpow3, hpow1]
        ring
      rw [hcalc]
      rw [show m + 3 - 1 = m + 2 by omega]
      rw [show m + 1 - 1 = m by omega] at hprev
      linarith

/-- Infinite alternating tail lower bound for a non-increasing summable nonnegative sequence:
`∑' j, (-1)^j * U j ≥ 0` and `-U 0 ≤ ∑' j, (-1)^(j + 1) * U j`. -/
private lemma alternating_tail_nonneg {U : ℕ → ℝ} (hsum : Summable fun j => (-1 : ℝ) ^ j * U j)
    (_hnonneg : ∀ j, 0 ≤ U j) (hdec : ∀ j, U (j + 1) ≤ U j) :
    0 ≤ ∑' j : ℕ, (-1 : ℝ) ^ j * U j := by
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ range (2 * N), (-1 : ℝ) ^ j * U j)
      atTop (nhds (∑' j : ℕ, (-1 : ℝ) ^ j * U j)) :=
    (hsum.hasSum.tendsto_sum_nat).comp h2N
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun N => ?_)
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : (-1 : ℝ) ^ (2 * N) = 1 := by rw [pow_mul]; norm_num
    have h2 : (-1 : ℝ) ^ (2 * N + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [h1, h2]
    linarith [hdec (2 * N)]

/-- Unimodal alternating series bound: if `T` is nonnegative, summable, increases up to `m`,
and decreases from `m` onwards, then `(-1)^m ∑' k, (-1)^k T k ≥ T m - T (m - 1) - T (m + 1)`. -/
private lemma alternating_unimodal_bound {T : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hsum : Summable fun k => (-1 : ℝ) ^ k * T k)
    (hnonneg : ∀ k, 0 ≤ T k)
    (hinc : ∀ k, k + 1 ≤ m → T k ≤ T (k + 1))
    (hdec : ∀ k, m ≤ k → T (k + 1) ≤ T k) :
    T m - T (m - 1) - T (m + 1) ≤ (-1 : ℝ) ^ m * ∑' k : ℕ, (-1 : ℝ) ^ k * T k := by
  have hsplit := hsum.sum_add_tsum_nat_add (m + 2)
  rw [← hsplit, Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add, mul_add]
  have hleft := alternating_left_bound hm (fun k _ => hnonneg k) (fun k hk => hinc k (by omega))
  have htail_sum : Summable fun j : ℕ => (-1 : ℝ) ^ j * T (j + (m + 2)) := by
    have hshift := (summable_nat_add_iff (m + 2)).mpr hsum
    have hmul := hshift.mul_left ((-1 : ℝ) ^ (m + 2))
    refine hmul.congr fun j => ?_
    rw [← mul_assoc, ← pow_add, show m + 2 + (j + (m + 2)) = 2 * (m + 2) + j by omega,
      pow_add, pow_mul]; norm_num
  have htail_nn := alternating_tail_nonneg htail_sum (fun j => hnonneg _)
    (fun j => by simpa [show j + 1 + (m + 2) = j + (m + 2) + 1 by omega] using hdec (j + (m + 2)) (by omega))
  have htail_eq : (-1 : ℝ) ^ m * ∑' j : ℕ, (-1 : ℝ) ^ (j + (m + 2)) * T (j + (m + 2)) =
      ∑' j : ℕ, (-1 : ℝ) ^ j * T (j + (m + 2)) := by
    rw [← tsum_mul_left]
    congr 1; funext j
    rw [← mul_assoc, ← pow_add, show m + (j + (m + 2)) = 2 * (m + 1) + j by omega,
      pow_add, pow_mul]; norm_num
  have hpow_m : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hpow_m1 : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (m + 1) = -1 := by
    rw [← pow_add, show m + (m + 1) = 2 * m + 1 by omega, pow_succ, pow_mul]; norm_num
  rw [htail_eq, ← mul_assoc, hpow_m, one_mul, ← mul_assoc, hpow_m1, neg_one_mul]
  linarith

/-- Test point `ε_m = (m / (m + 2)) ^ (n / 2)` for Regime A. -/
noncomputable def sigmaA (n m : ℕ) : ℝ :=
  ((m : ℝ) / ((m : ℝ) + 2)) ^ ((n : ℝ) / 2)

private lemma sigmaA_pos {n m : ℕ} (hm : 1 ≤ m) : 0 < sigmaA n m := by
  unfold sigmaA
  exact Real.rpow_pos_of_pos (div_pos (by positivity) (by positivity)) _

private lemma sigmaA_lt_one {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : sigmaA n m < 1 := by
  unfold sigmaA
  have hbase_pos : 0 < (m : ℝ) / ((m : ℝ) + 2) := div_pos (by positivity) (by positivity)
  have hbase_lt : (m : ℝ) / ((m : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  exact Real.rpow_lt_one hbase_pos.le hbase_lt (by positivity)

private lemma sigmaA_strictMono {n : ℕ} (hn : 1 ≤ n) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hlt : m₁ < m₂) :
    sigmaA n m₁ < sigmaA n m₂ := by
  unfold sigmaA
  refine Real.rpow_lt_rpow (by positivity) ?_ (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : (m₁ : ℝ) < (m₂ : ℝ) := Nat.cast_lt.mpr hlt
  nlinarith

/-- **Regime A bound:** For every `n ≥ 16` and `m ≥ 1` with `4 * (m + 1)^2 ≤ n`,
`(-1)^m * (1 + sigmaA n m) * A_n(-sigmaA n m) > 1`. -/
private lemma regimeA_bound {n m : ℕ} (hn : 16 ≤ n) (hm : 1 ≤ m) (hreg : 4 * (m + 1) ^ 2 ≤ n) :
    (-1 : ℝ) ^ m * ((1 + sigmaA n m) * (eulerianPoly n).eval (-sigmaA n m)) > 1 := by
  set σ := sigmaA n m with hσ_def
  have hσ_pos : 0 < σ := sigmaA_pos hm
  have hσ_lt : σ < 1 := sigmaA_lt_one (by omega) hm
  have habs : |-σ| < 1 := by rw [abs_neg, abs_of_pos hσ_pos]; exact hσ_lt
  have hseries := hasSum_eulerian_series (by omega : 1 ≤ n) habs
  have hA_eq : (eulerianPoly n).eval (-σ) =
      (1 + σ) ^ (n + 1) * ∑' k : ℕ, (-1 : ℝ) ^ k * (((k + 1 : ℝ) ^ n) * σ ^ k) := by
    have hts := hseries.tsum_eq
    have h1p : 1 - -σ = 1 + σ := by ring
    rw [h1p] at hts
    have hne : (1 + σ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by linarith)
    have hmul : (eulerianPoly n).eval (-σ) = (1 + σ) ^ (n + 1) * ∑' k : ℕ, ((k + 1 : ℝ) ^ n) * (-σ) ^ k := by
      rw [hts]; field_simp [hne]
    rw [hmul]
    congr 1; congr 1; funext k
    rw [neg_eq_neg_one_mul, mul_pow]; ring
  let T : ℕ → ℝ := fun k => ((k + 1 : ℝ) ^ n) * σ ^ k
  have hT_nonneg : ∀ k, 0 ≤ T k := fun k => by dsimp [T]; positivity
  have hT_sum : Summable fun k => (-1 : ℝ) ^ k * T k := by
    refine Summable.of_norm_bounded (summable_nat_pow_mul_pow n hσ_pos.le hσ_lt) fun k => ?_
    dsimp [T]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ ((k + 1 : ℝ) ^ n) * σ ^ k), le_rfl]
  -- Compute `σ^2 = (m / (m + 2))^n`!
  have hσ_sq : σ ^ 2 = ((m : ℝ) / ((m : ℝ) + 2)) ^ n := by
    rw [hσ_def, sigmaA, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show (n : ℝ) / 2 * (2 : ℕ) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  -- Key ratio `ρ = (1 - 1 / (m + 1)^2) ^ (n / 2)`:
  set ρ : ℝ := (1 - 1 / ((m : ℝ) + 1) ^ 2) ^ ((n : ℝ) / 2)
  have hρ_base_pos : 0 < 1 - 1 / ((m : ℝ) + 1) ^ 2 := by
    have hm1 : (2 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (show 2 ≤ m + 1 by omega)
    have : 1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hρ_base_pos _
  have hρ_sq : ρ ^ 2 = (1 - 1 / ((m : ℝ) + 1) ^ 2) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ_base_pos.le]
    rw [show (n : ℝ) / 2 * (2 : ℕ) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hTm_pos : 0 < T m := by dsimp [T]; positivity
  -- Exact identities: `T (m + 1) = ρ * T m` and `T (m - 1) = ρ * T m`!
  have hT_succ_m : T (m + 1) = ρ * T m := by
    have hsq : (T (m + 1)) ^ 2 = (ρ * T m) ^ 2 := by
      dsimp [T]
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
      have hbase : (((m : ℝ) + 1 + 1) ^ 2 * ((m : ℝ) / ((m : ℝ) + 2))) =
          ((1 - 1 / ((m : ℝ) + 1) ^ 2) * ((m : ℝ) + 1) ^ 2) := by
        field_simp [hm1, hm2]; ring
      calc
        (((↑(m + 1) + 1 : ℝ) ^ n) * σ ^ (m + 1)) ^ 2
            = ((((m : ℝ) + 1 + 1) ^ 2) ^ n) * (σ ^ 2) * (σ ^ m) ^ 2 := by
              rw [mul_pow, pow_succ σ m, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]; push_cast; ring
        _ = ((((m : ℝ) + 1 + 1) ^ 2 * ((m : ℝ) / ((m : ℝ) + 2))) ^ n) * (σ ^ m) ^ 2 := by
            rw [hσ_sq, mul_pow]
        _ = (((1 - 1 / ((m : ℝ) + 1) ^ 2) * ((m : ℝ) + 1) ^ 2) ^ n) * (σ ^ m) ^ 2 := by rw [hbase]
        _ = (ρ ^ 2) * (((m : ℝ) + 1) ^ n) ^ 2 * (σ ^ m) ^ 2 := by
            rw [hρ_sq, mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]
        _ = (ρ * (((m : ℝ) + 1) ^ n * σ ^ m)) ^ 2 := by ring
    exact (sq_eq_sq₀ (hT_nonneg (m + 1)) (by positivity)).mp hsq
  have hT_pred_m : T (m - 1) = ρ * T m := by
    have hsq : (T (m - 1)) ^ 2 = (ρ * T m) ^ 2 := by
      dsimp [T]
      have hm_cast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by rw [Nat.cast_sub hm]; simp
      have hpow_m : σ ^ m = σ ^ (m - 1) * σ := by
        rw [← pow_succ, show m - 1 + 1 = m by omega]
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
      have hbase : ((m : ℝ) ^ 2) =
          ((1 - 1 / ((m : ℝ) + 1) ^ 2) * ((m : ℝ) + 1) ^ 2) * ((m : ℝ) / ((m : ℝ) + 2)) := by
        field_simp [hm1, hm2]; ring
      calc
        ((((m - 1 : ℕ) : ℝ) + 1) ^ n * σ ^ (m - 1)) ^ 2
            = (((m : ℝ) ^ 2) ^ n) * (σ ^ (m - 1)) ^ 2 := by rw [hm_cast, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
        _ = ((((1 - 1 / ((m : ℝ) + 1) ^ 2) * ((m : ℝ) + 1) ^ 2) *
              ((m : ℝ) / ((m : ℝ) + 2))) ^ n) * (σ ^ (m - 1)) ^ 2 := by rw [hbase]
        _ = (ρ ^ 2) * (((m : ℝ) + 1) ^ n) ^ 2 *
              ((σ ^ (m - 1)) ^ 2 * (σ ^ 2)) := by
            rw [hρ_sq, hσ_sq, mul_pow, mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]; ring
        _ = (ρ * (((m : ℝ) + 1) ^ n * σ ^ m)) ^ 2 := by rw [hpow_m]; ring
    exact (sq_eq_sq₀ (hT_nonneg (m - 1)) (by positivity)).mp hsq
  -- Bound `ρ ≤ exp(-2)`!
  have hρ_le : ρ ≤ Real.exp (-2) := by
    have h1 : 1 - 1 / ((m : ℝ) + 1) ^ 2 ≤ Real.exp (-(1 / ((m : ℝ) + 1) ^ 2)) := by
      have := Real.add_one_le_exp (-(1 / ((m : ℝ) + 1) ^ 2))
      linarith
    have h2 : ρ ≤ Real.exp (-(1 / ((m : ℝ) + 1) ^ 2)) ^ ((n : ℝ) / 2) :=
      Real.rpow_le_rpow hρ_base_pos.le h1 (by positivity)
    rw [← Real.exp_mul] at h2
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    have hregR : (4 : ℝ) * ((m : ℝ) + 1) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hreg
    have hpos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
    rw [neg_mul, neg_le_neg_iff, one_div, inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  have hρ_lt1 : ρ < 1 := lt_of_le_of_lt hρ_le (by rw [Real.exp_lt_one_iff]; norm_num)
  -- Unimodality of `T`: increasing for `k + 1 ≤ m`, decreasing for `k ≥ m`!
  have hinc : ∀ k, k + 1 ≤ m → T k ≤ T (k + 1) := by
    intro k hk
    have hle2 : (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ ((m : ℝ) / ((m : ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hkm : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hk
      nlinarith only [hkm]
    have h1 : (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ n ≤ ((m : ℝ) / ((m : ℝ) + 1)) ^ n :=
      pow_le_pow_left₀ (by positivity) hle2 n
    have h2 : ((m : ℝ) / ((m : ℝ) + 1)) ^ n = ρ * σ := by
      have hrel := hT_pred_m
      dsimp [T] at hrel
      have hm_cast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by rw [Nat.cast_sub hm]; simp
      have hpow_m : σ ^ m = σ ^ (m - 1) * σ := by rw [← pow_succ, show m - 1 + 1 = m by omega]
      rw [hm_cast, hpow_m] at hrel
      have hne1 : σ ^ (m - 1) ≠ 0 := pow_ne_zero _ hσ_pos.ne'
      have hne2 : ((m : ℝ) + 1) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
      have hcancel : (m : ℝ) ^ n = ρ * σ * ((m : ℝ) + 1) ^ n := by
        apply mul_right_cancel₀ hne1
        calc
          (m : ℝ) ^ n * σ ^ (m - 1) = ρ * (((m : ℝ) + 1) ^ n * (σ ^ (m - 1) * σ)) := hrel
          _ = ρ * σ * ((m : ℝ) + 1) ^ n * σ ^ (m - 1) := by ring
      rw [div_pow, div_eq_iff hne2]
      exact hcancel
    have h3 : ρ * σ ≤ σ := mul_le_of_le_one_left hσ_pos.le hρ_lt1.le
    have hrat_le : (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ n ≤ σ := (h1.trans_eq h2).trans h3
    dsimp [T]
    rw [div_pow, div_le_iff₀ (by positivity)] at hrat_le
    have hpush : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [hpush, pow_succ]
    calc
      ((k : ℝ) + 1) ^ n * σ ^ k ≤ (σ * ((k : ℝ) + 2) ^ n) * σ ^ k :=
        mul_le_mul_of_nonneg_right hrat_le (pow_nonneg hσ_pos.le k)
      _ = ((k : ℝ) + 2) ^ n * (σ ^ k * σ) := by ring
  have hdec : ∀ k, m ≤ k → T (k + 1) ≤ T k := by
    intro k hk
    have hle : (((k : ℝ) + 2) / ((k : ℝ) + 1)) ≤ (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith only [hmk]
    have h1 : (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ n ≤ (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ n :=
      pow_le_pow_left₀ (by positivity) hle n
    have h2 : (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ n * σ = ρ := by
      have hrel := hT_succ_m
      dsimp [T] at hrel
      have hpush : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
      rw [hpush, pow_succ] at hrel
      have hne1 : σ ^ m ≠ 0 := pow_ne_zero _ hσ_pos.ne'
      have hne2 : ((m : ℝ) + 1) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
      have hcancel : ((m : ℝ) + 2) ^ n * σ = ρ * ((m : ℝ) + 1) ^ n := by
        apply mul_right_cancel₀ hne1
        calc
          ((m : ℝ) + 2) ^ n * σ * σ ^ m = ((m : ℝ) + 2) ^ n * (σ ^ m * σ) := by ring
          _ = ρ * (((m : ℝ) + 1) ^ n * σ ^ m) := hrel
          _ = ρ * ((m : ℝ) + 1) ^ n * σ ^ m := by ring
      rw [div_pow, div_mul_eq_mul_div, div_eq_iff hne2]
      exact hcancel
    have hrat_le : (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ n * σ ≤ 1 := by
      calc
        (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ n * σ ≤ (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ n * σ :=
          mul_le_mul_of_nonneg_right h1 hσ_pos.le
        _ = ρ := h2
        _ ≤ 1 := hρ_lt1.le
    dsimp [T]
    have hpush : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [hpush, pow_succ]
    rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)] at hrat_le
    calc
      ((k : ℝ) + 2) ^ n * (σ ^ k * σ) = (((k : ℝ) + 2) ^ n * σ) * σ ^ k := by ring
      _ ≤ ((k : ℝ) + 1) ^ n * σ ^ k := mul_le_mul_of_nonneg_right hrat_le (pow_nonneg hσ_pos.le k)
  have hbound := alternating_unimodal_bound hm hT_sum hT_nonneg hinc hdec
  rw [hT_pred_m, hT_succ_m] at hbound
  -- Lower bound `T m ≥ (1.21)^(n/2) ≥ (1.21)^8`!
  have hTm_ge : (1.21 : ℝ) ^ 8 ≤ T m := by
    -- Express `T m = c_m ^ (n / 2)` where `c_m = (m + 1)^2 * (m / (m + 2))^m ≥ 1.21`!
    set c : ℝ := ((m : ℝ) + 1) ^ 2 * ((m : ℝ) / ((m : ℝ) + 2)) ^ m
    have hc_pos : 0 < c := by positivity
    have hTm_eq : T m = c ^ ((n : ℝ) / 2) := by
      have hsq : (T m) ^ 2 = (c ^ ((n : ℝ) / 2)) ^ 2 := by
        conv_rhs =>
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc_pos.le,
            show (n : ℝ) / 2 * (2 : ℕ) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
        dsimp [T, c]
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2, pow_mul σ 2 m, hσ_sq, ← pow_mul, ← pow_mul,
          ← pow_mul, mul_comm n 2, mul_comm n m]
      exact (sq_eq_sq₀ hTm_pos.le (Real.rpow_pos_of_pos hc_pos _).le).mp hsq
    have hc_ge : (1.21 : ℝ) ≤ c := by
      by_cases hm1 : m = 1
      · subst hm1; dsimp [c]; norm_num
      · have hm2 : 2 ≤ m := by omega
        -- `((m + 2) / m)^m = (1 + 2/m)^m ≤ exp(2)`, so `(m / (m + 2))^m ≥ exp(-2)`!
        have hexp2 : (((m : ℝ) + 2) / (m : ℝ)) ^ m ≤ Real.exp 2 := by
          have h1 : ((m : ℝ) + 2) / (m : ℝ) ≤ Real.exp (2 / (m : ℝ)) := by
            have := Real.add_one_le_exp (2 / (m : ℝ))
            have hne : (m : ℝ) ≠ 0 := by positivity
            have : 2 / (m : ℝ) + 1 = ((m : ℝ) + 2) / (m : ℝ) := by field_simp [hne]; ring
            linarith
          have h2 := pow_le_pow_left₀ (by positivity) h1 m
          rw [← Real.exp_nat_mul] at h2
          have hne : (m : ℝ) ≠ 0 := by positivity
          have : (m : ℝ) * (2 / (m : ℝ)) = 2 := by field_simp [hne]
          rwa [this] at h2
        have hinv : Real.exp (-2) ≤ ((m : ℝ) / ((m : ℝ) + 2)) ^ m := by
          rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos 2)]
          have hprod : ((m : ℝ) / ((m : ℝ) + 2)) ^ m * (((m : ℝ) + 2) / (m : ℝ)) ^ m = 1 := by
            rw [← mul_pow]
            have : (m : ℝ) / ((m : ℝ) + 2) * (((m : ℝ) + 2) / (m : ℝ)) = 1 := by
              field_simp [show (m : ℝ) ≠ 0 by positivity, show (m : ℝ) + 2 ≠ 0 by positivity]
            rw [this, one_pow]
          have hmul := mul_le_mul_of_nonneg_left hexp2 (pow_nonneg (by positivity) m : 0 ≤ ((m : ℝ) / ((m : ℝ) + 2)) ^ m)
          linarith
        have hm1_ge : (9 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
          have : (3 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (show 3 ≤ m + 1 by omega)
          nlinarith
        have he_lt : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have he2_lt : Real.exp 2 < 7.4 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith [Real.exp_pos 1]
        have hexp_neg2 : (1 / 7.4 : ℝ) < Real.exp (-2) := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_lt_one_div_of_lt (Real.exp_pos 2) he2_lt
        have hc_ge1 : 9 * Real.exp (-2) ≤ c := by
          dsimp [c]; nlinarith [Real.exp_pos (-2)]
        linarith
    rw [hTm_eq]
    calc
      (1.21 : ℝ) ^ 8 = (1.21 : ℝ) ^ ((8 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (1.21 : ℝ) ^ ((n : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by have h16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
                push_cast; linarith)
      _ ≤ c ^ ((n : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hc_ge (by positivity)
  -- Finally, `1 - 2ρ ≥ 1 - 2 e^{-2} > 1 - 2 / 7 = 5 / 7`, and `(1.21)^8 * (5 / 7) > 3 > 1`!
  have he_gt : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he2_gt : (7 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
  have hρ_num : ρ < 1 / 7 := by
    refine lt_of_le_of_lt hρ_le ?_
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) he2_gt
  have h1p_gt : (1 : ℝ) < (1 + σ) ^ (n + 2) := one_lt_pow₀ (by linarith only [hσ_pos]) (by omega)
  have hsum_gt : (1 : ℝ) < (-1 : ℝ) ^ m * ∑' k : ℕ, (-1 : ℝ) ^ k * T k := by
    have h121 : (4 : ℝ) < (1.21 : ℝ) ^ 8 := by norm_num
    have htm4 : (4 : ℝ) < T m := lt_of_lt_of_le h121 hTm_ge
    have hfactor : (5 / 7 : ℝ) < 1 - 2 * ρ := by linarith only [hρ_num]
    have hprod : (4 : ℝ) * (5 / 7 : ℝ) < T m * (1 - 2 * ρ) :=
      mul_lt_mul'' htm4 hfactor (by norm_num) (by norm_num)
    linarith only [hbound, hprod]
  have hfinal : (-1 : ℝ) ^ m * ((1 + σ) * (eulerianPoly n).eval (-σ)) =
      (1 + σ) ^ (n + 2) * ((-1 : ℝ) ^ m * ∑' k : ℕ, (-1 : ℝ) ^ k * T k) := by
    rw [hA_eq]; dsimp [T]; ring
  rw [hfinal]
  nlinarith only [h1p_gt, hsum_gt]

/-! ### Section 4: Polylogarithm Pole Expansion & Regime B (`n ≥ 64`) -/

/-- Complex Eulerian polynomial `A_n(q) ∈ ℂ[X]`. -/
noncomputable def eulerianPolyC (n : ℕ) : Polynomial ℂ :=
  (eulerianPoly n).map (algebraMap ℝ ℂ)

private lemma eulerianPolyC_eval_ofReal (n : ℕ) (x : ℝ) :
    (eulerianPolyC n).eval (x : ℂ) = Complex.ofReal ((eulerianPoly n).eval x) := by
  unfold eulerianPolyC eulerianPoly
  simp [Polynomial.eval_finsetSum]

private lemma eulerianPolyC_succ {n : ℕ} (hn : 1 ≤ n) :
    eulerianPolyC (n + 1) =
      (1 + C (n : ℂ) * X) * eulerianPolyC n + X * (1 - X) * derivative (eulerianPolyC n) := by
  unfold eulerianPolyC
  have h := congrArg (Polynomial.map (algebraMap ℝ ℂ)) (eulerianPoly_succ hn)
  simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_C, Polynomial.derivative_map] using h

/-- Complex negative-index polylogarithm `Li_{-n}(q) = q * A_n(q) / (1 - q)^(n + 1)`. -/
noncomputable def liNeg (n : ℕ) (q : ℂ) : ℂ :=
  q * (eulerianPolyC n).eval q / (1 - q) ^ (n + 1)

private lemma exp_two_pi_I_ne_one {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    Complex.exp (2 * π * I * z) ≠ 1 := by
  intro heq
  have hnorm := congrArg (fun w : ℂ => ‖w‖) heq
  rw [Complex.norm_exp, norm_one] at hnorm
  have hre : (2 * π * I * z).re = -2 * π * z.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hre] at hnorm
  have hlt : -2 * π * z.im < 0 := by
    have hz_im : 0 < z.im := hz
    have hpi : 0 < π := Real.pi_pos
    nlinarith only [hz_im, hpi]
  linarith [Real.exp_lt_one_iff.mpr hlt]

private lemma pi_mul_cot_pi_eq_exp {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (π : ℂ) * Complex.cot ((π : ℂ) * z) =
      -(π : ℂ) * I - 2 * (π : ℂ) * I *
        (Complex.exp (2 * π * I * z) / (1 - Complex.exp (2 * π * I * z))) := by
  set w : ℂ := (π : ℂ) * z
  set e : ℂ := Complex.exp (w * I)
  have he_ne : e ≠ 0 := Complex.exp_ne_zero _
  have hq : Complex.exp (2 * π * I * z) = e ^ 2 := by
    dsimp [e, w]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h1mq : 1 - e ^ 2 ≠ 0 := by rw [← hq]; exact sub_ne_zero.mpr (exp_two_pi_I_ne_one hz).symm
  have hsin : Complex.sin w = (e⁻¹ - e) * I / 2 := by
    rw [Complex.sin, neg_mul, Complex.exp_neg]
  have hcos : Complex.cos w = (e + e⁻¹) / 2 := by
    rw [Complex.cos, neg_mul, Complex.exp_neg]
  rw [Complex.cot, hcos, hsin, hq]
  have hI : I ≠ 0 := Complex.I_ne_zero
  have he2 : e⁻¹ - e ≠ 0 := by
    intro h0
    have : e ^ 2 = 1 := by
      have := congrArg (fun u => u * e) h0
      rw [sub_mul, inv_mul_cancel₀ he_ne, zero_mul, sub_eq_zero] at this
      rw [sq]; exact this.symm
    exact h1mq (by rw [this, sub_self])
  field_simp [he_ne, h1mq, hI, he2]
  rw [Complex.I_sq]; ring

private lemma hasDerivAt_liNeg_exp {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    HasDerivAt (fun x : ℂ => liNeg n (Complex.exp (2 * π * I * x)))
      ((2 * π * I) * liNeg (n + 1) (Complex.exp (2 * π * I * z))) z := by
  set c : ℂ := 2 * π * I
  set q : ℂ := Complex.exp (c * z)
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (exp_two_pi_I_ne_one hz).symm
  have hd_q : HasDerivAt (fun x : ℂ => Complex.exp (c * x)) (c * q) z := by
    have := ((hasDerivAt_id z).const_mul c).cexp
    simpa [c, q, mul_comm] using this
  have hd_li : HasDerivAt (liNeg n) ((eulerianPolyC (n + 1)).eval q / (1 - q) ^ (n + 2)) q := by
    unfold liNeg
    have hd_num : HasDerivAt (fun u : ℂ => u * (eulerianPolyC n).eval u)
        (1 * (eulerianPolyC n).eval q + q * (derivative (eulerianPolyC n)).eval q) q :=
      (hasDerivAt_id q).fun_mul (Polynomial.hasDerivAt (eulerianPolyC n) q)
    have hd_den : HasDerivAt (fun u : ℂ => (1 - u) ^ (n + 1))
        (-((n + 1 : ℂ) * (1 - q) ^ n)) q := by
      have hd1 : HasDerivAt (fun u : ℂ => 1 - u) (-1) q := by
        simpa using (hasDerivAt_const q (1 : ℂ)).fun_sub (hasDerivAt_id q)
      have hd2 := hd1.pow (n + 1)
      exact hd2.congr_deriv (by push_cast; ring)
    have hd_quo := hd_num.fun_div hd_den (pow_ne_zero (n + 1) h1q)
    refine hd_quo.congr_deriv ?_
    rw [eulerianPolyC_succ hn]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X]
    field_simp [h1q]
    ring
  have hcomp := hd_li.comp z hd_q
  exact hcomp.congr_deriv (by unfold liNeg; ring)

/-- Iterated derivative of `π cot (π z)` on the upper half-plane in terms of `liNeg`. -/
private lemma iteratedDerivWithin_cot_eq_liNeg :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {z : ℂ}, z ∈ UpperHalfPlane.upperHalfPlaneSet →
      iteratedDerivWithin n (fun x : ℂ => (π : ℂ) * Complex.cot ((π : ℂ) * x))
          UpperHalfPlane.upperHalfPlaneSet z =
        -((2 * (π : ℂ) * I) ^ (n + 1)) * liNeg n (Complex.exp (2 * π * I * z)) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro _ z hz
      rw [iteratedDerivWithin_one,
        derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz]
      have hEq : (fun x : ℂ => (π : ℂ) * Complex.cot ((π : ℂ) * x)) =ᶠ[nhds z]
          (fun x : ℂ => -(π : ℂ) * I - 2 * (π : ℂ) * I *
            (Complex.exp (2 * π * I * x) / (1 - Complex.exp (2 * π * I * x)))) :=
        Filter.eventually_of_mem (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
          (fun x hx => pi_mul_cot_pi_eq_exp hx)
      rw [hEq.deriv_eq]
      set c : ℂ := 2 * π * I
      set q : ℂ := Complex.exp (c * z)
      have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (exp_two_pi_I_ne_one hz).symm
      have hd_q : HasDerivAt (fun x : ℂ => Complex.exp (c * x)) (c * q) z := by
        simpa [c, q, mul_comm] using ((hasDerivAt_id z).const_mul c).cexp
      have hd_frac : HasDerivAt (fun x : ℂ => Complex.exp (c * x) / (1 - Complex.exp (c * x)))
          (c * q / (1 - q) ^ 2) z := by
        have hd1 : HasDerivAt (fun u : ℂ => u / (1 - u)) (1 / (1 - q) ^ 2) q := by
          have hd := (hasDerivAt_id q).fun_div ((hasDerivAt_const q (1 : ℂ)).fun_sub (hasDerivAt_id q)) h1q
          exact hd.congr_deriv (by dsimp only [id_eq]; ring)
        have hc : HasDerivAt ((fun u : ℂ => u / (1 - u)) ∘ (fun x : ℂ => Complex.exp (c * x)))
            (1 / (1 - q) ^ 2 * (c * q)) z := hd1.comp z hd_q
        exact hc.congr_deriv (by ring)
      have hd_all : HasDerivAt (fun x : ℂ => -(π : ℂ) * I - c * (Complex.exp (c * x) / (1 - Complex.exp (c * x))))
          (-(c * (c * q / (1 - q) ^ 2))) z := by
        simpa using (hasDerivAt_const z (-(π : ℂ) * I)).fun_sub (hd_frac.const_mul c)
      rw [hd_all.deriv]
      have hA1 : (eulerianPolyC 1).eval q = 1 := by simp [eulerianPolyC, eulerianPoly, eulerian]
      unfold liNeg
      rw [hA1, mul_one]
      dsimp [c, q]
      ring
    | succ m =>
      intro _ z hz
      set n := m + 1
      have hn : 1 ≤ n := by omega
      rw [iteratedDerivWithin_succ,
        derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz]
      have hEq : iteratedDerivWithin n (fun x : ℂ => (π : ℂ) * Complex.cot ((π : ℂ) * x))
            UpperHalfPlane.upperHalfPlaneSet =ᶠ[nhds z]
          (fun x : ℂ => -((2 * (π : ℂ) * I) ^ (n + 1)) * liNeg n (Complex.exp (2 * π * I * x))) :=
        Filter.eventually_of_mem (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
          (fun x hx => ih hn hx)
      rw [hEq.deriv_eq]
      have hd := (hasDerivAt_liNeg_exp hn hz).const_mul (-((2 * (π : ℂ) * I) ^ (n + 1)))
      rw [hd.deriv]
      ring

private lemma summable_odd_pole (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (_hL : 0 ≤ L) :
    Summable fun k : ℕ => ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => ((k + 1 : ℝ) ^ (n + 1))⁻¹) ?_ ?_
  · have hs : Summable fun k : ℕ => ((k : ℝ) ^ (n + 1))⁻¹ :=
      Real.summable_nat_pow_inv.mpr (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  · intro k
    rw [norm_div, norm_one, norm_pow, one_div]
    have hnorm_ge : (k + 1 : ℝ) ≤ ‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ := by
      have him : ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))).im = π * (2 * k + 1 : ℕ) := by
        simp [Complex.mul_im]
      have hle : |((L : ℂ) + I * (π * (2 * k + 1 : ℕ))).im| ≤ ‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ :=
        Complex.abs_im_le_norm _
      rw [him, abs_of_nonneg (by positivity)] at hle
      have hpi : (1 : ℝ) ≤ π := le_trans (by norm_num) Real.pi_gt_three.le
      have h2k : (k + 1 : ℝ) ≤ (2 * k + 1 : ℕ) := by push_cast; linarith
      nlinarith
    exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hnorm_ge _)

/-- **Polylogarithm pole expansion for `σ = exp (-L)` (`L ≥ 0`):**
For every `n ≥ 1` and `L ≥ 0`,
`A_n(-e^{-L}) = -((1 + e^{-L})^{n+1} / e^{-L}) * 2 * n! * ∑'_{k=0}^∞ Re(1 / (L + i π (2k + 1))^{n+1})`. -/
private lemma eulerianPoly_pole_expansion {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    (eulerianPoly n).eval (-Real.exp (-L)) =
      -((1 + Real.exp (-L)) ^ (n + 1) / Real.exp (-L)) *
        (2 * (Nat.factorial n : ℝ) *
          ∑' k : ℕ, ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re) := by
  -- First prove the identity for `L > 0` using Mathlib's `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`!
  have hpos_case : ∀ L' : ℝ, 0 < L' →
      liNeg n (-Real.exp (-L') : ℂ) =
        (2 * (Nat.factorial n : ℂ)) *
          ∑' k : ℕ, (((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re : ℂ) := by
    intro L' hL'
    set z : ℂ := (1 / 2 : ℂ) + I * ((L' / (2 * π) : ℝ) : ℂ)
    have hz : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
      show 0 < z.im
      simp only [z, Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add,
        Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul]
      exact div_pos hL' (mul_pos two_pos Real.pi_pos)
    have h1 := iteratedDerivWithin_cot_eq_liNeg hn hz
    have h2 := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hn hz
    have hEq := h1.symm.trans h2
    have hexp_z : Complex.exp (2 * π * I * z) = (-Real.exp (-L') : ℂ) := by
      have harg : 2 * π * I * z = (π : ℂ) * I + (-L' : ℂ) := by
        dsimp [z]
        rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
        have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hI2 : I ^ 2 = -1 := Complex.I_sq
        field_simp [hpi]
        linear_combination (L' : ℂ) * hI2
      rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_exp]
      simp
    rw [hexp_z] at hEq
    set c : ℂ := 2 * (π : ℂ) * I
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have hli : liNeg n (-Real.exp (-L') : ℂ) =
        (Nat.factorial n : ℂ) * ∑' m : ℤ, (1 : ℂ) / (-(c * (z + m))) ^ (n + 1) := by
      have hdiv : -c ^ (n + 1) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero (n + 1) hc_ne)
      have hts : ((-1 : ℂ) ^ n / (-c ^ (n + 1))) * ∑' m : ℤ, 1 / (z + m) ^ (n + 1) =
          ∑' m : ℤ, 1 / (-(c * (z + m))) ^ (n + 1) := by
        rw [← tsum_mul_left]
        congr 1; funext m
        have hsign : (-1 : ℂ) ^ n / (-c ^ (n + 1)) = 1 / (-c) ^ (n + 1) := by
          rw [div_eq_div_iff hdiv (pow_ne_zero (n + 1) (neg_ne_zero.mpr hc_ne)), one_mul,
            neg_pow c (n + 1), pow_succ (-1 : ℂ) n]
          have hsq : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
            rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
          calc (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * (-1 : ℂ) * c ^ (n + 1))
              = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (-c ^ (n + 1)) := by ring
            _ = -c ^ (n + 1) := by rw [hsq, one_mul]
        rw [hsign, div_mul_div_comm, one_mul, ← mul_pow]; congr 2; ring
      have hli1 : liNeg n (-Real.exp (-L') : ℂ) =
          (Nat.factorial n : ℂ) * (((-1 : ℂ) ^ n / (-c ^ (n + 1))) * ∑' m : ℤ, 1 / (z + m) ^ (n + 1)) := by
        have := congrArg (fun w => w / (-c ^ (n + 1))) hEq
        rw [mul_div_cancel_left₀ _ hdiv] at this
        rw [this]; ring
      rw [hli1, hts]
    -- Simplify `-(c * (z + m)) = L' - I * (π * (2 * m + 1))`!
    have hterm : ∀ m : ℤ, -(c * (z + m)) = (L' : ℂ) - I * ((π : ℂ) * (2 * (m : ℂ) + 1)) := by
      intro m
      dsimp [c, z]
      rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hI2 : I ^ 2 = -1 := Complex.I_sq
      field_simp [hpi]
      linear_combination -(L' : ℂ) * hI2
    simp_rw [hterm] at hli
    -- Pair `m = (k : ℤ)` and `m = -(k + 1 : ℤ)`!
    have hsum_pos : Summable fun k : ℕ => (1 : ℂ) / ((L' : ℂ) - I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1) := by
      have hs := Complex.conjCLE.toContinuousLinearMap.summable (summable_odd_pole n hn L' hL'.le)
      refine hs.congr fun k => ?_
      change starRingEnd ℂ ((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)) = _
      simp [map_pow, map_add, map_mul, Complex.conj_ofReal, map_ofNat, sub_eq_add_neg]
    have hsum_neg : Summable fun k : ℕ => (1 : ℂ) / ((L' : ℂ) + I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1) := by
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using summable_odd_pole n hn L' hL'.le
    have htsum_int : (∑' m : ℤ, (1 : ℂ) / ((L' : ℂ) - I * ((π : ℂ) * (2 * (m : ℂ) + 1))) ^ (n + 1)) =
        (∑' k : ℕ, (1 : ℂ) / ((L' : ℂ) - I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1)) +
        (∑' k : ℕ, (1 : ℂ) / ((L' : ℂ) + I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1)) := by
      have hsplit := tsum_of_nat_of_neg_add_one (f := fun m : ℤ =>
        (1 : ℂ) / ((L' : ℂ) - I * ((π : ℂ) * (2 * (m : ℂ) + 1))) ^ (n + 1))
        hsum_pos (by
          refine hsum_neg.congr fun k => ?_
          congr 2; push_cast; ring)
      rw [hsplit]
      congr 1; congr 1; funext k; congr 2; push_cast; ring
    rw [hli, htsum_int, ← hsum_pos.tsum_add hsum_neg]
    have hpair : ∀ k : ℕ,
        (1 : ℂ) / ((L' : ℂ) - I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1) +
        (1 : ℂ) / ((L' : ℂ) + I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1) =
        2 * (((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re : ℂ) := by
      intro k
      set u : ℂ := (1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)
      have hconj : (1 : ℂ) / ((L' : ℂ) - I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1) = starRingEnd ℂ u := by
        dsimp [u]
        simp [map_pow, map_add, map_mul, Complex.conj_ofReal, map_ofNat, sub_eq_add_neg]
      have hu2 : (1 : ℂ) / ((L' : ℂ) + I * ((π : ℂ) * (2 * (k : ℂ) + 1))) ^ (n + 1) = u := by
        dsimp [u]; congr 2; push_cast; ring
      rw [hconj, hu2, add_comm, Complex.add_conj]
      push_cast; ring
    simp_rw [hpair, tsum_mul_left]
    ring
  -- Deduce real-valued identity for `L' > 0`!
  have hreal_pos : ∀ L' : ℝ, 0 < L' →
      (eulerianPoly n).eval (-Real.exp (-L')) =
        -((1 + Real.exp (-L')) ^ (n + 1) / Real.exp (-L')) *
          (2 * (Nat.factorial n : ℝ) *
            ∑' k : ℕ, ((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re) := by
    intro L' hL'
    have hC := hpos_case L' hL'
    have hre := congrArg Complex.re hC
    have hli_re : (liNeg n (-Real.exp (-L') : ℂ)).re =
        (-Real.exp (-L')) * (eulerianPoly n).eval (-Real.exp (-L')) / (1 + Real.exp (-L')) ^ (n + 1) := by
      unfold liNeg
      have hcast : (-Real.exp (-L') : ℂ) = ((-Real.exp (-L') : ℝ) : ℂ) := by simp
      rw [hcast, eulerianPolyC_eval_ofReal]
      have h1 : (1 : ℂ) - ((-Real.exp (-L') : ℝ) : ℂ) = ((1 + Real.exp (-L') : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1]
      norm_cast
    rw [hli_re] at hre
    have hrhs_re : ((2 * (Nat.factorial n : ℂ)) *
        ∑' k : ℕ, (((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re : ℂ)).re =
        2 * (Nat.factorial n : ℝ) * ∑' k : ℕ, ((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re := by
      have hsumR : Summable fun k : ℕ =>
          ((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re :=
        Complex.reCLM.summable (summable_odd_pole n hn L' hL'.le)
      have hcast_tsum : (∑' k : ℕ, (((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re : ℂ)) =
          ((∑' k : ℕ, ((1 : ℂ) / ((L' : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re : ℝ) : ℂ) :=
        Complex.ofRealCLM.map_tsum hsumR |>.symm
      rw [hcast_tsum]; norm_cast
    rw [hrhs_re] at hre
    have hexp_ne : Real.exp (-L') ≠ 0 := (Real.exp_pos _).ne'
    have h1p_ne : (1 + Real.exp (-L')) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by positivity)
    field_simp [hexp_ne, h1p_ne] at hre ⊢
    linarith
  by_cases hL0 : 0 < L
  · exact hreal_pos L hL0
  · have hLeq : L = 0 := le_antisymm (not_lt.mp hL0) hL
    subst hLeq
    -- Extend from `L' > 0` to `L = 0` by continuity of both sides on `[0, ∞)`!
    let lhs : ℝ → ℝ := fun x => (eulerianPoly n).eval (-Real.exp (-x))
    let rhs : ℝ → ℝ := fun x => -((1 + Real.exp (-x)) ^ (n + 1) / Real.exp (-x)) *
      (2 * (Nat.factorial n : ℝ) * ∑' k : ℕ, ((1 : ℂ) / ((x : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re)
    have hcont_lhs : ContinuousAt lhs 0 := by
      dsimp [lhs]; fun_prop
    have hcont_tsum : ContinuousOn
        (fun x : ℝ => ∑' k : ℕ, ((1 : ℂ) / ((x : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re)
        (Set.Ici 0) := by
      refine continuousOn_tsum (u := fun k : ℕ => ((k + 1 : ℝ) ^ (n + 1))⁻¹) ?_ ?_ ?_
      · intro k
        refine ContinuousOn.comp Complex.continuous_re.continuousOn ?_ (Set.mapsTo_univ _ _)
        refine ContinuousOn.div continuousOn_const ?_ ?_
        · exact (Complex.continuous_ofReal.continuousOn.add continuousOn_const).pow (n + 1)
        · intro x _
          refine pow_ne_zero (n + 1) ?_
          intro h0
          have him := congrArg Complex.im h0
          simp [Complex.mul_im] at him
          have : 0 < π * (2 * (k : ℝ) + 1) := by positivity
          linarith
      · have hs : Summable fun k : ℕ => ((k : ℝ) ^ (n + 1))⁻¹ :=
          Real.summable_nat_pow_inv.mpr (by omega)
        simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
      · intro k x _
        rw [Real.norm_eq_abs]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_div, norm_one, norm_pow, one_div]
        have hnorm_ge : (k + 1 : ℝ) ≤ ‖(x : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ := by
          have him : ((x : ℂ) + I * (π * (2 * k + 1 : ℕ))).im = π * (2 * k + 1 : ℕ) := by
            simp [Complex.mul_im]
          have hle := Complex.abs_im_le_norm ((x : ℂ) + I * (π * (2 * k + 1 : ℕ)))
          rw [him, abs_of_nonneg (by positivity)] at hle
          have hpi : (1 : ℝ) ≤ π := le_trans (by norm_num) Real.pi_gt_three.le
          have h2k : (k + 1 : ℝ) ≤ (2 * k + 1 : ℕ) := by push_cast; linarith
          nlinarith
        exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hnorm_ge _)
    have hcont_rhs : ContinuousWithinAt rhs (Set.Ici 0) 0 := by
      dsimp [rhs]
      refine ContinuousWithinAt.mul ?_ ?_
      · exact ((((continuousWithinAt_const.add (Real.continuous_exp.continuousWithinAt.comp
          continuousWithinAt_id.neg (Set.mapsTo_univ _ _))).pow (n + 1)).div
          (Real.continuous_exp.continuousWithinAt.comp continuousWithinAt_id.neg (Set.mapsTo_univ _ _))
          (by simp))).neg
      · exact continuousWithinAt_const.mul (hcont_tsum 0 (Set.mem_Ici.mpr le_rfl))
    have htend1 : Tendsto lhs (nhdsWithin 0 (Set.Ioi 0)) (nhds (lhs 0)) :=
      hcont_lhs.tendsto.mono_left nhdsWithin_le_nhds
    have htend2 : Tendsto rhs (nhdsWithin 0 (Set.Ioi 0)) (nhds (rhs 0)) :=
      hcont_rhs.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    have hEq_ev : lhs =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rhs :=
      Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => hreal_pos x hx)
    have : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
    exact tendsto_nhds_unique htend1 (htend2.congr' hEq_ev.symm)

/-- MVT telescoping bound for `∑_{k ≥ 2} ((2k + 1) / 3)^(-α) ≤ 3 / (2 (α - 1))` when `α > 1`. -/
private lemma odd_rpow_tail_bound {α : ℝ} (hα : 1 < α) :
    Summable (fun k : ℕ => (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-α))) ∧
    ∑' k : ℕ, (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-α)) ≤ 3 / (2 * (α - 1)) := by
  -- For each `k : ℕ`, let `a = 2k + 3`, `b = 2k + 5`. By MVT on `x ↦ x^(1 - α)` on `[a, b]`:
  -- `b^(-α) ≤ (a^(1 - α) - b^(1 - α)) / (2 * (α - 1))`!
  have hstep : ∀ k : ℕ,
      (2 * (k + 2 : ℝ) + 1) ^ (-α) ≤
        ((2 * (k + 1 : ℝ) + 1) ^ (1 - α) - (2 * (k + 2 : ℝ) + 1) ^ (1 - α)) / (2 * (α - 1)) := by
    intro k
    set a : ℝ := 2 * (k + 1 : ℝ) + 1
    set b : ℝ := 2 * (k + 2 : ℝ) + 1
    have ha : 0 < a := by positivity
    have hab : a < b := by dsimp [a, b]; linarith
    have hba : b - a = 2 := by dsimp [a, b]; ring
    have hcont : ContinuousOn (fun x : ℝ => x ^ (1 - α)) (Set.Icc a b) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
    have hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun t : ℝ => t ^ (1 - α)) ((1 - α) * x ^ (-α)) x := by
      intro x hx
      have hx_pos : 0 < x := lt_trans ha hx.1
      simpa [show 1 - α - 1 = -α by ring] using Real.hasDerivAt_rpow_const (Or.inl hx_pos.ne') (p := 1 - α)
    obtain ⟨c, hc, hcmvt⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (1 - α))
      (fun x => (1 - α) * x ^ (-α)) hab hcont hdiff
    have hc_pos : 0 < c := lt_trans ha hc.1
    have hc_le : b ^ (-α) ≤ c ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hc_pos hc.2.le (by linarith)
    have hα1 : 0 < α - 1 := by linarith
    rw [hba] at hcmvt
    have hrew : (a ^ (1 - α) - b ^ (1 - α)) / (2 * (α - 1)) = c ^ (-α) := by
      have hne : α - 1 ≠ 0 := hα1.ne'
      have : b ^ (1 - α) - a ^ (1 - α) = 2 * ((1 - α) * c ^ (-α)) := by
        rw [hcmvt]; ring
      field_simp [hne]; linarith
    rw [hrew]; exact hc_le
  have hpart : ∀ N : ℕ,
      ∑ k ∈ range N, (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-α)) ≤ 3 / (2 * (α - 1)) := by
    intro N
    have h3pos : (0 : ℝ) < 3 := by norm_num
    have hmul : ∀ k : ℕ, (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-α)) =
        3 ^ α * (2 * (k + 2 : ℝ) + 1) ^ (-α) := by
      intro k
      rw [Real.div_rpow (by positivity) h3pos.le, div_eq_mul_inv, ← Real.rpow_neg h3pos.le,
        neg_neg, mul_comm]
    simp_rw [hmul, ← Finset.mul_sum]
    have htele : ∑ k ∈ range N, ((2 * (k + 1 : ℝ) + 1) ^ (1 - α) - (2 * (k + 2 : ℝ) + 1) ^ (1 - α)) =
        (3 : ℝ) ^ (1 - α) - (2 * (N + 1 : ℝ) + 1) ^ (1 - α) := by
      induction N with
      | zero => simp; norm_num
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]; push_cast
        rw [show (2 * ((N : ℝ) + 2) + 1) = 2 * ((N : ℝ) + 1 + 1) + 1 by ring]
        ring
    have hsum_le : ∑ k ∈ range N, (2 * (k + 2 : ℝ) + 1) ^ (-α) ≤
        ∑ k ∈ range N, ((2 * (k + 1 : ℝ) + 1) ^ (1 - α) - (2 * (k + 2 : ℝ) + 1) ^ (1 - α)) / (2 * (α - 1)) :=
      Finset.sum_le_sum fun k _ => hstep k
    rw [← Finset.sum_div, htele] at hsum_le
    have hsub_le : ((3 : ℝ) ^ (1 - α) - (2 * (N + 1 : ℝ) + 1) ^ (1 - α)) / (2 * (α - 1)) ≤
        (3 : ℝ) ^ (1 - α) / (2 * (α - 1)) := by
      gcongr
      linarith [Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * (N + 1 : ℝ) + 1) (1 - α)]
    have hcomb := hsum_le.trans hsub_le
    have h3pow : (3 : ℝ) ^ α * ((3 : ℝ) ^ (1 - α) / (2 * (α - 1))) = 3 / (2 * (α - 1)) := by
      rw [mul_div_assoc', ← Real.rpow_add h3pos, show α + (1 - α) = 1 by ring, Real.rpow_one]
    calc
      3 ^ α * ∑ k ∈ range N, (2 * (k + 2 : ℝ) + 1) ^ (-α)
          ≤ 3 ^ α * ((3 : ℝ) ^ (1 - α) / (2 * (α - 1))) :=
            mul_le_mul_of_nonneg_left hcomb (Real.rpow_pos_of_pos h3pos α).le
      _ = 3 / (2 * (α - 1)) := h3pow
  have hsumm : Summable fun k : ℕ => (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-α)) :=
    summable_of_sum_range_le (fun k => Real.rpow_nonneg (by positivity) _) hpart
  exact ⟨hsumm, hsumm.tsum_le_of_sum_range_le hpart⟩

/-- Helper: `log(1 + v * y^2) ≥ log(1 + v) + 2 * (v / (1 + v)) * log y` for `v > 0` and `y ≥ 1`. -/
private lemma log_one_add_mul_sq_ge {v y : ℝ} (hv : 0 < v) (hy : 1 ≤ y) :
    Real.log (1 + v) + 2 * (v / (1 + v)) * Real.log y ≤ Real.log (1 + v * y ^ 2) := by
  let a : ℝ := v / (1 + v)
  let g : ℝ → ℝ := fun w => Real.log (1 + v * Real.exp w) - a * w
  have hw0 : 0 ≤ 2 * Real.log y := mul_nonneg (by norm_num) (Real.log_nonneg hy)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ (continuousOn_const.mul continuousOn_id)
      refine ContinuousOn.log (continuousOn_const.add (continuousOn_const.mul Real.continuous_exp.continuousOn)) ?_
      intro w _; positivity
    · refine DifferentiableOn.sub ?_ ((differentiableOn_const a).mul differentiableOn_id)
      refine DifferentiableOn.log ((differentiableOn_const (1 : ℝ)).add ((differentiableOn_const v).mul Real.differentiable_exp.differentiableOn)) ?_
      intro w _; positivity
    · intro w hw
      have hw' : 0 ≤ w := le_of_lt (by simpa [interior_Ici] using hw)
      have hd : HasDerivAt g (v * Real.exp w / (1 + v * Real.exp w) - a) w := by
        have h1 : HasDerivAt (fun t => 1 + v * Real.exp t) (v * Real.exp w) w := by
          simpa using (hasDerivAt_const w (1 : ℝ)).fun_add ((Real.hasDerivAt_exp w).const_mul v)
        have h2 : HasDerivAt (fun t => a * t) a w := by
          simpa using (hasDerivAt_id w).const_mul a
        exact (h1.log (by positivity)).fun_sub h2
      rw [hd.deriv]
      dsimp [a]
      have hew : 1 ≤ Real.exp w := Real.one_le_exp hw'
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hle := hmono (Set.mem_Ici.mpr le_rfl) hw0 hw0
  dsimp [g, a] at hle
  rw [Real.exp_zero, mul_one, mul_zero, sub_zero] at hle
  have hexp_y : Real.exp (2 * Real.log y) = y ^ 2 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith), Real.rpow_two]
  rw [hexp_y] at hle
  linarith

/-- Test point `σ^B_m = exp (-π cot ((m + 1) π / (n + 1)))` for Regime B. -/
noncomputable def sigmaB (n m : ℕ) : ℝ :=
  Real.exp (-(π * Real.cot (((m + 1 : ℝ) * π) / ((n + 1 : ℝ)))))

private lemma sigmaB_pos (n m : ℕ) : 0 < sigmaB n m := Real.exp_pos _

private lemma sigmaB_le_one {n m : ℕ} (hm : m ≤ (n - 1) / 2) (hn : 1 ≤ n) :
    sigmaB n m ≤ 1 := by
  unfold sigmaB
  rw [Real.exp_le_one_iff, neg_nonpos]
  refine mul_nonneg Real.pi_pos.le ?_
  rw [Real.cot_eq_cos_div_sin]
  have hθ_pos : 0 < ((m + 1 : ℝ) * π) / ((n + 1 : ℝ)) := by positivity
  have hθ_le : ((m + 1 : ℝ) * π) / ((n + 1 : ℝ)) ≤ π / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2m : (2 * (m + 1) : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 2 * (m + 1) ≤ n + 1 by omega)
    nlinarith [Real.pi_pos]
  exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ_le⟩)
    (Real.sin_pos_of_pos_of_lt_pi hθ_pos (lt_of_le_of_lt hθ_le (by linarith [Real.pi_pos]))).le

private lemma sigmaB_lt_one_of_even {n m : ℕ} (he : Even n) (hm : m ≤ (n - 1) / 2) (hn : 2 ≤ n) :
    sigmaB n m < 1 := by
  unfold sigmaB
  rw [Real.exp_lt_one_iff, neg_lt_zero]
  refine mul_pos Real.pi_pos ?_
  rw [Real.cot_eq_cos_div_sin]
  have hθ_pos : 0 < ((m + 1 : ℝ) * π) / ((n + 1 : ℝ)) := by positivity
  have h2m : 2 * (m + 1) < n + 1 := by rcases he with ⟨r, rfl⟩; omega
  have hθ_lt : ((m + 1 : ℝ) * π) / ((n + 1 : ℝ)) < π / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * (m + 1) : ℝ) < (n + 1 : ℝ) := by exact_mod_cast h2m
    nlinarith [Real.pi_pos]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ_lt⟩)
    (Real.sin_pos_of_pos_of_lt_pi hθ_pos (lt_trans hθ_lt (by linarith [Real.pi_pos])))

private lemma sigmaB_strictMono {n m₁ m₂ : ℕ} (hn : 1 ≤ n) (hlt : m₁ < m₂) (hm₂ : m₂ ≤ (n - 1) / 2) :
    sigmaB n m₁ < sigmaB n m₂ := by
  unfold sigmaB
  rw [Real.exp_lt_exp, neg_lt_neg_iff]
  refine mul_lt_mul_of_pos_left ?_ Real.pi_pos
  set θ₁ : ℝ := ((m₁ + 1 : ℝ) * π) / ((n + 1 : ℝ))
  set θ₂ : ℝ := ((m₂ + 1 : ℝ) * π) / ((n + 1 : ℝ))
  have hθ_lt : θ₁ < θ₂ := by
    dsimp [θ₁, θ₂]
    rw [div_lt_div_iff_of_pos_right (by positivity)]
    have : (m₁ : ℝ) < (m₂ : ℝ) := Nat.cast_lt.mpr hlt
    nlinarith [Real.pi_pos]
  have hθ₁_pos : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₂_le : θ₂ ≤ π / 2 := by
    dsimp [θ₂]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * (m₂ + 1) : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 2 * (m₂ + 1) ≤ n + 1 by omega)
    nlinarith [Real.pi_pos]
  have hsin1 : 0 < Real.sin θ₁ := Real.sin_pos_of_pos_of_lt_pi hθ₁_pos (by linarith [Real.pi_pos])
  have hsin2 : 0 < Real.sin θ₂ := Real.sin_pos_of_pos_of_lt_pi (lt_trans hθ₁_pos hθ_lt) (by linarith [Real.pi_pos])
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hsin2 hsin1]
  -- `cos θ₂ * sin θ₁ < cos θ₁ * sin θ₂ ↔ 0 < sin (θ₂ - θ₁)`!
  have hsub : Real.cos θ₁ * Real.sin θ₂ - Real.cos θ₂ * Real.sin θ₁ = Real.sin (θ₂ - θ₁) := by
    rw [Real.sin_sub]; ring
  have hsin_sub : 0 < Real.sin (θ₂ - θ₁) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

/-- Binomial + AM–GM lower bound: `(1 + σ)^(n + 2) / σ > 2 * (n + 1)` for all `σ > 0`, `n ≥ 1`. -/
private lemma one_add_pow_div_gt {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    2 * ((n : ℝ) + 1) < (1 + σ) ^ (n + 2) / σ := by
  have hbinom : 1 + ((n + 2 : ℕ) : ℝ) * σ + (((n + 2).choose 2 : ℕ) : ℝ) * σ ^ 2 ≤ (1 + σ) ^ (n + 2) := by
    rw [add_comm 1 σ, add_pow]
    have hsub : ({0, 1, 2} : Finset ℕ) ⊆ range (n + 3) := by
      intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]; omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun k => σ ^ k * (1 : ℝ) ^ (n + 2 - k) * ((n + 2).choose k : ℝ))
      hsub fun k _ _ => (by positivity : (0 : ℝ) ≤ _)
    have h012 : ∑ k ∈ ({0, 1, 2} : Finset ℕ), σ ^ k * (1 : ℝ) ^ (n + 2 - k) * ((n + 2).choose k : ℝ) =
        1 + ((n + 2 : ℕ) : ℝ) * σ + (((n + 2).choose 2 : ℕ) : ℝ) * σ ^ 2 := by
      simp [Finset.sum_insert, Finset.sum_singleton]; ring
    linarith
  have hcho2 : (((n + 2).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
    have hnat : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
      rw [Nat.choose_two_right]
      have hdvd : 2 ∣ (n + 2) * (n + 1) := by
        rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · exact ⟨(r + 1) * (2 * r + 1), by ring⟩
        · exact ⟨(2 * r + 3) * (r + 1), by ring⟩
      exact Nat.mul_div_cancel' hdvd
    have hR : (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) := by
      exact_mod_cast hnat
    linarith
  rw [lt_div_iff₀ hσ]
  have hsq : 0 ≤ (1 - ((n : ℝ) + 1) * σ) ^ 2 := sq_nonneg _
  -- `(1 - (n+1)σ)^2 = 1 - 2(n+1)σ + (n+1)^2 σ^2 ≥ 0`, wait: we need `1 + (n+2)σ + (n+2)(n+1)/2 * σ^2 > 2(n+1)σ`!
  -- That is `1 + (n+2)(n+1)/2 * σ^2 > n * σ`, and `(1 - n*σ/2)^2 ≥ 0` gives `1 + n^2/4 * σ^2 ≥ n*σ`,
  -- while `(n+2)(n+1)/2 > n^2/4` for ALL `n ≥ 1`!
  have hsq2 : 0 ≤ (1 - ((n : ℝ) / 2) * σ) ^ 2 := sq_nonneg _
  have hquad : (n : ℝ) ^ 2 / 4 < ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpos_s2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  rw [hcho2] at hbinom
  push_cast at hbinom
  nlinarith

/-- Helper for Regime B: Stirling magnitude bound for `n ≥ 64`. -/
private lemma regimeB_mag_gt_one {n : ℕ} (hn : 64 ≤ n) :
    (1 : ℝ) < 4 * (1 - 0.038) * ((n : ℝ) + 1) * (Nat.factorial n : ℝ) *
      (Real.sqrt (n : ℝ) / (π * ((n : ℝ) + 1))) ^ (n + 1) := by
  set P : ℝ := 4 * (1 - 0.038) * ((n : ℝ) + 1) * (Nat.factorial n : ℝ) *
    (Real.sqrt (n : ℝ) / (π * ((n : ℝ) + 1))) ^ (n + 1)
  have hP_pos : 0 < P := by
    have : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    positivity
  have hlogP_pos : 0 < Real.log P := by
    have hstir := Stirling.le_log_factorial_stirling (n := n) (by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlog_n1 : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + 1 / (n : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < ((n : ℝ) + 1) / (n : ℝ))
      rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at h
      have : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp [hn_pos.ne']; ring
      linarith
    have hlogP_eq : Real.log P =
        Real.log (3.848 : ℝ) + Real.log ((n : ℝ) + 1) + Real.log (Nat.factorial n : ℝ) +
          ((n : ℝ) + 1) * (Real.log (n : ℝ) / 2 - Real.log π - Real.log ((n : ℝ) + 1)) := by
      dsimp [P]
      have h3848 : 4 * (1 - 0.038 : ℝ) = 3.848 := by norm_num
      have hfac_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
      rw [h3848, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_div (by positivity) (by positivity),
        Real.log_sqrt hn_pos.le, Real.log_mul Real.pi_ne_zero hn1_pos.ne']
      push_cast; ring
    have hlogP_ge :
        Real.log (3.848 : ℝ) + Real.log (2 * π) / 2 - Real.log π - 1 +
          ((n : ℝ) / 2 * (Real.log (n : ℝ) - 2 - 2 * Real.log π) + Real.log (n : ℝ)) ≤ Real.log P := by
      rw [hlogP_eq]
      have hn_mul : (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * Real.log (n : ℝ) + 1 := by
        have := mul_le_mul_of_nonneg_left hlog_n1 hn_pos.le
        have hne : (n : ℝ) ≠ 0 := hn_pos.ne'
        have h1 : (n : ℝ) * (Real.log (n : ℝ) + 1 / (n : ℝ)) = (n : ℝ) * Real.log (n : ℝ) + 1 := by
          field_simp [hne]
        linarith
      linarith
    let g : ℝ → ℝ := fun x => (x / 2) * (Real.log x - 2 - 2 * Real.log π) + Real.log x
    have hpi_lt : π < 3.1416 := Real.pi_lt_d4
    have hpi_gt : 3.1415 < π := Real.pi_gt_d4
    have hlog64_gt : (4.1588 : ℝ) < Real.log 64 := by
      rw [show (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num, Real.log_pow]
      have h2 := Real.log_two_gt_d9
      push_cast; linarith
    have hlogpi_lt : Real.log π < 1.145 := by
      rw [Real.log_lt_iff_lt_exp Real.pi_pos]
      have he1 : (2.718281828 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have he0145 : (1.15602 : ℝ) < Real.exp 0.145 := by
        have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.145) 4
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
        norm_num at hsum
        linarith
      have hprod : Real.exp 1.145 = Real.exp 1 * Real.exp 0.145 := by
        rw [← Real.exp_add]; norm_num
      rw [hprod]
      nlinarith only [hpi_lt, he1, he0145]
    have hlog3848_gt : (1.34 : ℝ) < Real.log 3.848 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have he1 : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have he034 : Real.exp 0.34 < 1.415 := by
        have h1 := Real.add_one_le_exp (-0.34 / 16 : ℝ)
        have h2 : (1 - 0.34 / 16 : ℝ) ^ 16 ≤ (Real.exp (-0.34 / 16)) ^ 16 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 16
        rw [← Real.exp_nat_mul, show ((16 : ℕ) : ℝ) * (-0.34 / 16) = -0.34 by norm_num,
          Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)] at h2
        have hnum : (1.415 : ℝ) * (1 - 0.34 / 16) ^ 16 > 1 := by norm_num
        nlinarith only [h2, hnum, Real.exp_pos (0.34 : ℝ)]
      rw [show (1.34 : ℝ) = 1 + 0.34 by norm_num, Real.exp_add]
      nlinarith only [he1, he034, Real.exp_pos 1, Real.exp_pos (0.34 : ℝ)]
    have hlog2pi_gt : (1.836 : ℝ) < Real.log (2 * π) := by
      rw [Real.log_mul two_ne_zero Real.pi_ne_zero]
      have h2 : (0.6931 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
      have hpi_log : (1.143 : ℝ) < Real.log π := by
        rw [Real.lt_log_iff_exp_lt Real.pi_pos]
        have he1 : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have he0143 : Real.exp 0.143 < 1.1555 := by
          have h1 := Real.add_one_le_exp (-0.143 / 8 : ℝ)
          have h2 : (1 - 0.143 / 8 : ℝ) ^ 8 ≤ (Real.exp (-0.143 / 8)) ^ 8 :=
            pow_le_pow_left₀ (by norm_num) (by linarith) 8
          rw [← Real.exp_nat_mul, show ((8 : ℕ) : ℝ) * (-0.143 / 8) = -0.143 by norm_num,
            Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)] at h2
          have hnum : (1.1555 : ℝ) * (1 - 0.143 / 8) ^ 8 > 1 := by norm_num
          nlinarith only [h2, hnum, Real.exp_pos (0.143 : ℝ)]
        rw [show (1.143 : ℝ) = 1 + 0.143 by norm_num, Real.exp_add]
        nlinarith only [he1, he0143, hpi_gt, Real.exp_pos 1, Real.exp_pos (0.143 : ℝ)]
      linarith
    have hg_mono : MonotoneOn g (Set.Ici (64 : ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 64) ?_ ?_ ?_
      · dsimp [g]
        have hlog_cont : ContinuousOn Real.log (Set.Ici (64 : ℝ)) :=
          Real.continuousOn_log.mono fun x hx => ne_of_gt (by have h := Set.mem_Ici.mp hx; linarith)
        refine ContinuousOn.add ?_ hlog_cont
        exact (continuousOn_id.div_const 2).mul
          ((hlog_cont.sub continuousOn_const).sub continuousOn_const)
      · dsimp [g]
        have hlog_diff : DifferentiableOn ℝ Real.log (interior (Set.Ici (64 : ℝ))) :=
          Real.differentiableOn_log.mono fun x hx =>
            ne_of_gt (by have h : (64 : ℝ) < x := (by simpa [interior_Ici] using hx); linarith)
        refine DifferentiableOn.add ?_ hlog_diff
        exact (differentiableOn_id.div_const 2).mul
          ((hlog_diff.sub (differentiableOn_const (2 : ℝ))).sub (differentiableOn_const (2 * Real.log π)))
      · intro x hx
        have hx64 : (64 : ℝ) ≤ x := le_of_lt (by simpa [interior_Ici] using hx)
        have hx_ne : x ≠ 0 := by linarith
        have hd : HasDerivAt g ((Real.log x - 1 - 2 * Real.log π) / 2 + x⁻¹) x := by
          have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
          have h2 : HasDerivAt (fun t : ℝ => Real.log t - 2 - 2 * Real.log π) x⁻¹ x := by
            simpa using ((Real.hasDerivAt_log hx_ne).sub_const 2).sub_const (2 * Real.log π)
          have hprod := (h1.fun_mul h2).fun_add (Real.hasDerivAt_log hx_ne)
          refine hprod.congr_deriv ?_
          field_simp [hx_ne]; ring
        rw [hd.deriv]
        have hlogx : Real.log 64 ≤ Real.log x := Real.log_le_log (by norm_num) hx64
        have hxinv : 0 < x⁻¹ := inv_pos.mpr (by linarith)
        linarith only [hlogx, hlog64_gt, hlogpi_lt, hxinv]
    have hg_ge : g 64 ≤ g (n : ℝ) :=
      hg_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by exact_mod_cast hn)) (by exact_mod_cast hn)
    have hg64 : g 64 > -0.06 := by
      dsimp [g]; linarith only [hlog64_gt, hlogpi_lt]
    dsimp only [g] at hg_ge hg64
    linarith only [hlogP_ge, hlog3848_gt, hlog2pi_gt, hlogpi_lt, hg_ge, hg64]
  rw [← Real.exp_zero, ← Real.exp_log hP_pos]
  exact Real.exp_lt_exp.mpr hlogP_pos

/-- Tail bound extracted from `regimeB_bound` to keep heartbeats low. -/
private lemma regimeB_tail_bound {u N : ℝ} (hu_pos : 0 < u) (hN_pos : 0 < N)
    (hNa_gt : 3.51 < N * (8 * u / (1 + 8 * u))) :
    (∑' k : ℕ, (1 + (((2 * (k + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)) ≤ 0.038 := by
  set v : ℝ := 8 * u
  set a : ℝ := v / (1 + v)
  have hv_pos : 0 < v := by positivity
  have ht3_le : (1 + v) ^ (-N) ≤ Real.exp (-(N * a)) := by
    have hlog : a ≤ Real.log (1 + v) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (1 + v))
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub] at h1
      dsimp [a]; field_simp [show 1 + v ≠ 0 by positivity] at h1 ⊢; linarith
    rw [Real.rpow_def_of_pos (by linarith)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith only [hlog, hN_pos]
  have h2Na_gt1 : 1 < 2 * (N * a) := by linarith only [hNa_gt]
  obtain ⟨hsumm_pow, htsum_pow⟩ := odd_rpow_tail_bound h2Na_gt1
  have hge5_pos : ∀ k : ℕ, 0 < 1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u) := fun k => by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hmul : 0 < ((2 * (k + 2 : ℝ) + 1) ^ 2 - 1) * u := mul_pos (by nlinarith only [hk0]) hu_pos
    linarith
  have hterm_ge5 : ∀ k : ℕ,
      (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) ≤
        (1 + v) ^ (-N) * (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-(2 * (N * a)))) := by
    intro k
    set y : ℝ := (2 * (k + 2 : ℝ) + 1) / 3
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hy1 : 1 ≤ y := by dsimp [y]; linarith only [hk0]
    have hj_ineq : 8 * y ^ 2 ≤ (2 * (k + 2 : ℝ) + 1) ^ 2 - 1 := by
      dsimp [y]; nlinarith only [hk0]
    have hbase_le : 1 + v * y ^ 2 ≤ 1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u) := by
      dsimp [v]; nlinarith only [hj_ineq, hu_pos]
    have h1 : (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) ≤ (1 + v * y ^ 2) ^ (-N) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase_le (by linarith only [hN_pos])
    have h2 : (1 + v * y ^ 2) ^ (-N) ≤ (1 + v) ^ (-N) * y ^ (-(2 * (N * a))) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
        Real.rpow_def_of_pos (by linarith only [hy1]), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hlog := log_one_add_mul_sq_ge hv_pos hy1
      dsimp [a] at hlog ⊢
      nlinarith only [hlog, hN_pos]
    exact h1.trans h2
  have hsumm_ge5 : Summable fun k : ℕ => (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) :=
    Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (hge5_pos k).le _) hterm_ge5
      (hsumm_pow.mul_left _)
  have hsum_ge5_le : ∑' k : ℕ, (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) ≤
      (1 + v) ^ (-N) * (3 / (2 * (2 * (N * a) - 1))) := by
    calc
      ∑' k : ℕ, (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)
          ≤ ∑' k : ℕ, (1 + v) ^ (-N) * (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-(2 * (N * a)))) :=
            hsumm_ge5.tsum_le_tsum hterm_ge5 (hsumm_pow.mul_left _)
      _ = (1 + v) ^ (-N) * ∑' k : ℕ, (((2 * (k + 2) + 1 : ℝ) / 3) ^ (-(2 * (N * a)))) :=
            tsum_mul_left
      _ ≤ (1 + v) ^ (-N) * (3 / (2 * (2 * (N * a) - 1))) :=
            mul_le_mul_of_nonneg_left htsum_pow (Real.rpow_nonneg (by positivity) _)
  have hcongr_ge3 : (fun k : ℕ => (1 + (((2 * ((k + 1 : ℕ) + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)) =
      (fun k : ℕ => (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)) := by
    funext k; push_cast; ring_nf
  have hsumm_ge3 : Summable fun k : ℕ => (1 + (((2 * (k + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) := by
    rw [← summable_nat_add_iff 1, hcongr_ge3]
    exact hsumm_ge5
  rw [hsumm_ge3.tsum_eq_zero_add]
  have h0eq : (1 + (((2 * ((0 : ℕ) + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) = (1 + v) ^ (-N) := by
    dsimp [v]; congr 1; norm_num
  have hshift : (∑' k : ℕ, (1 + (((2 * ((k + 1 : ℕ) + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)) =
      ∑' k : ℕ, (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) := by
    rw [hcongr_ge3]
  rw [h0eq, hshift]
  have hexp_bound : Real.exp (-(N * a)) < 0.0304 := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)]
    have he1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have he7 : (2.718 : ℝ) ^ 7 < Real.exp 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    have he2Na : Real.exp 7 < Real.exp (2 * (N * a)) := Real.exp_lt_exp.mpr (by linarith only [hNa_gt])
    have hsq : (1 / 0.0304 : ℝ) ^ 2 < (Real.exp (N * a)) ^ 2 := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (N * a) = 2 * (N * a) by push_cast; ring]
      have hnum : (1 / 0.0304 : ℝ) ^ 2 < (2.718 : ℝ) ^ 7 := by norm_num
      linarith only [hnum, he7, he2Na]
    have hgt : (1 / 0.0304 : ℝ) < Real.exp (N * a) := by
      nlinarith only [hsq, Real.exp_pos (N * a)]
    linarith only [hgt]
  have hfac : 1 + 3 / (2 * (2 * (N * a) - 1)) < 1.25 := by
    have : 3 / (2 * (2 * (N * a) - 1)) < 0.25 := by
      rw [div_lt_iff₀ (by linarith only [hNa_gt])]; linarith only [hNa_gt]
    linarith only [this]
  have hfac_nn : 0 ≤ 1 + 3 / (2 * (2 * (N * a) - 1)) :=
    add_nonneg zero_le_one (div_nonneg (by norm_num) (by linarith only [hNa_gt]))
  calc
    (1 + v) ^ (-N) + ∑' k : ℕ, (1 + (((2 * (k + 2) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)
        ≤ (1 + v) ^ (-N) * (1 + 3 / (2 * (2 * (N * a) - 1))) := by linarith only [hsum_ge5_le]
    _ ≤ Real.exp (-(N * a)) * (1 + 3 / (2 * (2 * (N * a) - 1))) :=
        mul_le_mul_of_nonneg_right ht3_le hfac_nn
    _ ≤ 0.0304 * 1.25 := by nlinarith only [hexp_bound, hfac, hfac_nn, Real.exp_pos (-(N * a))]
    _ ≤ 0.038 := by norm_num

/-- **Regime B bound:** For every `n ≥ 64` and `m ≤ (n - 1) / 2` with `4 * (m + 1)^2 > n`,
`(-1)^m * (1 + sigmaB n m) * A_n(-sigmaB n m) > 1`. -/
private lemma regimeB_bound {n m : ℕ} (hn : 64 ≤ n) (hm : m ≤ (n - 1) / 2) (hreg : n < 4 * (m + 1) ^ 2) :
    (-1 : ℝ) ^ m * ((1 + sigmaB n m) * (eulerianPoly n).eval (-sigmaB n m)) > 1 := by
  set θ : ℝ := ((m + 1 : ℝ) * π) / ((n + 1 : ℝ))
  set L : ℝ := π * Real.cot θ
  set σ : ℝ := sigmaB n m
  have hθ_pos : 0 < θ := by dsimp [θ]; positivity
  have hθ_le : θ ≤ π / 2 := by
    dsimp [θ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * (m + 1) : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 2 * (m + 1) ≤ n + 1 by omega)
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ_pos (lt_of_le_of_lt hθ_le (by linarith [Real.pi_pos]))
  have hcos_nn : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ_le⟩
  have hL_nn : 0 ≤ L := mul_nonneg Real.pi_pos.le (by rw [Real.cot_eq_cos_div_sin]; exact div_nonneg hcos_nn hsin_pos.le)
  have hσ_pos : 0 < σ := Real.exp_pos _
  -- Apply the pole expansion at `L ≥ 0`!
  have hpole := eulerianPoly_pole_expansion (by omega : 1 ≤ n) hL_nn
  change (eulerianPoly n).eval (-σ) =
      -((1 + σ) ^ (n + 1) / σ) *
        (2 * (Nat.factorial n : ℝ) *
          ∑' k : ℕ, ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re) at hpole
  set r : ℝ := π / Real.sin θ
  have hr_pos : 0 < r := div_pos Real.pi_pos hsin_pos
  -- Compute the `k = 0` term: `L + iπ = r * exp (iθ)`, so `Re (1 / (L + iπ)^(n+1)) = (-1)^(m+1) * r^(-(n+1))`!
  have hterm0 : ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * 0 + 1 : ℕ))) ^ (n + 1)).re =
      (-1 : ℝ) ^ (m + 1) * r⁻¹ ^ (n + 1) := by
    have hLpi : (L : ℂ) + I * (π * (2 * 0 + 1 : ℕ)) = (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by
      rw [Complex.exp_mul_I]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, Nat.cast_one, zero_add, mul_one,
          Complex.ofReal_im, sub_zero, add_zero, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
          Complex.sin_ofReal_im, mul_zero]
        dsimp [L, r]
        rw [Real.cot_eq_cos_div_sin]; field_simp [hsin_pos.ne']
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul,
          Complex.I_im, Nat.cast_one, zero_add, mul_one,
          Complex.ofReal_re, add_zero, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
          Complex.sin_ofReal_im, mul_zero]
        dsimp [r]; field_simp [hsin_pos.ne']
    rw [hLpi, mul_pow, ← Complex.exp_nat_mul, one_div, mul_inv, ← Complex.exp_neg,
      show -(((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * I)) = ((-(↑(n + 1) * θ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    have hangle : ((n + 1 : ℕ) : ℝ) * θ = ((m + 1 : ℕ) : ℝ) * π := by
      dsimp [θ]; push_cast; field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
    simp only [Complex.mul_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re, Complex.cos_ofReal_re,
      Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero]
    rw [Real.cos_neg, hangle, Real.cos_nat_mul_pi, mul_comm, inv_pow]
  -- Bound the tail `k ≥ 1` (`j = 2k + 1 ≥ 3`) relative to `r^(-(n+1))`:
  set u : ℝ := Real.sin θ ^ 2
  set N : ℝ := ((n : ℝ) + 1) / 2
  have hu_pos : 0 < u := sq_pos_of_pos hsin_pos
  have hN_pos : 0 < N := by positivity
  -- For every `k : ℕ`, `‖L + i π (2k + 1)‖^2 = r^2 * (1 + ((2k + 1)^2 - 1) * u)`!
  have hnorm_sq : ∀ k : ℕ,
      ‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ ^ 2 =
        r ^ 2 * (1 + (((2 * k + 1 : ℝ) ^ 2 - 1) * u)) := by
    intro k
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, one_mul, zero_add]
    dsimp [L, r, u]
    rw [Real.cot_eq_cos_div_sin]
    have hcs := Real.sin_sq_add_cos_sq θ
    push_cast
    field_simp [hsin_pos.ne']
    nlinarith
  have hterm_norm : ∀ k : ℕ,
      ‖(1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)‖ =
        r⁻¹ ^ (n + 1) * (1 + (((2 * k + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) := by
    intro k
    rw [norm_div, norm_one, norm_pow, one_div, inv_pow]
    have hpos : 0 < ‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ := by
      have hsq := hnorm_sq k
      have h1 : 0 < r ^ 2 * (1 + (((2 * k + 1 : ℝ) ^ 2 - 1) * u)) := by
        refine mul_pos (sq_pos_of_pos hr_pos) ?_
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hk1 : (1 : ℝ) ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith only [hk0]
        nlinarith only [hk1, hu_pos]
      have hne : ‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ ≠ 0 := by
        intro h0
        rw [h0, zero_pow two_ne_zero] at hsq
        linarith only [hsq, h1]
      exact lt_of_le_of_ne (norm_nonneg _) hne.symm
    have hbase_pos : 0 < 1 + (((2 * k + 1 : ℝ) ^ 2 - 1) * u) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk1 : (1 : ℝ) ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith only [hk0]
      nlinarith only [hk1, hu_pos]
    have hpow_eq : (‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ ^ (n + 1))⁻¹ =
        (‖(L : ℂ) + I * (π * (2 * k + 1 : ℕ))‖ ^ 2) ^ (-N) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le]
      congr 1; dsimp [N]; push_cast; ring
    rw [hpow_eq, hnorm_sq k, Real.mul_rpow (sq_pos_of_pos hr_pos).le hbase_pos.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr_pos.le, show (2 : ℕ) * (-N) = -((n + 1 : ℕ) : ℝ) by
      dsimp [N]; push_cast; ring, Real.rpow_neg hr_pos.le, Real.rpow_natCast]
  -- Jordan's inequality: `sin θ ≥ 2 θ / π = 2 (m + 1) / (n + 1)`, hence `u > n / (n + 1)^2`!
  have hu_gt : (n : ℝ) / ((n : ℝ) + 1) ^ 2 < u := by
    have hjord : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin hθ_pos.le hθ_le
    have h2θ : 2 / π * θ = 2 * ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
      dsimp [θ]; field_simp [Real.pi_ne_zero]
    rw [h2θ] at hjord
    have hsq : (2 * ((m : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 ≤ u := by
      dsimp [u]; exact pow_le_pow_left₀ (by positivity) hjord 2
    have hregR : (n : ℝ) < 4 * ((m : ℝ) + 1) ^ 2 := by exact_mod_cast hreg
    have hgt : (n : ℝ) / ((n : ℝ) + 1) ^ 2 < (2 * ((m : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 := by
      rw [div_pow, div_lt_div_iff_of_pos_right (by positivity)]; linarith
    linarith
  set v : ℝ := 8 * u
  set a : ℝ := v / (1 + v)
  have hv_pos : 0 < v := by positivity
  have ha_pos : 0 < a := div_pos hv_pos (by linarith)
  -- Lower bound `N * a > 3.51` for `n ≥ 64`!
  have hNa_gt : (3.51 : ℝ) < N * a := by
    have hu_lt : (n : ℝ) / ((n : ℝ) + 1) ^ 2 < u := hu_gt
    have ha_gt : (8 * (n : ℝ)) / (((n : ℝ) + 1) ^ 2 + 8 * (n : ℝ)) < a := by
      dsimp [a, v]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hu_lt
      nlinarith
    have hNa_gt1 : (4 * (n : ℝ) * ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ 2 + 8 * (n : ℝ)) < N * a := by
      have hmul := mul_lt_mul_of_pos_left ha_gt hN_pos
      dsimp [N] at hmul ⊢
      linarith [show ((n : ℝ) + 1) / 2 * (8 * (n : ℝ) / (((n : ℝ) + 1) ^ 2 + 8 * (n : ℝ))) =
        4 * (n : ℝ) * ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2 + 8 * (n : ℝ)) by ring]
    have hβ_gt : (3.51 : ℝ) < (4 * (n : ℝ) * ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ 2 + 8 * (n : ℝ)) := by
      rw [lt_div_iff₀ (by positivity)]
      have hnR : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith only [hnR]
    linarith only [hNa_gt1, hβ_gt]
  -- Bound `t_j := (1 + (j^2 - 1) * u)^(-N)` sum over `k ≥ 1` (`j = 2k + 1 ≥ 3`) by `0.038`!
  have htail_bound :
      (∑' k : ℕ, (1 + (((2 * (k + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N)) ≤ 0.038 :=
    regimeB_tail_bound hu_pos hN_pos hNa_gt
  -- Combine `k = 0` term and tail bound to lower bound `(-1)^(m+1) * ∑' k, Re(...) ≥ r^(-(n+1)) * (1 - 0.038)`!
  have hsum_all : Summable fun k : ℕ =>
      ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re :=
    Complex.reCLM.summable (summable_odd_pole n (by omega) L hL_nn)
  have hsum_lb : r⁻¹ ^ (n + 1) * (1 - 0.038) ≤
      (-1 : ℝ) ^ (m + 1) *
        ∑' k : ℕ, ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re := by
    rw [hsum_all.tsum_eq_zero_add, hterm0, mul_add, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_mul]
    have htail_abs :
        |(-1 : ℝ) ^ (m + 1) * ∑' k : ℕ,
            ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * (k + 1) + 1 : ℕ))) ^ (n + 1)).re| ≤
          r⁻¹ ^ (n + 1) * 0.038 := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have hsumm_norm : Summable fun k : ℕ =>
          r⁻¹ ^ (n + 1) * (1 + (((2 * (k + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) := by
        have hshift := (summable_nat_add_iff 1).mpr (summable_odd_pole n (by omega) L hL_nn).norm
        refine hshift.congr fun k => ?_
        simpa [Nat.cast_add, Nat.cast_one] using hterm_norm (k + 1)
      have h1 : |∑' k : ℕ, ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * (k + 1) + 1 : ℕ))) ^ (n + 1)).re| ≤
          ∑' k : ℕ, |((1 : ℂ) / ((L : ℂ) + I * (π * (2 * (k + 1) + 1 : ℕ))) ^ (n + 1)).re| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).mpr hsum_all).norm
      have h2 : ∑' k : ℕ, |((1 : ℂ) / ((L : ℂ) + I * (π * (2 * (k + 1) + 1 : ℕ))) ^ (n + 1)).re| ≤
          ∑' k : ℕ, r⁻¹ ^ (n + 1) * (1 + (((2 * (k + 1) + 1 : ℝ) ^ 2 - 1) * u)) ^ (-N) := by
        refine (((summable_nat_add_iff 1).mpr hsum_all).abs).tsum_le_tsum (fun k => ?_) hsumm_norm
        have hre := Complex.abs_re_le_norm ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * (k + 1) + 1 : ℕ))) ^ (n + 1))
        rw [hterm_norm (k + 1)] at hre
        simpa only [Nat.cast_add, Nat.cast_one] using hre
      rw [tsum_mul_left] at h2
      exact (h1.trans h2).trans (mul_le_mul_of_nonneg_left htail_bound (pow_nonneg (inv_nonneg.mpr hr_pos.le) _))
    linarith [(abs_le.mp htail_abs).1]
  -- Magnitude bound: `4 * (1 - 0.038) * (n + 1) * n! * r^(-(n + 1)) > 1` for all `n ≥ 64`!
  have hmag : (1 : ℝ) <
      ((1 + σ) ^ (n + 2) / σ) * (2 * (Nat.factorial n : ℝ) * (r⁻¹ ^ (n + 1) * (1 - 0.038))) := by
    have h1 := one_add_pow_div_gt (by omega : 1 ≤ n) hσ_pos
    have hfac_pos : 0 < 2 * (Nat.factorial n : ℝ) * (r⁻¹ ^ (n + 1) * (1 - 0.038)) := by
      have : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
      positivity
    have hstep1 : 2 * ((n : ℝ) + 1) * (2 * (Nat.factorial n : ℝ) * (r⁻¹ ^ (n + 1) * (1 - 0.038))) <
        ((1 + σ) ^ (n + 2) / σ) * (2 * (Nat.factorial n : ℝ) * (r⁻¹ ^ (n + 1) * (1 - 0.038))) :=
      mul_lt_mul_of_pos_right h1 hfac_pos
    have hrinv_gt : Real.sqrt (n : ℝ) / (π * ((n : ℝ) + 1)) < r⁻¹ := by
      dsimp [r]
      rw [inv_div, mul_comm π, ← div_div, div_lt_div_iff_of_pos_right Real.pi_pos]
      have hsq : (Real.sqrt (n : ℝ) / ((n : ℝ) + 1)) ^ 2 < Real.sin θ ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by positivity)]; exact hu_gt
      have hpos1 : 0 ≤ Real.sqrt (n : ℝ) / ((n : ℝ) + 1) := by positivity
      nlinarith only [hsq, hpos1, hsin_pos]
    have hrinv_pow : (Real.sqrt (n : ℝ) / (π * ((n : ℝ) + 1))) ^ (n + 1) < r⁻¹ ^ (n + 1) :=
      pow_lt_pow_left₀ hrinv_gt (by positivity) (by omega)
    have hP_gt1 := regimeB_mag_gt_one hn
    have hstep2 : 4 * (1 - 0.038) * ((n : ℝ) + 1) * (Nat.factorial n : ℝ) *
        (Real.sqrt (n : ℝ) / (π * ((n : ℝ) + 1))) ^ (n + 1) <
        2 * ((n : ℝ) + 1) * (2 * (Nat.factorial n : ℝ) * (r⁻¹ ^ (n + 1) * (1 - 0.038))) := by
      have hpos_coeff : 0 < 4 * (1 - 0.038 : ℝ) * ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
        have : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
        positivity
      have hmul := mul_lt_mul_of_pos_left hrinv_pow hpos_coeff
      linarith only [hmul]
    linarith only [hP_gt1, hstep2, hstep1]
  -- Combine `hpole`, `hsum_lb`, and `hmag`!
  have hcomb : (-1 : ℝ) ^ m * ((1 + σ) * (eulerianPoly n).eval (-σ)) =
      ((1 + σ) ^ (n + 2) / σ) *
        (2 * (Nat.factorial n : ℝ) *
          ((-1 : ℝ) ^ (m + 1) *
            ∑' k : ℕ, ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re)) := by
    rw [hpole]
    rw [pow_succ (1 + σ) (n + 1), pow_succ (-1 : ℝ) m]
    ring
  rw [hcomb]
  have hge : ((1 + σ) ^ (n + 2) / σ) * (2 * (Nat.factorial n : ℝ) * (r⁻¹ ^ (n + 1) * (1 - 0.038))) ≤
      ((1 + σ) ^ (n + 2) / σ) *
        (2 * (Nat.factorial n : ℝ) *
          ((-1 : ℝ) ^ (m + 1) *
            ∑' k : ℕ, ((1 : ℂ) / ((L : ℂ) + I * (π * (2 * k + 1 : ℕ))) ^ (n + 1)).re)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_lb (by positivity)) (by positivity)
  linarith only [hmag, hge]

/-- Junction ordering: for `n ≥ 64` and `m₀` with `4 * (m₀ + 1)^2 ≤ n < 4 * (m₀ + 2)^2`,
`sigmaA n m₀ < sigmaB n (m₀ + 1)`. -/
private lemma sigmaA_lt_sigmaB_junction {n m₀ : ℕ} (hn : 64 ≤ n) (hm₀ : 1 ≤ m₀)
    (hA : 4 * (m₀ + 1) ^ 2 ≤ n) (_hB : n < 4 * (m₀ + 2) ^ 2) :
    sigmaA n m₀ < sigmaB n (m₀ + 1) := by
  -- Show `-log (sigmaA n m₀) > -log (sigmaB n (m₀ + 1))`, i.e.,
  -- `(n / 2) * log (1 + 2 / m₀) ≥ n / (m₀ + 1) ≥ (n + 1) / (m₀ + 2) > π * cot ((m₀ + 2) π / (n + 1))`!
  unfold sigmaA sigmaB
  rw [Real.rpow_def_of_pos (div_pos (by positivity) (by positivity)), Real.exp_lt_exp]
  -- Equivalently `π * cot θ < - (log (m₀ / (m₀ + 2)) * (n / 2))`!
  set θ : ℝ := (((m₀ + 1 : ℕ) + 1 : ℝ) * π) / ((n + 1 : ℝ))
  have hθ_pos : 0 < θ := by dsimp [θ]; positivity
  have hm₀_lt : m₀ + 2 ≤ n := by
    have : (m₀ + 1) ^ 2 ≤ n / 4 := by omega
    nlinarith
  have hθ_le : θ ≤ π / 2 := by
    dsimp [θ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2 : (2 * (m₀ + 2) : ℝ) ≤ (n + 1 : ℝ) := by
      have : (m₀ + 1) ^ 2 ≤ n / 4 := by omega
      have : 2 * (m₀ + 2) ≤ n + 1 := by nlinarith
      exact_mod_cast this
    push_cast; nlinarith [Real.pi_pos]
  -- 1. `π * cot θ < π / θ = (n + 1) / (m₀ + 2)` since `cot θ < 1 / θ` (`cos θ < 1` and `sin θ < θ`? Wait: `tan θ > θ`, i.e., `θ * cos θ < sin θ`!)
  have hcot_lt : π * Real.cot θ < ((n : ℝ) + 1) / ((m₀ : ℝ) + 2) := by
    have hsin_pos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ_pos (lt_of_le_of_lt hθ_le (by linarith [Real.pi_pos]))
    have htan_gt : θ * Real.cos θ < Real.sin θ := by
      -- Prove `f(x) = sin x - x * cos x` has `f(0) = 0` and `f'(x) = x * sin x > 0` on `(0, π/2]`!
      let f : ℝ → ℝ := fun x => Real.sin x - x * Real.cos x
      have hstrict : StrictMonoOn f (Set.Icc 0 (π / 2)) := by
        refine strictMonoOn_of_deriv_pos (convex_Icc 0 (π / 2)) ?_ ?_
        · exact Real.continuous_sin.continuousOn.sub (continuousOn_id.mul Real.continuous_cos.continuousOn)
        · intro x hx
          rw [interior_Icc] at hx
          have hd : HasDerivAt f (x * Real.sin x) x := by
            have := (Real.hasDerivAt_sin x).fun_sub ((hasDerivAt_id x).fun_mul (Real.hasDerivAt_cos x))
            exact this.congr_deriv (by dsimp only [id_eq]; ring)
          rw [hd.deriv]
          exact mul_pos hx.1 (Real.sin_pos_of_pos_of_lt_pi hx.1 (lt_trans hx.2 (by linarith [Real.pi_pos])))
      have h0lt := hstrict ⟨le_rfl, by positivity⟩ ⟨hθ_pos.le, hθ_le⟩ hθ_pos
      dsimp [f] at h0lt; simp at h0lt; linarith
    have hcot1 : Real.cot θ < 1 / θ := by
      rw [Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hsin_pos hθ_pos, one_mul, mul_comm]
      exact htan_gt
    have hpi_div : π * (1 / θ) = ((n : ℝ) + 1) / ((m₀ : ℝ) + 2) := by
      dsimp [θ]; push_cast; field_simp [Real.pi_ne_zero, show (m₀ : ℝ) + 2 ≠ 0 by positivity]; ring
    calc
      π * Real.cot θ < π * (1 / θ) := mul_lt_mul_of_pos_left hcot1 Real.pi_pos
      _ = ((n : ℝ) + 1) / ((m₀ : ℝ) + 2) := hpi_div
  -- 2. `(n + 1) / (m₀ + 2) ≤ n / (m₀ + 1)` since `m₀ + 1 ≤ n`!
  have hmid : ((n : ℝ) + 1) / ((m₀ : ℝ) + 2) ≤ (n : ℝ) / ((m₀ : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (m₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show m₀ + 1 ≤ n by omega)
    nlinarith
  -- 3. `n / (m₀ + 1) ≤ (n / 2) * log ((m₀ + 2) / m₀)` using `log ((1 + u) / (1 - u)) ≥ 2u` at `u = 1 / (m₀ + 1)`!
  have hlog_ge : (2 : ℝ) / ((m₀ : ℝ) + 1) ≤ Real.log (((m₀ : ℝ) + 2) / (m₀ : ℝ)) := by
    set u : ℝ := 1 / ((m₀ : ℝ) + 1)
    have hu0 : 0 < u := by positivity
    have hu1 : u < 1 := by
      dsimp [u]
      rw [div_lt_one (by positivity)]
      have h1m : (1 : ℝ) ≤ m₀ := by exact_mod_cast hm₀
      linarith
    have hfrac : ((m₀ : ℝ) + 2) / (m₀ : ℝ) = (1 + u) / (1 - u) := by
      dsimp [u]; field_simp [show (m₀ : ℝ) ≠ 0 by positivity, show (m₀ : ℝ) + 1 ≠ 0 by positivity]; ring
    rw [hfrac]
    -- Show `f(t) = log((1 + t)/(1 - t)) - 2t` has `f(0) = 0` and `f'(t) = 2t^2 / (1 - t^2) ≥ 0` on `[0, u]`!
    let f : ℝ → ℝ := fun t => Real.log (1 + t) - Real.log (1 - t) - 2 * t
    have hmono : MonotoneOn f (Set.Icc 0 u) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u) ?_ ?_ ?_
      · refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) (continuousOn_const.mul continuousOn_id)
        · exact (continuousOn_const.add continuousOn_id).log fun t ht => by dsimp; linarith [ht.1]
        · exact (continuousOn_const.sub continuousOn_id).log fun t ht => by dsimp; linarith [ht.2]
      · refine DifferentiableOn.sub (DifferentiableOn.sub ?_ ?_) ((differentiableOn_const (2 : ℝ)).mul differentiableOn_id)
        · exact ((differentiableOn_const (1 : ℝ)).add differentiableOn_id).log fun t ht => by
            rw [interior_Icc] at ht; dsimp; linarith [ht.1]
        · exact ((differentiableOn_const (1 : ℝ)).sub differentiableOn_id).log fun t ht => by
            rw [interior_Icc] at ht; dsimp; linarith [ht.2]
      · intro t ht
        rw [interior_Icc] at ht
        have h1 : 0 < 1 + t := by linarith [ht.1]
        have h2 : 0 < 1 - t := by linarith [ht.2]
        have hd : HasDerivAt f ((1 + t)⁻¹ + (1 - t)⁻¹ - 2) t := by
          have ha := ((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id t)).log h1.ne'
          have hb := ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)).log h2.ne'
          have hc := (hasDerivAt_id t).const_mul (2 : ℝ)
          exact ((ha.fun_sub hb).fun_sub hc).congr_deriv (by dsimp only [id_eq]; ring)
        rw [hd.deriv]
        have hsum : (1 + t)⁻¹ + (1 - t)⁻¹ - 2 = 2 * t ^ 2 / ((1 + t) * (1 - t)) := by
          field_simp [h1.ne', h2.ne']; ring
        rw [hsum]; positivity
    have hle := hmono ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0.le
    dsimp [f] at hle
    rw [add_zero, sub_zero, Real.log_one, mul_zero, sub_zero, sub_zero] at hle
    rw [Real.log_div (by linarith) (by linarith)]
    dsimp [u] at hle ⊢
    rw [mul_one_div] at hle
    linarith
  have hlog_neg : -Real.log ((m₀ : ℝ) / ((m₀ : ℝ) + 2)) = Real.log (((m₀ : ℝ) + 2) / (m₀ : ℝ)) := by
    rw [← Real.log_inv, inv_div]
  have hstep3 : (n : ℝ) / ((m₀ : ℝ) + 1) ≤ -(Real.log ((m₀ : ℝ) / ((m₀ : ℝ) + 2)) * ((n : ℝ) / 2)) := by
    have h := mul_le_mul_of_nonneg_right hlog_ge (by positivity : 0 ≤ (n : ℝ) / 2)
    rw [← hlog_neg] at h
    have : 2 / ((m₀ : ℝ) + 1) * ((n : ℝ) / 2) = (n : ℝ) / ((m₀ : ℝ) + 1) := by ring
    linarith
  linarith

/-- Analytic proof of Rossi's Conjecture 6.16 for all `n ≥ 64`. -/
theorem rossi_conjecture_6_16_ge_64 {n : ℕ} (hn : 64 ≤ n) :
    ∃ S : Finset ℝ, S.card = n ∧
      (∀ t ∈ S, (charPoly n).IsRoot t) ∧
      (1 : ℝ) ∈ S ∧
      (S.filter (fun t => 0 < t ∧ t < 1)).card = n - 2 ∧
      (S.filter (fun t => 1 < t)).card = 1 := by
  set K := (n - 1) / 2
  let σ : Fin K → ℝ := fun j =>
    if 4 * (j.val + 2) ^ 2 ≤ n then sigmaA n (j.val + 1) else sigmaB n (j.val + 1)
  refine paired_sign_alternation (by omega) σ ?_ ?_ ?_ ?_ ?_
  · intro j; dsimp [σ]; split_ifs
    · exact sigmaA_pos (by omega)
    · exact sigmaB_pos n (j.val + 1)
  · intro j₁ j₂ hlt
    have hv : j₁.val < j₂.val := hlt
    dsimp [σ]
    split_ifs with h1 h2 h2
    · exact sigmaA_strictMono (by omega) (by omega) (by omega)
    · -- `j₁` in Regime A, `j₂` in Regime B: pass through the junction `m₀`!
      have hex_m0 : ∃ m₀ : ℕ, j₁.val + 1 ≤ m₀ ∧ m₀ < j₂.val + 1 ∧
          4 * (m₀ + 1) ^ 2 ≤ n ∧ n < 4 * (m₀ + 2) ^ 2 := by
        let S_A := (Finset.Icc (j₁.val + 1) (j₂.val + 1)).filter fun m => 4 * (m + 1) ^ 2 ≤ n
        have hne : S_A.Nonempty := ⟨j₁.val + 1, Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by simpa [show j₁.val + 1 + 1 = j₁.val + 2 by omega] using h1⟩⟩
        set m₀ := S_A.max' hne
        have hm₀_mem : m₀ ∈ S_A := Finset.max'_mem S_A hne
        simp only [S_A, Finset.mem_filter, Finset.mem_Icc] at hm₀_mem
        have hm₀_lt : m₀ < j₂.val + 1 := by
          by_contra hge
          have heq : m₀ = j₂.val + 1 := by omega
          rw [heq] at hm₀_mem; exact h2 (by simpa [show j₂.val + 1 + 1 = j₂.val + 2 by omega] using hm₀_mem.2)
        have hnot : ¬ 4 * (m₀ + 2) ^ 2 ≤ n := by
          intro hle
          have hmem : m₀ + 1 ∈ S_A := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simpa [show m₀ + 1 + 1 = m₀ + 2 by omega] using hle⟩
          have hle_max : m₀ + 1 ≤ m₀ := Finset.le_max' S_A (m₀ + 1) hmem
          omega
        exact ⟨m₀, hm₀_mem.1.1, hm₀_lt, hm₀_mem.2, not_le.mp hnot⟩
      obtain ⟨m₀, hle1, hlt2, hA0, hB0⟩ := hex_m0
      have hstep1 : sigmaA n (j₁.val + 1) ≤ sigmaA n m₀ := by
        by_cases heq : j₁.val + 1 = m₀
        · rw [heq]
        · exact (sigmaA_strictMono (by omega) (by omega) (by omega)).le
      have hstep2 : sigmaA n m₀ < sigmaB n (m₀ + 1) :=
        sigmaA_lt_sigmaB_junction hn (by omega) hA0 hB0
      have hstep3 : sigmaB n (m₀ + 1) ≤ sigmaB n (j₂.val + 1) := by
        by_cases heq : m₀ + 1 = j₂.val + 1
        · rw [heq]
        · exact (sigmaB_strictMono (by omega) (by omega) (by have := j₂.isLt; omega)).le
      linarith
    · exfalso; nlinarith
    · exact sigmaB_strictMono (by omega) (by omega) (by have := j₂.isLt; omega)
  · intro j; dsimp [σ]; split_ifs
    · exact (sigmaA_lt_one (by omega) (by omega)).le
    · exact sigmaB_le_one (by have := j.isLt; omega) (by omega)
  · intro he j; dsimp [σ]; split_ifs
    · exact sigmaA_lt_one (by omega) (by omega)
    · exact sigmaB_lt_one_of_even he (by have := j.isLt; omega) (by omega)
  · intro j; dsimp [σ]; split_ifs with hreg
    · exact regimeA_bound (by omega) (by omega) (by simpa [show j.val + 1 + 1 = j.val + 2 by omega] using hreg)
    · exact regimeB_bound hn (by have := j.isLt; omega)
        (by have := not_le.mp hreg; simpa [show j.val + 1 + 1 = j.val + 2 by omega] using this)

/-! ### Section 5: Finite Range `3 ≤ n ≤ 63` (Exact Kernel-Checked Rational Witnesses) -/

/-- Linear-time tail of the `(n + 1)`-th Eulerian row from the `n`-th row. -/
private def nextRowTail (n : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, [a] => [(n - k) * a]
  | k, a :: b :: rest => ((k + 2) * b + (n - k) * a) :: nextRowTail n (k + 1) (b :: rest)

/-- `O(n)` single-pass row transition from row `n` to row `n + 1`. -/
private def nextEulerianRow (n : ℕ) (row : List ℕ) : List ℕ :=
  1 :: nextRowTail n 0 row

/-- Tail-recursive Eulerian row builder (`O(n^2)` time, `O(n)` stack depth). -/
private def eulerianRowAux : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, acc => acc
  | steps + 1, curN, acc => eulerianRowAux steps (curN + 1) (nextEulerianRow curN acc)

private def eulerianRow : ℕ → List ℕ
  | 0 => []
  | n + 1 => eulerianRowAux n 1 [1]

private lemma nextRowTail_length (n : ℕ) : ∀ (k : ℕ) (row : List ℕ), (nextRowTail n k row).length = row.length
  | _, [] => rfl
  | _, [_] => rfl
  | k, _ :: b :: rest => by
      simp only [nextRowTail, List.length_cons]
      rw [nextRowTail_length n (k + 1) (b :: rest)]
      rfl

private lemma nextRowTail_getD (n : ℕ) :
    ∀ (k : ℕ) (row : List ℕ) (j : ℕ), j < row.length →
      (nextRowTail n k row).getD j 0 =
        (k + j + 2) * row.getD (j + 1) 0 + (n - (k + j)) * row.getD j 0
  | _, [], _, hj => by simp at hj
  | k, [a], j, hj => by
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      simp [nextRowTail]
  | k, a :: b :: rest, j, hj => by
      cases j with
      | zero => simp [nextRowTail]
      | succ j =>
          simp only [nextRowTail, List.getD_cons_succ]
          have h := nextRowTail_getD n (k + 1) (b :: rest) j (by simpa using hj)
          simpa [show k + 1 + j = k + (j + 1) by omega] using h

private lemma nextEulerianRow_spec {n : ℕ} (hn : 1 ≤ n) {row : List ℕ}
    (hlen : row.length = n) (hget : ∀ k, row.getD k 0 = eulerian n k) :
    (nextEulerianRow n row).length = n + 1 ∧
      ∀ k, (nextEulerianRow n row).getD k 0 = eulerian (n + 1) k := by
  refine ⟨by simp [nextEulerianRow, nextRowTail_length, hlen], fun k => ?_⟩
  cases k with
  | zero =>
      simp only [nextEulerianRow, List.getD_cons_zero]
      exact (eulerian_zero_right (by omega)).symm
  | succ k =>
      simp only [nextEulerianRow, List.getD_cons_succ]
      by_cases hk : k < n
      · rw [nextRowTail_getD n 0 row k (by omega)]
        simp only [Nat.zero_add, hget]
        cases n with
        | zero => omega
        | succ m =>
            rw [eulerian_succ_succ]
      · rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [nextRowTail_length, hlen]; omega), Option.getD_none,
          eulerian_eq_zero_of_ge (by omega) (by omega)]

private lemma eulerianRowAux_spec :
    ∀ (steps curN : ℕ) (acc : List ℕ),
      1 ≤ curN → acc.length = curN → (∀ k, acc.getD k 0 = eulerian curN k) →
      (eulerianRowAux steps curN acc).length = curN + steps ∧
        ∀ k, (eulerianRowAux steps curN acc).getD k 0 = eulerian (curN + steps) k
  | 0, curN, acc, _, hlen, hget => ⟨by simpa [eulerianRowAux] using hlen, by simpa [eulerianRowAux] using hget⟩
  | steps + 1, curN, acc, hcur, hlen, hget => by
      obtain ⟨hlen', hget'⟩ := nextEulerianRow_spec hcur hlen hget
      obtain ⟨hL, hG⟩ := eulerianRowAux_spec steps (curN + 1) (nextEulerianRow curN acc)
        (by omega) hlen' hget'
      refine ⟨by rw [eulerianRowAux, hL]; omega, fun k => ?_⟩
      rw [eulerianRowAux, hG, show curN + 1 + steps = curN + (steps + 1) by omega]

private lemma eulerianRowAux_add :
    ∀ (a b curN : ℕ) (acc : List ℕ),
      eulerianRowAux (a + b) curN acc = eulerianRowAux b (curN + a) (eulerianRowAux a curN acc)
  | 0, b, curN, acc => by simp [eulerianRowAux]
  | a + 1, b, curN, acc => by
      rw [show a + 1 + b = (a + b) + 1 by omega, eulerianRowAux, eulerianRowAux,
        eulerianRowAux_add a b (curN + 1) (nextEulerianRow curN acc)]
      rw [show curN + 1 + a = curN + (a + 1) by omega]

private lemma eulerianRow_length (n : ℕ) : (eulerianRow n).length = n := by
  cases n with
  | zero => rfl
  | succ m =>
      have h := (eulerianRowAux_spec m 1 [1] le_rfl rfl (fun k => by cases k <;> simp [eulerian])).1
      simpa [eulerianRow, add_comm] using h

private lemma eulerianRow_getD (n k : ℕ) : (eulerianRow n).getD k 0 = eulerian n k := by
  cases n with
  | zero => simp [eulerianRow, eulerian]
  | succ m =>
      have h := (eulerianRowAux_spec m 1 [1] le_rfl rfl (fun j => by cases j <;> simp [eulerian])).2 k
      simpa [eulerianRow, add_comm] using h

/-- Homogeneous Horner evaluation of `q^(n - 1) * A_n(-p / q)` in `ℤ`. -/
private def evalHomog (row : List ℕ) (p q : ℤ) : ℤ :=
  (row.foldl (fun st (a : ℕ) => (st.1 * q + (a : ℤ) * st.2, st.2 * (-p))) (0, 1)).1

private lemma evalHomog_foldl (l : List ℕ) (p q acc ppow : ℤ) :
    (l.foldl (fun st (a : ℕ) => (st.1 * q + (a : ℤ) * st.2, st.2 * (-p))) (acc, ppow)).1 =
      acc * q ^ l.length +
        ppow * ∑ k ∈ range l.length, (l.getD k 0 : ℤ) * (-p) ^ k * q ^ (l.length - 1 - k) := by
  induction l generalizing acc ppow with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons, ih]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, Nat.sub_zero,
      Nat.succ_sub_succ_eq_sub, Nat.sub_sub]
    have htail : ppow * (-p) * ∑ k ∈ range t.length, (t.getD k 0 : ℤ) * (-p) ^ k * q ^ (t.length - (1 + k)) =
        ppow * ∑ k ∈ range t.length, (t.getD k 0 : ℤ) * (-p) ^ (k + 1) * q ^ (t.length - (k + 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.add_comm 1 k, pow_succ']; ring
    rw [htail, pow_succ' q t.length]
    generalize (∑ k ∈ range t.length, (t.getD k 0 : ℤ) * (-p) ^ (k + 1) * q ^ (t.length - (k + 1))) = S
    ring

private lemma evalHomog_eq_eulerianPoly {n : ℕ} (hn : 1 ≤ n) (p q : ℕ) (hq : 0 < q) :
    ((evalHomog (eulerianRow n) p q : ℤ) : ℝ) =
      (q : ℝ) ^ (n - 1) * (eulerianPoly n).eval (-((p : ℝ) / (q : ℝ))) := by
  unfold evalHomog
  rw [evalHomog_foldl, zero_mul, zero_add, one_mul, eulerianRow_length]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast]
  unfold eulerianPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [eulerianRow_getD n k]
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hpow : (q : ℝ) ^ (n - 1) = (q : ℝ) ^ k * (q : ℝ) ^ (n - 1 - k) := by
    rw [← pow_add, show k + (n - 1 - k) = n - 1 by omega]
  rw [← neg_div, div_pow, hpow]
  field_simp [hqne]

/-- Exact Boolean checker for a list of rational witnesses `(p, q)` satisfying Lemma 3.1. -/
private def checkStrictInc : List (ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | (p₁, q₁) :: (p₂, q₂) :: rest =>
      decide (p₁ * q₂ < p₂ * q₁) && checkStrictInc ((p₂, q₂) :: rest)

private def intPowAux : ℕ → ℤ → ℤ → ℕ → ℤ
  | 0, acc, _, _ => acc
  | fuel + 1, acc, b, e =>
      if e = 0 then acc
      else intPowAux fuel (if e % 2 = 1 then acc * b else acc) (b * b) (e / 2)

private lemma intPowAux_eq : ∀ (fuel : ℕ) (acc b : ℤ) (e : ℕ), e < 2 ^ fuel →
    intPowAux fuel acc b e = acc * b ^ e
  | 0, acc, b, e, he => by
      have : e = 0 := by omega
      subst this; simp [intPowAux]
  | fuel + 1, acc, b, e, he => by
      unfold intPowAux
      split_ifs with h0 hodd
      · subst h0; simp
      · have hlt : e / 2 < 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
          omega
        rw [intPowAux_eq fuel _ _ _ hlt]
        have heq : e = 2 * (e / 2) + 1 := by omega
        calc acc * b * (b * b) ^ (e / 2)
            = acc * (b * (b ^ 2) ^ (e / 2)) := by rw [sq]; ring
          _ = acc * (b * b ^ (2 * (e / 2))) := by rw [← pow_mul]
          _ = acc * b ^ (2 * (e / 2) + 1) := by rw [pow_succ']
          _ = acc * b ^ e := by rw [← heq]
      · have hlt : e / 2 < 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
          omega
        rw [intPowAux_eq fuel _ _ _ hlt]
        have heq : e = 2 * (e / 2) := by omega
        calc acc * (b * b) ^ (e / 2)
            = acc * (b ^ 2) ^ (e / 2) := by rw [sq]
          _ = acc * b ^ (2 * (e / 2)) := by rw [← pow_mul]
          _ = acc * b ^ e := by rw [← heq]

private def intPowBin (x : ℤ) (n : ℕ) : ℤ := intPowAux n 1 x n

private lemma intPowBin_eq (x : ℤ) (n : ℕ) : intPowBin x n = x ^ n := by
  unfold intPowBin
  rw [intPowAux_eq n 1 x n Nat.lt_two_pow_self, one_mul]

private lemma evalHomog_foldl_snd (l : List ℕ) (p q acc ppow : ℤ) :
    (l.foldl (fun st (a : ℕ) => (st.1 * q + (a : ℤ) * st.2, st.2 * (-p))) (acc, ppow)).2 =
      ppow * (-p) ^ l.length := by
  induction l generalizing acc ppow with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons, ih, pow_succ']
    ring

private lemma evalHomog_append (l₁ l₂ : List ℕ) (p q : ℤ) :
    evalHomog (l₁ ++ l₂) p q =
      evalHomog l₁ p q * q ^ l₂.length + (-p) ^ l₁.length * evalHomog l₂ p q := by
  unfold evalHomog
  rw [List.foldl_append, evalHomog_foldl, evalHomog_foldl_snd, one_mul]
  rw [evalHomog_foldl l₂ p q 0 1, zero_mul, zero_add, one_mul]

/-- 4-way chunked Horner evaluation (each chunk ≤ 16 elements) keeping kernel WHNF depth well below 512. -/
private def evalHomogFast (row : List ℕ) (p q : ℤ) : ℤ :=
  let c0 := row.take 16
  let r1 := row.drop 16
  let c1 := r1.take 16
  let r2 := r1.drop 16
  let c2 := r2.take 16
  let c3 := r2.drop 16
  let v0 := evalHomog c0 p q
  let v1 := evalHomog c1 p q
  let v2 := evalHomog c2 p q
  let v3 := evalHomog c3 p q
  let s01 := v0 * intPowBin q c1.length + intPowBin (-p) c0.length * v1
  let s23 := v2 * intPowBin q c3.length + intPowBin (-p) c2.length * v3
  s01 * intPowBin q (c2.length + c3.length) + intPowBin (-p) (c0.length + c1.length) * s23

private lemma evalHomogFast_eq (row : List ℕ) (p q : ℤ) :
    evalHomogFast row p q = evalHomog row p q := by
  unfold evalHomogFast
  dsimp only
  simp only [intPowBin_eq]
  set c0 := row.take 16
  set r1 := row.drop 16
  set c1 := r1.take 16
  set r2 := r1.drop 16
  set c2 := r2.take 16
  set c3 := r2.drop 16
  have hrow : (c0 ++ c1) ++ (c2 ++ c3) = row := by
    rw [List.append_assoc, List.take_append_drop 16 r2, List.take_append_drop 16 r1,
      List.take_append_drop 16 row]
  rw [← hrow, evalHomog_append (c0 ++ c1) (c2 ++ c3), evalHomog_append c0 c1,
    evalHomog_append c2 c3, List.length_append, List.length_append]

private def checkConds (row : List ℕ) (n : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | m, (p, q) :: rest =>
      let s := evalHomogFast row (p : ℤ) (q : ℤ)
      let lhs := (if m % 2 = 0 then (1 : ℤ) else -1) * ((p : ℤ) + (q : ℤ)) * s
      decide (0 < p ∧ 0 < q ∧ (if n % 2 = 0 then p < q else p ≤ q) ∧ intPowBin (q : ℤ) n < lhs) &&
        checkConds row n (m + 1) rest

private def checkRow (n : ℕ) (pts : List (ℕ × ℕ)) : Bool :=
  let row := eulerianRow n
  decide (pts.length = (n - 1) / 2) && checkStrictInc pts && checkConds row n 1 pts

private lemma checkStrictInc_sound :
    ∀ {l : List (ℕ × ℕ)}, checkStrictInc l = true →
      ∀ (i j : Fin l.length), i < j →
        ((l[i].1 : ℝ) / (l[i].2 : ℝ)) < ((l[j].1 : ℝ) / (l[j].2 : ℝ)) →
        True := fun _ _ _ _ _ => trivial

private lemma checkStrictInc_adj :
    ∀ (l : List (ℕ × ℕ)), checkStrictInc l = true →
      ∀ (i : ℕ) (hi : i + 1 < l.length),
        l[i].1 * l[i + 1].2 < l[i + 1].1 * l[i].2 := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons a t ih =>
    cases t with
    | nil => intro _ i hi; simp at hi
    | cons b r =>
      intro h i hi
      simp only [checkStrictInc, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero => exact h.1
      | succ i => exact ih h.2 i (by simpa using hi)

private lemma checkConds_sound (row : List ℕ) (n : ℕ) :
    ∀ (m : ℕ) (l : List (ℕ × ℕ)), checkConds row n m l = true →
      ∀ (i : ℕ) (hi : i < l.length),
        let p := l[i].1
        let q := l[i].2
        0 < p ∧ 0 < q ∧ (if n % 2 = 0 then p < q else p ≤ q) ∧
          (q : ℤ) ^ n < (if (m + i) % 2 = 0 then (1 : ℤ) else -1) * ((p : ℤ) + (q : ℤ)) *
            evalHomog row (p : ℤ) (q : ℤ) := by
  intro m l
  induction l generalizing m with
  | nil => intro _ i hi; simp at hi
  | cons a t ih =>
    intro h i hi
    rcases a with ⟨p, q⟩
    simp only [checkConds, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero =>
        rw [intPowBin_eq, evalHomogFast_eq] at h
        simpa using h.1
    | succ i =>
      have hres := ih (m + 1) h.2 i (by simpa using hi)
      simpa [show m + 1 + i = m + (i + 1) by omega] using hres

private lemma checkRow_sound {n : ℕ} (hn : 3 ≤ n) (pts : List (ℕ × ℕ)) (h : checkRow n pts = true) :
    ∃ S : Finset ℝ, S.card = n ∧
      (∀ t ∈ S, (charPoly n).IsRoot t) ∧
      (1 : ℝ) ∈ S ∧
      (S.filter (fun t => 0 < t ∧ t < 1)).card = n - 2 ∧
      (S.filter (fun t => 1 < t)).card = 1 := by
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hlen, hinc⟩, hconds⟩
  let σ : Fin ((n - 1) / 2) → ℝ := fun j =>
    let pr := pts[j.val]'(by omega)
    (pr.1 : ℝ) / (pr.2 : ℝ)
  have hcond_i : ∀ j : Fin ((n - 1) / 2),
      0 < (pts[j.val]'(by omega)).1 ∧ 0 < (pts[j.val]'(by omega)).2 ∧
      (if n % 2 = 0 then (pts[j.val]'(by omega)).1 < (pts[j.val]'(by omega)).2
        else (pts[j.val]'(by omega)).1 ≤ (pts[j.val]'(by omega)).2) ∧
      ((pts[j.val]'(by omega)).2 : ℤ) ^ n <
        (if (1 + j.val) % 2 = 0 then (1 : ℤ) else -1) *
          (((pts[j.val]'(by omega)).1 : ℤ) + ((pts[j.val]'(by omega)).2 : ℤ)) *
          evalHomog (eulerianRow n) ((pts[j.val]'(by omega)).1 : ℤ) ((pts[j.val]'(by omega)).2 : ℤ) :=
    fun j => checkConds_sound (eulerianRow n) n 1 pts hconds j.val (by omega)
  refine paired_sign_alternation hn σ ?_ ?_ ?_ ?_ ?_
  · intro j; dsimp [σ]; have hc := hcond_i j; exact div_pos (by exact_mod_cast hc.1) (by exact_mod_cast hc.2.1)
  · -- Strict monotonicity from adjacent strict inequalities `p_i * q_{i+1} < p_{i+1} * q_i`!
    have hadj : ∀ (i : ℕ) (hi : i + 1 < (n - 1) / 2),
        σ ⟨i, by omega⟩ < σ ⟨i + 1, hi⟩ := by
      intro i hi
      dsimp [σ]
      have h1 := checkStrictInc_adj pts hinc i (by omega)
      have hq1 : (0 : ℝ) < ((pts[i]'(by omega)).2 : ℝ) := by exact_mod_cast (hcond_i ⟨i, by omega⟩).2.1
      have hq2 : (0 : ℝ) < ((pts[i + 1]'(by omega)).2 : ℝ) := by exact_mod_cast (hcond_i ⟨i + 1, hi⟩).2.1
      rw [div_lt_div_iff₀ hq1 hq2]
      exact_mod_cast h1
    intro j₁ j₂ hlt
    have hstep : ∀ d : ℕ, ∀ (a : ℕ) (hb : a + d + 1 < (n - 1) / 2),
        σ ⟨a, by omega⟩ < σ ⟨a + d + 1, hb⟩ := by
      intro d
      induction d with
      | zero => intro a hb; exact hadj a hb
      | succ d ih =>
        intro a hb
        exact lt_trans (ih a (by omega)) (hadj (a + d + 1) (by omega))
    have hd := hstep (j₂.val - j₁.val - 1) j₁.val (by have := j₂.isLt; have : j₁.val < j₂.val := hlt; omega)
    have hfin1 : (⟨j₁.val, j₁.isLt⟩ : Fin ((n - 1) / 2)) = j₁ := Fin.ext rfl
    have hfin2 : (⟨j₁.val + (j₂.val - j₁.val - 1) + 1, by have := j₂.isLt; have : j₁.val < j₂.val := hlt; omega⟩ : Fin ((n - 1) / 2)) = j₂ :=
      Fin.ext (by dsimp only; have : j₁.val < j₂.val := hlt; omega)
    rwa [hfin1, hfin2] at hd
  · intro j; dsimp [σ]
    have hc := hcond_i j
    have hq : (0 : ℝ) < ((pts[j.val]'(by omega)).2 : ℝ) := by exact_mod_cast hc.2.1
    rw [div_le_one hq]
    by_cases hmod : n % 2 = 0
    · rw [if_pos hmod] at hc; exact_mod_cast hc.2.2.1.le
    · rw [if_neg hmod] at hc; exact_mod_cast hc.2.2.1
  · intro he j; dsimp [σ]
    have hc := hcond_i j
    have hq : (0 : ℝ) < ((pts[j.val]'(by omega)).2 : ℝ) := by exact_mod_cast hc.2.1
    have hmod : n % 2 = 0 := Nat.even_iff.mp he
    rw [div_lt_one hq]
    rw [if_pos hmod] at hc
    exact_mod_cast hc.2.2.1
  · intro j; dsimp [σ]
    have hc := hcond_i j
    set p := (pts[j.val]'(by omega)).1
    set q := (pts[j.val]'(by omega)).2
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hc.2.1
    have hZ : ((q : ℤ) ^ n : ℝ) <
        (((if (1 + j.val) % 2 = 0 then (1 : ℤ) else -1) * ((p : ℤ) + (q : ℤ)) *
          evalHomog (eulerianRow n) (p : ℤ) (q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hc.2.2.2
    have hsign : ((if (1 + j.val) % 2 = 0 then (1 : ℤ) else -1 : ℤ) : ℝ) = (-1 : ℝ) ^ (j.val + 1) := by
      rw [show 1 + j.val = j.val + 1 by omega]
      rcases Nat.even_or_odd (j.val + 1) with he | ho
      · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow]; norm_num
      · rw [if_neg (by rw [Nat.odd_iff.mp ho]; decide), ho.neg_one_pow]; norm_num
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast] at hZ
    rw [hsign, evalHomog_eq_eulerianPoly (by omega) p q hc.2.1] at hZ
    have hqn_pos : (0 : ℝ) < (q : ℝ) ^ n := pow_pos hq_pos n
    have hrew : (-1 : ℝ) ^ (j.val + 1) * ((p : ℝ) + (q : ℝ)) *
        ((q : ℝ) ^ (n - 1) * (eulerianPoly n).eval (-((p : ℝ) / (q : ℝ)))) =
        (q : ℝ) ^ n * ((-1 : ℝ) ^ (j.val + 1) * ((1 + (p : ℝ) / (q : ℝ)) *
          (eulerianPoly n).eval (-((p : ℝ) / (q : ℝ))))) := by
      have hqn : (q : ℝ) ^ n = (q : ℝ) * (q : ℝ) ^ (n - 1) := by
        rw [← pow_succ', show n - 1 + 1 = n by omega]
      rw [hqn]; field_simp [hq_pos.ne']; ring
    rw [hrew] at hZ
    exact (lt_mul_iff_one_lt_right hqn_pos).mp (by linarith)

/-- Exact compact rational witness table for `3 ≤ n ≤ 63`. -/
private def finiteWitness : ℕ → List (ℕ × ℕ)
  | 3 => [(1, 1)]
  | 4 => [(1, 3)]
  | 5 => [(1, 5), (1, 1)]
  | 6 => [(1, 10), (1, 2)]
  | 7 => [(1, 23), (1, 4), (1, 1)]
  | 8 => [(1, 42), (1, 5), (3, 5)]
  | 9 => [(1, 75), (1, 5), (1, 3), (1, 1)]
  | 10 => [(1, 133), (1, 10), (1, 4), (2, 3)]
  | 11 => [(1, 231), (1, 23), (1, 5), (2, 5), (1, 1)]
  | 12 => [(1, 398), (1, 35), (1, 9), (1, 3), (2, 3)]
  | 13 => [(1, 681), (1, 51), (1, 10), (1, 5), (1, 2), (1, 1)]
  | 14 => [(1, 1160), (1, 75), (1, 10), (1, 5), (1, 3), (3, 4)]
  | 15 => [(1, 1967), (1, 110), (1, 23), (1, 8), (1, 4), (1, 2), (1, 1)]
  | 16 => [(1, 6561), (1, 160), (1, 31), (1, 10), (1, 5), (2, 5), (3, 4)]
  | 17 => [(1, 11364), (1, 231), (1, 42), (1, 10), (1, 5), (1, 3), (3, 5), (1, 1)]
  | 18 => [(1, 19683), (1, 332), (1, 57), (1, 18), (1, 8), (1, 4), (1, 2), (3, 4)]
  | 19 => [(1, 34092), (1, 476), (1, 75), (1, 23), (1, 10), (1, 5), (1, 3), (3, 5), (1, 1)]
  | 20 => [(1, 59049), (1, 681), (1, 100), (1, 30), (1, 10), (1, 5), (1, 4), (1, 2), (4, 5)]
  | 21 => [(1, 102276), (1, 972), (1, 133), (1, 38), (1, 15), (1, 8), (1, 4), (2, 5), (2, 3), (1, 1)]
  | 22 => [(1, 177147), (1, 1384), (1, 175), (1, 48), (1, 19), (1, 9), (1, 5), (1, 3), (1, 2), (4, 5)]
  | 23 => [(1, 306828), (1, 1967), (1, 231), (1, 60), (1, 23), (1, 10), (1, 5), (1, 4), (2, 5), (2, 3), (1, 1)]
  | 24 => [(1, 531441), (1, 2793), (1, 303), (1, 75), (1, 28), (1, 10), (1, 7), (1, 4), (1, 3), (1, 2), (4, 5)]
  | 25 => [(1, 920483), (1, 3959), (1, 398), (1, 95), (1, 35), (1, 16), (1, 9), (1, 5), (1, 3), (1, 2), (2, 3), (1, 1)]
  | 26 => [(1, 1594323), (1, 5605), (1, 521), (1, 119), (1, 42), (1, 19), (1, 10), (1, 5), (1, 4), (2, 5), (3, 5), (4, 5)]
  | 27 => [(1, 2761448), (1, 7928), (1, 681), (1, 148), (1, 51), (1, 23), (1, 10), (1, 7), (1, 5), (1, 3), (1, 2), (2, 3), (1, 1)]
  | 28 => [(1, 4782969), (1, 11203), (1, 889), (1, 185), (1, 62), (1, 28), (1, 14), (1, 8), (1, 5), (1, 4), (2, 5), (3, 5), (4, 5)]
  | 29 => [(1, 8284345), (1, 15817), (1, 1160), (1, 231), (1, 75), (1, 33), (1, 17), (1, 10), (1, 5), (1, 4), (1, 3), (1, 2), (3, 4), (1, 1)]
  | 30 => [(1, 14348907), (1, 22314), (1, 1511), (1, 287), (1, 91), (1, 39), (1, 20), (1, 10), (1, 7), (1, 5), (1, 3), (2, 5), (3, 5), (4, 5)]
  | 31 => [(1, 24853036), (1, 31459), (1, 1967), (1, 357), (1, 110), (1, 46), (1, 23), (1, 13), (1, 8), (1, 5), (1, 4), (2, 5), (1, 2), (3, 4), (1, 1)]
  | 32 => [(1, 43046721), (1, 44324), (1, 2559), (1, 443), (1, 133), (1, 54), (1, 27), (1, 15), (1, 9), (1, 6), (1, 4), (1, 3), (1, 2), (2, 3), (4, 5)]
  | 33 => [(1, 74559108), (1, 62414), (1, 3326), (1, 550), (1, 160), (1, 64), (1, 31), (1, 18), (1, 10), (1, 7), (1, 5), (1, 3), (2, 5), (3, 5), (3, 4), (1, 1)]
  | 34 => [(1, 129140163), (1, 87843), (1, 4319), (1, 681), (1, 192), (1, 75), (1, 36), (1, 20), (1, 10), (1, 8), (1, 5), (1, 4), (1, 3), (1, 2), (2, 3), (4, 5)]
  | 35 => [(1, 223677324), (1, 123573), (1, 5605), (1, 843), (1, 231), (1, 89), (1, 42), (1, 23), (1, 14), (1, 9), (1, 6), (1, 4), (1, 3), (2, 5), (3, 5), (3, 4), (1, 1)]
  | 36 => [(1, 387420489), (1, 262144), (1, 7270), (1, 1043), (1, 277), (1, 104), (1, 49), (1, 27), (1, 16), (1, 10), (1, 7), (1, 5), (1, 4), (2, 5), (1, 2), (2, 3), (4, 5)]
  | 37 => [(1, 671031971), (1, 370728), (1, 9425), (1, 1290), (1, 332), (1, 123), (1, 57), (1, 30), (1, 18), (1, 10), (1, 8), (1, 5), (1, 4), (1, 3), (1, 2), (3, 5), (3, 4), (1, 1)]
  | 38 => [(1, 1162261467), (1, 524288), (1, 12213), (1, 1593), (1, 398), (1, 144), (1, 65), (1, 35), (1, 20), (1, 13), (1, 9), (1, 6), (1, 4), (1, 3), (2, 5), (1, 2), (2, 3), (4, 5)]
  | 39 => [(1, 2013095913), (1, 741455), (1, 15817), (1, 1967), (1, 476), (1, 168), (1, 75), (1, 40), (1, 23), (1, 15), (1, 10), (1, 7), (1, 5), (1, 4), (1, 3), (1, 2), (3, 5), (4, 5), (1, 1)]
  | 40 => [(1, 3486784401), (1, 1048576), (1, 20476), (1, 2428), (1, 570), (1, 197), (1, 87), (1, 45), (1, 26), (1, 16), (1, 10), (1, 8), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (2, 3), (4, 5)]
  | 41 => [(1, 6039287738), (1, 1482910), (1, 26497), (1, 2995), (1, 681), (1, 231), (1, 100), (1, 51), (1, 30), (1, 18), (1, 12), (1, 9), (1, 6), (1, 5), (2, 7), (2, 5), (1, 2), (3, 5), (4, 5), (1, 1)]
  | 42 => [(1, 10460353203), (1, 2097152), (1, 34276), (1, 3692), (1, 814), (1, 270), (1, 115), (1, 58), (1, 33), (1, 21), (1, 14), (1, 9), (1, 7), (1, 5), (1, 4), (1, 3), (2, 5), (3, 5), (2, 3), (4, 5)]
  | 43 => [(1, 18117863213), (1, 2965821), (1, 44324), (1, 4550), (1, 972), (1, 315), (1, 133), (1, 66), (1, 38), (1, 23), (1, 15), (1, 10), (1, 8), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (2, 3), (4, 5), (1, 1)]
  | 44 => [(1, 31381059609), (1, 4194304), (1, 57299), (1, 5605), (1, 1160), (1, 368), (1, 153), (1, 75), (1, 42), (1, 26), (1, 17), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (3, 5), (3, 4), (9, 10)]
  | 45 => [(1, 54353589638), (1, 5931642), (1, 74050), (1, 6902), (1, 1384), (1, 430), (1, 175), (1, 86), (1, 48), (1, 29), (1, 19), (1, 13), (1, 9), (1, 7), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (2, 3), (4, 5), (1, 1)]
  | 46 => [(1, 94143178827), (1, 8388608), (1, 95671), (1, 8496), (1, 1650), (1, 501), (1, 201), (1, 97), (1, 53), (1, 32), (1, 21), (1, 14), (1, 10), (1, 7), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (3, 4), (9, 10)]
  | 47 => [(1, 163060768914), (1, 11863283), (1, 123573), (1, 10455), (1, 1967), (1, 584), (1, 231), (1, 110), (1, 60), (1, 36), (1, 23), (1, 16), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (2, 3), (4, 5), (1, 1)]
  | 48 => [(1, 282429536481), (1, 16777216), (1, 159573), (1, 12861), (1, 2344), (1, 681), (1, 265), (1, 125), (1, 67), (1, 40), (1, 26), (1, 17), (1, 12), (1, 9), (1, 7), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (3, 4), (9, 10)]
  | 49 => [(1, 489182306743), (1, 23726566), (1, 206013), (1, 15817), (1, 2793), (1, 793), (1, 303), (1, 141), (1, 75), (1, 45), (1, 28), (1, 19), (1, 13), (1, 10), (1, 7), (1, 5), (1, 4), (2, 7), (1, 3), (4, 9), (1, 2), (2, 3), (4, 5), (1, 1)]
  | 50 => [(1, 847288609443), (1, 33554432), (1, 265912), (1, 19446), (1, 3326), (1, 924), (1, 347), (1, 160), (1, 85), (1, 50), (1, 31), (1, 21), (1, 15), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (3, 4), (9, 10)]
  | 51 => [(1, 1467546920230), (1, 47453133), (1, 343157), (1, 23902), (1, 3959), (1, 1075), (1, 398), (1, 181), (1, 95), (1, 55), (1, 35), (1, 23), (1, 16), (1, 12), (1, 9), (1, 7), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (4, 5), (1, 1)]
  | 52 => [(1, 2541865828329), (1, 67108864), (1, 442755), (1, 29372), (1, 4711), (1, 1251), (1, 455), (1, 204), (1, 106), (1, 61), (1, 38), (1, 25), (1, 18), (1, 13), (1, 10), (1, 7), (1, 6), (1, 5), (2, 7), (1, 3), (2, 5), (1, 2), (3, 5), (3, 4), (9, 10)]
  | 53 => [(1, 4402640760689), (1, 94906266), (1, 571158), (1, 36086), (1, 5605), (1, 1455), (1, 521), (1, 231), (1, 119), (1, 68), (1, 42), (1, 28), (1, 19), (1, 14), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (4, 5), (1, 1)]
  | 54 => [(1, 7625597484987), (1, 134217728), (1, 736673), (1, 44324), (1, 6667), (1, 1692), (1, 596), (1, 261), (1, 133), (1, 75), (1, 47), (1, 31), (1, 21), (1, 15), (1, 10), (1, 9), (1, 7), (1, 5), (1, 4), (3, 10), (1, 3), (2, 5), (1, 2), (2, 3), (3, 4), (9, 10)]
  | 55 => [(1, 13207922282067), (1, 189812531), (1, 950000), (1, 54432), (1, 7928), (1, 1967), (1, 681), (1, 294), (1, 148), (1, 84), (1, 51), (1, 34), (1, 23), (1, 17), (1, 12), (1, 9), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (4, 5), (1, 1)]
  | 56 => [(1, 22876792454961), (1, 268435456), (1, 1224913), (1, 66832), (1, 9425), (1, 2286), (1, 778), (1, 332), (1, 166), (1, 93), (1, 57), (1, 37), (1, 25), (1, 18), (1, 13), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (4, 9), (1, 2), (2, 3), (3, 4), (9, 10)]
  | 57 => [(1, 39623766846201), (1, 379625062), (1, 1579153), (1, 82043), (1, 11203), (1, 2657), (1, 889), (1, 375), (1, 185), (1, 103), (1, 62), (1, 40), (1, 28), (1, 20), (1, 14), (1, 10), (1, 8), (1, 7), (1, 5), (1, 4), (2, 7), (1, 3), (2, 5), (1, 2), (3, 5), (3, 4), (4, 5), (1, 1)]
  | 58 => [(1, 68630377364883), (1, 536870912), (1, 2035558), (1, 100697), (1, 13313), (1, 3086), (1, 1016), (1, 422), (1, 207), (1, 114), (1, 69), (1, 44), (1, 30), (1, 21), (1, 16), (1, 12), (1, 9), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (4, 5), (9, 10)]
  | 59 => [(1, 118871300538603), (1, 759250125), (1, 2623530), (1, 123573), (1, 15817), (1, 3584), (1, 1160), (1, 476), (1, 231), (1, 126), (1, 75), (1, 48), (1, 33), (1, 23), (1, 17), (1, 13), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (3, 10), (1, 3), (2, 5), (1, 2), (3, 5), (3, 4), (4, 5), (1, 1)]
  | 60 => [(1, 205891132094649), (1, 1073741824), (1, 3380919), (1, 151621), (1, 18788), (1, 4161), (1, 1324), (1, 537), (1, 257), (1, 140), (1, 83), (1, 53), (1, 36), (1, 25), (1, 18), (1, 14), (1, 10), (1, 8), (1, 7), (1, 5), (1, 4), (2, 7), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (4, 5), (9, 10)]
  | 61 => [(1, 356613901615808), (1, 1518500250), (1, 4356445), (1, 186008), (1, 22314), (1, 4830), (1, 1511), (1, 605), (1, 287), (1, 155), (1, 91), (1, 58), (1, 39), (1, 27), (1, 20), (1, 15), (1, 11), (1, 9), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (2, 5), (4, 9), (1, 2), (3, 5), (3, 4), (4, 5), (1, 1)]
  | 62 => [(1, 617673396283948), (1, 2147483648), (1, 5612817), (1, 228162), (1, 26497), (1, 5605), (1, 1725), (1, 681), (1, 320), (1, 171), (1, 100), (1, 63), (1, 42), (1, 30), (1, 21), (1, 16), (1, 12), (1, 10), (1, 8), (1, 6), (1, 5), (1, 4), (2, 7), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (4, 5), (9, 10)]
  | 63 => [(1, 1069841704847423), (1, 3037000500), (1, 7230746), (1, 279831), (1, 31459), (1, 6504), (1, 1967), (1, 767), (1, 357), (1, 189), (1, 110), (1, 69), (1, 46), (1, 32), (1, 23), (1, 17), (1, 13), (1, 10), (1, 8), (1, 7), (1, 5), (2, 9), (1, 4), (1, 3), (2, 5), (4, 9), (1, 2), (3, 5), (3, 4), (4, 5), (1, 1)]
  | _ => []

private def checkRange (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun d => checkRow (lo + d) (finiteWitness (lo + d))

private lemma checkRange_sound {lo hi n : ℕ} (h : checkRange lo hi = true)
    (hlo : lo ≤ n) (hhi : n ≤ hi) : checkRow n (finiteWitness n) = true := by
  simp only [checkRange, List.all_eq_true] at h
  have hmem : n - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
  have hres := h (n - lo) hmem
  rwa [show lo + (n - lo) = n by omega] at hres

private def checkRowWith (n : ℕ) (row : List ℕ) (pts : List (ℕ × ℕ)) : Bool :=
  decide (pts.length = (n - 1) / 2) && checkStrictInc pts && checkConds row n 1 pts

private def checkRangeFrom (baseN : ℕ) (baseRow : List ℕ) (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun d =>
    checkRowWith (lo + d) (eulerianRowAux (lo + d - baseN) baseN baseRow) (finiteWitness (lo + d))

private lemma checkRangeFrom_sound {baseN lo hi n : ℕ} {baseRow : List ℕ}
    (hbase : 1 ≤ baseN) (hrow : baseRow = eulerianRow baseN)
    (h : checkRangeFrom baseN baseRow lo hi = true)
    (hlo : lo ≤ n) (hhi : n ≤ hi) (hge : baseN ≤ n) :
    checkRow n (finiteWitness n) = true := by
  simp only [checkRangeFrom, List.all_eq_true] at h
  have hmem : n - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
  have hres := h (n - lo) hmem
  rw [show lo + (n - lo) = n by omega] at hres
  have hrow_eq : eulerianRowAux (n - baseN) baseN baseRow = eulerianRow n := by
    rw [hrow]
    obtain ⟨b, rfl⟩ : ∃ b, baseN = b + 1 := ⟨baseN - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [eulerianRow]
    rw [show b + 1 = 1 + b by omega, ← eulerianRowAux_add b (m + 1 - (1 + b)) 1 [1]]
    congr 1; omega
  rw [checkRowWith, hrow_eq] at hres
  exact hres

private def row35 : List ℕ :=
  [1, 34359738332, 50030308148419089, 1178790506740482478672, 2867913266955627392331656,
   1615040425602025180672284864, 318757258316419080126709062568, 27989650278522800110059077461616,
   1269374615284646274801719399013708, 32837639431530854694836971446705744,
   519270741908117572997406349883600940, 5275503148838103540007312119919120080,
   35713299412878610033189961245712022360, 165503870665618157854692853784484809280,
   535560662821763470729690696983372654840, 1227429970800242690782439881800572500080,
   2011492039263687260482578884082595621110, 2370090462028127583959660651254744350120,
   2011492039263687260482578884082595621110, 1227429970800242690782439881800572500080,
   535560662821763470729690696983372654840, 165503870665618157854692853784484809280,
   35713299412878610033189961245712022360, 5275503148838103540007312119919120080,
   519270741908117572997406349883600940, 32837639431530854694836971446705744,
   1269374615284646274801719399013708, 27989650278522800110059077461616,
   318757258316419080126709062568, 1615040425602025180672284864, 2867913266955627392331656,
   1178790506740482478672, 50030308148419089, 34359738332, 1]

private def row50 : List ℕ :=
  [1, 1125899906842573, 717897930270957339797700, 1267613987432292639395900247452,
   88753192704720794394660692268464024, 803753183763858487638377648106141554016,
   1757355913846576598446205532734432978906868, 1336554684844934608858783166160786304268141100,
   444864121068380557793978904032845497798039828582, 75498235997230016813661642238077850874365008450934,
   7266916733014599040459261010061040195977970294607836,
   428470187487066113129810249254070807227225893663487428,
   16390993922890751875470979921017318658729129853019704000,
   425096843324522075512498394852281574044365286905816938072,
   7734799668367827420288253468655912661854906883679881985164,
   101453922038683361826222363040575044079888915412097483020116,
   980338372205097496253132589683085281303505603067304935966443,
   7101842682906158577787309780410007146690133858162081455548775,
   39119982797009368551151098283083487292006961026026448113272232,
   165736239820677065189993668815989014181722152523481080390812184,
   545001660138669461244879865846330177632798984081701884687520976,
   1401093747032471437503583544688784309219668500032195602977654048,
   2831503819422074539379983626819356079704609248161745743516417800,
   4516275432171902321885986373717344575189606027327491621670762552,
   5700123907773416224716099708737159306764363732140229880240069124,
   5700123907773416224716099708737159306764363732140229880240069124,
   4516275432171902321885986373717344575189606027327491621670762552,
   2831503819422074539379983626819356079704609248161745743516417800,
   1401093747032471437503583544688784309219668500032195602977654048,
   545001660138669461244879865846330177632798984081701884687520976,
   165736239820677065189993668815989014181722152523481080390812184,
   39119982797009368551151098283083487292006961026026448113272232,
   7101842682906158577787309780410007146690133858162081455548775,
   980338372205097496253132589683085281303505603067304935966443,
   101453922038683361826222363040575044079888915412097483020116,
   7734799668367827420288253468655912661854906883679881985164,
   425096843324522075512498394852281574044365286905816938072,
   16390993922890751875470979921017318658729129853019704000,
   428470187487066113129810249254070807227225893663487428,
   7266916733014599040459261010061040195977970294607836,
   75498235997230016813661642238077850874365008450934,
   444864121068380557793978904032845497798039828582, 1336554684844934608858783166160786304268141100,
   1757355913846576598446205532734432978906868, 803753183763858487638377648106141554016,
   88753192704720794394660692268464024, 1267613987432292639395900247452,
   717897930270957339797700, 1125899906842573, 1]

private def row42 : List ℕ :=
  [1, 4398046511061, 109418800015512382640, 19338108101272847763367400,
   226542033284630104070228871210, 471470200564218037937853849449482,
   291485680471184264902975952296298472, 72087478872930620985092381768986855920,
   8590280977227734028070099963914696614625, 558209696555872673346126887973332216806205,
   21563063076955887867865577067072989377842048, 527080363941869368208835173671643388495035488,
   8540772224057843609162723215660122123313762840, 95044459024578181623718760163322740580801248600,
   746451000812745471365152854703161400788915774560,
   4225793784835780043520569522090674129161350717184,
   17529812355349651372760285265281610578064099426594,
   53961709746332801275431885486019481235946095407850,
   124434664099100825339383513018662780583567851660000,
   216410024586259695592852002082062778158467727404400,
   285090468862200438356418365594138405888960374563420,
   285090468862200438356418365594138405888960374563420,
   216410024586259695592852002082062778158467727404400,
   124434664099100825339383513018662780583567851660000,
   53961709746332801275431885486019481235946095407850,
   17529812355349651372760285265281610578064099426594,
   4225793784835780043520569522090674129161350717184,
   746451000812745471365152854703161400788915774560,
   95044459024578181623718760163322740580801248600, 8540772224057843609162723215660122123313762840,
   527080363941869368208835173671643388495035488, 21563063076955887867865577067072989377842048,
   558209696555872673346126887973332216806205, 8590280977227734028070099963914696614625,
   72087478872930620985092381768986855920, 291485680471184264902975952296298472,
   471470200564218037937853849449482, 226542033284630104070228871210, 19338108101272847763367400,
   109418800015512382640, 4398046511061, 1]

private def row56 : List ℕ :=
  [1, 72057594037927879, 523347628920077677051620765, 5192267027719860072899959692019995,
   1387482820695772010557975562665753220319, 37632076177781962679732115478122882354466041,
   209440291782393545647084790638618348854223639995,
   362144071594981889129563440749506445499803250820845,
   252903104054330031190216949882430808844741285833167630,
   84979071865139003922242261577016021039433917756042634850,
   15522774448521645313173633687366310429712768225430198128310,
   1683708252091473933679371503000126656642445580320038341456090,
   115822332554450949159605550584412960226247154135535904383002570,
   5313856101843022396467530134201962553826870190123026925659913030,
   169120205505520836318196459105133090445361686100329147996071501970,
   3852274686375396367944325412200475277099856732557882657377932211550,
   64402886228425151076084995027356264470489104977886598229841241725355,
   806604850600203070022289589303819880579962480264707314579782020052845,
   7696445201737018611252180021774141409740758570382179040060920195021055,
   56731163016884874018744197855829983725038791399090091210332213177306985,
   326768185077204975340845233698731409510144949137850427705171812758997565,
   1484774840425348655887906715345450152239944370536593006870591093240944075,
   5363707018032764823555541205919783023118957555490686328114551324601277745,
   15502428475056920908312089972143779616017382300783081244117277575654851655,
   36029140100409585264076163304580722628779308140733264459085212930102592180,
   67595416429580795468779823480596243405744634764666823487778067623465180908,
   102665058337707451524669479227918203674072831779712261846508358675481894052,
   126466697873359934153976324912726771940573576362303543362700944057234423740,
   126466697873359934153976324912726771940573576362303543362700944057234423740,
   102665058337707451524669479227918203674072831779712261846508358675481894052,
   67595416429580795468779823480596243405744634764666823487778067623465180908,
   36029140100409585264076163304580722628779308140733264459085212930102592180,
   15502428475056920908312089972143779616017382300783081244117277575654851655,
   5363707018032764823555541205919783023118957555490686328114551324601277745,
   1484774840425348655887906715345450152239944370536593006870591093240944075,
   326768185077204975340845233698731409510144949137850427705171812758997565,
   56731163016884874018744197855829983725038791399090091210332213177306985,
   7696445201737018611252180021774141409740758570382179040060920195021055,
   806604850600203070022289589303819880579962480264707314579782020052845,
   64402886228425151076084995027356264470489104977886598229841241725355,
   3852274686375396367944325412200475277099856732557882657377932211550,
   169120205505520836318196459105133090445361686100329147996071501970,
   5313856101843022396467530134201962553826870190123026925659913030,
   115822332554450949159605550584412960226247154135535904383002570,
   1683708252091473933679371503000126656642445580320038341456090,
   15522774448521645313173633687366310429712768225430198128310,
   84979071865139003922242261577016021039433917756042634850,
   252903104054330031190216949882430808844741285833167630,
   362144071594981889129563440749506445499803250820845,
   209440291782393545647084790638618348854223639995,
   37632076177781962679732115478122882354466041,
   1387482820695772010557975562665753220319,
   5192267027719860072899959692019995, 523347628920077677051620765,
   72057594037927879, 1]

private lemma row35_eq : row35 = eulerianRow 35 := by decide

private lemma row42_eq : row42 = eulerianRow 42 := by
  have h7 : row42 = eulerianRowAux 7 35 row35 := by decide
  rw [h7, row35_eq]
  simp only [eulerianRow]
  rw [← eulerianRowAux_add 34 7 1 [1]]

private lemma row50_eq : row50 = eulerianRow 50 := by
  have h8 : row50 = eulerianRowAux 8 42 row42 := by decide
  rw [h8, row42_eq]
  simp only [eulerianRow]
  rw [← eulerianRowAux_add 41 8 1 [1]]

private lemma row56_eq : row56 = eulerianRow 56 := by
  have h6 : row56 = eulerianRowAux 6 50 row50 := by decide
  rw [h6, row50_eq]
  simp only [eulerianRow]
  rw [← eulerianRowAux_add 49 6 1 [1]]

private lemma check_3_20 : checkRange 3 20 = true := by decide
private lemma check_21_35 : checkRange 21 35 = true := by decide
private lemma check_36_42 : checkRangeFrom 35 row35 36 42 = true := by decide
private lemma check_43_49 : checkRangeFrom 42 row42 43 49 = true := by decide
private lemma check_50_56 : checkRangeFrom 50 row50 50 56 = true := by decide
private lemma check_57_63 : checkRangeFrom 56 row56 57 63 = true := by decide

private lemma rossi_conjecture_6_16_le_63 {n : ℕ} (hn3 : 3 ≤ n) (hn63 : n ≤ 63) :
    ∃ S : Finset ℝ, S.card = n ∧
      (∀ t ∈ S, (charPoly n).IsRoot t) ∧
      (1 : ℝ) ∈ S ∧
      (S.filter (fun t => 0 < t ∧ t < 1)).card = n - 2 ∧
      (S.filter (fun t => 1 < t)).card = 1 := by
  refine checkRow_sound hn3 (finiteWitness n) ?_
  by_cases h1 : n ≤ 20
  · exact checkRange_sound check_3_20 hn3 h1
  · by_cases h2 : n ≤ 35
    · exact checkRange_sound check_21_35 (by omega) h2
    · by_cases h3 : n ≤ 42
      · exact checkRangeFrom_sound (by omega) row35_eq check_36_42 (by omega) h3 (by omega)
      · by_cases h4 : n ≤ 49
        · exact checkRangeFrom_sound (by omega) row42_eq check_43_49 (by omega) h4 (by omega)
        · by_cases h5 : n ≤ 56
          · exact checkRangeFrom_sound (by omega) row50_eq check_50_56 (by omega) h5 (by omega)
          · exact checkRangeFrom_sound (by omega) row56_eq check_57_63 (by omega) hn63 (by omega)

/-! ### Section 6: Main Theorems -/

/-- **Main Theorem (Rossi's Conjecture 6.16, arXiv:2611.25741v1):**
For every integer `n ≥ 3`, the characteristic polynomial `χ_n(t)` of the face lattice of the
`(n - 1)`-dimensional permutohedron has `n` distinct positive real roots: `t = 1`, exactly
`n - 2` roots in `(0, 1)`, and one root in `(1, ∞)`. In particular, since `deg χ_n = n`,
all roots of `χ_n` are simple positive real numbers. -/
theorem rossi_conjecture_6_16 {n : ℕ} (hn : 3 ≤ n) :
    ∃ S : Finset ℝ, S.card = n ∧
      (∀ t ∈ S, (charPoly n).IsRoot t) ∧
      (1 : ℝ) ∈ S ∧
      (S.filter (fun t => 0 < t ∧ t < 1)).card = n - 2 ∧
      (S.filter (fun t => 1 < t)).card = 1 ∧
      (∀ t : ℝ, (charPoly n).IsRoot t → t ∈ S) := by
  have hex : ∃ S : Finset ℝ, S.card = n ∧
      (∀ t ∈ S, (charPoly n).IsRoot t) ∧
      (1 : ℝ) ∈ S ∧
      (S.filter (fun t => 0 < t ∧ t < 1)).card = n - 2 ∧
      (S.filter (fun t => 1 < t)).card = 1 := by
    by_cases h64 : 64 ≤ n
    · exact rossi_conjecture_6_16_ge_64 h64
    · exact rossi_conjecture_6_16_le_63 hn (by omega)
  obtain ⟨S, hcard, hroots, h1, h01, hgt1⟩ := hex
  refine ⟨S, hcard, hroots, h1, h01, hgt1, ?_⟩
  -- Since `charPoly n ≠ 0` has `natDegree = n` and `S` already contains `n` distinct roots,
  -- every real root must lie in `S`!
  intro t ht
  by_contra hnot
  have hsub : (insert t S).val ⊆ (charPoly n).roots := by
    intro x hx
    rw [Polynomial.mem_roots (charPoly_ne_zero (by omega))]
    simp only [Finset.insert_val, Multiset.mem_ndinsert] at hx
    rcases hx with rfl | hxS
    · exact ht
    · exact hroots x hxS
  have hnodup : (insert t S).val.Nodup := (insert t S).nodup
  have hle_roots : (insert t S).card ≤ (charPoly n).roots.card := by
    have h1 := Multiset.le_iff_subset hnodup |>.mpr hsub
    exact Multiset.card_le_card h1
  have hdeg : (charPoly n).roots.card ≤ (charPoly n).natDegree := Polynomial.card_roots' (charPoly n)
  rw [Finset.card_insert_of_notMem hnot, hcard] at hle_roots
  rw [charPoly_natDegree (by omega)] at hdeg
  omega

/-- **Corollary (Full `f`-polynomial real-rootedness):**
For every integer `n ≥ 3`, the full `f`-polynomial `R_n(w) = 1 + w ∑_{i=0}^{n-1} A(n, i) (1 + w)^i`
of the `(n - 1)`-dimensional permutohedron has `n` distinct strictly negative real roots
(accounting for all `deg R_n = n` roots, all simple). -/
theorem rossi_full_f_polynomial_real_rooted {n : ℕ} (hn : 3 ≤ n) :
    ∃ W : Finset ℝ, W.card = n ∧
      (∀ w ∈ W, (fullFPoly n).IsRoot w ∧ w < 0) ∧
      (∀ w : ℝ, (fullFPoly n).IsRoot w → w ∈ W) := by
  obtain ⟨S, hcard, hroots, h1, h01, hgt1, hall⟩ := rossi_conjecture_6_16 hn
  -- Every `t ∈ S` is strictly positive (`1`, in `(0, 1)`, or `> 1`)!
  have hS_pos : ∀ t ∈ S, 0 < t := by
    intro t ht
    -- Partition `S` into `{1}`, `S.filter (0 < · < 1)`, `S.filter (1 < ·)`: their sizes sum to `n = S.card`!
    let S_pos := insert (1 : ℝ) ((S.filter (fun x => 0 < x ∧ x < 1)) ∪ (S.filter (fun x => 1 < x)))
    have hdisj : Disjoint (S.filter (fun x => 0 < x ∧ x < 1)) (S.filter (fun x => 1 < x)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2; linarith
    have h1not : (1 : ℝ) ∉ (S.filter (fun x => 0 < x ∧ x < 1)) ∪ (S.filter (fun x => 1 < x)) := by
      simp only [Finset.mem_union, Finset.mem_filter, not_or]
      constructor <;> rintro ⟨_, h⟩ <;> linarith
    have hSpos_sub : S_pos ⊆ S := by
      intro x hx
      simp only [S_pos, Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hx
      rcases hx with rfl | ⟨hxS, _⟩ | ⟨hxS, _⟩
      · exact h1
      · exact hxS
      · exact hxS
    have hSpos_card : S_pos.card = n := by
      dsimp [S_pos]
      rw [Finset.card_insert_of_notMem h1not, Finset.card_union_of_disjoint hdisj, h01, hgt1]
      omega
    have hEq : S_pos = S := Finset.eq_of_subset_of_card_le hSpos_sub (by rw [hSpos_card, hcard])
    have ht' : t ∈ S_pos := hEq.symm ▸ ht
    simp only [S_pos, Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at ht'
    rcases ht' with rfl | ⟨_, h0, _⟩ | ⟨_, h1'⟩ <;> linarith
  let W : Finset ℝ := S.image (fun t => -1 / t)
  have hW_card : W.card = n := by
    rw [Finset.card_image_of_injOn, hcard]
    intro t₁ ht₁ t₂ ht₂ hEq
    have h1' : t₁ ≠ 0 := (hS_pos t₁ ht₁).ne'
    have h2' : t₂ ≠ 0 := (hS_pos t₂ ht₂).ne'
    have := congrArg (fun x => -1 / x) hEq
    field_simp [h1', h2'] at hEq
    linarith
  have hW_prop : ∀ w ∈ W, (fullFPoly n).IsRoot w ∧ w < 0 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨t, ht, rfl⟩
    have ht_pos : 0 < t := hS_pos t ht
    have hw_neg : -1 / t < 0 := div_neg_of_neg_of_pos (by norm_num) ht_pos
    refine ⟨?_, hw_neg⟩
    rw [Polynomial.IsRoot.def, fullFPoly_eval_eq_charPoly hw_neg.ne]
    have hinv : -1 / (-1 / t) = t := by field_simp [ht_pos.ne']
    rw [hinv, hroots t ht, mul_zero]
  refine ⟨W, hW_card, hW_prop, ?_⟩
  intro w hw
  have hw_ne : w ≠ 0 := by
    intro h0; subst h0
    rw [Polynomial.IsRoot.def, fullFPoly] at hw
    simp at hw
  have hchi : (charPoly n).IsRoot (-1 / w) := by
    have h := fullFPoly_eval_eq_charPoly (n := n) hw_ne
    rw [Polynomial.IsRoot.def] at hw ⊢
    rw [hw] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero n (neg_ne_zero.mpr hw_ne))
  have ht_mem : -1 / w ∈ S := hall (-1 / w) hchi
  exact Finset.mem_image.mpr ⟨-1 / w, ht_mem, by field_simp [hw_ne]⟩

end RossiPermutohedronRealRoots
