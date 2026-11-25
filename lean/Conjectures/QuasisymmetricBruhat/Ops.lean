import Conjectures.QuasisymmetricBruhat.Poly
import Mathlib.RingTheory.Adjoin.Basic

/-!
# The operators `Rᵢ`, `Dⱼ` and the Monk factors `L_k`

`Rᵢ f = f(x₁, …, x_{i-1}, 0, x_i, x_{i+1}, …)` and `Dⱼ = R_{j+1} - Rⱼ`; thus `Dⱼ = xⱼ Tⱼ` for the
quasisymmetric divided difference `Tⱼ` of Nadeau–Spink–Tewari.  `L_k = x₁ + ⋯ + x_k`.
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset

/-- `Rᵢ`: insert a zero at position `i`. -/
noncomputable def R (i : ℕ) : Pol →ₐ[ℤ] Pol :=
  aeval (fun m => if m < i then X m else if m = i then 0 else X (m - 1))

/-- `Dⱼ = R_{j+1} - Rⱼ`. -/
noncomputable def D (j : ℕ) (f : Pol) : Pol := R (j + 1) f - R j f

/-- `L_k = x₁ + ⋯ + x_k`. -/
noncomputable def L (k : ℕ) : Pol := ∑ m ∈ Icc 1 k, x m

lemma R_X (i m : ℕ) : R i (X m) = if m < i then X m else if m = i then 0 else X (m - 1) := by
  simp [R]

lemma R_comm {a b : ℕ} (h : a < b) (f : Pol) : R a (R b f) = R (b - 1) (R a f) := by
  have : (R a).comp (R b) = (R (b - 1)).comp (R a) := by
    apply MvPolynomial.algHom_ext; intro m
    simp only [AlgHom.comp_apply, R_X]
    split_ifs <;> simp only [map_zero, R_X] <;> split_ifs <;> first | rfl | omega
  exact congrArg (fun φ : Pol →ₐ[ℤ] Pol => φ f) this

lemma D_add (j : ℕ) (f g : Pol) : D j (f + g) = D j f + D j g := by
  simp only [D, map_add]; ring

lemma D_smul (j : ℕ) (a : ℤ) (f : Pol) : D j (a • f) = a • D j f := by
  simp only [D, map_zsmul, smul_sub]

lemma D_zero (j : ℕ) : D j 0 = 0 := by simp [D]

lemma D_sum {ι : Type*} (j : ℕ) (s : Finset ι) (f : ι → Pol) :
    D j (∑ i ∈ s, f i) = ∑ i ∈ s, D j (f i) := by
  simp only [D, map_sum, sum_sub_distrib]

/-- Twisted Leibniz rule. -/
lemma D_mul (j : ℕ) (f g : Pol) : D j (f * g) = D j f * R (j + 1) g + R j f * D j g := by
  simp only [D, map_mul]; ring

lemma R_L {i : ℕ} (hi : 1 ≤ i) (k : ℕ) : R i (L k) = L (if i ≤ k then k - 1 else k) := by
  induction k with
  | zero => simp [L]
  | succ k ih =>
    have hL : ∀ n, L (n + 1) = L n + X (n + 1) := fun n => by
      simp [L, Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
    rw [hL, map_add, ih, R_X]
    rcases lt_trichotomy i (k + 1) with h | h | h
    · rw [if_pos (show i ≤ k by omega), if_pos (show i ≤ k + 1 by omega),
        if_neg (show ¬ k + 1 < i by omega), if_neg (show ¬ k + 1 = i by omega),
        Nat.add_sub_cancel]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, hL]
    · rw [if_neg (show ¬ i ≤ k by omega), if_pos (show i ≤ k + 1 by omega),
        if_neg (show ¬ k + 1 < i by omega), if_pos h.symm, add_zero, Nat.add_sub_cancel]
    · rw [if_neg (show ¬ i ≤ k by omega), if_neg (show ¬ i ≤ k + 1 by omega), if_pos h, ← hL]

lemma D_L {j : ℕ} (hj : 1 ≤ j) (k : ℕ) : D j (L k) = if j = k then X j else 0 := by
  rw [D, R_L (by omega), R_L hj]
  rcases lt_trichotomy j k with h | rfl | h
  · rw [if_pos (show j + 1 ≤ k by omega), if_pos (show j ≤ k by omega), if_neg (by omega),
      sub_self]
  · rw [if_neg (show ¬ j + 1 ≤ j by omega), if_pos le_rfl, if_pos rfl]
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [L, Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)]
  · rw [if_neg (show ¬ j + 1 ≤ k by omega), if_neg (show ¬ j ≤ k by omega), if_neg (by omega),
      sub_self]

lemma R_constantCoeff (i : ℕ) (f : Pol) : constantCoeff (R i f) = constantCoeff f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [R]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p m hp =>
    rw [map_mul, map_mul, map_mul, hp, R_X]
    split_ifs <;> simp

lemma L_constantCoeff (k : ℕ) : constantCoeff (L k) = 0 := by simp [L, x]

lemma L_mem_supported (k : ℕ) : L k ∈ supported ℤ posVars := by
  apply Subalgebra.sum_mem; intro m hm
  exact X_mem_supported.2 (mem_Icc.1 hm).1

lemma R_mem_supported {i : ℕ} (hi : 1 ≤ i) {f : Pol} (hf : f ∈ supported ℤ posVars) :
    R i f ∈ supported ℤ posVars := by
  rw [supported_eq_adjoin_X] at hf ⊢
  induction hf using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, hm, rfl⟩ := hy
    have hm' : 1 ≤ m := hm
    rw [R_X]
    split_ifs with h1 h2
    · exact Algebra.subset_adjoin ⟨m, hm, rfl⟩
    · exact Subalgebra.zero_mem _
    · exact Algebra.subset_adjoin ⟨m - 1, show 1 ≤ m - 1 by omega, rfl⟩
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | add y z _ _ hy hz => rw [map_add]; exact Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact Subalgebra.mul_mem _ hy hz

/-! ### Commutation of `D` with `R` (NST (7.1), multiplied by `xⱼ`) -/

lemma D_R_low {i j : ℕ} (h : j + 1 < i) (f : Pol) : D j (R i f) = R (i - 1) (D j f) := by
  simp only [D, map_sub, R_comm h, R_comm (show j < i by omega)]

lemma D_R_high {i j : ℕ} (h : i ≤ j) (f : Pol) : D j (R i f) = R i (D (j + 1) f) := by
  simp only [D, map_sub]
  rw [R_comm (show i < j + 1 + 1 by omega), R_comm (show i < j + 1 by omega)]
  simp

lemma D_R_mid {i : ℕ} (h : 2 ≤ i) (f : Pol) :
    D (i - 1) (R i f) = R i (D (i - 1) f) + R (i - 1) (D i f) := by
  simp only [D, map_sub, show i - 1 + 1 = i by omega]
  rw [R_comm (show i - 1 < i + 1 by omega), show i + 1 - 1 = i by omega]
  ring

end QuasisymmetricBruhat
