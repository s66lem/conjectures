import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Full Rank Reversal Between Right and Inverse Left Eigenvectors for Four Alternatives
# (Resolution of Bozóki–Csató, arXiv:2603.24274)

In *Theoretical properties of the eigenvector method* (`arXiv:2603.24274`, math.OC,
March 2026), S. Bozóki and L. Csató ask whether there exists a 4×4 pairwise
comparison matrix (PCM) whose right Perron eigenvector `w^R` and inverse left
Perron eigenvector `w^(-L)` induce strictly opposite rankings of the four
alternatives, and ask for a characterization of the class of PCMs exhibiting
such full rank reversal.

We formalize:
1. Self-contained uniqueness of positive right and left eigenvectors (`right_perron_unique`,
   `left_perron_unique`) for arbitrary entrywise-positive real matrices.
2. Exact characterization (`reversal_class_characterization` and `reversal_from_const_rowsum`)
   of the full-reversal class for every dimension `n`, via diagonal rescaling
   `B = D_w⁻¹ A D_w` to constant-row-sum PCMs.
3. Exact 4×4 rational witness `A4` with `λ_max = 5`, `w4 = (34, 33, 32, 22)` (ranking
   `0 > 1 > 2 > 3`) and `v4 = (42/17, 27/11, 77/32, 26/11)` (so `v4⁻¹` ranks
   `0 < 1 < 2 < 3`), proving full reversal for all positive Perron vectors of `A4`
   (`bozoki_csato_four_alternatives`).
4. Sharpness (`n3_right_eq_inv_left`): for every 3×3 PCM, `w^R` and `w^(-L)` are
   positively proportional, so `n = 4` is the minimum dimension for any reversal.
-/

namespace BozokiCsatoEigenvectorReversal

open scoped BigOperators
open Matrix

/-- A real `n × n` matrix is a pairwise comparison matrix (PCM) if it is
entrywise positive and reciprocal (`A i j * A j i = 1`). -/
def IsPCM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 < A i j) ∧ (∀ i j, A i j * A j i = 1)

/-- Diagonal entries of a PCM equal `1`. -/
lemma pcm_diag_eq_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPCM A) (i : Fin n) :
    A i i = 1 := by
  have hpos := hA.1 i i
  have hsq : A i i * A i i = 1 := hA.2 i i
  nlinarith

/-- Self-contained uniqueness of positive right eigenvectors for any entrywise-positive
`n × n` real matrix (`n ≥ 1`): if `M *ᵥ w = lam • w` and `v ᵥ* M = lam • v` with
`w, v > 0`, then any positive right eigenvector `x` has eigenvalue `lam` and is a
positive scalar multiple of `w`. -/
theorem right_perron_unique {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j) (w v x : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (hx : ∀ i, 0 < x i)
    (lam mu : ℝ)
    (hw_eig : M *ᵥ w = lam • w)
    (hv_eig : v ᵥ* M = lam • v)
    (hx_eig : M *ᵥ x = mu • x) :
    mu = lam ∧ ∃ t : ℝ, 0 < t ∧ x = t • w := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hvx_pos : 0 < dotProduct v x := by
    refine Finset.sum_pos (fun i _ => mul_pos (hv i) (hx i)) hne
  have hmu_eq : mu = lam := by
    have h1 : dotProduct v (M *ᵥ x) = mu * dotProduct v x := by
      rw [hx_eig, dotProduct_smul, smul_eq_mul]
    have h2 : dotProduct v (M *ᵥ x) = lam * dotProduct v x := by
      rw [Matrix.dotProduct_mulVec, hv_eig, smul_dotProduct, smul_eq_mul]
    have : (mu - lam) * dotProduct v x = 0 := by linarith
    rcases mul_eq_zero.mp this with hsub | h0
    · linarith
    · linarith
  refine ⟨hmu_eq, ?_⟩
  rw [hmu_eq] at hx_eig
  obtain ⟨k, _, hk_min⟩ := Finset.exists_min_image Finset.univ (fun i => x i / w i) hne
  set t : ℝ := x k / w k
  have ht_pos : 0 < t := div_pos (hx k) (hw k)
  refine ⟨t, ht_pos, ?_⟩
  let z : Fin n → ℝ := fun i => x i - t * w i
  have hz_nn : ∀ i, 0 ≤ z i := by
    intro i
    have hle : t ≤ x i / w i := hk_min i (Finset.mem_univ i)
    have : t * w i ≤ x i := (le_div_iff₀ (hw i)).mp hle
    dsimp only [z]
    linarith
  have hzk : z k = 0 := by
    dsimp only [z, t]
    field_simp [ne_of_gt (hw k)]
    ring
  have hz_eig : M *ᵥ z = lam • z := by
    ext i
    have h1 : (M *ᵥ x) i = lam * x i := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx_eig i
    have h2 : (M *ᵥ w) i = lam * w i := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hw_eig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, z]
    have hexp : ∑ j : Fin n, M i j * (x j - t * w j) =
        (∑ j : Fin n, M i j * x j) - t * (∑ j : Fin n, M i j * w j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hexp]
    simp only [Matrix.mulVec, dotProduct] at h1 h2
    rw [h1, h2]
    ring
  have hz_zero : ∀ i, z i = 0 := by
    intro i
    by_contra hne
    have hpos_i : 0 < z i := lt_of_le_of_ne (hz_nn i) (Ne.symm hne)
    have hMz_k : (M *ᵥ z) k = lam * z k := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hz_eig k
    rw [hzk, mul_zero] at hMz_k
    have hsum_pos : 0 < ∑ j : Fin n, M k j * z j :=
      Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hM k j)) (hz_nn j))
        ⟨i, Finset.mem_univ i, mul_pos (hM k i) hpos_i⟩
    simp only [Matrix.mulVec, dotProduct] at hMz_k
    linarith
  ext i
  have hi := hz_zero i
  dsimp only [z] at hi
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- Self-contained uniqueness of positive left eigenvectors for any entrywise-positive
`n × n` real matrix (`n ≥ 1`), obtained by applying `right_perron_unique` to `Mᵀ`. -/
theorem left_perron_unique {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j) (w v y : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (hy : ∀ i, 0 < y i)
    (lam mu : ℝ)
    (hw_eig : M *ᵥ w = lam • w)
    (hv_eig : v ᵥ* M = lam • v)
    (hy_eig : y ᵥ* M = mu • y) :
    mu = lam ∧ ∃ t : ℝ, 0 < t ∧ y = t • v := by
  refine right_perron_unique hn Mᵀ (fun i j => hM j i) v w y hv hw hy lam mu ?_ ?_ ?_
  · rw [Matrix.mulVec_transpose]; exact hv_eig
  · rw [Matrix.vecMul_transpose]; exact hw_eig
  · rw [Matrix.mulVec_transpose]; exact hy_eig

/-- Scaling a positive vector by a positive scalar preserves `StrictAnti`. -/
lemma strictAnti_smul_of_pos {n : ℕ} {t : ℝ} {w : Fin n → ℝ} (ht : 0 < t)
    (hw : StrictAnti w) : StrictAnti (t • w) := by
  intro i j hij
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_of_pos_left (hw hij) ht

/-- Scaling a positive vector by a positive scalar preserves `StrictMono` of its
entrywise reciprocal. -/
lemma strictMono_inv_smul_of_pos {n : ℕ} {t : ℝ} {v : Fin n → ℝ} (ht : 0 < t)
    (hv : StrictMono (fun i => (v i)⁻¹)) :
    StrictMono (fun i => ((t • v) i)⁻¹) := by
  intro i j hij
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv]
  exact mul_lt_mul_of_pos_left (hv hij) (inv_pos.mpr ht)

/-- Diagonal rescaling of a matrix `A` by a positive vector `w`: `(D_w⁻¹ A D_w)_{ij} = A_{ij} w_j / w_i`. -/
noncomputable def rescalePCM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => A i j * w j / w i

/-- **Theorem 1 (Characterization of the Full-Reversal Class):**
For any PCM `A` with positive right eigenvector `w` and positive left eigenvector `v`
at eigenvalue `lam`, the rescaled matrix `B = D_w⁻¹ A D_w` is a PCM with constant row
sums `lam` and positive left eigenvector `u = v ∘ w`. Moreover, `w` is strictly
decreasing and `v⁻¹` is strictly increasing if and only if `u` is strictly decreasing
and `u j / u i < w j / w i < 1` for all `i < j`. -/
theorem reversal_class_characterization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsPCM A) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (lam : ℝ) (hw_eig : A *ᵥ w = lam • w) (hv_eig : v ᵥ* A = lam • v) :
    let B := rescalePCM A w
    let u : Fin n → ℝ := fun i => v i * w i
    IsPCM B ∧
    (∀ i, ∑ j : Fin n, B i j = lam) ∧
    (u ᵥ* B = lam • u) ∧
    ((StrictAnti w ∧ StrictMono (fun i => (v i)⁻¹)) ↔
      (StrictAnti u ∧ ∀ i j : Fin n, i < j → u j / u i < w j / w i ∧ w j / w i < 1)) := by
  intro B u
  have hB_pcm : IsPCM B := by
    refine ⟨fun i j => div_pos (mul_pos (hA.1 i j) (hw j)) (hw i), fun i j => ?_⟩
    simp only [B, rescalePCM, Matrix.of_apply]
    calc
      A i j * w j / w i * (A j i * w i / w j)
          = (A i j * A j i) * ((w j / w j) * (w i / w i)) := by ring
      _ = 1 * (1 * 1) := by
          rw [hA.2 i j, div_self (ne_of_gt (hw j)), div_self (ne_of_gt (hw i))]
      _ = 1 := by ring
  have hB_row : ∀ i, ∑ j : Fin n, B i j = lam := by
    intro i
    have hi : ∑ j : Fin n, A i j * w j = lam * w i := by
      simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hw_eig i
    simp only [B, rescalePCM, Matrix.of_apply]
    rw [← Finset.sum_div, hi, mul_div_cancel_right₀ _ (ne_of_gt (hw i))]
  have hB_left : u ᵥ* B = lam • u := by
    ext j
    have hj : ∑ i : Fin n, v i * A i j = lam * v j := by
      simpa [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hv_eig j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, B, rescalePCM,
      Matrix.of_apply, u]
    have hterm : ∀ i : Fin n, v i * w i * (A i j * w j / w i) = (v i * A i j) * w j := by
      intro i
      field_simp [ne_of_gt (hw i)]
    simp_rw [hterm, ← Finset.sum_mul, hj]
    ring
  refine ⟨hB_pcm, hB_row, hB_left, ?_⟩
  constructor
  · rintro ⟨hw_anti, hvinv_mono⟩
    have hv_anti : StrictAnti v := by
      intro i j hij
      have hlt : (v i)⁻¹ < (v j)⁻¹ := hvinv_mono hij
      exact (inv_lt_inv₀ (hv i) (hv j)).mp hlt
    have hu_anti : StrictAnti u := by
      intro i j hij
      dsimp only [u]
      exact mul_lt_mul'' (hv_anti hij) (hw_anti hij) (le_of_lt (hv j)) (le_of_lt (hw j))
    refine ⟨hu_anti, fun i j hij => ⟨?_, ?_⟩⟩
    · dsimp only [u]
      rw [div_lt_div_iff₀ (mul_pos (hv i) (hw i)) (hw i)]
      have hlt : v j < v i := hv_anti hij
      have hpos : 0 < w j * w i := mul_pos (hw j) (hw i)
      nlinarith
    · exact (div_lt_one (hw i)).mpr (hw_anti hij)
  · rintro ⟨_, hratio⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact (div_lt_one (hw i)).mp (hratio i j hij).2
    · intro i j hij
      have hlt := (hratio i j hij).1
      dsimp only [u] at hlt
      rw [div_lt_div_iff₀ (mul_pos (hv i) (hw i)) (hw i)] at hlt
      have hv_lt : v j < v i := by
        have hpos : 0 < w j * w i := mul_pos (hw j) (hw i)
        nlinarith
      exact (inv_lt_inv₀ (hv i) (hv j)).mpr hv_lt

/-- **Converse Construction (Theorem 1(c)):**
Given any constant-row-sum PCM `B` with positive strictly-decreasing left eigenvector
`u`, and any positive vector `w` satisfying `u j / u i < w j / w i < 1` for all `i < j`,
the diagonally rescaled matrix `A = D_w B D_w⁻¹` is a PCM whose right and inverse left
Perron eigenvectors induce strictly opposite rankings. -/
theorem reversal_from_const_rowsum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsPCM B) (lam : ℝ) (hrow : ∀ i, ∑ j : Fin n, B i j = lam)
    (u w : Fin n → ℝ) (hu : ∀ i, 0 < u i) (hw : ∀ i, 0 < w i)
    (hu_eig : u ᵥ* B = lam • u)
    (hratio : ∀ i j : Fin n, i < j → u j / u i < w j / w i ∧ w j / w i < 1) :
    let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => w i * B i j / w j
    let v : Fin n → ℝ := fun i => u i / w i
    IsPCM A ∧ (∀ i, 0 < v i) ∧ A *ᵥ w = lam • w ∧ v ᵥ* A = lam • v ∧
      StrictAnti w ∧ StrictMono (fun i => (v i)⁻¹) := by
  intro A v
  have hA_pcm : IsPCM A := by
    refine ⟨fun i j => div_pos (mul_pos (hw i) (hB.1 i j)) (hw j), fun i j => ?_⟩
    simp only [A, Matrix.of_apply]
    calc
      w i * B i j / w j * (w j * B j i / w i)
          = (B i j * B j i) * ((w i / w i) * (w j / w j)) := by ring
      _ = 1 * (1 * 1) := by
          rw [hB.2 i j, div_self (ne_of_gt (hw i)), div_self (ne_of_gt (hw j))]
      _ = 1 := by ring
  have hv_pos : ∀ i, 0 < v i := fun i => div_pos (hu i) (hw i)
  have hw_eig : A *ᵥ w = lam • w := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, A, Matrix.of_apply]
    have hterm : ∀ j : Fin n, w i * B i j / w j * w j = w i * B i j := fun j =>
      div_mul_cancel₀ _ (ne_of_gt (hw j))
    simp_rw [hterm, ← Finset.mul_sum, hrow i]
    ring
  have hv_eig : v ᵥ* A = lam • v := by
    ext j
    have hj : ∑ i : Fin n, u i * B i j = lam * u j := by
      simpa [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hu_eig j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, A, Matrix.of_apply, v]
    have hterm : ∀ i : Fin n, u i / w i * (w i * B i j / w j) = (u i * B i j) / w j := by
      intro i
      field_simp [ne_of_gt (hw i), ne_of_gt (hw j)]
    simp_rw [hterm, ← Finset.sum_div, hj]
    ring
  have hw_anti : StrictAnti w := fun i j hij => (div_lt_one (hw i)).mp (hratio i j hij).2
  have hvinv_mono : StrictMono (fun i => (v i)⁻¹) := by
    intro i j hij
    have hlt := (hratio i j hij).1
    have hv_lt : v j < v i := by
      dsimp only [v]
      rw [div_lt_div_iff₀ (hw j) (hw i)]
      rw [div_lt_div_iff₀ (hu i) (hw i)] at hlt
      nlinarith
    exact (inv_lt_inv₀ (hv_pos i) (hv_pos j)).mpr hv_lt
  exact ⟨hA_pcm, hv_pos, hw_eig, hv_eig, hw_anti, hvinv_mono⟩

/-- The explicit 4×4 rational pairwise comparison matrix resolving the open question
of Bozóki–Csató (arXiv:2603.24274). -/
noncomputable def A4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 34 / 11, 17 / 48, 34 / 33;
     11 / 34, 1, 77 / 32, 2;
     48 / 17, 32 / 77, 1, 64 / 77;
     33 / 34, 1 / 2, 77 / 64, 1]

/-- Right Perron eigenvector of `A4` with eigenvalue `5`. -/
noncomputable def w4 : Fin 4 → ℝ := ![34, 33, 32, 22]

/-- Left Perron eigenvector of `A4` with eigenvalue `5`. -/
noncomputable def v4 : Fin 4 → ℝ := ![42 / 17, 27 / 11, 77 / 32, 26 / 11]

/-- `A4` is a valid pairwise comparison matrix (entrywise positive and reciprocal). -/
theorem A4_isPCM : IsPCM A4 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A4]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A4]

/-- `w4` is entrywise positive. -/
lemma w4_pos : ∀ i : Fin 4, 0 < w4 i := by
  intro i; fin_cases i <;> norm_num [w4]

/-- `v4` is entrywise positive. -/
lemma v4_pos : ∀ i : Fin 4, 0 < v4 i := by
  intro i; fin_cases i <;> norm_num [v4]

/-- `A4 *ᵥ w4 = 5 • w4`. -/
theorem A4_mulVec_w4 : A4 *ᵥ w4 = (5 : ℝ) • w4 := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A4, w4] <;>
    norm_num

/-- `v4 ᵥ* A4 = 5 • v4`. -/
theorem v4_vecMul_A4 : v4 ᵥ* A4 = (5 : ℝ) • v4 := by
  ext j
  fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four, A4, v4] <;>
    norm_num

/-- `w4` is strictly decreasing (`0 ≻ 1 ≻ 2 ≻ 3`). -/
theorem w4_strictAnti : StrictAnti w4 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [w4] <;> norm_num

/-- `v4⁻¹` is strictly increasing (`3 ≻ 2 ≻ 1 ≻ 0`), fully reversing `w4`. -/
theorem v4_inv_strictMono : StrictMono (fun i => (v4 i)⁻¹) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [v4] <;> norm_num

/-- **Main Theorem (Affirmative Resolution of Bozóki–Csató, arXiv:2603.24274):**
There exists a 4×4 pairwise comparison matrix `A` (`A = A4`) with common Perron
eigenvalue `5` such that **every** positive right eigenvector `w` of `A` induces the
strict ranking `0 ≻ 1 ≻ 2 ≻ 3` (`StrictAnti w`) while the entrywise reciprocal of
**every** positive left eigenvector `v` of `A` induces the strictly opposite ranking
`3 ≻ 2 ≻ 1 ≻ 0` (`StrictMono (fun i => (v i)⁻¹)`). -/
theorem bozoki_csato_four_alternatives :
    ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
      IsPCM A ∧
      (∃ w : Fin 4 → ℝ, (∀ i, 0 < w i) ∧ A *ᵥ w = (5 : ℝ) • w) ∧
      (∃ v : Fin 4 → ℝ, (∀ i, 0 < v i) ∧ v ᵥ* A = (5 : ℝ) • v) ∧
      (∀ (w : Fin 4 → ℝ) (mu : ℝ), (∀ i, 0 < w i) → A *ᵥ w = mu • w →
        mu = 5 ∧ StrictAnti w) ∧
      (∀ (v : Fin 4 → ℝ) (mu : ℝ), (∀ i, 0 < v i) → v ᵥ* A = mu • v →
        mu = 5 ∧ StrictMono (fun i => (v i)⁻¹)) := by
  refine ⟨A4, A4_isPCM, ⟨w4, w4_pos, A4_mulVec_w4⟩, ⟨v4, v4_pos, v4_vecMul_A4⟩, ?_, ?_⟩
  · intro w mu hw hwe
    obtain ⟨hmu, t, ht, rfl⟩ :=
      right_perron_unique (by decide) A4 A4_isPCM.1 w4 v4 w w4_pos v4_pos hw 5 mu
        A4_mulVec_w4 v4_vecMul_A4 hwe
    exact ⟨hmu, strictAnti_smul_of_pos ht w4_strictAnti⟩
  · intro v mu hv hve
    obtain ⟨hmu, t, ht, rfl⟩ :=
      left_perron_unique (by decide) A4 A4_isPCM.1 w4 v4 v w4_pos v4_pos hv 5 mu
        A4_mulVec_w4 v4_vecMul_A4 hve
    exact ⟨hmu, strictMono_inv_smul_of_pos ht v4_inv_strictMono⟩

/-- **Sharpness at `n = 3` (Saaty's Theorem):**
For every 3×3 pairwise comparison matrix `A`, every positive right eigenvector `w`
and every positive left eigenvector `v` satisfy `∃ t > 0, w = t • v⁻¹`. Hence the
right and inverse left eigenvector rankings always coincide for `n = 3`, making
`n = 4` the minimum dimension where any reversal can occur. -/
theorem n3_right_eq_inv_left (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsPCM A)
    (w v : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (lamR lamL : ℝ) (hw_eig : A *ᵥ w = lamR • w) (hv_eig : v ᵥ* A = lamL • v) :
    lamR = lamL ∧ ∃ t : ℝ, 0 < t ∧ w = t • (fun i => (v i)⁻¹) := by
  set a : ℝ := A 0 1
  set b : ℝ := A 1 2
  set c : ℝ := A 0 2
  have ha : 0 < a := hA.1 0 1
  have hb : 0 < b := hA.1 1 2
  have hc : 0 < c := hA.1 0 2
  have h00 : A 0 0 = 1 := pcm_diag_eq_one hA 0
  have h11 : A 1 1 = 1 := pcm_diag_eq_one hA 1
  have h22 : A 2 2 = 1 := pcm_diag_eq_one hA 2
  have h10 : A 1 0 = a⁻¹ := by
    have := hA.2 0 1; field_simp [ne_of_gt ha]; linarith
  have h21 : A 2 1 = b⁻¹ := by
    have := hA.2 1 2; field_simp [ne_of_gt hb]; linarith
  have h20 : A 2 0 = c⁻¹ := by
    have := hA.2 0 2; field_simp [ne_of_gt hc]; linarith
  set q : ℝ := (a * b / c) ^ ((1 : ℝ) / 3)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos (div_pos (mul_pos ha hb) hc) _
  have hq3 : q ^ 3 = a * b / c := by
    have hnn : 0 ≤ a * b / c := le_of_lt (div_pos (mul_pos ha hb) hc)
    dsimp only [q]
    calc
      ((a * b / c) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
          = ((a * b / c) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
      _ = (a * b / c) ^ (((1 : ℝ) / 3) * 3) := by rw [← Real.rpow_mul hnn]
      _ = a * b / c := by norm_num
  have ha_eq : a = q ^ 3 * c / b := by
    have hmul : q ^ 3 * c = a * b := by rw [hq3, div_mul_cancel₀ _ (ne_of_gt hc)]
    rw [hmul, mul_div_cancel_right₀ _ (ne_of_gt hb)]
  set lam : ℝ := 1 + q + q⁻¹
  let w0 : Fin 3 → ℝ := fun i =>
    match i with
    | ⟨0, _⟩ => c * q
    | ⟨1, _⟩ => b / q
    | ⟨2, _⟩ => 1
  let v0 : Fin 3 → ℝ := fun i => (w0 i)⁻¹
  have hw0_pos : ∀ i : Fin 3, 0 < w0 i := by
    intro i; fin_cases i <;> dsimp only [w0] <;> positivity
  have hv0_pos : ∀ i : Fin 3, 0 < v0 i := fun i => inv_pos.mpr (hw0_pos i)
  have hw0_eig : A *ᵥ w0 = lam • w0 := by
    ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      change A 0 0 * (c * q) + A 0 1 * (b / q) + A 0 2 * 1 = (1 + q + q⁻¹) * (c * q)
      rw [h00]
      change 1 * (c * q) + a * (b / q) + c * 1 = (1 + q + q⁻¹) * (c * q)
      rw [ha_eq]
      field_simp [ne_of_gt hb, ne_of_gt hq_pos]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      change A 1 0 * (c * q) + A 1 1 * (b / q) + A 1 2 * 1 = (1 + q + q⁻¹) * (b / q)
      rw [h10, h11]
      change a⁻¹ * (c * q) + 1 * (b / q) + b * 1 = (1 + q + q⁻¹) * (b / q)
      rw [ha_eq]
      field_simp [ne_of_gt hb, ne_of_gt hc, ne_of_gt hq_pos]
      ring
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      change A 2 0 * (c * q) + A 2 1 * (b / q) + A 2 2 * 1 = (1 + q + q⁻¹) * 1
      rw [h20, h21, h22]
      field_simp [ne_of_gt hb, ne_of_gt hc, ne_of_gt hq_pos]
      ring
  have hv0_eig : v0 ᵥ* A = lam • v0 := by
    ext j
    fin_cases j
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      change (c * q)⁻¹ * A 0 0 + (b / q)⁻¹ * A 1 0 + (1 : ℝ)⁻¹ * A 2 0 = (1 + q + q⁻¹) * (c * q)⁻¹
      rw [h00, h10, h20, ha_eq]
      field_simp [ne_of_gt hb, ne_of_gt hc, ne_of_gt hq_pos]
      ring
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      change (c * q)⁻¹ * A 0 1 + (b / q)⁻¹ * A 1 1 + (1 : ℝ)⁻¹ * A 2 1 = (1 + q + q⁻¹) * (b / q)⁻¹
      rw [h11, h21]
      change (c * q)⁻¹ * a + (b / q)⁻¹ * 1 + (1 : ℝ)⁻¹ * b⁻¹ = (1 + q + q⁻¹) * (b / q)⁻¹
      rw [ha_eq]
      field_simp [ne_of_gt hb, ne_of_gt hc, ne_of_gt hq_pos]
      ring
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      change (c * q)⁻¹ * A 0 2 + (b / q)⁻¹ * A 1 2 + (1 : ℝ)⁻¹ * A 2 2 = (1 + q + q⁻¹) * (1 : ℝ)⁻¹
      rw [h22]
      change (c * q)⁻¹ * c + (b / q)⁻¹ * b + (1 : ℝ)⁻¹ * 1 = (1 + q + q⁻¹) * (1 : ℝ)⁻¹
      field_simp [ne_of_gt hb, ne_of_gt hc, ne_of_gt hq_pos]
      ring
  obtain ⟨hR, tR, htR, rfl⟩ :=
    right_perron_unique (by decide) A hA.1 w0 v0 w hw0_pos hv0_pos hw lam lamR hw0_eig hv0_eig hw_eig
  obtain ⟨hL, tL, htL, rfl⟩ :=
    left_perron_unique (by decide) A hA.1 w0 v0 v hw0_pos hv0_pos hv lam lamL hw0_eig hv0_eig hv_eig
  refine ⟨hR.trans hL.symm, tR * tL, mul_pos htR htL, ?_⟩
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv, v0, inv_inv]
  calc
    tR * w0 i = tR * (tL * tL⁻¹) * w0 i := by rw [mul_inv_cancel₀ (ne_of_gt htL), mul_one]
    _ = tR * tL * (tL⁻¹ * w0 i) := by ring

end BozokiCsatoEigenvectorReversal
