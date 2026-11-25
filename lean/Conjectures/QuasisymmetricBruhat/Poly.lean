import Conjectures.QuasisymmetricBruhat.Structure
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finset.Pi

/-!
# Forest polynomials (Definition 2.3) and the leading monomial (Fact 2.5)

A valid labeling of `F` is a map `λ : IN(F) → ℤ_{>0}` with `1 ≤ λ(v) ≤ ρ(v)`, `λ(v) ≤ λ(u)` for
the left child `u` and `λ(v) < λ(u)` for the right child `u` of `v`;
`P_F = ∑_λ ∏_v x_{λ(v)}`.  Labelings are stored as total functions vanishing off `IN(F)`.

Fact 2.5 is proved in the weighted form used for triangularity: every monomial `x^e` of `P_F`
comes from a labeling with `λ ≤ ρ` pointwise, so `∑ i eᵢ ≤ ∑ i cᵢ(F)` with equality only for
`λ = ρ`, which gives `x^{c(F)}` with coefficient one.
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset

/-- Polynomials in `x₁, x₂, …` (the variable `X 0` is never used). -/
abbrev Pol := MvPolynomial ℕ ℤ

namespace Forest

/-- Valid labelings (Definition 2.3). -/
def Valid (F : Forest) (lam : ℕ × ℕ → ℕ) : Prop :=
  ∀ v ∈ F.IN, 1 ≤ lam v ∧ lam v ≤ rho v ∧ (∀ u, lc v = some u → lam v ≤ lam u) ∧
    (∀ u, F.rc v = some u → lam v < lam u)

open Classical in
/-- Maps `IN(F) → ℕ` with `1 ≤ λ v ≤ ρ v`, extended by zero. -/
noncomputable def boundedFns (F : Forest) : Finset (ℕ × ℕ → ℕ) :=
  (F.IN.pi (fun v => Icc 1 v.1)).image (fun g v => if h : v ∈ F.IN then g v h else 0)

lemma mem_boundedFns {F : Forest} {lam : ℕ × ℕ → ℕ} :
    lam ∈ F.boundedFns ↔ (∀ v ∈ F.IN, 1 ≤ lam v ∧ lam v ≤ v.1) ∧ ∀ v ∉ F.IN, lam v = 0 := by
  classical
  unfold boundedFns
  simp only [mem_image, mem_pi, mem_Icc]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp only [dif_pos hv]; exact hg v hv
    · simp only [dif_neg hv]
  · rintro ⟨h1, h2⟩
    refine ⟨fun v _ => lam v, fun v hv => h1 v hv, funext fun v => ?_⟩
    by_cases hv : v ∈ F.IN
    · simp only [dif_pos hv]
    · simp only [dif_neg hv]; exact (h2 v hv).symm

open Classical in
/-- The finite set of valid labelings. -/
noncomputable def labelings (F : Forest) : Finset (ℕ × ℕ → ℕ) :=
  F.boundedFns.filter (F.Valid)

lemma mem_labelings {F : Forest} {lam : ℕ × ℕ → ℕ} :
    lam ∈ F.labelings ↔ F.Valid lam ∧ ∀ v ∉ F.IN, lam v = 0 := by
  classical
  unfold labelings
  rw [mem_filter, mem_boundedFns]
  constructor
  · rintro ⟨⟨-, h⟩, hv⟩; exact ⟨hv, h⟩
  · rintro ⟨hv, h⟩; exact ⟨⟨fun v hm => ⟨(hv v hm).1, (hv v hm).2.1⟩, h⟩, hv⟩

end Forest

open Forest

/-- The variable `x_i`. -/
noncomputable abbrev x (i : ℕ) : Pol := X i

/-- The forest polynomial `P_F = ∑_{λ valid} ∏_{v ∈ IN(F)} x_{λ(v)}` (Definition 2.3). -/
noncomputable def forestPoly (F : Forest) : Pol :=
  ∑ lam ∈ F.labelings, ∏ v ∈ F.IN, x (lam v)

/-! ### Monomials of labelings -/

/-- Exponent vector of a labeling. -/
noncomputable def mono (F : Forest) (lam : ℕ × ℕ → ℕ) : ℕ →₀ ℕ :=
  ∑ v ∈ F.IN, Finsupp.single (lam v) 1

lemma prod_X_eq (F : Forest) (lam : ℕ × ℕ → ℕ) :
    ∏ v ∈ F.IN, x (lam v) = monomial (mono F lam) 1 := by
  rw [mono, monomial_sum_one]; rfl

lemma forestPoly_eq (F : Forest) :
    forestPoly F = ∑ lam ∈ F.labelings, monomial (mono F lam) (1 : ℤ) := by
  simp only [forestPoly, prod_X_eq]

/-- Weight `∑ i eᵢ` of an exponent vector. -/
noncomputable def wt : (ℕ →₀ ℕ) →+ ℕ := Finsupp.weight id

lemma wt_mono (F : Forest) (lam : ℕ × ℕ → ℕ) : wt (mono F lam) = ∑ v ∈ F.IN, lam v := by
  simp [wt, mono, map_sum, Finsupp.weight_apply, Finsupp.sum_single_index]

/-- The labeling `λ = ρ`. -/
noncomputable def Forest.rhoLab (F : Forest) : ℕ × ℕ → ℕ := fun v => if v ∈ F.IN then v.1 else 0

lemma rhoLab_mem (F : Forest) : F.rhoLab ∈ F.labelings := by
  rw [mem_labelings]
  refine ⟨fun v hv => ?_, fun v hv => by simp [rhoLab, hv]⟩
  have hv' := mem_IN.1 hv
  refine ⟨by simp [rhoLab, hv, hv'.1], by simp [rhoLab, hv, rho], fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨hum, hu1⟩ := lc_mem hv hu; simp [rhoLab, hv, hum, hu1]
  · obtain ⟨hum, hu1⟩ := rc_mem hu; simp [rhoLab, hv, hum]; exact hu1

/-- The code as an exponent vector: `x^{c(F)}` is the monomial of `λ = ρ`. -/
noncomputable def codeF (F : Forest) : ℕ →₀ ℕ := mono F F.rhoLab

lemma le_rho_of_mem {F : Forest} {lam : ℕ × ℕ → ℕ} (h : lam ∈ F.labelings) {v : ℕ × ℕ}
    (hv : v ∈ F.IN) : lam v ≤ F.rhoLab v := by
  have := ((mem_labelings.1 h).1 v hv).2.1; simpa [rhoLab, hv, rho] using this

lemma wt_le (F : Forest) {lam : ℕ × ℕ → ℕ} (h : lam ∈ F.labelings) :
    wt (mono F lam) ≤ wt (codeF F) := by
  rw [codeF, wt_mono, wt_mono]; exact sum_le_sum fun v hv => le_rho_of_mem h hv

lemma eq_rhoLab_of_wt {F : Forest} {lam : ℕ × ℕ → ℕ} (h : lam ∈ F.labelings)
    (hw : wt (mono F lam) = wt (codeF F)) : lam = F.rhoLab := by
  rw [codeF, wt_mono, wt_mono] at hw
  have hle : ∀ v ∈ F.IN, lam v ≤ F.rhoLab v := fun v hv => le_rho_of_mem h hv
  have heq := (sum_eq_sum_iff_of_le hle).1 hw
  funext v
  by_cases hv : v ∈ F.IN
  · exact heq v hv
  · rw [(mem_labelings.1 h).2 v hv]; simp [rhoLab, hv]

lemma coeff_forestPoly (F : Forest) (e : ℕ →₀ ℕ) :
    coeff e (forestPoly F) = ((F.labelings.filter (fun lam => mono F lam = e)).card : ℤ) := by
  classical
  rw [forestPoly_eq, coeff_sum]
  simp only [coeff_monomial]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]

/-- Fact 2.5 (coefficient part): `x^{c(F)}` occurs in `P_F` with coefficient one. -/
lemma coeff_codeF (F : Forest) : coeff (codeF F) (forestPoly F) = 1 := by
  classical
  rw [coeff_forestPoly]
  have : F.labelings.filter (fun lam => mono F lam = codeF F) = {F.rhoLab} := by
    ext lam
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact eq_rhoLab_of_wt h1 (by rw [h2])
    · rintro rfl; exact ⟨rhoLab_mem F, rfl⟩
  rw [this]; simp

lemma mem_support_forestPoly {F : Forest} {e : ℕ →₀ ℕ} (h : coeff e (forestPoly F) ≠ 0) :
    ∃ lam ∈ F.labelings, mono F lam = e := by
  classical
  rw [coeff_forestPoly] at h
  obtain ⟨lam, hlam⟩ := Finset.card_ne_zero.1 (by exact_mod_cast h)
  rw [mem_filter] at hlam
  exact ⟨lam, hlam.1, hlam.2⟩

/-- Fact 2.5 (weighted form): every monomial of `P_F` has weight at most that of `x^{c(F)}`, with
equality only for `x^{c(F)}` itself. -/
lemma wt_le_of_coeff {F : Forest} {e : ℕ →₀ ℕ} (h : coeff e (forestPoly F) ≠ 0) :
    wt e ≤ wt (codeF F) ∧ (wt e = wt (codeF F) → e = codeF F) := by
  obtain ⟨lam, hl, rfl⟩ := mem_support_forestPoly h
  refine ⟨wt_le F hl, fun hw => ?_⟩
  rw [eq_rhoLab_of_wt hl hw]; rfl

lemma codeF_apply (F : Forest) (i : ℕ) : codeF F i = F.c i := by
  classical
  simp only [codeF, mono, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [sum_boole]
  cases i with
  | zero =>
    simp only [c_zero, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro v hv; simp [rhoLab, hv]; have := (mem_IN.1 hv).1; omega
  | succ i =>
    have : F.IN.filter (fun v => F.rhoLab v = i + 1) =
        (Icc 1 (F.c (i + 1))).map ⟨fun t => (i + 1, t), fun a b h => by simpa using h⟩ := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_map, mem_Icc, rhoLab, mem_IN]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        simp only [h1, h2, h3, and_self, if_true] at h4
        subst h4; exact ⟨b, ⟨h2, h3⟩, rfl⟩
      · rintro ⟨t, ⟨h1, h2⟩, ht⟩
        have ht' : (i + 1, t) = (a, b) := ht
        simp only [Prod.mk.injEq] at ht'
        obtain ⟨rfl, rfl⟩ := ht'
        simp [h1, h2]
    rw [this, card_map, Nat.card_Icc]; simp

lemma codeF_injective : Function.Injective codeF := by
  intro F G h
  ext i hi
  rw [← codeF_apply, ← codeF_apply, h]

/-- `P_∅ = 1` and `P_F` has zero constant term otherwise. -/
lemma constantCoeff_forestPoly (F : Forest) :
    constantCoeff (forestPoly F) = if F = empty then 1 else 0 := by
  classical
  rw [forestPoly, map_sum]
  split_ifs with h
  · subst h
    have hIN : empty.IN = ∅ := by
      ext v; simp only [mem_IN, c_empty, Finset.notMem_empty, iff_false]; omega
    have : empty.labelings = {fun _ => 0} := by
      ext lam
      simp only [mem_labelings, mem_singleton, hIN, Finset.notMem_empty, not_false_eq_true,
        forall_const]
      constructor
      · rintro ⟨-, h⟩; funext v; exact h v
      · rintro rfl
        exact ⟨fun v hv => by rw [hIN] at hv; exact absurd hv (Finset.notMem_empty v),
          fun _ => rfl⟩
    rw [this, hIN]; simp
  · apply sum_eq_zero; intro lam _
    rw [map_prod]
    have hne : F.IN.Nonempty := by
      rw [← card_pos, card_IN]
      by_contra h0; exact h ((eq_empty_iff_size F).2 (by omega))
    obtain ⟨v, hv⟩ := hne
    exact prod_eq_zero hv (by simp [x])

/-- The variables `x₁, x₂, …`. -/
def posVars : Set ℕ := {m | 1 ≤ m}

lemma forestPoly_mem_supported (F : Forest) :
    forestPoly F ∈ supported ℤ posVars := by
  apply Subalgebra.sum_mem; intro lam hl
  apply Subalgebra.prod_mem; intro v hv
  apply X_mem_supported.2
  exact ((mem_labelings.1 hl).1 v hv).1

end QuasisymmetricBruhat
