import Conjectures.QuasisymmetricBruhat.DTheorem
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Forest expansions

Every polynomial in `x₁, x₂, …` is a unique `ℤ`-combination of forest polynomials.
Uniqueness: in a nonzero combination take a forest `F₀` maximizing `∑ i cᵢ(F₀)`; by Fact 2.5 the
monomial `x^{c(F₀)}` occurs only in `P_{F₀}`, with coefficient one.  Existence: induction on the
weight, peeling `x^e = P_{F(e)} - (lighter monomials)`.

`ecoeff f G` is the coefficient of `P_G` in `f`, and `ecoeff_extract` reads it off after one
divided difference: if `Dⱼ f = xⱼ g` and `j` is terminal in `G`, then
`[P_G] f = [P_{G/j}] g`.
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset Forest

/-- `a` is an expansion of `f` in forest polynomials. -/
def Expansion (f : Pol) (a : Forest →₀ ℤ) : Prop := f = a.sum (fun F c => c • forestPoly F)

lemma expansion_unique_zero {a : Forest →₀ ℤ} (h : a.sum (fun F c => c • forestPoly F) = 0) :
    a = 0 := by
  classical
  by_contra ha
  obtain ⟨F₀, hF₀, hmax⟩ := a.support.exists_max_image (fun F => wt (codeF F))
    (Finsupp.support_nonempty_iff.2 ha)
  have hc := congrArg (coeff (codeF F₀)) h
  rw [Finsupp.sum, coeff_sum, coeff_zero] at hc
  rw [sum_eq_single F₀] at hc
  · rw [coeff_smul, coeff_codeF, smul_eq_mul, mul_one] at hc
    exact (Finsupp.mem_support_iff.1 hF₀) hc
  · intro F hF hne
    rw [coeff_smul]
    by_cases h0 : coeff (codeF F₀) (forestPoly F) = 0
    · rw [h0, smul_zero]
    · obtain ⟨hle, heq⟩ := wt_le_of_coeff h0
      exact absurd (codeF_injective (heq (le_antisymm hle (hmax F hF)))).symm hne
  · intro h'; exact absurd hF₀ h'

lemma expansion_unique {f : Pol} {a b : Forest →₀ ℤ} (ha : Expansion f a) (hb : Expansion f b) :
    a = b := by
  have : (a - b).sum (fun F c => c • forestPoly F) = 0 := by
    rw [Finsupp.sum_sub_index (fun F c d => sub_smul c d _), ← ha, ← hb, sub_self]
  exact sub_eq_zero.1 (expansion_unique_zero this)

/-- The forest with code `e` (for `e 0 = 0`). -/
noncomputable def ofExp (e : ℕ →₀ ℕ) : Forest := Forest.ofCode (fun i => e i) (e.support.sup id)

lemma codeF_ofExp {e : ℕ →₀ ℕ} (h0 : e 0 = 0) : codeF (ofExp e) = e := by
  ext i
  rw [codeF_apply]
  cases i with
  | zero => simp [h0]
  | succ i =>
    unfold ofExp
    rw [c_ofCode_of _ _ _ (by omega)]
    intro k hk
    by_contra hne
    have : k ∈ e.support := Finsupp.mem_support_iff.2 hne
    have := Finset.le_sup (f := id) this
    simp at this; omega

lemma mono_zero_of_mem {F : Forest} {lam : ℕ × ℕ → ℕ} (h : lam ∈ F.labelings) : mono F lam 0 = 0 := by
  classical
  simp only [mono, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  apply sum_eq_zero; intro v hv
  have := ((mem_labelings.1 h).1 v hv).1
  rw [if_neg (by omega)]

lemma monomial_mem_span (e : ℕ →₀ ℕ) (h0 : e 0 = 0) :
    monomial e (1 : ℤ) ∈ Submodule.span ℤ (Set.range forestPoly) := by
  classical
  induction hw : wt e using Nat.strong_induction_on generalizing e with
  | _ n ih =>
    set G := ofExp e
    have hG : codeF G = e := codeF_ofExp h0
    have hP : forestPoly G = monomial e 1 +
        ∑ lam ∈ G.labelings.erase G.rhoLab, monomial (mono G lam) 1 := by
      rw [forestPoly_eq, ← add_sum_erase _ _ (rhoLab_mem G)]
      rw [show mono G G.rhoLab = e from hG]
    have : monomial e (1 : ℤ) = forestPoly G -
        ∑ lam ∈ G.labelings.erase G.rhoLab, monomial (mono G lam) 1 := by
      rw [hP]; ring
    rw [this]
    apply Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self G))
    apply Submodule.sum_mem; intro lam hl
    obtain ⟨hne, hlab⟩ := mem_erase.1 hl
    refine ih (wt (mono G lam)) ?_ _ (mono_zero_of_mem hlab) rfl
    rw [← hw, ← hG]
    exact lt_of_le_of_ne (wt_le G hlab) (fun h => hne (eq_rhoLab_of_wt hlab h))

lemma mem_span_of_supported {f : Pol} (hf : f ∈ supported ℤ posVars) :
    f ∈ Submodule.span ℤ (Set.range forestPoly) := by
  classical
  rw [f.as_sum]
  apply Submodule.sum_mem; intro e he
  rw [show monomial e (coeff e f) = coeff e f • monomial e (1 : ℤ) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  apply Submodule.smul_mem
  apply monomial_mem_span
  by_contra h0
  have : 0 ∈ f.vars := (mem_vars_iff_mem_support 0).2 ⟨e, he, Finsupp.mem_support_iff.2 h0⟩
  have := (mem_supported.1 hf) this
  simp [posVars] at this

lemma exists_expansion {f : Pol} (hf : f ∈ supported ℤ posVars) : ∃ a, Expansion f a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_supported hf)
  exact ⟨c, hc.symm⟩

open Classical in
/-- The coefficient of `P_G` in `f`. -/
noncomputable def ecoeff (f : Pol) : Forest →₀ ℤ :=
  if h : ∃ a, Expansion f a then h.choose else 0

lemma ecoeff_spec {f : Pol} (hf : f ∈ supported ℤ posVars) : Expansion f (ecoeff f) := by
  have h := exists_expansion hf
  rw [ecoeff, dif_pos h]; exact h.choose_spec

lemma ecoeff_eq {f : Pol} {a : Forest →₀ ℤ} (ha : Expansion f a) : ecoeff f = a := by
  have h : ∃ a, Expansion f a := ⟨a, ha⟩
  rw [ecoeff, dif_pos h]; exact expansion_unique h.choose_spec ha

lemma ecoeff_add {f g : Pol} (hf : f ∈ supported ℤ posVars) (hg : g ∈ supported ℤ posVars) :
    ecoeff (f + g) = ecoeff f + ecoeff g := by
  apply ecoeff_eq
  rw [Expansion, Finsupp.sum_add_index' (h := fun F c => c • forestPoly F)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _),
    ← ecoeff_spec hf, ← ecoeff_spec hg]

lemma ecoeff_zero : ecoeff 0 = 0 := ecoeff_eq (by simp [Expansion])

lemma ecoeff_finset_sum (T : Finset Forest) (b : Forest → ℤ) (G : Forest) :
    ecoeff (∑ F ∈ T, b F • forestPoly F) G = if G ∈ T then b G else 0 := by
  classical
  have : Expansion (∑ F ∈ T, b F • forestPoly F) (∑ F ∈ T, Finsupp.single F (b F)) := by
    rw [Expansion, ← Finsupp.sum_finsetSum_index (h := fun F c => c • forestPoly F)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    apply sum_congr rfl; intro F _
    rw [Finsupp.sum_single_index (h := fun F c => c • forestPoly F) (zero_smul _ _)]
  rw [ecoeff_eq this, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [sum_ite_eq']

lemma ecoeff_forestPoly (F G : Forest) : ecoeff (forestPoly F) G = if G = F then 1 else 0 := by
  have := ecoeff_finset_sum {F} (fun _ => 1) G
  simp only [sum_singleton, one_smul, mem_singleton] at this
  exact this

lemma ecoeff_empty {f : Pol} (hf : f ∈ supported ℤ posVars) :
    ecoeff f empty = constantCoeff f := by
  classical
  conv_rhs => rw [ecoeff_spec hf]
  rw [Finsupp.sum, map_sum]
  simp only [map_zsmul, constantCoeff_forestPoly, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h)

lemma D_expansion {f : Pol} {a : Forest →₀ ℤ} (ha : Expansion f a) {j : ℕ} (hj : 1 ≤ j) :
    D j f = x j * ∑ F ∈ a.support.filter (fun F => F.term j), a F • forestPoly (rem j F) := by
  classical
  rw [ha, Finsupp.sum, D_sum, mul_sum, sum_filter]
  apply sum_congr rfl; intro F _
  rw [D_smul, D_forestPoly hj]
  split_ifs
  · rw [mul_smul_comm]
  · simp

/-- Coefficient extraction through one divided difference. -/
theorem ecoeff_extract {f g : Pol} (hf : f ∈ supported ℤ posVars) {j : ℕ} (hj : 1 ≤ j)
    (hD : D j f = x j * g) {G : Forest} (hG : G.term j) :
    ecoeff f G = ecoeff g (rem j G) := by
  classical
  set a := ecoeff f
  have hexp := D_expansion (ecoeff_spec hf) hj
  rw [hD] at hexp
  have hg : g = ∑ F ∈ a.support.filter (fun F => F.term j), a F • forestPoly (rem j F) :=
    mul_left_cancel₀ (X_ne_zero j) hexp
  set S := a.support.filter (fun F => F.term j)
  have hinj : Set.InjOn (rem j) S := fun F hF F' hF' h =>
    rem_injOn (mem_filter.1 hF).2 (mem_filter.1 hF').2 h
  have hg' : g = ∑ F' ∈ S.image (rem j), a (ins j F') • forestPoly F' := by
    rw [hg, sum_image hinj]
    apply sum_congr rfl; intro F hF
    rw [ins_rem (mem_filter.1 hF).2]
  rw [hg', ecoeff_finset_sum, ins_rem hG]
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (mem_image_of_mem _ (mem_filter.2 ⟨Finsupp.mem_support_iff.2 (Ne.symm hne), hG⟩))

end QuasisymmetricBruhat
