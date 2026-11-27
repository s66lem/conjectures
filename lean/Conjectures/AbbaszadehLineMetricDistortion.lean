import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Proof of the Line-Metric Distortion Conjecture of Abbaszadeh et al. (arXiv:2601.02095v1)

This file formalizes a complete proof of the Section 6 conjecture of
M. Abbaszadeh, A. Ansarifar, M. Latifian, and M. Seddighin,
"Metric Distortion with Preference Intensities" (arXiv:2601.02095v1, AAAI 2026):

For two-alternative elections on the 1-Euclidean line under mandatory elicitation
with intensity threshold `α ∈ (0, 1]`, the optimal rule `f^tal_α` achieves worst-case
metric distortion exactly
  `M(α) = max ((3 - α) / (1 + α)) (1 + 2 * α)`,
and no deterministic voting rule achieves strictly smaller distortion.
-/

namespace AbbaszadehLineMetricDistortion

open scoped BigOperators ENNReal

/-- The two alternatives in a two-alternative election. -/
inductive Alt where
  | a1
  | a2
  deriving DecidableEq

/-- The four preference types under mandatory elicitation with threshold `α ∈ (0, 1]`. -/
inductive PrefType where
  | a1PrefA2
  | a2PrefA1
  | a1IntenseA2
  | a2IntenseA1
  deriving DecidableEq

/-- Swap the roles of `a1` and `a2` in a preference type. -/
def swapType : PrefType → PrefType
  | .a1PrefA2 => .a2PrefA1
  | .a2PrefA1 => .a1PrefA2
  | .a1IntenseA2 => .a2IntenseA1
  | .a2IntenseA1 => .a1IntenseA2

/-- Position of an alternative on the real line. -/
def altPos (a₁ a₂ : ℝ) : Alt → ℝ
  | .a1 => a₁
  | .a2 => a₂

/-- Consistency of a single agent's position `xi ∈ ℝ` with preference type `τ`
under mandatory elicitation with threshold `α` and alternatives at `a₁, a₂ ∈ ℝ`. -/
def AgentConsistent (α a₁ a₂ : ℝ) (τ : PrefType) (xi : ℝ) : Prop :=
  match τ with
  | .a1PrefA2 => α * |xi - a₂| < |xi - a₁| ∧ |xi - a₁| ≤ |xi - a₂|
  | .a2PrefA1 => α * |xi - a₁| < |xi - a₂| ∧ |xi - a₂| ≤ |xi - a₁|
  | .a1IntenseA2 => |xi - a₁| ≤ α * |xi - a₂|
  | .a2IntenseA1 => |xi - a₂| ≤ α * |xi - a₁|

/-- Consistency of a full 1-Euclidean placement `(a₁, a₂, x)` with an `N`-agent profile. -/
def Consistent {N : ℕ} (α a₁ a₂ : ℝ) (prof : Fin N → PrefType) (x : Fin N → ℝ) : Prop :=
  ∀ i : Fin N, AgentConsistent α a₁ a₂ (prof i) (x i)

/-- Social cost of an alternative placed at `a ∈ ℝ` for agent positions `x`. -/
def socialCost {N : ℕ} (x : Fin N → ℝ) (a : ℝ) : ℝ :=
  ∑ i : Fin N, |x i - a|

/-- Worst-case distortion of alternative `c` on profile `prof` is at most `t`. -/
def DistLe {N : ℕ} (α : ℝ) (prof : Fin N → PrefType) (c : Alt) (t : ℝ) : Prop :=
  ∀ (a₁ a₂ : ℝ) (x : Fin N → ℝ), Consistent α a₁ a₂ prof x →
    socialCost x (altPos a₁ a₂ c) ≤ t * min (socialCost x a₁) (socialCost x a₂)

/-- The conjectured optimal distortion bound `M(α) = max((3 - α) / (1 + α), 1 + 2α)`. -/
noncomputable def M (α : ℝ) : ℝ :=
  max ((3 - α) / (1 + α)) (1 + 2 * α)

/-- Extended-real worst-case distortion `dist_α(c, prof) ∈ [1, ∞]`. -/
noncomputable def dist {N : ℕ} (α : ℝ) (prof : Fin N → PrefType) (c : Alt) : ℝ≥0∞ :=
  sInf { t : ℝ≥0∞ | ∃ r : ℝ, 1 ≤ r ∧ t = ENNReal.ofReal r ∧ DistLe α prof c r }

/-- The rule `f^tal_α` selecting the alternative with smaller worst-case distortion. -/
noncomputable def fTal {N : ℕ} (α : ℝ) (prof : Fin N → PrefType) : Alt :=
  open Classical in
  if dist α prof .a1 ≤ dist α prof .a2 then .a1 else .a2

/-- Worst-case distortion of a deterministic rule `f` over all nonempty two-alternative elections. -/
noncomputable def ruleDist (α : ℝ) (f : ∀ {N : ℕ}, (Fin N → PrefType) → Alt) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (_ : 0 < N) (prof : Fin N → PrefType), dist α prof (f prof)

/-- The 2-agent symmetric normal-preference profile `(a1 ≻ a2, a2 ≻ a1)`. -/
def profNormal : Fin 2 → PrefType
  | ⟨0, _⟩ => .a1PrefA2
  | ⟨1, _⟩ => .a2PrefA1

/-- The 2-agent symmetric intense-preference profile `(a1 ≫ a2, a2 ≫ a1)`. -/
def profIntense : Fin 2 → PrefType
  | ⟨0, _⟩ => .a1IntenseA2
  | ⟨1, _⟩ => .a2IntenseA1

private lemma socialCost_nonneg {N : ℕ} (x : Fin N → ℝ) (a : ℝ) :
    0 ≤ socialCost x a :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma distLe_a1_iff {N : ℕ} {α t : ℝ} (ht : 1 ≤ t) (prof : Fin N → PrefType) :
    DistLe α prof .a1 t ↔
      ∀ (a₁ a₂ : ℝ) (x : Fin N → ℝ), Consistent α a₁ a₂ prof x →
        socialCost x a₁ ≤ t * socialCost x a₂ := by
  constructor
  · intro h a₁ a₂ x hx
    exact (h a₁ a₂ x hx).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith))
  · intro h a₁ a₂ x hx
    simp only [altPos]
    rw [mul_min_of_nonneg _ _ (by linarith)]
    refine le_min ?_ (h a₁ a₂ x hx)
    have hnn := socialCost_nonneg x a₁
    nlinarith

private lemma agentConsistent_swap (α a₁ a₂ : ℝ) (τ : PrefType) (xi : ℝ) :
    AgentConsistent α a₂ a₁ (swapType τ) xi ↔ AgentConsistent α a₁ a₂ τ xi := by
  cases τ <;> rfl

private lemma distLe_a2_iff_swap {N : ℕ} (α t : ℝ) (prof : Fin N → PrefType) :
    DistLe α prof .a2 t ↔ DistLe α (swapType ∘ prof) .a1 t := by
  constructor
  · intro h a₁ a₂ x hx
    have hx' : Consistent α a₂ a₁ prof x := fun i => by
      have hi := hx i
      simpa [Function.comp, agentConsistent_swap] using hi
    have hres := h a₂ a₁ x hx'
    simpa [altPos, min_comm] using hres
  · intro h a₁ a₂ x hx
    have hx' : Consistent α a₂ a₁ (swapType ∘ prof) x := fun i => by
      simpa [Function.comp, agentConsistent_swap] using hx i
    have hres := h a₂ a₁ x hx'
    simpa [altPos, min_comm] using hres

private lemma distLe_comp_equiv {N : ℕ} (α t : ℝ) (c : Alt)
    (prof : Fin N → PrefType) (e : Fin N ≃ Fin N) :
    DistLe α (prof ∘ e) c t ↔ DistLe α prof c t := by
  constructor
  · intro h a₁ a₂ x hx
    have hx' : Consistent α a₁ a₂ (prof ∘ e) (x ∘ e) := fun i => hx (e i)
    have hres := h a₁ a₂ (x ∘ e) hx'
    have hsum : ∀ a : ℝ, socialCost (x ∘ e) a = socialCost x a := fun a =>
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [hsum, hsum, hsum] at hres
    exact hres
  · intro h a₁ a₂ x hx
    have hx' : Consistent α a₁ a₂ prof (x ∘ e.symm) := fun i => by
      have hi := hx (e.symm i)
      simpa [Function.comp] using hi
    have hres := h a₁ a₂ (x ∘ e.symm) hx'
    have hsum : ∀ a : ℝ, socialCost (x ∘ e.symm) a = socialCost x a := fun a =>
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [hsum, hsum, hsum] at hres
    exact hres

private lemma agentConsistent_normalize {α a₁ a₂ : ℝ} (hne : a₁ ≠ a₂) (τ : PrefType) (xi : ℝ) :
    AgentConsistent α 0 1 τ ((xi - a₁) / (a₂ - a₁)) ↔ AgentConsistent α a₁ a₂ τ xi := by
  set s : ℝ := a₂ - a₁
  have hs : s ≠ 0 := sub_ne_zero.mpr hne.symm
  have hspos : 0 < |s| := abs_pos.mpr hs
  have h0 : |(xi - a₁) / s - 0| = |xi - a₁| / |s| := by
    rw [sub_zero, abs_div]
  have h1 : |(xi - a₁) / s - 1| = |xi - a₂| / |s| := by
    have heq : (xi - a₁) / s - 1 = (xi - a₂) / s := by
      field_simp [hs]
      ring
    rw [heq, abs_div]
  cases τ <;> simp only [AgentConsistent, h0, h1]
  · rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hspos, div_le_div_iff_of_pos_right hspos]
  · rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hspos, div_le_div_iff_of_pos_right hspos]
  · rw [← mul_div_assoc, div_le_div_iff_of_pos_right hspos]
  · rw [← mul_div_assoc, div_le_div_iff_of_pos_right hspos]

private lemma distLe_a1_of_normalized {N : ℕ} {α t : ℝ} (ht : 1 ≤ t) (prof : Fin N → PrefType)
    (h01 : ∀ y : Fin N → ℝ, Consistent α 0 1 prof y →
      ∑ i : Fin N, (|y i| - t * |y i - 1|) ≤ 0) :
    DistLe α prof .a1 t := by
  rw [distLe_a1_iff ht]
  intro a₁ a₂ x hx
  by_cases heq : a₁ = a₂
  · subst heq
    have hnn := socialCost_nonneg x a₁
    nlinarith
  · set s : ℝ := a₂ - a₁
    have hs : s ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
    have hspos : 0 < |s| := abs_pos.mpr hs
    let y : Fin N → ℝ := fun i => (x i - a₁) / s
    have hy : Consistent α 0 1 prof y := fun i =>
      (agentConsistent_normalize heq (prof i) (x i)).mpr (hx i)
    have hsum := h01 y hy
    have hsc1 : socialCost x a₁ = |s| * ∑ i : Fin N, |y i| := by
      rw [socialCost, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hdiv : |y i| = |x i - a₁| / |s| := by simp [y, abs_div]
      rw [hdiv, mul_div_cancel₀ _ (ne_of_gt hspos)]
    have hsc2 : socialCost x a₂ = |s| * ∑ i : Fin N, |y i - 1| := by
      rw [socialCost, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsub : y i - 1 = (x i - a₂) / s := by
        dsimp only [y]
        field_simp [hs]
        ring
      rw [hsub, abs_div, mul_div_cancel₀ _ (ne_of_gt hspos)]
    have hlin : ∑ i : Fin N, |y i| ≤ t * ∑ i : Fin N, |y i - 1| := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
      linarith
    rw [hsc1, hsc2]
    have : |s| * ∑ i : Fin N, |y i| ≤ |s| * (t * ∑ i : Fin N, |y i - 1|) :=
      mul_le_mul_of_nonneg_left hlin (le_of_lt hspos)
    linarith

private noncomputable def uCoeff (α t : ℝ) : ℝ := (1 - t * α) / (1 + α)
private noncomputable def vCoeff (α t : ℝ) : ℝ := (1 - t * α) / (1 - α)

private lemma bound_a1PrefA2 {α t y : ℝ} (ht : 1 ≤ t)
    (h : AgentConsistent α 0 1 .a1PrefA2 y) :
    |y| - t * |y - 1| ≤ (1 - t) / 2 := by
  simp only [AgentConsistent, sub_zero] at h
  have htri : (1 : ℝ) ≤ |y| + |y - 1| := by
    have h1 : |(y - 1) - y| ≤ |y - 1| + |y| := abs_sub (y - 1) y
    have h2 : |(y - 1) - y| = 1 := by
      have : (y - 1) - y = -1 := by ring
      rw [this, abs_neg, abs_one]
    linarith
  have hhalf : (1 : ℝ) / 2 ≤ |y - 1| := by linarith [h.2]
  nlinarith [h.2]

private lemma bound_a1IntenseA2 {α t y : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (ht : 1 ≤ t)
    (h : AgentConsistent α 0 1 .a1IntenseA2 y) :
    |y| - t * |y - 1| ≤ (α - t) / (1 + α) := by
  simp only [AgentConsistent, sub_zero] at h
  have htri : (1 : ℝ) ≤ |y| + |y - 1| := by
    have h1 : |(y - 1) - y| ≤ |y - 1| + |y| := abs_sub (y - 1) y
    have h2 : |(y - 1) - y| = 1 := by
      have : (y - 1) - y = -1 := by ring
      rw [this, abs_neg, abs_one]
    linarith
  have hpos : 0 < 1 + α := by linarith
  have hlow : 1 / (1 + α) ≤ |y - 1| := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have hneg : α - t ≤ 0 := by linarith
  have hstep1 : |y| - t * |y - 1| ≤ (α - t) * |y - 1| := by linarith
  have hstep2 : (α - t) * |y - 1| ≤ (α - t) * (1 / (1 + α)) :=
    mul_le_mul_of_nonpos_left hlow hneg
  calc
    |y| - t * |y - 1| ≤ (α - t) * (1 / (1 + α)) := hstep1.trans hstep2
    _ = (α - t) / (1 + α) := by ring

private lemma bound_a2IntenseA1 {α t y : ℝ} (ht : 1 ≤ t)
    (_ : AgentConsistent α 0 1 .a2IntenseA1 y) :
    |y| - t * |y - 1| ≤ 1 := by
  have htri : |y| ≤ |y - 1| + 1 := by
    have h1 : |(y - 1) + 1| ≤ |y - 1| + |1| := abs_add_le (y - 1) 1
    simpa using h1
  have habs : 0 ≤ |y - 1| := abs_nonneg _
  nlinarith

private lemma bound_a2PrefA1 {α t y : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht : 1 ≤ t)
    (h : AgentConsistent α 0 1 .a2PrefA1 y) :
    |y| - t * |y - 1| ≤ max (uCoeff α t) (vCoeff α t) := by
  simp only [AgentConsistent, sub_zero] at h
  by_cases hy1 : y ≤ 1
  · have hy0 : 0 ≤ y := by
      by_contra hneg
      push Not at hneg
      rw [abs_of_neg hneg, abs_of_nonpos (by linarith : y - 1 ≤ 0)] at h
      linarith [h.2]
    rw [abs_of_nonneg hy0, abs_of_nonpos (by linarith : y - 1 ≤ 0)] at h ⊢
    have hpos : 0 < 1 + α := by linarith
    have hyub : y ≤ 1 / (1 + α) := by
      rw [le_div_iff₀ hpos]
      linarith [h.1]
    have hbound : y - t * -(y - 1) ≤ uCoeff α t := by
      rw [uCoeff, le_div_iff₀ hpos]
      have hmul : y * (1 + α) ≤ 1 := (le_div_iff₀ hpos).mp hyub
      nlinarith
    exact hbound.trans (le_max_left _ _)
  · push Not at hy1
    have hy0 : 0 ≤ y := by linarith
    rw [abs_of_nonneg hy0, abs_of_pos (by linarith : 0 < y - 1)] at h ⊢
    have hpos : 0 < 1 - α := by linarith
    have hylb : 1 / (1 - α) ≤ y := by
      rw [div_le_iff₀ hpos]
      linarith [h.1]
    have hbound : y - t * (y - 1) ≤ vCoeff α t := by
      rw [vCoeff, le_div_iff₀ hpos]
      have hmul : 1 ≤ y * (1 - α) := (div_le_iff₀ hpos).mp hylb
      nlinarith
    exact hbound.trans (le_max_right _ _)

private noncomputable def B1 (α t n₁ n₂ n₃ n₄ : ℝ) : ℝ :=
  ((1 - t) / 2) * n₁ + uCoeff α t * n₂ + ((α - t) / (1 + α)) * n₃ + n₄

private noncomputable def B2 (α t n₁ n₂ n₃ n₄ : ℝ) : ℝ :=
  ((1 - t) / 2) * n₁ + vCoeff α t * n₂ + ((α - t) / (1 + α)) * n₃ + n₄

private lemma count_sum_le {N : ℕ} {α t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht : 1 ≤ t)
    (prof : Fin N → PrefType) (y : Fin N → ℝ) (hy : Consistent α 0 1 prof y) :
    let n₁ : ℝ := ((Finset.univ.filter fun i => prof i = .a1PrefA2).card : ℝ)
    let n₂ : ℝ := ((Finset.univ.filter fun i => prof i = .a2PrefA1).card : ℝ)
    let n₃ : ℝ := ((Finset.univ.filter fun i => prof i = .a1IntenseA2).card : ℝ)
    let n₄ : ℝ := ((Finset.univ.filter fun i => prof i = .a2IntenseA1).card : ℝ)
    ∑ i : Fin N, (|y i| - t * |y i - 1|) ≤
      max (B1 α t n₁ n₂ n₃ n₄) (B2 α t n₁ n₂ n₃ n₄) := by
  intro n₁ n₂ n₃ n₄
  let w : PrefType → ℝ
    | .a1PrefA2 => (1 - t) / 2
    | .a2PrefA1 => max (uCoeff α t) (vCoeff α t)
    | .a1IntenseA2 => (α - t) / (1 + α)
    | .a2IntenseA1 => 1
  have hpoint : ∑ i : Fin N, (|y i| - t * |y i - 1|) ≤ ∑ i : Fin N, w (prof i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := hy i
    cases hpi : prof i with
    | a1PrefA2 => rw [hpi] at hi; exact bound_a1PrefA2 ht hi
    | a2PrefA1 => rw [hpi] at hi; exact bound_a2PrefA1 hα0 hα1 ht hi
    | a1IntenseA2 => rw [hpi] at hi; exact bound_a1IntenseA2 hα0 (le_of_lt hα1) ht hi
    | a2IntenseA1 => rw [hpi] at hi; exact bound_a2IntenseA1 ht hi
  have hsplit : ∑ i : Fin N, w (prof i) =
      ((1 - t) / 2) * n₁ + max (uCoeff α t) (vCoeff α t) * n₂ +
        ((α - t) / (1 + α)) * n₃ + n₄ := by
    have hterm : ∀ i : Fin N,
        w (prof i) =
          (if prof i = .a1PrefA2 then (1 - t) / 2 else 0) +
          (if prof i = .a2PrefA1 then max (uCoeff α t) (vCoeff α t) else 0) +
          (if prof i = .a1IntenseA2 then (α - t) / (1 + α) else 0) +
          (if prof i = .a2IntenseA1 then (1 : ℝ) else 0) := by
      intro i
      cases prof i <;> simp [w]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hn2 : 0 ≤ n₂ := Nat.cast_nonneg _
  have hmax : ((1 - t) / 2) * n₁ + max (uCoeff α t) (vCoeff α t) * n₂ +
      ((α - t) / (1 + α)) * n₃ + n₄ = max (B1 α t n₁ n₂ n₃ n₄) (B2 α t n₁ n₂ n₃ n₄) := by
    rcases le_total (uCoeff α t) (vCoeff α t) with huv | hvu
    · have hB : B1 α t n₁ n₂ n₃ n₄ ≤ B2 α t n₁ n₂ n₃ n₄ := by
        simp only [B1, B2]
        nlinarith
      rw [max_eq_right huv, max_eq_right hB]
      rfl
    · have hB : B2 α t n₁ n₂ n₃ n₄ ≤ B1 α t n₁ n₂ n₃ n₄ := by
        simp only [B1, B2]
        nlinarith
      rw [max_eq_left hvu, max_eq_left hB]
      rfl
  linarith

/-- Key pairing coefficients at `t = M(α)` are all nonpositive. -/
lemma pairing_coeffs_nonpos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - M α) / 2 + uCoeff α (M α) ≤ 0 ∧
    (1 - M α) / 2 + vCoeff α (M α) ≤ 0 ∧
    (α - M α) / (1 + α) + 1 ≤ 0 := by
  have hM1 : (3 - α) / (1 + α) ≤ M α := le_max_left _ _
  have hM2 : 1 + 2 * α ≤ M α := le_max_right _ _
  have hpos1 : 0 < 1 + α := by linarith
  have hpos2 : 0 < 1 - α := by linarith
  have hM1' : 3 - α ≤ M α * (1 + α) := (div_le_iff₀ hpos1).mp hM1
  refine ⟨?_, ?_, ?_⟩
  · rw [uCoeff]
    have hnum : (1 - M α) * (1 + α) + 2 * (1 - M α * α) ≤ 0 := by
      have haux : 3 + α ≤ M α * (1 + 3 * α) := by
        have hdiff : (3 - α) * (1 + 3 * α) - (3 + α) * (1 + α) = 4 * α * (1 - α) := by ring
        have hprod : (3 + α) * (1 + α) ≤ (3 - α) * (1 + 3 * α) := by nlinarith
        have hstep : (3 - α) * (1 + 3 * α) ≤ M α * (1 + α) * (1 + 3 * α) :=
          mul_le_mul_of_nonneg_right hM1' (by linarith)
        nlinarith
      nlinarith
    have heq : (1 - M α) / 2 + (1 - M α * α) / (1 + α) =
        ((1 - M α) * (1 + α) + 2 * (1 - M α * α)) / (2 * (1 + α)) := by
      field_simp [ne_of_gt hpos1]
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hnum (by linarith)
  · rw [vCoeff]
    have hnum : (1 - M α) * (1 - α) + 2 * (1 - M α * α) ≤ 0 := by nlinarith
    have heq : (1 - M α) / 2 + (1 - M α * α) / (1 - α) =
        ((1 - M α) * (1 - α) + 2 * (1 - M α * α)) / (2 * (1 - α)) := by
      field_simp [ne_of_gt hpos2]
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hnum (by linarith)
  · have heq : (α - M α) / (1 + α) + 1 = (1 + 2 * α - M α) / (1 + α) := by
      field_simp [ne_of_gt hpos1]
      ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos1)

/-- For every `α ∈ (0, 1)` and nonnegative type counts `(n₁, n₂, n₃, n₄)`,
at least one of the two alternatives satisfies both linear forms at `t = M(α)`. -/
lemma key_pairing_dichotomy {α n₁ n₂ n₃ n₄ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hn1 : 0 ≤ n₁) (hn2 : 0 ≤ n₂) (hn3 : 0 ≤ n₃) (hn4 : 0 ≤ n₄) :
    (B1 α (M α) n₁ n₂ n₃ n₄ ≤ 0 ∧ B2 α (M α) n₁ n₂ n₃ n₄ ≤ 0) ∨
    (B1 α (M α) n₂ n₁ n₄ n₃ ≤ 0 ∧ B2 α (M α) n₂ n₁ n₄ n₃ ≤ 0) := by
  obtain ⟨hcu, hcv, hci⟩ := pairing_coeffs_nonpos hα0 hα1
  have h11 : B1 α (M α) n₁ n₂ n₃ n₄ + B1 α (M α) n₂ n₁ n₄ n₃ ≤ 0 := by
    dsimp only [B1]
    nlinarith
  have h12 : B1 α (M α) n₁ n₂ n₃ n₄ + B2 α (M α) n₂ n₁ n₄ n₃ ≤ 0 := by
    dsimp only [B1, B2]
    nlinarith
  have h21 : B2 α (M α) n₁ n₂ n₃ n₄ + B1 α (M α) n₂ n₁ n₄ n₃ ≤ 0 := by
    dsimp only [B1, B2]
    nlinarith
  have h22 : B2 α (M α) n₁ n₂ n₃ n₄ + B2 α (M α) n₂ n₁ n₄ n₃ ≤ 0 := by
    dsimp only [B2]
    nlinarith
  by_cases ha : B1 α (M α) n₁ n₂ n₃ n₄ ≤ 0 ∧ B2 α (M α) n₁ n₂ n₃ n₄ ≤ 0
  · exact Or.inl ha
  · refine Or.inr ⟨?_, ?_⟩
    · by_contra hpos
      push Not at hpos
      by_cases h1 : B1 α (M α) n₁ n₂ n₃ n₄ ≤ 0
      · have h2 : 0 < B2 α (M α) n₁ n₂ n₃ n₄ := by
          by_contra hle; push Not at hle; exact ha ⟨h1, hle⟩
        linarith
      · push Not at h1; linarith
    · by_contra hpos
      push Not at hpos
      by_cases h1 : B1 α (M α) n₁ n₂ n₃ n₄ ≤ 0
      · have h2 : 0 < B2 α (M α) n₁ n₂ n₃ n₄ := by
          by_contra hle; push Not at hle; exact ha ⟨h1, hle⟩
        linarith
      · push Not at h1; linarith

private lemma one_le_M {α : ℝ} (hα0 : 0 < α) : 1 ≤ M α := by
  have : 1 ≤ 1 + 2 * α := by linarith
  exact this.trans (le_max_right _ _)

/-- **Upper Bound Theorem:** For every `α ∈ (0, 1]` and every two-alternative profile on the line,
at least one of the two alternatives has worst-case distortion at most `M(α)`. -/
theorem exists_alt_distLe_M {N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (prof : Fin N → PrefType) :
    DistLe α prof .a1 (M α) ∨ DistLe α prof .a2 (M α) := by
  have hM1 : 1 ≤ M α := one_le_M hα0
  rcases lt_or_eq_of_le hα1 with hlt | rfl
  · let n₁ : ℝ := ((Finset.univ.filter fun i => prof i = .a1PrefA2).card : ℝ)
    let n₂ : ℝ := ((Finset.univ.filter fun i => prof i = .a2PrefA1).card : ℝ)
    let n₃ : ℝ := ((Finset.univ.filter fun i => prof i = .a1IntenseA2).card : ℝ)
    let n₄ : ℝ := ((Finset.univ.filter fun i => prof i = .a2IntenseA1).card : ℝ)
    have hdich := key_pairing_dichotomy (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) (n₄ := n₄) hα0 hlt
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rcases hdich with ⟨hB1, hB2⟩ | ⟨hB1, hB2⟩
    · left
      refine distLe_a1_of_normalized hM1 prof fun y hy => ?_
      have hle := count_sum_le hα0 hlt hM1 prof y hy
      exact hle.trans (max_le hB1 hB2)
    · right
      rw [distLe_a2_iff_swap]
      refine distLe_a1_of_normalized hM1 (swapType ∘ prof) fun y hy => ?_
      have hle := count_sum_le hα0 hlt hM1 (swapType ∘ prof) y hy
      have hc1 : (Finset.univ.filter fun i => (swapType ∘ prof) i = .a1PrefA2) =
          (Finset.univ.filter fun i => prof i = .a2PrefA1) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
        cases prof i <;> simp [swapType]
      have hc2 : (Finset.univ.filter fun i => (swapType ∘ prof) i = .a2PrefA1) =
          (Finset.univ.filter fun i => prof i = .a1PrefA2) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
        cases prof i <;> simp [swapType]
      have hc3 : (Finset.univ.filter fun i => (swapType ∘ prof) i = .a1IntenseA2) =
          (Finset.univ.filter fun i => prof i = .a2IntenseA1) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
        cases prof i <;> simp [swapType]
      have hc4 : (Finset.univ.filter fun i => (swapType ∘ prof) i = .a2IntenseA1) =
          (Finset.univ.filter fun i => prof i = .a1IntenseA2) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
        cases prof i <;> simp [swapType]
      simp only [hc1, hc2, hc3, hc4] at hle
      exact hle.trans (max_le hB1 hB2)
  · have hMval : M 1 = 3 := by
      unfold M
      norm_num
    let n₃ : ℝ := ((Finset.univ.filter fun i => prof i = .a1IntenseA2).card : ℝ)
    let n₄ : ℝ := ((Finset.univ.filter fun i => prof i = .a2IntenseA1).card : ℝ)
    rcases le_total n₄ n₃ with h43 | h34
    · left
      refine distLe_a1_of_normalized hM1 prof fun y hy => ?_
      have hpoint : ∑ i : Fin N, (|y i| - M 1 * |y i - 1|) ≤
          ∑ i : Fin N, (if prof i = .a1IntenseA2 then (-1 : ℝ) else
            if prof i = .a2IntenseA1 then 1 else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := hy i
        cases hpi : prof i with
        | a1PrefA2 =>
          rw [hpi] at hi
          simp only [AgentConsistent, one_mul] at hi
          linarith
        | a2PrefA1 =>
          rw [hpi] at hi
          simp only [AgentConsistent, one_mul] at hi
          linarith
        | a1IntenseA2 =>
          rw [hpi] at hi
          have hb := bound_a1IntenseA2 (by norm_num) (le_refl 1) hM1 hi
          rw [hMval] at hb ⊢
          norm_num at hb
          simpa using hb
        | a2IntenseA1 =>
          rw [hpi] at hi
          have hb := bound_a2IntenseA1 hM1 hi
          simpa using hb
      have heval : ∑ i : Fin N,
          (if prof i = .a1IntenseA2 then (-1 : ℝ) else
            if prof i = .a2IntenseA1 then 1 else 0) = -n₃ + n₄ := by
        have hterm : ∀ i : Fin N,
            (if prof i = .a1IntenseA2 then (-1 : ℝ) else
              if prof i = .a2IntenseA1 then 1 else 0) =
            (if prof i = .a1IntenseA2 then (-1 : ℝ) else 0) +
            (if prof i = .a2IntenseA1 then (1 : ℝ) else 0) := by
          intro i; cases prof i <;> simp
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul]
        dsimp only [n₃, n₄]
        ring
      linarith
    · right
      rw [distLe_a2_iff_swap]
      refine distLe_a1_of_normalized hM1 (swapType ∘ prof) fun y hy => ?_
      have hpoint : ∑ i : Fin N, (|y i| - M 1 * |y i - 1|) ≤
          ∑ i : Fin N, (if prof i = .a2IntenseA1 then (-1 : ℝ) else
            if prof i = .a1IntenseA2 then 1 else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := hy i
        cases hpi : prof i with
        | a1PrefA2 =>
          simp only [Function.comp, hpi, swapType, AgentConsistent, one_mul] at hi
          linarith
        | a2PrefA1 =>
          simp only [Function.comp, hpi, swapType, AgentConsistent, one_mul] at hi
          linarith
        | a1IntenseA2 =>
          simp only [Function.comp, hpi, swapType] at hi
          have hb := bound_a2IntenseA1 hM1 hi
          simpa using hb
        | a2IntenseA1 =>
          simp only [Function.comp, hpi, swapType] at hi
          have hb := bound_a1IntenseA2 (by norm_num) (le_refl 1) hM1 hi
          rw [hMval] at hb ⊢
          norm_num at hb
          simpa using hb
      have heval : ∑ i : Fin N,
          (if prof i = .a2IntenseA1 then (-1 : ℝ) else
            if prof i = .a1IntenseA2 then 1 else 0) = -n₄ + n₃ := by
        have hterm : ∀ i : Fin N,
            (if prof i = .a2IntenseA1 then (-1 : ℝ) else
              if prof i = .a1IntenseA2 then 1 else 0) =
            (if prof i = .a2IntenseA1 then (-1 : ℝ) else 0) +
            (if prof i = .a1IntenseA2 then (1 : ℝ) else 0) := by
          intro i; cases prof i <;> simp
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul]
        dsimp only [n₃, n₄]
        ring
      linarith

private lemma dist_le_of_distLe {N : ℕ} {α r : ℝ} {prof : Fin N → PrefType} {c : Alt}
    (hr : 1 ≤ r) (h : DistLe α prof c r) :
    dist α prof c ≤ ENNReal.ofReal r :=
  sInf_le ⟨r, hr, rfl, h⟩

private lemma ofReal_le_dist {N : ℕ} {α r : ℝ} {prof : Fin N → PrefType} {c : Alt}
    (h : ∀ t : ℝ, t < r → ¬ DistLe α prof c t) :
    ENNReal.ofReal r ≤ dist α prof c := by
  refine le_sInf ?_
  rintro _ ⟨s, _, rfl, hs⟩
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hlt
  push Not at hlt
  exact h s hlt hs

private lemma profIntense_not_distLe_a1 {α t : ℝ} (hα0 : 0 < α)
    (ht : t < 1 + 2 * α) :
    ¬ DistLe α profIntense .a1 t := by
  intro hdist
  let x : Fin 2 → ℝ := fun i => match i with
    | ⟨0, _⟩ => α / (1 + α)
    | ⟨1, _⟩ => 1
  have hpos : 0 < 1 + α := by linarith
  have hcons : Consistent α 0 1 profIntense x := by
    intro i
    fin_cases i
    · change |α / (1 + α) - 0| ≤ α * |α / (1 + α) - 1|
      have h0 : 0 ≤ α / (1 + α) := div_nonneg (le_of_lt hα0) (le_of_lt hpos)
      have h1 : α / (1 + α) - 1 = -(1 / (1 + α)) := by
        field_simp [ne_of_gt hpos]
        ring
      rw [sub_zero, abs_of_nonneg h0, h1, abs_neg, abs_of_pos (one_div_pos.mpr hpos)]
      ring_nf
      exact le_refl _
    · change |1 - 1| ≤ α * |1 - 0|
      simp only [sub_self, abs_zero, sub_zero, abs_one, mul_one]
      exact le_of_lt hα0
  have hres := hdist 0 1 x hcons
  have hsc0 : socialCost x 0 = (1 + 2 * α) / (1 + α) := by
    rw [socialCost, Fin.sum_univ_two]
    change |α / (1 + α) - 0| + |1 - 0| = (1 + 2 * α) / (1 + α)
    have h0 : 0 ≤ α / (1 + α) := div_nonneg (le_of_lt hα0) (le_of_lt hpos)
    rw [sub_zero, abs_of_nonneg h0, sub_zero, abs_one]
    field_simp [ne_of_gt hpos]
    ring
  have hsc1 : socialCost x 1 = 1 / (1 + α) := by
    rw [socialCost, Fin.sum_univ_two]
    change |α / (1 + α) - 1| + |1 - 1| = 1 / (1 + α)
    have h1 : α / (1 + α) - 1 = -(1 / (1 + α)) := by
      field_simp [ne_of_gt hpos]
      ring
    rw [h1, abs_neg, abs_of_pos (one_div_pos.mpr hpos), sub_self, abs_zero, add_zero]
  have hmin : min (socialCost x 0) (socialCost x 1) = 1 / (1 + α) := by
    rw [hsc0, hsc1]
    refine min_eq_right ?_
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hpos)
  simp only [altPos] at hres
  rw [hmin, hsc0, mul_one_div] at hres
  have hcmp : 1 + 2 * α ≤ t := (div_le_div_iff_of_pos_right hpos).mp hres
  linarith

private lemma profIntense_distLe_a1 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    DistLe α profIntense .a1 (1 + 2 * α) := by
  have ht : 1 ≤ 1 + 2 * α := by linarith
  refine distLe_a1_of_normalized ht profIntense fun y hy => ?_
  rw [Fin.sum_univ_two]
  have h0 := bound_a1IntenseA2 hα0 hα1 ht (hy 0)
  have h1 := bound_a2IntenseA1 ht (hy 1)
  have hpos : 0 < 1 + α := by linarith
  have hcancel : (α - (1 + 2 * α)) / (1 + α) + 1 = 0 := by
    field_simp [ne_of_gt hpos]
    ring
  linarith

private lemma swap_profIntense :
    swapType ∘ profIntense = profIntense ∘ Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
  funext i
  fin_cases i <;> rfl

/-- Exact distortion of both alternatives on the intense profile `(0, 0, 1, 1)`. -/
theorem dist_profIntense {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (c : Alt) :
    dist α profIntense c = ENNReal.ofReal (1 + 2 * α) := by
  have h1 : dist α profIntense .a1 = ENNReal.ofReal (1 + 2 * α) :=
    le_antisymm
      (dist_le_of_distLe (by linarith) (profIntense_distLe_a1 hα0 hα1))
      (ofReal_le_dist fun t ht => profIntense_not_distLe_a1 hα0 ht)
  cases c with
  | a1 => exact h1
  | a2 =>
    have heq : ∀ t : ℝ, DistLe α profIntense .a2 t ↔ DistLe α profIntense .a1 t := fun t => by
      rw [distLe_a2_iff_swap, swap_profIntense, distLe_comp_equiv]
    have hd : dist α profIntense .a2 = dist α profIntense .a1 := by
      unfold dist
      simp_rw [heq]
    rw [hd, h1]

private lemma profNormal_not_distLe_a1 {α t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ht : t < (3 - α) / (1 + α)) :
    ¬ DistLe α profNormal .a1 t := by
  intro hdist
  have hpos1 : 0 < 1 + α := by linarith
  have hpos2 : 0 < 1 - α := by linarith
  have hnum : 0 < (3 - α) - t * (1 + α) := by
    have : t * (1 + α) < 3 - α := (lt_div_iff₀ hpos1).mp ht
    linarith
  set δ : ℝ := ((3 - α) - t * (1 + α)) / (2 * (1 - α))
  have hδ : 0 < δ := div_pos hnum (by linarith)
  set ε : ℝ := δ / (2 * (|t| + 1))
  have hden : 0 < 2 * (|t| + 1) := by linarith [abs_nonneg t]
  have hε : 0 < ε := div_pos hδ hden
  let x : Fin 2 → ℝ := fun i => match i with
    | ⟨0, _⟩ => 1 / 2
    | ⟨1, _⟩ => 1 / (1 - α) + ε
  have hgt1 : 1 < 1 / (1 - α) := by
    rw [one_lt_div hpos2]
    linarith
  have hcons : Consistent α 0 1 profNormal x := by
    intro i
    fin_cases i
    · change α * |(1 : ℝ) / 2 - 1| < |(1 : ℝ) / 2 - 0| ∧ |(1 : ℝ) / 2 - 0| ≤ |(1 : ℝ) / 2 - 1|
      have h12 : |(1 : ℝ) / 2 - 1| = 1 / 2 := by norm_num
      have h02 : |(1 : ℝ) / 2 - 0| = 1 / 2 := by norm_num
      rw [h12, h02]
      exact ⟨by nlinarith, le_refl _⟩
    · change α * |1 / (1 - α) + ε - 0| < |1 / (1 - α) + ε - 1| ∧
        |1 / (1 - α) + ε - 1| ≤ |1 / (1 - α) + ε - 0|
      have hx0 : 0 < 1 / (1 - α) + ε := by linarith
      have hx1 : 0 < 1 / (1 - α) + ε - 1 := by linarith
      rw [sub_zero, abs_of_pos hx0, abs_of_pos hx1]
      have hsub : 1 / (1 - α) - 1 = α / (1 - α) := by
        field_simp [ne_of_gt hpos2]
        ring
      have hmul : α * (1 / (1 - α)) = α / (1 - α) := by ring
      constructor
      · nlinarith
      · linarith
  have hres := hdist 0 1 x hcons
  have hsc0 : socialCost x 0 = (3 - α) / (2 * (1 - α)) + ε := by
    rw [socialCost, Fin.sum_univ_two]
    change |(1 : ℝ) / 2 - 0| + |1 / (1 - α) + ε - 0| = (3 - α) / (2 * (1 - α)) + ε
    have h02 : |(1 : ℝ) / 2 - 0| = 1 / 2 := by norm_num
    have hx0 : 0 < 1 / (1 - α) + ε := by linarith
    rw [h02, sub_zero, abs_of_pos hx0]
    field_simp [ne_of_gt hpos2]
    ring
  have hsc1 : socialCost x 1 = (1 + α) / (2 * (1 - α)) + ε := by
    rw [socialCost, Fin.sum_univ_two]
    change |(1 : ℝ) / 2 - 1| + |1 / (1 - α) + ε - 1| = (1 + α) / (2 * (1 - α)) + ε
    have h12 : |(1 : ℝ) / 2 - 1| = 1 / 2 := by norm_num
    have hx1 : 0 < 1 / (1 - α) + ε - 1 := by linarith
    rw [h12, abs_of_pos hx1]
    field_simp [ne_of_gt hpos2]
    ring
  have hmin : min (socialCost x 0) (socialCost x 1) = socialCost x 1 := by
    refine min_eq_right ?_
    rw [hsc0, hsc1]
    have : (1 + α) / (2 * (1 - α)) ≤ (3 - α) / (2 * (1 - α)) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  simp only [altPos] at hres
  rw [hmin] at hres
  have hdiff : socialCost x 0 - t * socialCost x 1 = δ + (1 - t) * ε := by
    rw [hsc0, hsc1]
    dsimp only [δ]
    ring
  have htbound : t - 1 ≤ |t| + 1 := by linarith [le_abs_self t]
  have hprod : (t - 1) * ε ≤ δ / 2 := by
    have h1 : (t - 1) * ε ≤ (|t| + 1) * ε := mul_le_mul_of_nonneg_right htbound (le_of_lt hε)
    have h2 : (|t| + 1) * ε = δ / 2 := by
      dsimp only [ε]
      have hne : |t| + 1 ≠ 0 := by linarith [abs_nonneg t]
      field_simp [hne]
    linarith
  linarith

private lemma profNormal_distLe_a1 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    DistLe α profNormal .a1 ((3 - α) / (1 + α)) := by
  have hpos1 : 0 < 1 + α := by linarith
  have hpos2 : 0 < 1 - α := by linarith
  have ht : 1 ≤ (3 - α) / (1 + α) := by
    rw [le_div_iff₀ hpos1]
    linarith
  refine distLe_a1_of_normalized ht profNormal fun y hy => ?_
  rw [Fin.sum_univ_two]
  have h0 := bound_a1PrefA2 ht (hy 0)
  have h1 := bound_a2PrefA1 hα0 hα1 ht (hy 1)
  have hsum_v : (1 - (3 - α) / (1 + α)) / 2 + vCoeff α ((3 - α) / (1 + α)) = 0 := by
    rw [vCoeff]
    field_simp [ne_of_gt hpos1, ne_of_gt hpos2]
    ring
  have hsum_u : (1 - (3 - α) / (1 + α)) / 2 + uCoeff α ((3 - α) / (1 + α)) ≤ 0 := by
    rw [uCoeff]
    have heq : (1 - (3 - α) / (1 + α)) / 2 + (1 - (3 - α) / (1 + α) * α) / (1 + α) =
        -(2 * α * (1 - α)) / (1 + α) ^ 2 := by
      field_simp [ne_of_gt hpos1]
      ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  have hmax : (1 - (3 - α) / (1 + α)) / 2 +
      max (uCoeff α ((3 - α) / (1 + α))) (vCoeff α ((3 - α) / (1 + α))) ≤ 0 := by
    rcases le_total (uCoeff α ((3 - α) / (1 + α))) (vCoeff α ((3 - α) / (1 + α))) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  linarith

private lemma swap_profNormal :
    swapType ∘ profNormal = profNormal ∘ Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
  funext i
  fin_cases i <;> rfl

/-- Exact distortion of both alternatives on the normal profile `(1, 1, 0, 0)` for `α ∈ (0, 1)`. -/
theorem dist_profNormal {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (c : Alt) :
    dist α profNormal c = ENNReal.ofReal ((3 - α) / (1 + α)) := by
  have hpos1 : 0 < 1 + α := by linarith
  have ht : 1 ≤ (3 - α) / (1 + α) := by
    rw [le_div_iff₀ hpos1]
    linarith
  have h1 : dist α profNormal .a1 = ENNReal.ofReal ((3 - α) / (1 + α)) :=
    le_antisymm
      (dist_le_of_distLe ht (profNormal_distLe_a1 hα0 hα1))
      (ofReal_le_dist fun t ht' => profNormal_not_distLe_a1 hα0 hα1 ht')
  cases c with
  | a1 => exact h1
  | a2 =>
    have heq : ∀ t : ℝ, DistLe α profNormal .a2 t ↔ DistLe α profNormal .a1 t := fun t => by
      rw [distLe_a2_iff_swap, swap_profNormal, distLe_comp_equiv]
    have hd : dist α profNormal .a2 = dist α profNormal .a1 := by
      unfold dist
      simp_rw [heq]
    rw [hd, h1]

/-- For every profile, `f^tal_α` achieves the minimum of the two alternatives' distortions. -/
theorem dist_fTal_eq_min {N : ℕ} (α : ℝ) (prof : Fin N → PrefType) :
    dist α prof (fTal α prof) = min (dist α prof .a1) (dist α prof .a2) := by
  unfold fTal
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

/-- **Universal Lower Bound:** Every deterministic voting rule on 1-Euclidean two-alternative
elections under mandatory elicitation has worst-case distortion at least `M(α)`. -/
theorem any_rule_ruleDist_ge {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (f : ∀ {N : ℕ}, (Fin N → PrefType) → Alt) :
    ENNReal.ofReal (M α) ≤ ruleDist α f := by
  have hM : ENNReal.ofReal (M α) =
      max (ENNReal.ofReal ((3 - α) / (1 + α))) (ENNReal.ofReal (1 + 2 * α)) := by
    unfold M
    exact ENNReal.ofReal_max _ _
  rw [hM]
  have hint : ENNReal.ofReal (1 + 2 * α) ≤ ruleDist α f := by
    calc
      ENNReal.ofReal (1 + 2 * α) = dist α profIntense (f profIntense) :=
        (dist_profIntense hα0 hα1 (f profIntense)).symm
      _ ≤ ⨆ (prof : Fin 2 → PrefType), dist α prof (f prof) :=
        le_iSup (fun prof => dist α prof (f prof)) profIntense
      _ ≤ ⨆ (_ : 0 < (2 : ℕ)) (prof : Fin 2 → PrefType), dist α prof (f prof) :=
        le_iSup (fun _ : 0 < (2 : ℕ) => ⨆ prof, dist α prof (f prof)) (by decide : 0 < 2)
      _ ≤ ruleDist α f :=
        le_iSup (fun N => ⨆ (_ : 0 < N) (prof : Fin N → PrefType), dist α prof (f prof)) 2
  refine max_le ?_ hint
  rcases lt_or_eq_of_le hα1 with hlt | rfl
  · calc
      ENNReal.ofReal ((3 - α) / (1 + α)) = dist α profNormal (f profNormal) :=
        (dist_profNormal hα0 hlt (f profNormal)).symm
      _ ≤ ⨆ (prof : Fin 2 → PrefType), dist α prof (f prof) :=
        le_iSup (fun prof => dist α prof (f prof)) profNormal
      _ ≤ ⨆ (_ : 0 < (2 : ℕ)) (prof : Fin 2 → PrefType), dist α prof (f prof) :=
        le_iSup (fun _ : 0 < (2 : ℕ) => ⨆ prof, dist α prof (f prof)) (by decide : 0 < 2)
      _ ≤ ruleDist α f :=
        le_iSup (fun N => ⨆ (_ : 0 < N) (prof : Fin N → PrefType), dist α prof (f prof)) 2
  · have h13 : (3 - (1 : ℝ)) / (1 + 1) ≤ 1 + 2 * 1 := by norm_num
    exact (ENNReal.ofReal_le_ofReal h13).trans hint

/-- **Main Theorem (Abbaszadeh–Ansarifar–Latifian–Seddighin Conjecture):**
For every `α ∈ (0, 1]`, the rule `f^tal_α` has worst-case line-metric distortion
exactly `M(α) = max((3 - α) / (1 + α), 1 + 2α)` on two-alternative elections
under mandatory elicitation. -/
theorem fTal_ruleDist_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ruleDist α (fun prof => fTal α prof) = ENNReal.ofReal (M α) := by
  refine le_antisymm ?_ (any_rule_ruleDist_ge hα0 hα1 (fun prof => fTal α prof))
  refine iSup_le fun N => iSup_le fun _ => iSup_le fun prof => ?_
  rw [dist_fTal_eq_min]
  have hM1 : 1 ≤ M α := one_le_M hα0
  rcases exists_alt_distLe_M hα0 hα1 prof with h1 | h2
  · exact (min_le_left _ _).trans (dist_le_of_distLe hM1 h1)
  · exact (min_le_right _ _).trans (dist_le_of_distLe hM1 h2)

end AbbaszadehLineMetricDistortion
