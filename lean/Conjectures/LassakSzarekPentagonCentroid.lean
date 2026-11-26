import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Disproof of Lassak–Szarek's Conjecture on the Centroid Banach–Mazur Distance
# Between an Affine-Regular Pentagon and a Triangle (`arXiv:2611.21947v1`)

In *Banach–Mazur distance and related methods of comparing convex bodies*
(`arXiv:2611.21947v1`, November 2026), M. Lassak and S. J. Szarek recall
Lassak's upper bound `d_BM^cen(F, T) ≤ η := (7 - √5) / 2 ≈ 2.381966` for an
affine-regular pentagon `F` and a triangle `T`, conjecture that `η` is optimal,
and pose the open problem: **Is `d_BM^cen(F, T) = η`?**

We disprove this conjecture for every affine-regular pentagon `Φ '' regPentagon`
and every nondegenerate triangle `Ψ '' stdTriangle`:
- `dBMcen (Φ '' regPentagon) (Ψ '' stdTriangle) ≤ 19 / 8` (`= 2.375`),
- `19 / 8 < (7 - √5) / 2`, hence `dBMcen (Φ '' regPentagon) (Ψ '' stdTriangle) ≠ (7 - √5) / 2`.
-/

namespace LassakSzarekPentagonCentroid

open MeasureTheory Set

/-- Ambient Euclidean plane `ℝ²` equipped with Lebesgue product measure `volume`. -/
abbrev R2 := ℝ × ℝ

private instance : (volume : Measure R2).IsAddRightInvariant :=
  Measure.prod.instIsAddRightInvariant

private instance : (volume : Measure R2).IsAddLeftInvariant :=
  Measure.prod.instIsAddLeftInvariant

private instance : (volume : Measure R2).IsAddHaarMeasure := ⟨⟩

/-- Centroid of a planar set `K ⊆ ℝ²` with respect to 2-dimensional Lebesgue measure:
`cen K = (volume K).toReal⁻¹ • ∫ x in K, x`. -/
noncomputable def cen (K : Set R2) : R2 :=
  (volume K).toReal⁻¹ • ∫ x in K, x

/-- Planar homothety of ratio `lam` and translation vector `t`: `x ↦ lam • x + t`. -/
def homothety (lam : ℝ) (t : R2) (x : R2) : R2 :=
  lam • x + t

/-- Centroid Banach–Mazur distance between two planar sets `C, D ⊆ ℝ²`
(verbatim from `arXiv:2611.21947v1`, Section "Centroid Banach–Mazur distance"). -/
noncomputable def dBMcen (C D : Set R2) : ℝ :=
  sInf {lam : ℝ | 0 < lam ∧
    ∃ (a : R2 ≃ᵃ[ℝ] R2) (t : R2),
      C ⊆ a '' D ∧
      a '' D ⊆ (homothety lam t) '' C ∧
      cen C = cen (a '' D) ∧
      cen (a '' D) = cen ((homothety lam t) '' C)}

/-! ### 1. General Centroid Transformation Lemmas -/

private lemma cen_image_linearEquiv (L : R2 ≃ₗ[ℝ] R2) (K : Set R2) :
    cen (L '' K) = L (cen K) := by
  let Lc : R2 ≃L[ℝ] R2 := L.toContinuousLinearEquiv
  let e : R2 ≃ᵐ R2 := Lc.toHomeomorph.toMeasurableEquiv
  have hdet_ne : LinearMap.det (L : R2 →ₗ[ℝ] R2) ≠ 0 := (LinearEquiv.isUnit_det' L).ne_zero
  have habs_pos : 0 < |LinearMap.det (L : R2 →ₗ[ℝ] R2)| := abs_pos.mpr hdet_ne
  have hmap : Measure.map e volume =
      ENNReal.ofReal |(LinearMap.det (L : R2 →ₗ[ℝ] R2))⁻¹| • (volume : Measure R2) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet_ne
  have hint_map : ∫ x in L '' K, x ∂(Measure.map e volume) = ∫ y in K, L y := by
    have h1 := setIntegral_map_equiv e (fun x : R2 => x) (L '' K) (μ := volume)
    have hpre : e ⁻¹' (L '' K) = K := Set.preimage_image_eq K L.injective
    rw [hpre] at h1
    exact h1
  have hint_smul : ∫ x in L '' K, x ∂(Measure.map e volume) =
      |(LinearMap.det (L : R2 →ₗ[ℝ] R2))⁻¹| • ∫ x in L '' K, x := by
    rw [hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hint_L : ∫ y in K, L y = L (∫ y in K, y) :=
    (Lc : R2 →L[ℝ] R2).integral_comp_comm' Lc.antilipschitz (fun y : R2 => y)
  have hint_eq : ∫ x in L '' K, x = |LinearMap.det (L : R2 →ₗ[ℝ] R2)| • L (∫ y in K, y) := by
    have hcomb : |(LinearMap.det (L : R2 →ₗ[ℝ] R2))⁻¹| • ∫ x in L '' K, x = L (∫ y in K, y) := by
      rw [← hint_smul, hint_map, hint_L]
    have hmul := congr_arg (fun v : R2 => |LinearMap.det (L : R2 →ₗ[ℝ] R2)| • v) hcomb
    rw [smul_smul, abs_inv, mul_inv_cancel₀ habs_pos.ne', one_smul] at hmul
    exact hmul
  have hvol : (volume (L '' K)).toReal =
      |LinearMap.det (L : R2 →ₗ[ℝ] R2)| * (volume K).toReal := by
    have hv := (volume : Measure R2).addHaar_image_linearMap (L : R2 →ₗ[ℝ] R2) K
    change volume (L '' K) = ENNReal.ofReal |LinearMap.det (L : R2 →ₗ[ℝ] R2)| * volume K at hv
    rw [hv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  unfold cen
  rw [hvol, hint_eq, mul_inv, smul_smul, mul_assoc, mul_comm (volume K).toReal⁻¹,
    ← mul_assoc, inv_mul_cancel₀ habs_pos.ne', one_mul, map_smul]

private lemma cen_image_add (c : R2) {K : Set R2}
    (hK_ne : volume K ≠ 0) (hK_fin : volume K ≠ ⊤)
    (hK_int : IntegrableOn (fun x : R2 => x) K volume) :
    cen ((fun x => x + c) '' K) = cen K + c := by
  let e : R2 ≃ᵐ R2 := (Homeomorph.addRight c).toMeasurableEquiv
  have hmp : Measure.map e volume = (volume : Measure R2) :=
    (measurePreserving_add_right (volume : Measure R2) c).map_eq
  have hvol_eq : volume ((fun x => x + c) '' K) = volume K := by
    have : (fun x => x + c) '' K = (fun x => x + (-c)) ⁻¹' K := by
      ext y; simp
    rw [this, measure_preimage_add_right]
  have hint_eq : ∫ x in (fun x => x + c) '' K, x =
      (∫ y in K, y) + (volume K).toReal • c := by
    have h1 := setIntegral_map_equiv e (fun x : R2 => x) ((fun x => x + c) '' K) (μ := volume)
    rw [hmp] at h1
    have hpre : e ⁻¹' ((fun x => x + c) '' K) = K :=
      Set.preimage_image_eq K (add_left_injective c)
    rw [hpre] at h1
    rw [h1]
    have hc_int : IntegrableOn (fun _ : R2 => c) K volume :=
      integrableOn_const (hs := hK_fin)
    change ∫ y in K, (y + c) = (∫ y in K, y) + (volume K).toReal • c
    rw [integral_add hK_int hc_int, setIntegral_const, Measure.real_def]
  have hpos : (volume K).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hK_ne, hK_fin⟩
  unfold cen
  rw [hvol_eq, hint_eq, smul_add, smul_smul, inv_mul_cancel₀ hpos, one_smul]

private lemma cen_image_affineEquiv (a : R2 ≃ᵃ[ℝ] R2) {K : Set R2}
    (hK_comp : IsCompact K) (hK_ne : volume K ≠ 0) :
    cen (a '' K) = a (cen K) := by
  let L : R2 ≃ₗ[ℝ] R2 := a.linear
  let c : R2 := a 0
  have ha_eq : ∀ x : R2, a x = L x + c := by
    intro x
    have h := a.map_vadd 0 x
    simp only [vadd_eq_add, add_zero] at h
    rw [h, add_comm]
  have himg : a '' K = (fun x => x + c) '' (L '' K) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨L x, ⟨x, hx, rfl⟩, (ha_eq x).symm⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, ha_eq x⟩
  have hdet_ne : LinearMap.det (L : R2 →ₗ[ℝ] R2) ≠ 0 := (LinearEquiv.isUnit_det' L).ne_zero
  have habs_pos : 0 < |LinearMap.det (L : R2 →ₗ[ℝ] R2)| := abs_pos.mpr hdet_ne
  have hLK_comp : IsCompact (L '' K) :=
    hK_comp.image L.toContinuousLinearMap.continuous
  have hLK_vol : volume (L '' K) = ENNReal.ofReal |LinearMap.det (L : R2 →ₗ[ℝ] R2)| * volume K :=
    (volume : Measure R2).addHaar_image_linearMap (L : R2 →ₗ[ℝ] R2) K
  have hLK_ne : volume (L '' K) ≠ 0 := by
    rw [hLK_vol]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr habs_pos).ne' hK_ne
  have hLK_fin : volume (L '' K) ≠ ⊤ := hLK_comp.measure_lt_top.ne
  have hLK_int : IntegrableOn (fun x : R2 => x) (L '' K) volume :=
    continuous_id.continuousOn.integrableOn_compact hLK_comp
  rw [himg, cen_image_add c hLK_ne hLK_fin hLK_int, cen_image_linearEquiv, ha_eq]

private lemma mem_convexHull_of_three {S : Set R2} {a b c x : R2} {w1 w2 w3 : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3)
    (hsum : w1 + w2 + w3 = 1) (heq : w1 • a + w2 • b + w3 • c = x) :
    x ∈ convexHull ℝ S := by
  have ha' : a ∈ convexHull ℝ S := subset_convexHull ℝ S ha
  have hb' : b ∈ convexHull ℝ S := subset_convexHull ℝ S hb
  have hc' : c ∈ convexHull ℝ S := subset_convexHull ℝ S hc
  by_cases h12 : w1 + w2 = 0
  · have hw10 : w1 = 0 := by linarith
    have hw20 : w2 = 0 := by linarith
    have hw31 : w3 = 1 := by linarith
    rw [← heq, hw10, hw20, hw31, zero_smul, zero_smul, one_smul, zero_add, zero_add]
    exact hc'
  · have hpos : 0 < w1 + w2 := lt_of_le_of_ne (by linarith) (Ne.symm h12)
    have hp : (w1 / (w1 + w2)) • a + (w2 / (w1 + w2)) • b ∈ convexHull ℝ S := by
      refine (convex_convexHull ℝ S) ha' hb' (div_nonneg hw1 hpos.le) (div_nonneg hw2 hpos.le) ?_
      rw [← add_div, div_self hpos.ne']
    have hx : (w1 + w2) • ((w1 / (w1 + w2)) • a + (w2 / (w1 + w2)) • b) + w3 • c ∈
        convexHull ℝ S :=
      (convex_convexHull ℝ S) hp hc' hpos.le hw3 hsum
    have hcomb : (w1 + w2) • ((w1 / (w1 + w2)) • a + (w2 / (w1 + w2)) • b) + w3 • c = x := by
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne']
      exact heq
    rwa [hcomb] at hx

/-! ### 2. Standard Triangle `Δ` and Its Centroid -/

/-- The standard reference triangle `Δ = conv{(0, 0), (1, 0), (0, 1)}`. -/
def stdTriangle : Set R2 :=
  convexHull ℝ ({(0, 0), (1, 0), (0, 1)} : Set R2)

private lemma stdTriangle_eq_set :
    stdTriangle = {p : R2 | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · rintro p (rfl | rfl | rfl) <;> norm_num
    · intro x hx y hy a b ha hb hab
      refine ⟨by dsimp; nlinarith [hx.1, hy.1], by dsimp; nlinarith [hx.2.1, hy.2.1], ?_⟩
      dsimp; nlinarith [hx.2.2, hy.2.2]
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine mem_convexHull_of_three (a := (0, 0)) (b := (1, 0)) (c := (0, 1))
      (w1 := 1 - x - y) (w2 := x) (w3 := y)
      (by simp) (by simp) (by simp) (by linarith) hx hy (by ring) ?_
    ext <;> simp

private lemma stdTriangle_measurableSet : MeasurableSet stdTriangle := by
  rw [stdTriangle_eq_set]
  have h1 : MeasurableSet {p : R2 | 0 ≤ p.1} :=
    measurableSet_le measurable_const measurable_fst
  have h2 : MeasurableSet {p : R2 | 0 ≤ p.2} :=
    measurableSet_le measurable_const measurable_snd
  have h3 : MeasurableSet {p : R2 | p.1 + p.2 ≤ 1} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  exact h1.inter (h2.inter h3)

private lemma stdTriangle_isCompact : IsCompact stdTriangle := by
  unfold stdTriangle
  exact (Set.toFinite ({(0, 0), (1, 0), (0, 1)} : Set R2)).isCompact_convexHull (𝕜 := ℝ)

private lemma stdTriangle_integrableOn : IntegrableOn (fun x : R2 => x) stdTriangle volume :=
  continuous_id.continuousOn.integrableOn_compact stdTriangle_isCompact

private lemma stdTriangle_volume_toReal :
    (volume stdTriangle).toReal = 1 / 2 ∧ volume stdTriangle ≠ 0 ∧ volume stdTriangle ≠ ⊤ := by
  have hfin : volume stdTriangle ≠ ⊤ := stdTriangle_isCompact.measure_lt_top.ne
  have hvol_eq : (volume stdTriangle).toReal = ∫ p in stdTriangle, (1 : ℝ) := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real_def]
  have hind : ∫ p in stdTriangle, (1 : ℝ) = ∫ p : R2, stdTriangle.indicator (fun _ => (1 : ℝ)) p :=
    (integral_indicator stdTriangle_measurableSet).symm
  have hint_ind : Integrable (stdTriangle.indicator (fun _ : R2 => (1 : ℝ))) volume :=
    (integrableOn_const (hs := hfin)).integrable_indicator stdTriangle_measurableSet
  have hfub := MeasureTheory.integral_prod _ hint_ind
  have hslice : ∀ x : ℝ,
      (∫ y : ℝ, stdTriangle.indicator (fun _ : R2 => (1 : ℝ)) (x, y)) =
        (Set.Icc (0 : ℝ) 1).indicator (fun t => 1 - t) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hset : ∀ y : ℝ, (x, y) ∈ stdTriangle ↔ y ∈ Set.Icc (0 : ℝ) (1 - x) := by
        intro y; rw [stdTriangle_eq_set]; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · rintro ⟨_, h2, h3⟩; exact ⟨h2, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨hx.1, h1, by linarith⟩
      have hfun : (fun y : ℝ => stdTriangle.indicator (fun _ : R2 => (1 : ℝ)) (x, y)) =
          (Set.Icc (0 : ℝ) (1 - x)).indicator (fun _ => (1 : ℝ)) := by
        ext y; by_cases hy : y ∈ Set.Icc (0 : ℝ) (1 - x)
        · rw [Set.indicator_of_mem ((hset y).mpr hy), Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem (mt (hset y).mp hy), Set.indicator_of_notMem hy]
      rw [hfun, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
        Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hx.2]), sub_zero]
    · rw [Set.indicator_of_notMem hx]
      have hzero : ∀ y : ℝ, stdTriangle.indicator (fun _ : R2 => (1 : ℝ)) (x, y) = 0 := by
        intro y
        refine Set.indicator_of_notMem ?_ _
        rw [stdTriangle_eq_set]
        rintro ⟨h1, h2, h3⟩
        exact hx ⟨h1, by linarith⟩
      simp [hzero]
  have hcalc : (volume stdTriangle).toReal = 1 / 2 := by
    rw [hvol_eq, hind]
    change (∫ p : R2, stdTriangle.indicator (fun _ => (1 : ℝ)) p ∂(volume.prod volume)) = 1 / 2
    rw [hfub]
    simp_rw [hslice]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have h1 : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun x : ℝ => x - x * x / 2) (1 - t) t := fun t _ => by
        have h2 : HasDerivAt (fun x : ℝ => x * x) (1 * t + t * 1) t :=
          HasDerivAt.mul (hasDerivAt_id t) (hasDerivAt_id t)
        have hd := (hasDerivAt_id t).sub (h2.div_const 2)
        have heq : (1 : ℝ) - (1 * t + t * 1) / 2 = 1 - t := by ring
        rw [← heq]
        exact hd
      have hint1 : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
        (continuous_const.sub continuous_id).intervalIntegrable 0 1
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1]
      norm_num
    exact h1
  have hne0 : volume stdTriangle ≠ 0 := by
    intro h0; rw [h0, ENNReal.toReal_zero] at hcalc; norm_num at hcalc
  exact ⟨hcalc, hne0, hfin⟩

private lemma stdTriangle_integral :
    ∫ p in stdTriangle, p = ((1 / 6 : ℝ), (1 / 6 : ℝ)) := by
  have hfst_int : IntegrableOn (fun p : R2 => p.1) stdTriangle volume :=
    continuous_fst.continuousOn.integrableOn_compact stdTriangle_isCompact
  have hfst_eq : (∫ p in stdTriangle, p).1 = ∫ p in stdTriangle, p.1 :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).integral_comp_comm stdTriangle_integrableOn).symm
  have hsnd_eq : (∫ p in stdTriangle, p).2 = ∫ p in stdTriangle, p.2 :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).integral_comp_comm stdTriangle_integrableOn).symm
  have h1 : ∫ p in stdTriangle, p.1 = 1 / 6 := by
    rw [← integral_indicator stdTriangle_measurableSet]
    have hint : Integrable (stdTriangle.indicator (fun p : R2 => p.1)) volume :=
      hfst_int.integrable_indicator stdTriangle_measurableSet
    change ∫ p : R2, stdTriangle.indicator (fun q : R2 => q.1) p ∂(volume.prod volume) = 1 / 6
    rw [MeasureTheory.integral_prod _ hint]
    have hslice : ∀ x : ℝ,
        (∫ y : ℝ, stdTriangle.indicator (fun q : R2 => q.1) (x, y)) =
          (Set.Icc (0 : ℝ) 1).indicator (fun t => t * (1 - t)) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hx]
        have hset : ∀ y : ℝ, (x, y) ∈ stdTriangle ↔ y ∈ Set.Icc (0 : ℝ) (1 - x) := by
          intro y; rw [stdTriangle_eq_set]; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
          constructor
          · rintro ⟨_, h2, h3⟩; exact ⟨h2, by linarith⟩
          · rintro ⟨h1', h2'⟩; exact ⟨hx.1, h1', by linarith⟩
        have hfun : (fun y : ℝ => stdTriangle.indicator (fun q : R2 => q.1) (x, y)) =
            (Set.Icc (0 : ℝ) (1 - x)).indicator (fun _ => x) := by
          ext y; by_cases hy : y ∈ Set.Icc (0 : ℝ) (1 - x)
          · rw [Set.indicator_of_mem ((hset y).mpr hy), Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem (mt (hset y).mp hy), Set.indicator_of_notMem hy]
        rw [hfun, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hx.2]), sub_zero, mul_comm]
      · rw [Set.indicator_of_notMem hx]
        have hzero : ∀ y : ℝ, stdTriangle.indicator (fun q : R2 => q.1) (x, y) = 0 := by
          intro y; refine Set.indicator_of_notMem ?_ _
          rw [stdTriangle_eq_set]; rintro ⟨h1', h2', h3'⟩; exact hx ⟨h1', by linarith⟩
        simp [hzero]
    simp_rw [hslice]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hsub : (fun t : ℝ => t * (1 - t)) = (fun t : ℝ => t - t ^ 2) := by ext t; ring
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => x * x / 2 - x * x * x / 3) (t - t ^ 2) t := fun t _ => by
      have h2 : HasDerivAt (fun x : ℝ => x * x) (1 * t + t * 1) t :=
        HasDerivAt.mul (hasDerivAt_id t) (hasDerivAt_id t)
      have h3 : HasDerivAt (fun x : ℝ => x * x * x) ((1 * t + t * 1) * t + (t * t) * 1) t :=
        HasDerivAt.mul h2 (hasDerivAt_id t)
      have hd := (h2.div_const 2).sub (h3.div_const 3)
      have heq : (1 * t + t * 1) / 2 - ((1 * t + t * 1) * t + t * t * 1) / 3 = t - t ^ 2 := by ring
      rw [← heq]
      exact hd
    have hint2 : IntervalIntegrable (fun t : ℝ => t - t ^ 2) volume 0 1 :=
      (continuous_id.sub (continuous_pow 2)).intervalIntegrable 0 1
    rw [hsub, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
    norm_num
  have h2 : ∫ p in stdTriangle, p.2 = 1 / 6 := by
    let swapL : R2 ≃ₗ[ℝ] R2 := LinearEquiv.prodComm ℝ ℝ ℝ
    have hswap_img : swapL '' stdTriangle = stdTriangle := by
      ext ⟨x, y⟩
      simp only [Set.mem_image, stdTriangle_eq_set, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, h⟩
        have hx : b = x := congr_arg Prod.fst h
        have hy : a = y := congr_arg Prod.snd h
        subst hx; subst hy; exact ⟨hb, ha, by linarith⟩
      · rintro ⟨hx, hy, hxy⟩
        exact ⟨(y, x), ⟨hy, hx, by linarith⟩, rfl⟩
    have hcen := cen_image_linearEquiv swapL stdTriangle
    rw [hswap_img] at hcen
    have hvol := stdTriangle_volume_toReal.1
    have hcen_eq : (cen stdTriangle).1 = (cen stdTriangle).2 := by
      have := congr_arg Prod.fst hcen
      dsimp [swapL] at this
      exact this
    unfold cen at hcen_eq
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hvol, hfst_eq, hsnd_eq, h1] at hcen_eq
    linarith
  exact Prod.ext (hfst_eq.trans h1) (hsnd_eq.trans h2)

private lemma cen_stdTriangle : cen stdTriangle = ((1 / 3 : ℝ), (1 / 3 : ℝ)) := by
  unfold cen
  rw [stdTriangle_volume_toReal.1, stdTriangle_integral]
  ext <;> norm_num

/-! ### 3. Regular Pentagon, Affine-Regular Pentagon `F'`, and Certificate Triangle `T₀` -/

/-- Vertices of the unit regular pentagon `(cos (2πk/5), sin (2πk/5))`. -/
noncomputable def regVert (k : Fin 5) : R2 :=
  (Real.cos (2 * Real.pi * k.val / 5), Real.sin (2 * Real.pi * k.val / 5))

/-- The standard unit regular pentagon. -/
noncomputable def regPentagon : Set R2 :=
  convexHull ℝ (Set.range regVert)

/-- `c = cos(2π/5) = (√5 - 1) / 4`. -/
noncomputable def c72 : ℝ := (Real.sqrt 5 - 1) / 4

/-- `φ = (1 + √5) / 2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Vertices of the `ℚ(√5)` affine-regular pentagon `F' = L(regPentagon)`. -/
noncomputable def P0 : R2 := (1, 0)
noncomputable def P1 : R2 := (c72, 1)
noncomputable def P2 : R2 := (-phi / 2, (Real.sqrt 5 - 1) / 2)
noncomputable def P3 : R2 := (-phi / 2, -(Real.sqrt 5 - 1) / 2)
noncomputable def P4 : R2 := (c72, -1)

/-- The `ℚ(√5)` affine-regular pentagon `F' = conv{P0, P1, P2, P3, P4}`. -/
noncomputable def pentF : Set R2 :=
  convexHull ℝ ({P0, P1, P2, P3, P4} : Set R2)

/-- Vertices of the rational certificate triangle `T₀` with centroid `0`. -/
noncomputable def v0 : R2 := (112 / 200, 127 / 200)
noncomputable def v1 : R2 := (-161 / 200, 35 / 200)
noncomputable def v2 : R2 := (49 / 200, -162 / 200)

/-- The certificate triangle `T₀ = conv{v0, v1, v2}`. -/
noncomputable def certT : Set R2 :=
  convexHull ℝ ({v0, v1, v2} : Set R2)

private lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sqrt5_bounds : (2.236 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.237 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

private lemma sin_72_pos : 0 < Real.sin (2 * Real.pi / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

private lemma cos_72_eq : Real.cos (2 * Real.pi / 5) = c72 := by
  have h2 : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  rw [h2, Real.cos_two_mul, Real.cos_pi_div_five]
  unfold c72
  have hs := sqrt5_sq
  nlinarith

private lemma cos_144_eq : Real.cos (4 * Real.pi / 5) = -phi / 2 := by
  have h : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  unfold phi; ring

private lemma sin_144_div_sin_72 :
    Real.sin (4 * Real.pi / 5) / Real.sin (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 2 := by
  have h : 4 * Real.pi / 5 = 2 * (2 * Real.pi / 5) := by ring
  rw [h, Real.sin_two_mul, mul_assoc, mul_comm (Real.sin (2 * Real.pi / 5)),
    ← mul_assoc, mul_div_cancel_right₀ _ sin_72_pos.ne', cos_72_eq]
  unfold c72; ring

/-- Invertible linear map `L(x, y) = (x, y / sin(2π/5))` mapping `regPentagon` onto `pentF`. -/
noncomputable def pentLinearEquiv : R2 ≃ₗ[ℝ] R2 where
  toFun p := (p.1, p.2 / Real.sin (2 * Real.pi / 5))
  invFun p := (p.1, p.2 * Real.sin (2 * Real.pi / 5))
  map_add' p q := by ext <;> simp [add_div]
  map_smul' r p := by ext <;> simp [mul_div_assoc]
  left_inv p := by ext <;> simp [div_mul_cancel₀ _ sin_72_pos.ne']
  right_inv p := by ext <;> simp [mul_div_cancel_right₀ _ sin_72_pos.ne']

private lemma pentLinearEquiv_image_regPentagon :
    pentLinearEquiv '' regPentagon = pentF := by
  have hverts : pentLinearEquiv '' Set.range regVert = ({P0, P1, P2, P3, P4} : Set R2) := by
    have h0 : pentLinearEquiv (regVert 0) = P0 := by
      ext <;> simp [pentLinearEquiv, regVert, P0]
    have h1 : pentLinearEquiv (regVert 1) = P1 := by
      ext
      · simp [pentLinearEquiv, regVert, P1, cos_72_eq]
      · simp [pentLinearEquiv, regVert, P1, div_self sin_72_pos.ne']
    have h2 : pentLinearEquiv (regVert 2) = P2 := by
      have heq : 2 * Real.pi * 2 / 5 = 4 * Real.pi / 5 := by ring
      ext
      · simp [pentLinearEquiv, regVert, P2, heq, cos_144_eq]
      · simp [pentLinearEquiv, regVert, P2, heq, sin_144_div_sin_72]
    have h3 : pentLinearEquiv (regVert 3) = P3 := by
      have heq : 2 * Real.pi * 3 / 5 = 2 * Real.pi - 4 * Real.pi / 5 := by ring
      ext
      · simp [pentLinearEquiv, regVert, P3, heq, Real.cos_two_pi_sub, cos_144_eq]
      · simp [pentLinearEquiv, regVert, P3, heq, Real.sin_two_pi_sub, neg_div, sin_144_div_sin_72]; ring
    have h4 : pentLinearEquiv (regVert 4) = P4 := by
      have heq : 2 * Real.pi * 4 / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by ring
      ext
      · simp [pentLinearEquiv, regVert, P4, heq, Real.cos_two_pi_sub, cos_72_eq]
      · simp [pentLinearEquiv, regVert, P4, heq, Real.sin_two_pi_sub, neg_div, div_self sin_72_pos.ne']
    ext p
    simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      fin_cases k
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨regVert 0, ⟨0, rfl⟩, h0⟩
      · exact ⟨regVert 1, ⟨1, rfl⟩, h1⟩
      · exact ⟨regVert 2, ⟨2, rfl⟩, h2⟩
      · exact ⟨regVert 3, ⟨3, rfl⟩, h3⟩
      · exact ⟨regVert 4, ⟨4, rfl⟩, h4⟩
  unfold regPentagon pentF
  rw [← hverts]
  exact (pentLinearEquiv : R2 →ₗ[ℝ] R2).image_convexHull (Set.range regVert)

/-- Cyclic 5-fold symmetry `A(x, y) = (c x - (1 - c²) y, x + c y)` of `pentF`, with `det A = 1`. -/
noncomputable def pentRotEquiv : R2 ≃ₗ[ℝ] R2 where
  toFun p := (c72 * p.1 - (1 - c72 ^ 2) * p.2, p.1 + c72 * p.2)
  invFun p := (c72 * p.1 + (1 - c72 ^ 2) * p.2, -p.1 + c72 * p.2)
  map_add' p q := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' r p := by ext <;> simp <;> ring
  left_inv p := by ext <;> simp <;> ring
  right_inv p := by ext <;> simp <;> ring

private lemma pentRotEquiv_image_pentF : pentRotEquiv '' pentF = pentF := by
  have hs := sqrt5_sq
  have h0 : pentRotEquiv P0 = P1 := by
    ext <;> simp [pentRotEquiv, P0, P1, c72]
  have h1 : pentRotEquiv P1 = P2 := by
    ext <;> simp only [pentRotEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      P1, P2, c72, phi] <;> nlinarith
  have h2 : pentRotEquiv P2 = P3 := by
    ext <;> simp only [pentRotEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      P2, P3, c72, phi] <;> nlinarith
  have h3 : pentRotEquiv P3 = P4 := by
    ext <;> simp only [pentRotEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      P3, P4, c72, phi] <;> nlinarith
  have h4 : pentRotEquiv P4 = P0 := by
    ext <;> simp only [pentRotEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      P4, P0, c72] <;> nlinarith
  have hverts : pentRotEquiv '' ({P0, P1, P2, P3, P4} : Set R2) = ({P0, P1, P2, P3, P4} : Set R2) := by
    ext p
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, rfl | rfl | rfl | rfl | rfl, rfl⟩
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
      · exact Or.inl h4
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨P4, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h4⟩
      · exact ⟨P0, Or.inl rfl, h0⟩
      · exact ⟨P1, Or.inr (Or.inl rfl), h1⟩
      · exact ⟨P2, Or.inr (Or.inr (Or.inl rfl)), h2⟩
      · exact ⟨P3, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h3⟩
  unfold pentF
  change (pentRotEquiv : R2 →ₗ[ℝ] R2) '' convexHull ℝ ({P0, P1, P2, P3, P4} : Set R2) = _
  rw [(pentRotEquiv : R2 →ₗ[ℝ] R2).image_convexHull]
  exact congr_arg (convexHull ℝ) hverts

/-- **Lemma 1:** The centroid of the affine-regular pentagon `F'` is the origin `(0, 0)`. -/
theorem pentagon_centroid_zero : cen pentF = 0 := by
  have hfix : pentRotEquiv (cen pentF) = cen pentF := by
    rw [← cen_image_linearEquiv, pentRotEquiv_image_pentF]
  have h1 := congr_arg Prod.fst hfix
  have h2 := congr_arg Prod.snd hfix
  dsimp [pentRotEquiv] at h1 h2
  have hc_lt : c72 < 1 := by
    unfold c72; linarith [sqrt5_bounds.2]
  ext
  · dsimp; nlinarith
  · dsimp; nlinarith

/-- Invertible affine equivalence mapping `stdTriangle` onto `certT`. -/
noncomputable def certAffineEquiv : R2 ≃ᵃ[ℝ] R2 :=
  let L : R2 ≃ₗ[ℝ] R2 := {
    toFun := fun p => (p.1 * (v1.1 - v0.1) + p.2 * (v2.1 - v0.1),
                       p.1 * (v1.2 - v0.2) + p.2 * (v2.2 - v0.2))
    invFun := fun p =>
      let D : ℝ := (v1.1 - v0.1) * (v2.2 - v0.2) - (v2.1 - v0.1) * (v1.2 - v0.2)
      (((v2.2 - v0.2) * p.1 - (v2.1 - v0.1) * p.2) / D,
       (-(v1.2 - v0.2) * p.1 + (v1.1 - v0.1) * p.2) / D)
    map_add' := fun p q => by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    map_smul' := fun r p => by ext <;> simp <;> ring
    left_inv := fun p => by ext <;> simp [v0, v1, v2] <;> ring
    right_inv := fun p => by ext <;> simp [v0, v1, v2] <;> ring
  }
  L.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ R2 v0)

private lemma certAffineEquiv_apply (p : R2) :
    certAffineEquiv p =
      (v0.1 + (p.1 * (v1.1 - v0.1) + p.2 * (v2.1 - v0.1)),
       v0.2 + (p.1 * (v1.2 - v0.2) + p.2 * (v2.2 - v0.2))) := by
  ext <;> simp [certAffineEquiv]

private lemma certAffineEquiv_image_stdTriangle :
    certAffineEquiv '' stdTriangle = certT := by
  have h0 : certAffineEquiv (0, 0) = v0 := by
    rw [certAffineEquiv_apply]; ext <;> simp [v0, v1, v2]
  have h1 : certAffineEquiv (1, 0) = v1 := by
    rw [certAffineEquiv_apply]; ext <;> simp [v0, v1, v2]
  have h2 : certAffineEquiv (0, 1) = v2 := by
    rw [certAffineEquiv_apply]; ext <;> simp [v0, v1, v2]
  have hverts : certAffineEquiv '' ({(0, 0), (1, 0), (0, 1)} : Set R2) = ({v0, v1, v2} : Set R2) := by
    ext p
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, rfl | rfl | rfl, rfl⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨(0, 0), Or.inl rfl, h0⟩
      · exact ⟨(1, 0), Or.inr (Or.inl rfl), h1⟩
      · exact ⟨(0, 1), Or.inr (Or.inr rfl), h2⟩
  unfold stdTriangle certT
  change certAffineEquiv.toAffineMap '' convexHull ℝ ({(0, 0), (1, 0), (0, 1)} : Set R2) = _
  rw [certAffineEquiv.toAffineMap.image_convexHull]
  exact congr_arg (convexHull ℝ) hverts

/-- **Lemma 2:** The centroid of the certificate triangle `T₀` is `(0, 0)`. -/
theorem certTriangle_centroid_zero : cen certT = 0 := by
  rw [← certAffineEquiv_image_stdTriangle,
    cen_image_affineEquiv certAffineEquiv stdTriangle_isCompact stdTriangle_volume_toReal.2.1,
    cen_stdTriangle, certAffineEquiv_apply]
  ext <;> simp [v0, v1, v2] <;> norm_num

/-! ### 4. Exact `ℚ(√5)` Inclusions `T₀ ⊆ F'` and `F' ⊆ (19 / 8) • T₀` -/

/-- **Lemma 3:** The certificate triangle `T₀` is contained in the pentagon `F'`. -/
theorem certTriangle_subset_pentagon : certT ⊆ pentF := by
  have hs := sqrt5_sq
  have hlo := sqrt5_bounds.1
  have hhi := sqrt5_bounds.2
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro p (rfl | rfl | rfl)
  · -- `v0 ∈ conv{P0, P1, P2}`
    refine mem_convexHull_of_three (a := P0) (b := P1) (c := P2)
      (w1 := 497 / 800 - 459 / 4000 * Real.sqrt 5)
      (w2 := 381 / 800 + 283 / 4000 * Real.sqrt 5)
      (w3 := -39 / 400 + 11 / 250 * Real.sqrt 5)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P0, P1, P2, v0, c72, phi] <;> nlinarith
  · -- `v1 ∈ conv{P0, P2, P3}`
    refine mem_convexHull_of_three (a := P0) (b := P2) (c := P3)
      (w1 := -161 / 200 + 361 / 1000 * Real.sqrt 5)
      (w2 := 757 / 800 - 547 / 4000 * Real.sqrt 5)
      (w3 := 687 / 800 - 897 / 4000 * Real.sqrt 5)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P0, P2, P3, v1, phi] <;> nlinarith
  · -- `v2 ∈ conv{P0, P3, P4}`
    refine mem_convexHull_of_three (a := P0) (b := P3) (c := P4)
      (w1 := 21 / 50 - 127 / 1000 * Real.sqrt 5)
      (w2 := -11 / 400 + 151 / 2000 * Real.sqrt 5)
      (w3 := 243 / 400 + 103 / 2000 * Real.sqrt 5)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P0, P3, P4, v2, c72, phi] <;> nlinarith

/-- **Lemma 4:** The pentagon `F'` is contained in `(19 / 8) • T₀`. -/
theorem pentagon_subset_scaled_certTriangle :
    pentF ⊆ (homothety (19 / 8) 0) '' certT := by
  have hs := sqrt5_sq
  have hlo := sqrt5_bounds.1
  have hhi := sqrt5_bounds.2
  let L : R2 →ₗ[ℝ] R2 := (19 / 8 : ℝ) • LinearMap.id
  have himg : (homothety (19 / 8) 0) '' certT =
      convexHull ℝ ({(19 / 8 : ℝ) • v0, (19 / 8 : ℝ) • v1, (19 / 8 : ℝ) • v2} : Set R2) := by
    have h1 : (homothety (19 / 8) 0) '' certT = L '' certT := by
      ext y; simp [homothety, L]
    rw [h1]
    unfold certT
    rw [L.image_convexHull]
    congr 1
    ext y; simp [L, eq_comm]
  rw [himg]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro p (rfl | rfl | rfl | rfl | rfl)
  · -- `P0`
    refine mem_convexHull_of_three
      (a := (19 / 8 : ℝ) • v0) (b := (19 / 8 : ℝ) • v1) (c := (19 / 8 : ℝ) • v2)
      (w1 := 259391 / 462973) (w2 := 191 / 462973) (w3 := 203391 / 462973)
      (by simp) (by simp) (by simp)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P0, v0, v1, v2] <;> norm_num
  · -- `P1`
    refine mem_convexHull_of_three
      (a := (19 / 8 : ℝ) • v0) (b := (19 / 8 : ℝ) • v1) (c := (19 / 8 : ℝ) • v2)
      (w1 := (720173 + 78800 * Real.sqrt 5) / 1388919)
      (w2 := (679373 - 115600 * Real.sqrt 5) / 1388919)
      (w3 := (-10627 + 36800 * Real.sqrt 5) / 1388919)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P1, v0, v1, v2, c72] <;> ring
  · -- `P2`
    refine mem_convexHull_of_three
      (a := (19 / 8 : ℝ) • v0) (b := (19 / 8 : ℝ) • v1) (c := (19 / 8 : ℝ) • v2)
      (w1 := (216173 + 89200 * Real.sqrt 5) / 1388919)
      (w2 := (528173 + 166000 * Real.sqrt 5) / 1388919)
      (w3 := (644573 - 255200 * Real.sqrt 5) / 1388919)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P2, v0, v1, v2, phi] <;> ring
  · -- `P3`
    refine mem_convexHull_of_three
      (a := (19 / 8 : ℝ) • v0) (b := (19 / 8 : ℝ) • v1) (c := (19 / 8 : ℝ) • v2)
      (w1 := (552173 - 246800 * Real.sqrt 5) / 1388919)
      (w2 := (628973 + 65200 * Real.sqrt 5) / 1388919)
      (w3 := (207773 + 181600 * Real.sqrt 5) / 1388919)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P3, v0, v1, v2, phi] <;> ring
  · -- `P4`
    refine mem_convexHull_of_three
      (a := (19 / 8 : ℝ) • v0) (b := (19 / 8 : ℝ) • v1) (c := (19 / 8 : ℝ) • v2)
      (w1 := (48173 + 78800 * Real.sqrt 5) / 1388919)
      (w2 := (477773 - 115600 * Real.sqrt 5) / 1388919)
      (w3 := (862973 + 36800 * Real.sqrt 5) / 1388919)
      (by simp) (by simp) (by simp)
      (by nlinarith) (by nlinarith) (by nlinarith) (by ring) ?_
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      P4, v0, v1, v2, c72] <;> ring

/-! ### 5. Main Disproof Theorems -/

private lemma pentF_regularity : IsCompact pentF ∧ volume pentF ≠ 0 := by
  have hcomp : IsCompact pentF := by
    unfold pentF
    exact (Set.toFinite ({P0, P1, P2, P3, P4} : Set R2)).isCompact_convexHull (𝕜 := ℝ)
  have hne : volume pentF ≠ 0 := by
    have hsub : certT ⊆ pentF := certTriangle_subset_pentagon
    have hcert_ne : volume certT ≠ 0 := by
      rw [← certAffineEquiv_image_stdTriangle]
      let L : R2 ≃ₗ[ℝ] R2 := certAffineEquiv.linear
      let c : R2 := certAffineEquiv 0
      have himg : certAffineEquiv '' stdTriangle = (fun x => x + c) '' (L '' stdTriangle) := by
        ext y; simp only [Set.mem_image]
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨L x, ⟨x, hx, rfl⟩, ?_⟩
          have h := certAffineEquiv.map_vadd 0 x
          simp only [vadd_eq_add, add_zero] at h
          rw [h, add_comm]
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨x, hx, ?_⟩
          have h := certAffineEquiv.map_vadd 0 x
          simp only [vadd_eq_add, add_zero] at h
          rw [h, add_comm]
      rw [himg]
      have htrans : volume ((fun x => x + c) '' (L '' stdTriangle)) = volume (L '' stdTriangle) := by
        have : (fun x => x + c) '' (L '' stdTriangle) = (fun x => x + (-c)) ⁻¹' (L '' stdTriangle) := by
          ext y; simp
        rw [this, measure_preimage_add_right]
      rw [htrans]
      change volume ((L : R2 →ₗ[ℝ] R2) '' stdTriangle) ≠ 0
      rw [(volume : Measure R2).addHaar_image_linearMap (L : R2 →ₗ[ℝ] R2) stdTriangle]
      have hdet_ne : LinearMap.det (L : R2 →ₗ[ℝ] R2) ≠ 0 := (LinearEquiv.isUnit_det' L).ne_zero
      exact mul_ne_zero (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet_ne)).ne' stdTriangle_volume_toReal.2.1
    intro h0
    exact hcert_ne (measure_mono_null hsub h0)
  exact ⟨hcomp, hne⟩

/-- **Main Upper Bound:** For every affine-regular pentagon `Φ '' regPentagon` and every
nondegenerate triangle `Ψ '' stdTriangle`, `d_BM^cen(Φ '' regPentagon, Ψ '' stdTriangle) ≤ 19 / 8`. -/
theorem dBMcen_affinePentagon_le (Φ Ψ : R2 ≃ᵃ[ℝ] R2) :
    dBMcen (Φ '' regPentagon) (Ψ '' stdTriangle) ≤ 19 / 8 := by
  let S := {lam : ℝ | 0 < lam ∧
    ∃ (a : R2 ≃ᵃ[ℝ] R2) (t : R2),
      Φ '' regPentagon ⊆ a '' (Ψ '' stdTriangle) ∧
      a '' (Ψ '' stdTriangle) ⊆ (homothety lam t) '' (Φ '' regPentagon) ∧
      cen (Φ '' regPentagon) = cen (a '' (Ψ '' stdTriangle)) ∧
      cen (a '' (Ψ '' stdTriangle)) = cen ((homothety lam t) '' (Φ '' regPentagon))}
  have hbdd : BddBelow S := ⟨0, fun _ h => le_of_lt h.1⟩
  refine csInf_le hbdd ⟨by norm_num, ?_⟩
  let Φ' : R2 ≃ᵃ[ℝ] R2 := pentLinearEquiv.symm.toAffineEquiv.trans Φ
  have hΦ'_img : Φ' '' pentF = Φ '' regPentagon := by
    rw [← pentLinearEquiv_image_regPentagon]
    ext y
    simp only [Set.mem_image, Φ', AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨pentLinearEquiv x, ⟨x, hx, rfl⟩, by simp⟩
  let hScale : R2 ≃ᵃ[ℝ] R2 :=
    (LinearEquiv.smulOfNeZero ℝ R2 (19 / 8 : ℝ) (by norm_num)).toAffineEquiv
  let a : R2 ≃ᵃ[ℝ] R2 := Ψ.symm.trans (certAffineEquiv.trans (hScale.trans Φ'))
  let t : R2 := Φ' 0 - (19 / 8 : ℝ) • Φ' 0
  have ha_img : a '' (Ψ '' stdTriangle) = Φ' '' ((homothety (19 / 8) 0) '' certT) := by
    rw [← certAffineEquiv_image_stdTriangle]
    ext y
    simp only [Set.mem_image, a, AffineEquiv.trans_apply,
      hScale, LinearEquiv.coe_toAffineEquiv, homothety, add_zero]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨(19 / 8 : ℝ) • certAffineEquiv x, ⟨certAffineEquiv x, ⟨x, hx, rfl⟩, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨Ψ x, ⟨x, hx, rfl⟩, by simp⟩
  have hhom_eq : ∀ x : R2, homothety (19 / 8) t (Φ' x) = Φ' (homothety (19 / 8) 0 x) := by
    intro x
    have hlin : ∀ u : R2, Φ' u = Φ'.linear u + Φ' 0 := by
      intro u
      have h := Φ'.map_vadd 0 u
      simp only [vadd_eq_add, add_zero] at h
      rw [h, add_comm]
    rw [hlin x, hlin (homothety (19 / 8) 0 x)]
    simp only [homothety, add_zero, t, smul_add, map_smul]
    ext <;> dsimp <;> ring
  have hhom_img : (homothety (19 / 8) t) '' (Φ '' regPentagon) =
      Φ' '' ((homothety (19 / 8) 0) '' pentF) := by
    rw [← hΦ'_img]
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨homothety (19 / 8) 0 x, ⟨x, hx, rfl⟩, (hhom_eq x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Φ' x, ⟨x, hx, rfl⟩, hhom_eq x⟩
  have hsub1 : Φ '' regPentagon ⊆ a '' (Ψ '' stdTriangle) := by
    rw [← hΦ'_img, ha_img]
    exact Set.image_mono pentagon_subset_scaled_certTriangle
  have hsub2 : a '' (Ψ '' stdTriangle) ⊆ (homothety (19 / 8) t) '' (Φ '' regPentagon) := by
    rw [ha_img, hhom_img]
    exact Set.image_mono (Set.image_mono certTriangle_subset_pentagon)
  have hreg := pentF_regularity
  have hcen_F : cen (Φ '' regPentagon) = Φ' 0 := by
    rw [← hΦ'_img, cen_image_affineEquiv Φ' hreg.1 hreg.2, pentagon_centroid_zero]
  have hcen_aD : cen (a '' (Ψ '' stdTriangle)) = Φ' 0 := by
    have hcomp_img : a '' (Ψ '' stdTriangle) = (certAffineEquiv.trans (hScale.trans Φ')) '' stdTriangle := by
      ext y
      simp only [Set.mem_image, a, AffineEquiv.trans_apply]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Ψ x, ⟨x, hx, rfl⟩, by simp⟩
    rw [hcomp_img, cen_image_affineEquiv (certAffineEquiv.trans (hScale.trans Φ'))
      stdTriangle_isCompact stdTriangle_volume_toReal.2.1, cen_stdTriangle]
    have h0 : certAffineEquiv ((1 / 3 : ℝ), (1 / 3 : ℝ)) = 0 := by
      rw [certAffineEquiv_apply]; ext <;> simp [v0, v1, v2] <;> norm_num
    rw [AffineEquiv.trans_apply, AffineEquiv.trans_apply, h0]
    simp [hScale]
  have hcen_hF : cen ((homothety (19 / 8) t) '' (Φ '' regPentagon)) = Φ' 0 := by
    have hcomp_img : (homothety (19 / 8) t) '' (Φ '' regPentagon) = (hScale.trans Φ') '' pentF := by
      rw [hhom_img]
      ext y; simp [Set.mem_image, hScale, homothety, AffineEquiv.trans_apply]
    rw [hcomp_img, cen_image_affineEquiv (hScale.trans Φ') hreg.1 hreg.2, pentagon_centroid_zero]
    simp [AffineEquiv.trans_apply, hScale]
  exact ⟨a, t, hsub1, hsub2, hcen_F.trans hcen_aD.symm, hcen_aD.trans hcen_hF.symm⟩

/-- **Strict Inequality:** `19 / 8 < η = (7 - √5) / 2` (equivalently `√5 < 9 / 4`, i.e. `80 < 81`). -/
theorem nineteen_eighths_lt_eta : (19 / 8 : ℝ) < (7 - Real.sqrt 5) / 2 := by
  have hsqrt : Real.sqrt 5 < 9 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- **Main Disproof (Lassak–Szarek `arXiv:2611.21947v1`):**
For every affine-regular pentagon `Φ '' regPentagon` and every nondegenerate triangle
`Ψ '' stdTriangle`,
`d_BM^cen(Φ '' regPentagon, Ψ '' stdTriangle) ≤ 19 / 8 < (7 - √5) / 2`.
In particular, `d_BM^cen(F, T) ≠ η`, answering the authors' open problem in the negative. -/
theorem lassak_szarek_disproof (Φ Ψ : R2 ≃ᵃ[ℝ] R2) :
    dBMcen (Φ '' regPentagon) (Ψ '' stdTriangle) ≤ 19 / 8 ∧
    dBMcen (Φ '' regPentagon) (Ψ '' stdTriangle) < (7 - Real.sqrt 5) / 2 ∧
    dBMcen (Φ '' regPentagon) (Ψ '' stdTriangle) ≠ (7 - Real.sqrt 5) / 2 := by
  have hle := dBMcen_affinePentagon_le Φ Ψ
  have hlt := lt_of_le_of_lt hle nineteen_eighths_lt_eta
  exact ⟨hle, hlt, hlt.ne⟩

end LassakSzarekPentagonCentroid
