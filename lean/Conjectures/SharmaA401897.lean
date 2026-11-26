import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Proof of Karan Sharma's OEIS A401897 Conjecture

This file formalizes a complete proof of the conjecture in OEIS A401897
(Karan Sharma, Nov 9, 2026):

> Let `z_n = a + b i` be the `n`-th nonzero Gaussian integer (`n ≥ 1`) with
> `0 ≤ b ≤ a`, ordered first by norm `N(z) = a² + b²` and then by `b`.
> Let `a(n)` be the number of Gaussian integers `w` (including `w = 0`) with
> `N(w) < N(z_n)` that are visible from `z_n`, meaning
> `gcd(Re(z_n - w), Im(z_n - w)) = 1`.
> Then `a(n) ~ 48 n / π²` as `n → ∞`.

We prove:
1. `shifted_gauss_circle_open` and `shifted_gauss_circle_closed`: the shifted Gauss
   circle bound `|#(ℤ² ∩ D(c, r)) - π r²| ≤ π (√2 r + 1/2)` for every center `c : ℂ`
   and radius `r > 0`.
2. `uniform_visibility_bound`: for every nonzero Gaussian integer `z`,
   `|visibleCount z - 6 N(z) / π| ≤ π √N(z) (2 + √2 + √2 log(2 √N(z)))`.
3. `rank_norm_bound`: for every `n ≥ 1`, letting `N = N(z_n)`,
   `|n - π N / 8| ≤ 2 √N`.
4. `sharma_a401897_asymptotic`:
   `Filter.Tendsto (fun n => (a401897 n : ℝ) / (48 * (n : ℝ) / Real.pi ^ 2)) Filter.atTop (nhds 1)`.
-/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation
open MeasureTheory Metric Filter Topology

namespace SharmaA401897

/-! ### Basic definitions for Gaussian integers and OEIS A401897 -/

/-- Norm `a² + b²` of a Gaussian integer `(a, b) ∈ ℤ × ℤ`. -/
def gnorm (z : ℤ × ℤ) : ℕ :=
  z.1.natAbs ^ 2 + z.2.natAbs ^ 2

/-- Cast of `gnorm z` to `ℝ`. -/
lemma gnorm_cast_real (z : ℤ × ℤ) :
    ((gnorm z : ℕ) : ℝ) = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  unfold gnorm
  push_cast
  simp [sq_abs]

/-- Fundamental octant wedge `0 ≤ b ≤ a` of nonzero Gaussian integers. -/
def InWedge (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ 0 < gnorm z

instance : DecidablePred InWedge := fun _ => by
  unfold InWedge
  infer_instance

/-- Strict order on the fundamental wedge: first by norm, then by `b`. -/
def wedgeLt (z₁ z₂ : ℤ × ℤ) : Prop :=
  gnorm z₁ < gnorm z₂ ∨ (gnorm z₁ = gnorm z₂ ∧ z₁.2 < z₂.2)

instance : DecidableRel wedgeLt := fun _ _ => by
  unfold wedgeLt
  infer_instance

/-- Visibility predicate: `gcd(Re(z - w), Im(z - w)) = 1`. -/
def IsVisibleFrom (z w : ℤ × ℤ) : Prop :=
  Nat.gcd (z.1 - w.1).natAbs (z.2 - w.2).natAbs = 1

instance (z : ℤ × ℤ) : DecidablePred (IsVisibleFrom z) := fun _ => by
  unfold IsVisibleFrom
  infer_instance

/-- Square box `[-B, B]² ∩ ℤ²`. -/
noncomputable def intBox (B : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ Finset.Icc (-(B : ℤ)) (B : ℤ)

lemma mem_intBox_of_gnorm_le {w : ℤ × ℤ} {B : ℕ} (h : gnorm w ≤ B) : w ∈ intBox B := by
  have h1 : w.1.natAbs ≤ B := by
    have hsq : w.1.natAbs ^ 2 ≤ B := le_trans (Nat.le_add_right _ _) h
    exact le_trans (Nat.le_self_pow (by norm_num) _) hsq
  have h2 : w.2.natAbs ≤ B := by
    have hsq : w.2.natAbs ^ 2 ≤ B := le_trans (Nat.le_add_left _ _) h
    exact le_trans (Nat.le_self_pow (by norm_num) _) hsq
  simp only [intBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Finite set of Gaussian integers `w` with `N(w) < N(z)` visible from `z`. -/
noncomputable def visibleSet (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (intBox (gnorm z)).filter (fun w => gnorm w < gnorm z ∧ IsVisibleFrom z w)

lemma mem_visibleSet {z w : ℤ × ℤ} :
    w ∈ visibleSet z ↔ gnorm w < gnorm z ∧ IsVisibleFrom z w := by
  simp only [visibleSet, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  exact mem_intBox_of_gnorm_le (le_of_lt h.1)

/-- Number of Gaussian integers `w` with `N(w) < N(z)` visible from `z`. -/
noncomputable def visibleCount (z : ℤ × ℤ) : ℕ :=
  (visibleSet z).card

/-! ### Exact enumeration of the fundamental wedge in `(norm, b)` order -/

/-- Wedge points of norm `≤ M`. -/
noncomputable def wedgeLe (M : ℕ) : Finset (ℤ × ℤ) :=
  (intBox M).filter (fun z => InWedge z ∧ gnorm z ≤ M)

/-- Wedge points of norm `< M`. -/
noncomputable def wedgeLtSet (M : ℕ) : Finset (ℤ × ℤ) :=
  (intBox M).filter (fun z => InWedge z ∧ gnorm z < M)

lemma mem_wedgeLe {M : ℕ} {z : ℤ × ℤ} :
    z ∈ wedgeLe M ↔ InWedge z ∧ gnorm z ≤ M := by
  simp only [wedgeLe, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  exact mem_intBox_of_gnorm_le h.2

lemma mem_wedgeLtSet {M : ℕ} {z : ℤ × ℤ} :
    z ∈ wedgeLtSet M ↔ InWedge z ∧ gnorm z < M := by
  simp only [wedgeLtSet, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  exact mem_intBox_of_gnorm_le (le_of_lt h.2)

lemma wedgeLt_trans {a b c : ℤ × ℤ} (h1 : wedgeLt a b) (h2 : wedgeLt b c) : wedgeLt a c := by
  rcases h1 with h1 | ⟨h1n, h1b⟩ <;> rcases h2 with h2 | ⟨h2n, h2b⟩
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (h2n ▸ h1)
  · exact Or.inl (h1n.symm ▸ h2)
  · exact Or.inr ⟨h1n.trans h2n, lt_trans h1b h2b⟩

lemma wedgeLt_irrefl (a : ℤ × ℤ) : ¬ wedgeLt a a := by
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma wedgeLt_trichotomy {a b : ℤ × ℤ} (ha : InWedge a) (hb : InWedge b) :
    wedgeLt a b ∨ a = b ∨ wedgeLt b a := by
  rcases lt_trichotomy (gnorm a) (gnorm b) with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases lt_trichotomy a.2 b.2 with hblt | hbeq | hbgt
    · exact Or.inl (Or.inr ⟨heq, hblt⟩)
    · right; left
      have ha1 : 0 ≤ a.1 := le_trans ha.1 ha.2.1
      have hb1 : 0 ≤ b.1 := le_trans hb.1 hb.2.1
      have hsq : a.1.natAbs ^ 2 = b.1.natAbs ^ 2 := by
        unfold gnorm at heq
        rw [hbeq] at heq
        omega
      have habs : a.1.natAbs = b.1.natAbs :=
        Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq
      have ha1eq : a.1 = b.1 := by omega
      exact Prod.ext ha1eq hbeq
    · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hbgt⟩))
  · exact Or.inr (Or.inr (Or.inl hgt))

/-- Exact 1-based position of `z` in the `(norm, b)` enumeration of the fundamental wedge. -/
noncomputable def wedgeRank (z : ℤ × ℤ) : ℕ :=
  ((wedgeLe (gnorm z)).filter (fun u => wedgeLt u z ∨ u = z)).card

lemma wedgeRank_eq_filter_of_le {z : ℤ × ℤ} {M : ℕ} (hM : gnorm z ≤ M) :
    wedgeRank z = ((wedgeLe M).filter (fun u => wedgeLt u z ∨ u = z)).card := by
  unfold wedgeRank
  congr 1
  ext u
  simp only [Finset.mem_filter, mem_wedgeLe]
  constructor
  · rintro ⟨⟨hu, hun⟩, hlt⟩
    exact ⟨⟨hu, le_trans hun hM⟩, hlt⟩
  · rintro ⟨⟨hu, _⟩, hlt⟩
    refine ⟨⟨hu, ?_⟩, hlt⟩
    rcases hlt with (h | ⟨h, _⟩) | rfl
    · exact le_of_lt h
    · exact le_of_eq h
    · exact le_rfl

lemma wedgeRank_pos {z : ℤ × ℤ} (hz : InWedge z) : 1 ≤ wedgeRank z := by
  unfold wedgeRank
  refine Finset.one_le_card.mpr ⟨z, ?_⟩
  simp [mem_wedgeLe, hz]

lemma wedgeRank_strictMono {z₁ z₂ : ℤ × ℤ} (h₁ : InWedge z₁) (h₂ : InWedge z₂)
    (hlt : wedgeLt z₁ z₂) : wedgeRank z₁ < wedgeRank z₂ := by
  have hle : gnorm z₁ ≤ gnorm z₂ := by
    rcases hlt with h | ⟨h, _⟩
    · exact le_of_lt h
    · exact le_of_eq h
  rw [wedgeRank_eq_filter_of_le hle, wedgeRank_eq_filter_of_le (le_refl (gnorm z₂))]
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨z₂, ?_, ?_⟩
    · simp [mem_wedgeLe, h₂]
    · simp only [Finset.mem_filter, not_and]
      intro _ h
      rcases h with h' | rfl
      · exact wedgeLt_irrefl z₁ (wedgeLt_trans hlt h')
      · exact wedgeLt_irrefl z₂ hlt
  · intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, Or.inl ?_⟩
    rcases hu.2 with h' | rfl
    · exact wedgeLt_trans h' hlt
    · exact hlt

lemma wedgeRank_injOn {z₁ z₂ : ℤ × ℤ} (h₁ : InWedge z₁) (h₂ : InWedge z₂)
    (heq : wedgeRank z₁ = wedgeRank z₂) : z₁ = z₂ := by
  rcases wedgeLt_trichotomy h₁ h₂ with hlt | rfl | hgt
  · exact absurd heq (ne_of_lt (wedgeRank_strictMono h₁ h₂ hlt))
  · rfl
  · exact absurd heq (ne_of_gt (wedgeRank_strictMono h₂ h₁ hgt))

lemma wedgeRank_le_card_wedgeLe {z : ℤ × ℤ} {M : ℕ} (hM : gnorm z ≤ M) :
    wedgeRank z ≤ (wedgeLe M).card := by
  rw [wedgeRank_eq_filter_of_le hM]
  exact Finset.card_filter_le _ _

lemma card_wedgeLe_sq_ge (n : ℕ) : n ≤ (wedgeLe (n ^ 2)).card := by
  let f : ℕ → ℤ × ℤ := fun k => ((k + 1 : ℕ), 0)
  have hsub : (Finset.range n).image f ⊆ wedgeLe (n ^ 2) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    rw [mem_wedgeLe]
    dsimp only [f]
    refine ⟨⟨le_refl 0, by omega, ?_⟩, ?_⟩
    · unfold gnorm; simp; exact Nat.pow_pos (Nat.succ_pos k)
    · unfold gnorm; simp
      exact Nat.pow_le_pow_left hk 2
  calc
    n = (Finset.range n).card := (Finset.card_range n).symm
    _ = ((Finset.range n).image f).card := by
      symm
      refine Finset.card_image_of_injective _ ?_
      intro a b hab
      have h1 := congr_arg Prod.fst hab
      dsimp [f] at h1
      omega
    _ ≤ (wedgeLe (n ^ 2)).card := Finset.card_le_card hsub

/-- Every positive integer `n ≥ 1` is the exact rank of a unique wedge point. -/
lemma wedgeRank_existsUnique {n : ℕ} (hn : 1 ≤ n) :
    ∃! z : ℤ × ℤ, InWedge z ∧ wedgeRank z = n := by
  let S := wedgeLe (n ^ 2)
  have hmaps : Set.MapsTo wedgeRank (S : Set (ℤ × ℤ)) (Finset.Icc 1 S.card : Set ℕ) := by
    intro z hz
    rw [Finset.mem_coe, mem_wedgeLe] at hz
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨wedgeRank_pos hz.1, wedgeRank_le_card_wedgeLe hz.2⟩
  have hinj : Set.InjOn wedgeRank (S : Set (ℤ × ℤ)) := by
    intro z₁ hz₁ z₂ hz₂ heq
    rw [Finset.mem_coe, mem_wedgeLe] at hz₁ hz₂
    exact wedgeRank_injOn hz₁.1 hz₂.1 heq
  have hsub : S.image wedgeRank ⊆ Finset.Icc 1 S.card := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨z, hz, rfl⟩
    rw [mem_wedgeLe] at hz
    exact Finset.mem_Icc.mpr ⟨wedgeRank_pos hz.1, wedgeRank_le_card_wedgeLe hz.2⟩
  have himg_eq : S.image wedgeRank = Finset.Icc 1 S.card := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hn_mem : n ∈ S.image wedgeRank := by
    rw [himg_eq, Finset.mem_Icc]
    exact ⟨hn, card_wedgeLe_sq_ge n⟩
  rcases Finset.mem_image.mp hn_mem with ⟨z, hzS, hzr⟩
  rw [mem_wedgeLe] at hzS
  refine ⟨z, ⟨hzS.1, hzr⟩, ?_⟩
  intro w ⟨hw, hwr⟩
  exact wedgeRank_injOn hw hzS.1 (hwr.trans hzr.symm)

/-- The `n`-th nonzero Gaussian integer (`n ≥ 1`) in the fundamental wedge `0 ≤ b ≤ a`,
ordered first by norm and then by `b`. -/
noncomputable def a401897_z (n : ℕ) : ℤ × ℤ :=
  if h : 1 ≤ n then (wedgeRank_existsUnique h).choose else (0, 0)

lemma a401897_z_inWedge {n : ℕ} (hn : 1 ≤ n) : InWedge (a401897_z n) := by
  simp only [a401897_z, dif_pos hn]
  exact (wedgeRank_existsUnique hn).choose_spec.1.1

lemma a401897_z_rank {n : ℕ} (hn : 1 ≤ n) : wedgeRank (a401897_z n) = n := by
  simp only [a401897_z, dif_pos hn]
  exact (wedgeRank_existsUnique hn).choose_spec.1.2

lemma a401897_z_unique {n : ℕ} {z : ℤ × ℤ} (hn : 1 ≤ n) (hz : InWedge z)
    (hr : wedgeRank z = n) : a401897_z n = z := by
  exact wedgeRank_injOn (a401897_z_inWedge hn) hz ((a401897_z_rank hn).trans hr.symm)

lemma a401897_z_strictMono {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    wedgeLt (a401897_z m) (a401897_z n) := by
  have hn : 1 ≤ n := le_trans hm (le_of_lt hmn)
  rcases wedgeLt_trichotomy (a401897_z_inWedge hm) (a401897_z_inWedge hn) with hlt | heq | hgt
  · exact hlt
  · have h := congr_arg wedgeRank heq
    rw [a401897_z_rank hm, a401897_z_rank hn] at h
    omega
  · have h := wedgeRank_strictMono (a401897_z_inWedge hn) (a401897_z_inWedge hm) hgt
    rw [a401897_z_rank hm, a401897_z_rank hn] at h
    omega

/-- OEIS A401897: `a(n)` is the number of Gaussian integers `w` with `N(w) < N(z_n)`
that are visible from `z_n`. -/
noncomputable def a401897 (n : ℕ) : ℕ :=
  visibleCount (a401897_z n)

/-- Tie sandwich: for any `n ≥ 1` with `N = N(z_n)`, `W°(N) + 1 ≤ n ≤ W(N)`. -/
lemma rank_sandwich {n : ℕ} (hn : 1 ≤ n) :
    (wedgeLtSet (gnorm (a401897_z n))).card + 1 ≤ n ∧
      n ≤ (wedgeLe (gnorm (a401897_z n))).card := by
  set z := a401897_z n
  have hz : InWedge z := a401897_z_inWedge hn
  have hrank : wedgeRank z = n := a401897_z_rank hn
  constructor
  · have hsub : insert z (wedgeLtSet (gnorm z)) ⊆
        (wedgeLe (gnorm z)).filter (fun u => wedgeLt u z ∨ u = z) := by
      intro u hu
      simp only [Finset.mem_insert, mem_wedgeLtSet] at hu
      simp only [Finset.mem_filter, mem_wedgeLe]
      rcases hu with rfl | ⟨huW, hult⟩
      · exact ⟨⟨hz, le_rfl⟩, Or.inr rfl⟩
      · exact ⟨⟨huW, le_of_lt hult⟩, Or.inl (Or.inl hult)⟩
    have hnot : z ∉ wedgeLtSet (gnorm z) := by
      simp [mem_wedgeLtSet]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hcard
    have hrank' : ((wedgeLe (gnorm z)).filter (fun u => wedgeLt u z ∨ u = z)).card = n := hrank
    omega
  · rw [← hrank]
    exact wedgeRank_le_card_wedgeLe le_rfl

/-! ### Section 1: Shifted Gauss Circle Lemma -/

/-- Embedding of `ℤ × ℤ` into `ℂ`. -/
def latPt (p : ℤ × ℤ) : ℂ :=
  { re := (p.1 : ℝ), im := (p.2 : ℝ) }

lemma latPt_re (p : ℤ × ℤ) : (latPt p).re = (p.1 : ℝ) := rfl
lemma latPt_im (p : ℤ × ℤ) : (latPt p).im = (p.2 : ℝ) := rfl

lemma norm_latPt_sq (p : ℤ × ℤ) : ‖latPt p‖ ^ 2 = ((gnorm p : ℕ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, latPt_re, latPt_im, gnorm_cast_real]
  ring

/-- Half-open unit square centered at `p ∈ ℤ²`. -/
def unitSq (p : ℤ × ℤ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Set.Ico ((p.1 : ℝ) - 1 / 2) ((p.1 : ℝ) + 1 / 2) ×ˢ
      Set.Ico ((p.2 : ℝ) - 1 / 2) ((p.2 : ℝ) + 1 / 2))

lemma mem_unitSq {p : ℤ × ℤ} {x : ℂ} :
    x ∈ unitSq p ↔
      (p.1 : ℝ) - 1 / 2 ≤ x.re ∧ x.re < (p.1 : ℝ) + 1 / 2 ∧
      (p.2 : ℝ) - 1 / 2 ≤ x.im ∧ x.im < (p.2 : ℝ) + 1 / 2 := by
  simp [unitSq, Complex.measurableEquivRealProd_apply, Set.mem_prod, Set.mem_Ico, and_assoc]

lemma measurableSet_unitSq (p : ℤ × ℤ) : MeasurableSet (unitSq p) :=
  (measurableSet_Ico.prod measurableSet_Ico).preimage Complex.measurableEquivRealProd.measurable

lemma volume_unitSq (p : ℤ × ℤ) : volume (unitSq p) = 1 := by
  unfold unitSq
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  have h1 : ((p.1 : ℝ) + 1 / 2) - ((p.1 : ℝ) - 1 / 2) = 1 := by ring
  have h2 : ((p.2 : ℝ) + 1 / 2) - ((p.2 : ℝ) - 1 / 2) = 1 := by ring
  rw [h1, h2]
  simp

lemma pairwiseDisjoint_unitSq :
    Set.PairwiseDisjoint (Set.univ : Set (ℤ × ℤ)) unitSq := by
  intro p _ q _ hpq
  change Disjoint (unitSq p) (unitSq q)
  rw [Set.disjoint_left]
  intro x hxp hxq
  rw [mem_unitSq] at hxp hxq
  have h1 : p.1 = q.1 := by
    have ha : ((p.1 : ℝ) - (q.1 : ℝ)) < 1 := by linarith
    have hb : ((q.1 : ℝ) - (p.1 : ℝ)) < 1 := by linarith
    have ha' : (p.1 - q.1 : ℤ) < 1 := by exact_mod_cast ha
    have hb' : (q.1 - p.1 : ℤ) < 1 := by exact_mod_cast hb
    omega
  have h2 : p.2 = q.2 := by
    have ha : ((p.2 : ℝ) - (q.2 : ℝ)) < 1 := by linarith
    have hb : ((q.2 : ℝ) - (p.2 : ℝ)) < 1 := by linarith
    have ha' : (p.2 - q.2 : ℤ) < 1 := by exact_mod_cast ha
    have hb' : (q.2 - p.2 : ℤ) < 1 := by exact_mod_cast hb
    omega
  exact hpq (Prod.ext h1 h2)

lemma dist_le_inv_sqrt_two_of_mem_unitSq {p : ℤ × ℤ} {x : ℂ} (hx : x ∈ unitSq p) :
    dist x (latPt p) ≤ 1 / Real.sqrt 2 := by
  rw [mem_unitSq] at hx
  have hre : (x.re - (p.1 : ℝ)) ^ 2 ≤ 1 / 4 := by
    have habs : |x.re - (p.1 : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [sq_abs (x.re - (p.1 : ℝ))]
  have him : (x.im - (p.2 : ℝ)) ^ 2 ≤ 1 / 4 := by
    have habs : |x.im - (p.2 : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [sq_abs (x.im - (p.2 : ℝ))]
  have hsq : dist x (latPt p) ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, latPt_re, latPt_im]
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hpos : 0 ≤ (1 : ℝ) / Real.sqrt 2 := by positivity
  exact le_of_sq_le_sq hsq hpos

lemma exists_mem_unitSq (x : ℂ) : ∃ p : ℤ × ℤ, x ∈ unitSq p := by
  refine ⟨(⌊x.re + 1 / 2⌋, ⌊x.im + 1 / 2⌋), ?_⟩
  rw [mem_unitSq]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [Int.floor_le (x.re + 1 / 2)]
  · linarith [Int.lt_floor_add_one (x.re + 1 / 2)]
  · linarith [Int.floor_le (x.im + 1 / 2)]
  · linarith [Int.lt_floor_add_one (x.im + 1 / 2)]

/-- Generalized shifted Gauss circle bound for any finite set `S` of lattice points
sandwiched between the open disk `B(c, r)` and the closed disk `B̄(c, r)`. -/
lemma shifted_gauss_circle_general (c : ℂ) {r : ℝ} (hr : 0 < r) (S : Finset (ℤ × ℤ))
    (hsub : ∀ p ∈ S, dist (latPt p) c ≤ r)
    (hsup : ∀ p : ℤ × ℤ, dist (latPt p) c < r → p ∈ S) :
    |(S.card : ℝ) - Real.pi * r ^ 2| ≤ Real.pi * (Real.sqrt 2 * r + 1 / 2) := by
  have hvol_union : volume (⋃ p ∈ S, unitSq p) = (S.card : ENNReal) := by
    rw [measure_biUnion_finset]
    · simp [volume_unitSq]
    · intro p _ q _ hpq
      exact pairwiseDisjoint_unitSq (Set.mem_univ p) (Set.mem_univ q) hpq
    · intro p _
      exact measurableSet_unitSq p
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h2inv : 2 * r * (1 / Real.sqrt 2) = Real.sqrt 2 * r := by
    have h2 : (2 : ℝ) = Real.sqrt 2 * Real.sqrt 2 := (Real.mul_self_sqrt (by norm_num)).symm
    field_simp
    nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  -- Upper bound
  have hupper : (S.card : ℝ) ≤ Real.pi * r ^ 2 + Real.pi * (Real.sqrt 2 * r + 1 / 2) := by
    have hinc : (⋃ p ∈ S, unitSq p) ⊆ Metric.closedBall c (r + 1 / Real.sqrt 2) := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      rcases hx with ⟨p, hpS, hxp⟩
      rw [Metric.mem_closedBall]
      calc
        dist x c ≤ dist x (latPt p) + dist (latPt p) c := dist_triangle _ _ _
        _ ≤ 1 / Real.sqrt 2 + r := add_le_add (dist_le_inv_sqrt_two_of_mem_unitSq hxp) (hsub p hpS)
        _ = r + 1 / Real.sqrt 2 := add_comm _ _
    have hle : volume (⋃ p ∈ S, unitSq p) ≤ volume (Metric.closedBall c (r + 1 / Real.sqrt 2)) :=
      measure_mono hinc
    rw [hvol_union, Complex.volume_closedBall] at hle
    have hfin : ENNReal.ofReal (r + 1 / Real.sqrt 2) ^ 2 * ↑NNReal.pi ≠ ⊤ := by
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
    have hreal := ENNReal.toReal_mono hfin hle
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal, NNReal.coe_real_pi] at hreal
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    have hexp : (r + 1 / Real.sqrt 2) ^ 2 * Real.pi =
        Real.pi * r ^ 2 + Real.pi * (Real.sqrt 2 * r + 1 / 2) := by
      calc
        (r + 1 / Real.sqrt 2) ^ 2 * Real.pi
            = Real.pi * (r ^ 2 + 2 * r * (1 / Real.sqrt 2) + (1 / Real.sqrt 2) ^ 2) := by ring
        _ = Real.pi * (r ^ 2 + Real.sqrt 2 * r + 1 / 2) := by rw [h2inv, hinv_sq]
        _ = Real.pi * r ^ 2 + Real.pi * (Real.sqrt 2 * r + 1 / 2) := by ring
    linarith
  -- Lower bound
  have hlower : Real.pi * r ^ 2 - Real.pi * (Real.sqrt 2 * r + 1 / 2) ≤ (S.card : ℝ) := by
    by_cases hsmall : r < 1 / Real.sqrt 2
    · have hsq : r ^ 2 < 1 / 2 := by
        have h1 : r ^ 2 < (1 / Real.sqrt 2) ^ 2 := by nlinarith
        rwa [hinv_sq] at h1
      have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [mul_pos hsqrt2_pos hr]
    · push Not at hsmall
      have hinc : Metric.ball c (r - 1 / Real.sqrt 2) ⊆ (⋃ p ∈ S, unitSq p) := by
        intro x hx
        rw [Metric.mem_ball] at hx
        rcases exists_mem_unitSq x with ⟨p, hxp⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨p, hsup p ?_, hxp⟩
        calc
          dist (latPt p) c ≤ dist (latPt p) x + dist x c := dist_triangle _ _ _
          _ = dist x (latPt p) + dist x c := by rw [dist_comm]
          _ < 1 / Real.sqrt 2 + (r - 1 / Real.sqrt 2) :=
            add_lt_add_of_le_of_lt (dist_le_inv_sqrt_two_of_mem_unitSq hxp) hx
          _ = r := by ring
      have hle : volume (Metric.ball c (r - 1 / Real.sqrt 2)) ≤ volume (⋃ p ∈ S, unitSq p) :=
        measure_mono hinc
      rw [hvol_union, Complex.volume_ball] at hle
      have hreal := ENNReal.toReal_mono (ENNReal.natCast_ne_top S.card) hle
      simp only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.coe_toReal, NNReal.coe_real_pi] at hreal
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hsmall)] at hreal
      have hexp : (r - 1 / Real.sqrt 2) ^ 2 * Real.pi =
          Real.pi * r ^ 2 - Real.pi * (Real.sqrt 2 * r - 1 / 2) := by
        calc
          (r - 1 / Real.sqrt 2) ^ 2 * Real.pi
              = Real.pi * (r ^ 2 - 2 * r * (1 / Real.sqrt 2) + (1 / Real.sqrt 2) ^ 2) := by ring
          _ = Real.pi * (r ^ 2 - Real.sqrt 2 * r + 1 / 2) := by rw [h2inv, hinv_sq]
          _ = Real.pi * r ^ 2 - Real.pi * (Real.sqrt 2 * r - 1 / 2) := by ring
      have hpi : 0 < Real.pi := Real.pi_pos
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Bounding box large enough to contain all lattice points within distance `r` of `c`. -/
noncomputable def diskBox (c : ℂ) (r : ℝ) : Finset (ℤ × ℤ) :=
  intBox (Nat.ceil (‖c‖ + r) + 1)

lemma mem_diskBox_of_dist_le {c : ℂ} {r : ℝ} {p : ℤ × ℤ} (h : dist (latPt p) c ≤ r) :
    p ∈ diskBox c r := by
  have hnorm : ‖latPt p‖ ≤ ‖c‖ + r := by
    calc
      ‖latPt p‖ = dist (latPt p) 0 := by simp [dist_zero_right]
      _ ≤ dist (latPt p) c + dist c 0 := dist_triangle _ _ _
      _ ≤ r + ‖c‖ := by simpa [dist_zero_right] using add_le_add_right h ‖c‖
      _ = ‖c‖ + r := add_comm _ _
  have hre : |(p.1 : ℝ)| ≤ ‖c‖ + r := by
    calc
      |(p.1 : ℝ)| = |(latPt p).re| := rfl
      _ ≤ ‖latPt p‖ := Complex.abs_re_le_norm _
      _ ≤ ‖c‖ + r := hnorm
  have him : |(p.2 : ℝ)| ≤ ‖c‖ + r := by
    calc
      |(p.2 : ℝ)| = |(latPt p).im| := rfl
      _ ≤ ‖latPt p‖ := Complex.abs_im_le_norm _
      _ ≤ ‖c‖ + r := hnorm
  set B := Nat.ceil (‖c‖ + r) + 1
  have hB : ‖c‖ + r ≤ (B : ℝ) := by
    have hc : ‖c‖ + r ≤ (Nat.ceil (‖c‖ + r) : ℝ) := Nat.le_ceil _
    push_cast [B]
    linarith
  have h1 : |(p.1 : ℝ)| ≤ (B : ℝ) := le_trans hre hB
  have h2 : |(p.2 : ℝ)| ≤ (B : ℝ) := le_trans him hB
  have h1' : -(B : ℤ) ≤ p.1 ∧ p.1 ≤ (B : ℤ) := by
    have := abs_le.mp h1
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have h2' : -(B : ℤ) ≤ p.2 ∧ p.2 ≤ (B : ℤ) := by
    have := abs_le.mp h2
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  simp only [diskBox, intBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨h1', h2'⟩

/-- Lattice points in the open disk `B(c, r)`. -/
noncomputable def openDiskLattice (c : ℂ) (r : ℝ) : Finset (ℤ × ℤ) :=
  (diskBox c r).filter (fun p => dist (latPt p) c < r)

/-- Lattice points in the closed disk `B̄(c, r)`. -/
noncomputable def closedDiskLattice (c : ℂ) (r : ℝ) : Finset (ℤ × ℤ) :=
  (diskBox c r).filter (fun p => dist (latPt p) c ≤ r)

lemma mem_openDiskLattice {c : ℂ} {r : ℝ} {p : ℤ × ℤ} :
    p ∈ openDiskLattice c r ↔ dist (latPt p) c < r := by
  simp only [openDiskLattice, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  exact mem_diskBox_of_dist_le (le_of_lt h)

lemma mem_closedDiskLattice {c : ℂ} {r : ℝ} {p : ℤ × ℤ} :
    p ∈ closedDiskLattice c r ↔ dist (latPt p) c ≤ r := by
  simp only [closedDiskLattice, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  exact mem_diskBox_of_dist_le h

/-- Shifted Gauss circle bound for open disks. -/
theorem shifted_gauss_circle_open (c : ℂ) {r : ℝ} (hr : 0 < r) :
    |((openDiskLattice c r).card : ℝ) - Real.pi * r ^ 2| ≤
      Real.pi * (Real.sqrt 2 * r + 1 / 2) := by
  refine shifted_gauss_circle_general c hr (openDiskLattice c r) ?_ ?_
  · intro p hp
    exact le_of_lt (mem_openDiskLattice.mp hp)
  · intro p hp
    exact mem_openDiskLattice.mpr hp

/-- Shifted Gauss circle bound for closed disks. -/
theorem shifted_gauss_circle_closed (c : ℂ) {r : ℝ} (hr : 0 < r) :
    |((closedDiskLattice c r).card : ℝ) - Real.pi * r ^ 2| ≤
      Real.pi * (Real.sqrt 2 * r + 1 / 2) := by
  refine shifted_gauss_circle_general c hr (closedDiskLattice c r) ?_ ?_
  · intro p hp
    exact mem_closedDiskLattice.mp hp
  · intro p hp
    exact mem_closedDiskLattice.mpr (le_of_lt hp)

/-! ### Section 2: Möbius series `∑ μ(d)/d² = 6/π²`, tail bound, and harmonic bound -/

lemma hasSum_moebius_div_sq :
    HasSum (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hsumm : LSeriesSummable ↗μ (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr h2
  have hprod : L ↗ζ (2 : ℂ) * L ↗μ (2 : ℂ) = 1 :=
    ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius h2
  have hzeta : L ↗ζ (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta h2, riemannZeta_two]
  have hLval : L ↗μ (2 : ℂ) = (((6 / Real.pi ^ 2 : ℝ) : ℂ)) := by
    have hpi : ((Real.pi : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [hzeta] at hprod
    push_cast
    have hmul : ((Real.pi : ℂ) ^ 2 / 6) * (6 / (Real.pi : ℂ) ^ 2) = 1 := by
      field_simp
    have hne : ((Real.pi : ℂ) ^ 2 / 6) ≠ 0 := div_ne_zero hpi (by norm_num)
    exact mul_left_cancel₀ hne (hprod.trans hmul.symm)
  have hterm : ∀ d : ℕ, LSeries.term ↗μ (2 : ℂ) d = (((μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [LSeries.term]
    · simp only [LSeries.term, if_neg hd]
      have hcpow : (d : ℂ) ^ (2 : ℂ) = (d : ℂ) ^ (2 : ℕ) := by
        simp
      rw [hcpow]
      push_cast
      rfl
  have hhasC : HasSum (fun d : ℕ => (((μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ))
      (((6 / Real.pi ^ 2 : ℝ) : ℂ)) := by
    have h0 : HasSum (LSeries.term ↗μ (2 : ℂ)) (((6 / Real.pi ^ 2 : ℝ) : ℂ)) := by
      have h1 := hsumm.LSeriesHasSum
      rw [LSeriesHasSum, hLval] at h1
      exact h1
    have hfun : LSeries.term ↗μ (2 : ℂ) = fun d : ℕ => (((μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) :=
      funext hterm
    rwa [hfun] at h0
  exact Complex.hasSum_ofReal.mp hhasC

/-- Telescoping sum `∑_{k=0}^∞ 1 / ((M + k)(M + k - 1)) = 1 / (M - 1)` for `M ≥ 2`. -/
lemma hasSum_inv_mul_pred {M : ℕ} (hM : 2 ≤ M) :
    HasSum (fun k : ℕ => (1 : ℝ) / (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1)))
      (1 / ((M : ℝ) - 1)) := by
  have hnonneg : ∀ k : ℕ,
      0 ≤ (1 : ℝ) / (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1)) := by
    intro k
    have h1 : (1 : ℝ) < ((M + k : ℕ) : ℝ) := by
      have : 2 ≤ M + k := by omega
      exact_mod_cast (by omega : 1 < M + k)
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpart : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, (1 : ℝ) / (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1)) =
        1 / ((M : ℝ) - 1) - 1 / (((M + n : ℕ) : ℝ) - 1) := by
    intro n
    have hterm : ∀ k : ℕ,
        (1 : ℝ) / (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1)) =
          1 / (((M + k : ℕ) : ℝ) - 1) - 1 / (((M + (k + 1) : ℕ) : ℝ) - 1) := by
      intro k
      have h1 : ((M + k : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : (((M + k : ℕ) : ℝ) - 1) ≠ 0 := by
        have : 2 ≤ M + k := by omega
        have : (1 : ℝ) < ((M + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < M + k)
        linarith
      have h3 : (((M + (k + 1) : ℕ) : ℝ) - 1) = ((M + k : ℕ) : ℝ) := by
        push_cast; ring
      rw [h3]
      field_simp
      ring
    simp_rw [hterm]
    rw [Finset.sum_range_sub' (fun k => 1 / (((M + k : ℕ) : ℝ) - 1)) n]
    simp
  simp_rw [hpart]
  have htend : Tendsto (fun n : ℕ => (1 : ℝ) / (((M + n : ℕ) : ℝ) - 1)) atTop (nhds 0) := by
    have hinf : Tendsto (fun n : ℕ => (((M + n : ℕ) : ℝ) - 1)) atTop atTop := by
      refine tendsto_atTop_add_const_right atTop (-1 : ℝ) ?_
      have : (fun n : ℕ => ((M + n : ℕ) : ℝ)) = (fun n : ℕ => (M : ℝ) + (n : ℝ)) := by
        ext n; push_cast; ring
      rw [this]
      exact tendsto_atTop_add_const_left atTop (M : ℝ) tendsto_natCast_atTop_atTop
    convert tendsto_inv_atTop_zero.comp hinf using 1
    ext n
    simp [one_div]
  simpa using tendsto_const_nhds.sub htend

/-- Tail bound for the Möbius series `∑_{d < M} μ(d)/d²`. -/
lemma abs_sub_sum_moebius_div_sq_le {M : ℕ} (hM : 2 ≤ M) :
    |(∑ d ∈ Finset.range M, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤
      1 / ((M : ℝ) - 1) := by
  let f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2
  have hsum : HasSum f (6 / Real.pi ^ 2) := hasSum_moebius_div_sq
  have hsplit := hsum.summable.sum_add_tsum_nat_add M
  rw [hsum.tsum_eq] at hsplit
  have hdiff : (∑ d ∈ Finset.range M, f d) - 6 / Real.pi ^ 2 = -∑' k : ℕ, f (k + M) := by
    linarith
  rw [hdiff, abs_neg]
  let g : ℕ → ℝ := fun k => 1 / (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1))
  have hg_sum : HasSum g (1 / ((M : ℝ) - 1)) := hasSum_inv_mul_pred hM
  have hdom : ∀ k : ℕ, |f (k + M)| ≤ g k := by
    intro k
    dsimp only [f, g]
    have hmu : |(μ (k + M) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k + M)
    have hkm_eq : ((k + M : ℕ) : ℝ) = ((M + k : ℕ) : ℝ) := by
      push_cast; ring
    have hpos : (1 : ℝ) < ((M + k : ℕ) : ℝ) := by
      have : 2 ≤ M + k := by omega
      exact_mod_cast (by omega : 1 < M + k)
    have hnn : |((M + k : ℕ) : ℝ)| = ((M + k : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [abs_div, abs_pow, hkm_eq, hnn]
    calc
      |(μ (k + M) : ℝ)| / ((M + k : ℕ) : ℝ) ^ 2
          ≤ 1 / ((M + k : ℕ) : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hmu (sq_nonneg _)
      _ ≤ 1 / (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1)) := by
        refine one_div_le_one_div_of_le (by nlinarith) ?_
        nlinarith
  have hpart_g : ∀ n : ℕ, ∑ k ∈ Finset.range n, g k ≤ 1 / ((M : ℝ) - 1) := by
    intro n
    have hterm : ∀ k : ℕ,
        g k = 1 / (((M + k : ℕ) : ℝ) - 1) - 1 / (((M + (k + 1) : ℕ) : ℝ) - 1) := by
      intro k
      dsimp only [g]
      have h1 : ((M + k : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : (((M + k : ℕ) : ℝ) - 1) ≠ 0 := by
        have : (1 : ℝ) < ((M + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < M + k)
        linarith
      have h3 : (((M + (k + 1) : ℕ) : ℝ) - 1) = ((M + k : ℕ) : ℝ) := by
        push_cast; ring
      rw [h3]; field_simp; ring
    have hsum_eq : ∑ k ∈ Finset.range n, g k =
        1 / ((M : ℝ) - 1) - 1 / (((M + n : ℕ) : ℝ) - 1) := by
      simp_rw [hterm]
      rw [Finset.sum_range_sub' (fun k => 1 / (((M + k : ℕ) : ℝ) - 1)) n]
      simp
    rw [hsum_eq]
    have hpos_tail : 0 < 1 / (((M + n : ℕ) : ℝ) - 1) := by
      have : (1 : ℝ) < ((M + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < M + n)
      positivity
    linarith
  have hshift_summ : Summable (fun k : ℕ => f (k + M)) :=
    hsum.summable.comp_injective (add_left_injective M)
  have htend : Tendsto (fun n : ℕ => |∑ k ∈ Finset.range n, f (k + M)|)
      atTop (nhds |∑' k : ℕ, f (k + M)|) :=
    continuous_abs.continuousAt.tendsto.comp hshift_summ.hasSum.tendsto_sum_nat
  refine le_of_tendsto htend (Eventually.of_forall fun n => ?_)
  calc
    |∑ k ∈ Finset.range n, f (k + M)| ≤ ∑ k ∈ Finset.range n, |f (k + M)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, g k := Finset.sum_le_sum fun k _ => hdom k
    _ ≤ 1 / ((M : ℝ) - 1) := hpart_g n

/-- Elementary harmonic sum upper bound: `∑_{1 ≤ d < M} 1/d ≤ 1 + log(M - 1)` for `M ≥ 2`. -/
lemma sum_Ico_inv_le_one_add_log {M : ℕ} (hM : 2 ≤ M) :
    ∑ d ∈ Finset.Ico 1 M, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log ((M : ℝ) - 1) := by
  induction M, hM using Nat.le_induction with
  | base =>
    norm_num
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hstep : (1 : ℝ) / (k : ℝ) ≤ Real.log (k : ℝ) - Real.log ((k : ℝ) - 1) := by
      have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
      have hpos : 0 < ((k : ℝ) - 1) / (k : ℝ) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hpos
      rw [Real.log_div (by linarith) (by linarith)] at hlog
      have halg : ((k : ℝ) - 1) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
        field_simp
        ring
      linarith
    have hcast : (((k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by push_cast; ring
    rw [hcast]
    linarith

/-! ### Section 3: Möbius inversion and Proposition A (uniform visibility bound) -/

lemma sum_divisors_moebius {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (μ d : ℤ) = if g = 1 then 1 else 0 := by
  have h := congr_fun (congr_arg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) g
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  rw [Nat.sum_divisorsAntidiagonal (f := fun d e => μ d * (ζ : ArithmeticFunction ℤ) e)]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (by omega) (Nat.mem_divisors.mp hd).1
  have hq0 : g / d ≠ 0 := by
    have hle : d ≤ g := Nat.le_of_dvd hg (Nat.mem_divisors.mp hd).1
    exact (Nat.div_pos hle (Nat.pos_of_ne_zero hd0)).ne'
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq0]

/-- Shifted count `L(z, d) = #{u ∈ ℤ² : N(d u - z) < N(z)}`. -/
noncomputable def Lcount (z : ℤ × ℤ) (d : ℕ) : ℕ :=
  (openDiskLattice (latPt z / (d : ℂ)) (Real.sqrt (gnorm z) / (d : ℝ))).card

lemma mem_openDiskLattice_Lcount {z u : ℤ × ℤ} {d : ℕ} (hd : 0 < d) :
    u ∈ openDiskLattice (latPt z / (d : ℂ)) (Real.sqrt (gnorm z) / (d : ℝ)) ↔
      gnorm ((d : ℤ) * u.1 - z.1, (d : ℤ) * u.2 - z.2) < gnorm z := by
  rw [mem_openDiskLattice]
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdist : dist (latPt u) (latPt z / (d : ℂ)) =
      ‖latPt ((d : ℤ) * u.1 - z.1, (d : ℤ) * u.2 - z.2)‖ / (d : ℝ) := by
    rw [dist_eq_norm]
    have hsub : latPt u - latPt z / (d : ℂ) =
        latPt ((d : ℤ) * u.1 - z.1, (d : ℤ) * u.2 - z.2) / (d : ℂ) := by
      have hnat : (d : ℂ) = ((d : ℝ) : ℂ) := by norm_cast
      rw [hnat]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.div_ofReal_re, latPt_re]
        push_cast; field_simp
      · simp only [Complex.sub_im, Complex.div_ofReal_im, latPt_im]
        push_cast; field_simp
    rw [hsub, norm_div, Complex.norm_natCast]
  rw [hdist, div_lt_div_iff_of_pos_right hd_pos]
  have h1 : 0 ≤ ‖latPt ((d : ℤ) * u.1 - z.1, (d : ℤ) * u.2 - z.2)‖ := norm_nonneg _
  have h2 : 0 ≤ Real.sqrt (gnorm z) := Real.sqrt_nonneg _
  constructor
  · intro hlt
    have hsq : ‖latPt ((d : ℤ) * u.1 - z.1, (d : ℤ) * u.2 - z.2)‖ ^ 2 <
        (Real.sqrt (gnorm z)) ^ 2 := by nlinarith
    rw [norm_latPt_sq, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    exact_mod_cast hsq
  · intro hlt
    have hsq : ‖latPt ((d : ℤ) * u.1 - z.1, (d : ℤ) * u.2 - z.2)‖ ^ 2 <
        (Real.sqrt (gnorm z)) ^ 2 := by
      rw [norm_latPt_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
      exact_mod_cast hlt
    nlinarith

/-- Exact Möbius inversion formula: `visibleCount z = ∑_{1 ≤ d < ⌈2√N⌉} μ(d) L(z, d)`. -/
lemma visibleCount_eq_moebius_sum {z : ℤ × ℤ} (hz : 0 < gnorm z) :
    (visibleCount z : ℤ) =
      ∑ d ∈ Finset.Ico 1 (Nat.ceil (2 * Real.sqrt (gnorm z))),
        (μ d : ℤ) * (Lcount z d : ℤ) := by
  set N := gnorm z
  set R := Real.sqrt (N : ℝ)
  set M := Nat.ceil (2 * R)
  have hR_ge_one : (1 : ℝ) ≤ R := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hz
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hN1
  -- Step 1: Reindex `w ↦ v = z - w`
  let V : Finset (ℤ × ℤ) :=
    (intBox (2 * N)).filter (fun v => gnorm (v.1 - z.1, v.2 - z.2) < N)
  have hmemV : ∀ v : ℤ × ℤ, v ∈ V ↔ gnorm (v.1 - z.1, v.2 - z.2) < N := by
    intro v
    simp only [V, Finset.mem_filter, and_iff_right_iff_imp]
    intro hv
    have hnorm_vz : ‖latPt (v.1 - z.1, v.2 - z.2)‖ < R := by
      have hsq : ‖latPt (v.1 - z.1, v.2 - z.2)‖ ^ 2 < R ^ 2 := by
        rw [norm_latPt_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
        exact_mod_cast hv
      nlinarith [norm_nonneg (latPt (v.1 - z.1, v.2 - z.2))]
    have hnorm_z : ‖latPt z‖ = R := by
      have hsq : ‖latPt z‖ ^ 2 = R ^ 2 := by
        rw [norm_latPt_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
      nlinarith [norm_nonneg (latPt z)]
    have hnorm_v : ‖latPt v‖ < 2 * R := by
      have heq : latPt v = latPt (v.1 - z.1, v.2 - z.2) + latPt z := by
        apply Complex.ext <;> simp [latPt]
      calc
        ‖latPt v‖ = ‖latPt (v.1 - z.1, v.2 - z.2) + latPt z‖ := by rw [heq]
        _ ≤ ‖latPt (v.1 - z.1, v.2 - z.2)‖ + ‖latPt z‖ := norm_add_le _ _
        _ < R + R := by linarith
        _ = 2 * R := by ring
    have hsq_v : ((gnorm v : ℕ) : ℝ) < 4 * (N : ℝ) := by
      rw [← norm_latPt_sq]
      have : (2 * R) ^ 2 = 4 * (N : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
      nlinarith [norm_nonneg (latPt v)]
    have hgv : gnorm v < 4 * N := by exact_mod_cast hsq_v
    have h1 : v.1.natAbs ≤ 2 * N := by
      have hsq : v.1.natAbs ^ 2 ≤ 4 * N := le_trans (Nat.le_add_right _ _) (le_of_lt hgv)
      have h4N : 4 * N ≤ (2 * N) ^ 2 := by nlinarith
      nlinarith
    have h2 : v.2.natAbs ≤ 2 * N := by
      have hsq : v.2.natAbs ^ 2 ≤ 4 * N := le_trans (Nat.le_add_left _ _) (le_of_lt hgv)
      have h4N : 4 * N ≤ (2 * N) ^ 2 := by nlinarith
      nlinarith
    simp only [intBox, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hbij_vis :
      visibleCount z = (V.filter (fun v => Nat.gcd v.1.natAbs v.2.natAbs = 1)).card := by
    unfold visibleCount
    refine Finset.card_bij (fun w _ => (z.1 - w.1, z.2 - w.2)) ?_ ?_ ?_
    · intro w hw
      rw [mem_visibleSet] at hw
      simp only [Finset.mem_filter, hmemV]
      refine ⟨?_, hw.2⟩
      have heq : gnorm ((z.1 - w.1) - z.1, (z.2 - w.2) - z.2) = gnorm w := by
        unfold gnorm; simp
      rw [heq]; exact hw.1
    · intro w₁ _ w₂ _ h
      have h1 := congr_arg Prod.fst h
      have h2 := congr_arg Prod.snd h
      dsimp at h1 h2
      exact Prod.ext (by omega) (by omega)
    · intro v hv
      simp only [Finset.mem_filter, hmemV] at hv
      refine ⟨(z.1 - v.1, z.2 - v.2), ?_, ?_⟩
      · rw [mem_visibleSet]
        refine ⟨?_, ?_⟩
        · have heq : gnorm (z.1 - v.1, z.2 - v.2) = gnorm (v.1 - z.1, v.2 - z.2) := by
            unfold gnorm
            rw [← Int.natAbs_neg (z.1 - v.1), ← Int.natAbs_neg (z.2 - v.2)]
            simp
          rw [heq]; exact hv.1
        · unfold IsVisibleFrom
          have h1 : z.1 - (z.1 - v.1) = v.1 := by ring
          have h2 : z.2 - (z.2 - v.2) = v.2 := by ring
          rw [h1, h2]; exact hv.2
      · ext <;> dsimp <;> ring
  -- Step 2: Every `v ∈ V` is nonzero and every divisor `d` of `gcd(v.1, v.2)` satisfies `1 ≤ d < M`
  have hv_ne_zero : ∀ v ∈ V, 0 < Nat.gcd v.1.natAbs v.2.natAbs := by
    intro v hv
    rw [hmemV] at hv
    by_contra h0
    have hg0 : Nat.gcd v.1.natAbs v.2.natAbs = 0 := by omega
    have h1 : v.1.natAbs = 0 := (Nat.gcd_eq_zero_iff.mp hg0).1
    have h2 : v.2.natAbs = 0 := (Nat.gcd_eq_zero_iff.mp hg0).2
    have hv1 : v.1 = 0 := Int.natAbs_eq_zero.mp h1
    have hv2 : v.2 = 0 := Int.natAbs_eq_zero.mp h2
    rw [hv1, hv2] at hv
    have heq : gnorm (0 - z.1, 0 - z.2) = N := by unfold gnorm; simp; rfl
    omega
  have hdvd_lt_M : ∀ v ∈ V, ∀ d ∈ (Nat.gcd v.1.natAbs v.2.natAbs).divisors,
      d ∈ Finset.Ico 1 M := by
    intro v hv d hd
    rw [Nat.mem_divisors] at hd
    have hgpos : 0 < Nat.gcd v.1.natAbs v.2.natAbs := hv_ne_zero v hv
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hgpos
    have hmem' := (hmemV v).mp hv
    have hnorm_vz : ‖latPt (v.1 - z.1, v.2 - z.2)‖ < R := by
      have hsq : ‖latPt (v.1 - z.1, v.2 - z.2)‖ ^ 2 < R ^ 2 := by
        rw [norm_latPt_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
        exact_mod_cast hmem'
      nlinarith [norm_nonneg (latPt (v.1 - z.1, v.2 - z.2))]
    have hnorm_z : ‖latPt z‖ = R := by
      have hsq : ‖latPt z‖ ^ 2 = R ^ 2 := by
        rw [norm_latPt_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
      nlinarith [norm_nonneg (latPt z)]
    have hnorm_v : ‖latPt v‖ < 2 * R := by
      have heq : latPt v = latPt (v.1 - z.1, v.2 - z.2) + latPt z := by
        apply Complex.ext <;> simp [latPt]
      calc
        ‖latPt v‖ = ‖latPt (v.1 - z.1, v.2 - z.2) + latPt z‖ := by rw [heq]
        _ ≤ ‖latPt (v.1 - z.1, v.2 - z.2)‖ + ‖latPt z‖ := norm_add_le _ _
        _ < R + R := by linarith
        _ = 2 * R := by ring
    have hdle_gv : d ^ 2 ≤ gnorm v := by
      have hdv1 : d ∣ v.1.natAbs := dvd_trans hd.1 (Nat.gcd_dvd_left _ _)
      have hdv2 : d ∣ v.2.natAbs := dvd_trans hd.1 (Nat.gcd_dvd_right _ _)
      have hnot0 : v.1.natAbs ≠ 0 ∨ v.2.natAbs ≠ 0 := by
        by_contra h
        push Not at h
        rw [h.1, h.2] at hgpos
        simp at hgpos
      rcases hnot0 with h1 | h2
      · have hle : d ≤ v.1.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero h1) hdv1
        exact le_trans (Nat.pow_le_pow_left hle 2) (Nat.le_add_right _ _)
      · have hle : d ≤ v.2.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) hdv2
        exact le_trans (Nat.pow_le_pow_left hle 2) (Nat.le_add_left _ _)
    have hd_lt_2R : (d : ℝ) < 2 * R := by
      have hsq1 : (d : ℝ) ^ 2 ≤ ‖latPt v‖ ^ 2 := by
        rw [norm_latPt_sq]; exact_mod_cast hdle_gv
      have hsq2 : ‖latPt v‖ ^ 2 < (2 * R) ^ 2 := by
        nlinarith [norm_nonneg (latPt v)]
      nlinarith
    have hd_lt_M : d < M := by
      have h1 : (d : ℝ) < (M : ℝ) := lt_of_lt_of_le hd_lt_2R (Nat.le_ceil _)
      exact_mod_cast h1
    exact Finset.mem_Ico.mpr ⟨hdpos, hd_lt_M⟩
  -- Step 3: Expand indicator via Möbius and swap sums
  have hsum_V :
      (visibleCount z : ℤ) =
        ∑ v ∈ V, ∑ d ∈ Finset.Ico 1 M,
          if d ∣ Nat.gcd v.1.natAbs v.2.natAbs then (μ d : ℤ) else 0 := by
    rw [hbij_vis, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hgpos : 0 < Nat.gcd v.1.natAbs v.2.natAbs := hv_ne_zero v hv
    rw [← sum_divisors_moebius hgpos]
    symm
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, hgpos.ne'⟩
    · intro h
      exact ⟨hdvd_lt_M v hv d (Nat.mem_divisors.mpr h), h.1⟩
  rw [hsum_V, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Ico.mp hd).1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  -- Step 4: Bijection `u ↦ d • u` between `openDiskLattice (z/d) (R/d)` and `{v ∈ V | d ∣ gcd(v)}`
  unfold Lcount
  congr 1
  symm
  refine Finset.card_bij (fun u _ => ((d : ℤ) * u.1, (d : ℤ) * u.2)) ?_ ?_ ?_
  · intro u hu
    rw [mem_openDiskLattice_Lcount hdpos] at hu
    simp only [Finset.mem_filter, hmemV]
    refine ⟨hu, Nat.dvd_gcd ?_ ?_⟩
    · rw [Int.natAbs_mul, Int.natAbs_natCast]; exact dvd_mul_right d _
    · rw [Int.natAbs_mul, Int.natAbs_natCast]; exact dvd_mul_right d _
  · intro u₁ _ u₂ _ h
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.snd h
    dsimp at h1 h2
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
    exact Prod.ext (mul_left_cancel₀ hd0 h1) (mul_left_cancel₀ hd0 h2)
  · intro v hv
    simp only [Finset.mem_filter, hmemV] at hv
    have hd1 : (d : ℤ) ∣ v.1 := by
      have : d ∣ v.1.natAbs := dvd_trans hv.2 (Nat.gcd_dvd_left _ _)
      exact Int.natCast_dvd.mpr this
    have hd2 : (d : ℤ) ∣ v.2 := by
      have : d ∣ v.2.natAbs := dvd_trans hv.2 (Nat.gcd_dvd_right _ _)
      exact Int.natCast_dvd.mpr this
    rcases hd1 with ⟨u1, hu1⟩
    rcases hd2 with ⟨u2, hu2⟩
    refine ⟨(u1, u2), ?_, ?_⟩
    · rw [mem_openDiskLattice_Lcount hdpos, ← hu1, ← hu2]
      exact hv.1
    · exact Prod.ext hu1.symm hu2.symm

/-- **Proposition A (Uniform Moving-Viewpoint Visibility Bound):**
For every nonzero Gaussian integer `z` with norm `N = N(z) ≥ 1`,
`|a(z) - 6 N / π| ≤ π √N (2 + √2 + √2 log(2 √N))`. -/
theorem uniform_visibility_bound {z : ℤ × ℤ} (hz : 0 < gnorm z) :
    |(visibleCount z : ℝ) - 6 * (gnorm z : ℝ) / Real.pi| ≤
      Real.pi * Real.sqrt (gnorm z) *
        (2 + Real.sqrt 2 + Real.sqrt 2 * Real.log (2 * Real.sqrt (gnorm z))) := by
  set N : ℝ := (gnorm z : ℝ)
  set R : ℝ := Real.sqrt N
  set M : ℕ := Nat.ceil (2 * R)
  have hN_ge_one : (1 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast (by omega : 1 ≤ gnorm z)
  have hR_ge_one : (1 : ℝ) ≤ R := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hN_ge_one
  have hR_pos : 0 < R := by linarith
  have hR_sq : R ^ 2 = N := Real.sq_sqrt (by linarith)
  have hM_ge_2 : 2 ≤ M := by
    have : (2 : ℝ) ≤ 2 * R := by linarith
    exact Nat.le_ceil _ |> fun h => by
      have h2 : (2 : ℝ) ≤ (M : ℝ) := le_trans this h
      exact_mod_cast h2
  have hM_sub_lt : (M : ℝ) - 1 < 2 * R := by
    have hlt := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * R)
    linarith
  have hM_sub_ge : 2 * R - 1 ≤ (M : ℝ) - 1 := by
    have := Nat.le_ceil (2 * R)
    linarith
  have hvis_real :
      (visibleCount z : ℝ) =
        ∑ d ∈ Finset.Ico 1 M, (μ d : ℝ) * (Lcount z d : ℝ) := by
    have h := visibleCount_eq_moebius_sum hz
    have h' : ((visibleCount z : ℤ) : ℝ) =
        ((∑ d ∈ Finset.Ico 1 M, (μ d : ℤ) * (Lcount z d : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  -- Split `visibleCount z - 6 N / π` into the error sum plus the Möbius tail
  let mainSum : ℝ := ∑ d ∈ Finset.Ico 1 M, (μ d : ℝ) * (Real.pi * N / (d : ℝ) ^ 2)
  let errSum : ℝ := ∑ d ∈ Finset.Ico 1 M, (μ d : ℝ) * ((Lcount z d : ℝ) - Real.pi * N / (d : ℝ) ^ 2)
  have hdecomp : (visibleCount z : ℝ) - 6 * N / Real.pi =
      errSum + (mainSum - 6 * N / Real.pi) := by
    rw [hvis_real]
    have hadd : errSum + mainSum = ∑ d ∈ Finset.Ico 1 M, (μ d : ℝ) * (Lcount z d : ℝ) := by
      dsimp only [errSum, mainSum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    linarith
  -- Bound 1: tail `|mainSum - 6 N / π| ≤ π R`
  have hmain_eq : mainSum = Real.pi * N * ∑ d ∈ Finset.range M, (μ d : ℝ) / (d : ℝ) ^ 2 := by
    dsimp only [mainSum]
    have hrange : ∑ d ∈ Finset.range M, (μ d : ℝ) / (d : ℝ) ^ 2 =
        ∑ d ∈ Finset.Ico 1 M, (μ d : ℝ) / (d : ℝ) ^ 2 := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < M)]
      simp
    rw [hrange, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  have htail : |mainSum - 6 * N / Real.pi| ≤ Real.pi * R := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hfac : mainSum - 6 * N / Real.pi =
        Real.pi * N * ((∑ d ∈ Finset.range M, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2) := by
      rw [hmain_eq]
      field_simp
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi * N)]
    have htail1 := abs_sub_sum_moebius_div_sq_le hM_ge_2
    have hinv_le : 1 / ((M : ℝ) - 1) ≤ 1 / R := by
      refine one_div_le_one_div_of_le hR_pos ?_
      linarith
    calc
      Real.pi * N * |(∑ d ∈ Finset.range M, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2|
          ≤ Real.pi * N * (1 / R) :=
        mul_le_mul_of_nonneg_left (le_trans htail1 hinv_le) (by positivity)
      _ = Real.pi * R := by
        rw [← hR_sq]
        field_simp
  -- Bound 2: error sum `|errSum| ≤ π √2 R (1 + log(2R)) + π R`
  have herr : |errSum| ≤ Real.pi * Real.sqrt 2 * R * (1 + Real.log (2 * R)) + Real.pi * R := by
    have hterm_le : ∀ d ∈ Finset.Ico 1 M,
        |(μ d : ℝ) * ((Lcount z d : ℝ) - Real.pi * N / (d : ℝ) ^ 2)| ≤
          Real.pi * (Real.sqrt 2 * R / (d : ℝ) + 1 / 2) := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ico.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hdpos
      have hmu : |(μ d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hgauss := shifted_gauss_circle_open (latPt z / (d : ℂ)) (div_pos hR_pos hdR)
      have hr2 : Real.pi * (R / (d : ℝ)) ^ 2 = Real.pi * N / (d : ℝ) ^ 2 := by
        rw [div_pow, hR_sq]; ring
      rw [hr2] at hgauss
      have hmul : Real.sqrt 2 * (R / (d : ℝ)) = Real.sqrt 2 * R / (d : ℝ) := by ring
      rw [hmul] at hgauss
      rw [abs_mul]
      calc
        |(μ d : ℝ)| * |(Lcount z d : ℝ) - Real.pi * N / (d : ℝ) ^ 2|
            ≤ 1 * |(Lcount z d : ℝ) - Real.pi * N / (d : ℝ) ^ 2| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ = |(Lcount z d : ℝ) - Real.pi * N / (d : ℝ) ^ 2| := one_mul _
        _ ≤ Real.pi * (Real.sqrt 2 * R / (d : ℝ) + 1 / 2) := hgauss
    have hsum1 : |errSum| ≤ ∑ d ∈ Finset.Ico 1 M,
        Real.pi * (Real.sqrt 2 * R / (d : ℝ) + 1 / 2) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm_le)
    have hsum2 : ∑ d ∈ Finset.Ico 1 M, Real.pi * (Real.sqrt 2 * R / (d : ℝ) + 1 / 2) =
        Real.pi * Real.sqrt 2 * R * (∑ d ∈ Finset.Ico 1 M, (1 : ℝ) / (d : ℝ)) +
          Real.pi / 2 * ((M : ℝ) - 1) := by
      have hexp : ∀ d : ℕ, Real.pi * (Real.sqrt 2 * R / (d : ℝ) + 1 / 2) =
          Real.pi * Real.sqrt 2 * R * ((1 : ℝ) / (d : ℝ)) + Real.pi / 2 := by
        intro d; ring
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
        nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ M)]
      push_cast
      ring
    have hharm := sum_Ico_inv_le_one_add_log hM_ge_2
    have hlog_le : Real.log ((M : ℝ) - 1) ≤ Real.log (2 * R) :=
      Real.log_le_log (by linarith) (le_of_lt hM_sub_lt)
    have hharm2 : ∑ d ∈ Finset.Ico 1 M, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (2 * R) := by
      linarith
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hpart1 : Real.pi * Real.sqrt 2 * R * (∑ d ∈ Finset.Ico 1 M, (1 : ℝ) / (d : ℝ)) ≤
        Real.pi * Real.sqrt 2 * R * (1 + Real.log (2 * R)) :=
      mul_le_mul_of_nonneg_left hharm2 (by positivity)
    have hpart2 : Real.pi / 2 * ((M : ℝ) - 1) ≤ Real.pi * R := by
      nlinarith
    linarith
  -- Combine bounds
  rw [hdecomp]
  calc
    |errSum + (mainSum - 6 * N / Real.pi)|
        ≤ |errSum| + |mainSum - 6 * N / Real.pi| := abs_add_le _ _
    _ ≤ (Real.pi * Real.sqrt 2 * R * (1 + Real.log (2 * R)) + Real.pi * R) + Real.pi * R :=
      add_le_add herr htail
    _ = Real.pi * R * (2 + Real.sqrt 2 + Real.sqrt 2 * Real.log (2 * R)) := by ring

/-! ### Section 4: 8-fold dihedral symmetry and Proposition B (rank–norm bound) -/

/-- Exact 8-fold dihedral identity for a norm predicate `P : ℕ → Prop` on `ℤ² \ {0}`. -/
lemma dihedral_wedge_identity (M : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k, P k → k ≤ M) :
    let W := (intBox M).filter (fun z => InWedge z ∧ P (gnorm z))
    let All := (intBox M).filter (fun z => 0 < gnorm z ∧ P (gnorm z))
    let Axis := (Finset.Icc 1 M).filter (fun k => P (k ^ 2))
    let Diag := (Finset.Icc 1 M).filter (fun k => P (2 * k ^ 2))
    8 * W.card = All.card + 4 * Axis.card + 4 * Diag.card := by
  intro W All Axis Diag
  let Interior := W.filter (fun z => 0 < z.2 ∧ z.2 < z.1)
  let WAxis := W.filter (fun z => z.2 = 0)
  let WDiag := W.filter (fun z => z.2 = z.1)
  -- Partition `W = Interior ⊔ WAxis ⊔ WDiag`
  have hW_card : W.card = Interior.card + Axis.card + Diag.card := by
    have hWAxis_card : WAxis.card = Axis.card := by
      refine Finset.card_bij (fun z _ => z.1.natAbs) ?_ ?_ ?_
      · intro z hz
        simp only [WAxis, W, Finset.mem_filter] at hz
        have h1pos : 0 < z.1 := by
          rcases hz.1.2.1 with ⟨hb, hba, hgn⟩
          have hz2 : z.2 = 0 := hz.2
          unfold gnorm at hgn
          rw [hz2] at hgn
          have hne : z.1.natAbs ≠ 0 := by
            intro h0; rw [h0] at hgn; simp at hgn
          omega
        have hgn : gnorm z = z.1.natAbs ^ 2 := by unfold gnorm; simp [hz.2]
        have hle : z.1.natAbs ≤ M := by
          have hsq : z.1.natAbs ^ 2 ≤ M := hgn ▸ hP _ hz.1.2.2
          exact le_trans (Nat.le_self_pow (by norm_num) _) hsq
        simp only [Axis, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hle⟩, hgn ▸ hz.1.2.2⟩
      · intro z₁ hz₁ z₂ hz₂ heq
        simp only [WAxis, W, Finset.mem_filter] at hz₁ hz₂
        have h1 : 0 ≤ z₁.1 := le_trans hz₁.1.2.1.1 hz₁.1.2.1.2.1
        have h2 : 0 ≤ z₂.1 := le_trans hz₂.1.2.1.1 hz₂.1.2.1.2.1
        exact Prod.ext (by omega) (hz₁.2.trans hz₂.2.symm)
      · intro k hk
        simp only [Axis, Finset.mem_filter, Finset.mem_Icc] at hk
        refine ⟨((k : ℤ), 0), ?_, by simp⟩
        have hgn : gnorm ((k : ℤ), 0) = k ^ 2 := by unfold gnorm; simp
        simp only [WAxis, W, Finset.mem_filter]
        refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hk.2), ?_, hgn ▸ hk.2⟩, trivial⟩
        exact ⟨le_refl 0, by omega, by rw [hgn]; exact Nat.pow_pos hk.1.1⟩
    have hWDiag_card : WDiag.card = Diag.card := by
      refine Finset.card_bij (fun z _ => z.1.natAbs) ?_ ?_ ?_
      · intro z hz
        simp only [WDiag, W, Finset.mem_filter] at hz
        have hgn : gnorm z = 2 * z.1.natAbs ^ 2 := by
          unfold gnorm; rw [hz.2]; ring
        have h1pos : 0 < z.1 := by
          rcases hz.1.2.1 with ⟨hb, hba, hgn0⟩
          rw [hgn] at hgn0
          have hne : z.1.natAbs ≠ 0 := by
            intro h0; rw [h0] at hgn0; simp at hgn0
          omega
        have hle : z.1.natAbs ≤ M := by
          have hsq : z.1.natAbs ^ 2 ≤ M := le_trans (by omega : z.1.natAbs ^ 2 ≤ 2 * z.1.natAbs ^ 2)
            (hgn ▸ hP _ hz.1.2.2)
          exact le_trans (Nat.le_self_pow (by norm_num) _) hsq
        simp only [Diag, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hle⟩, hgn ▸ hz.1.2.2⟩
      · intro z₁ hz₁ z₂ hz₂ heq
        simp only [WDiag, W, Finset.mem_filter] at hz₁ hz₂
        have h1 : 0 ≤ z₁.1 := le_trans hz₁.1.2.1.1 hz₁.1.2.1.2.1
        have h2 : 0 ≤ z₂.1 := le_trans hz₂.1.2.1.1 hz₂.1.2.1.2.1
        have hx : z₁.1 = z₂.1 := by omega
        exact Prod.ext hx (hz₁.2.trans (hx.trans hz₂.2.symm))
      · intro k hk
        simp only [Diag, Finset.mem_filter, Finset.mem_Icc] at hk
        refine ⟨((k : ℤ), (k : ℤ)), ?_, by simp⟩
        have hgn : gnorm ((k : ℤ), (k : ℤ)) = 2 * k ^ 2 := by unfold gnorm; simp; ring
        simp only [WDiag, W, Finset.mem_filter]
        refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hk.2), ?_, hgn ▸ hk.2⟩, trivial⟩
        exact ⟨by omega, le_refl _, by rw [hgn]; exact Nat.mul_pos (by norm_num) (Nat.pow_pos hk.1.1)⟩
    have hunion : W = Interior ∪ (WAxis ∪ WDiag) := by
      ext z
      simp only [Finset.mem_union, Interior, WAxis, WDiag, Finset.mem_filter]
      constructor
      · intro hz
        have hzW := (Finset.mem_filter.mp hz).2.1
        have h0 : 0 ≤ z.2 := hzW.1
        have h1 : z.2 ≤ z.1 := hzW.2.1
        by_cases hb0 : z.2 = 0
        · exact Or.inr (Or.inl ⟨hz, hb0⟩)
        · by_cases hba : z.2 = z.1
          · exact Or.inr (Or.inr ⟨hz, hba⟩)
          · exact Or.inl ⟨hz, ⟨by omega, by omega⟩⟩
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    have hd1 : Disjoint WAxis WDiag := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [WAxis, WDiag, W, Finset.mem_filter] at hz1 hz2
      have hgn : gnorm z = 0 := by unfold gnorm; rw [hz1.2] at hz2; rw [hz1.2, ← hz2.2]; simp
      have := hz1.1.2.1.2.2
      omega
    have hd2 : Disjoint Interior (WAxis ∪ WDiag) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_union, Interior, WAxis, WDiag, Finset.mem_filter] at hz1 hz2
      rcases hz2 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      hWAxis_card, hWDiag_card]
    omega
  -- Partition `All` into `AllInt` (size `8 * Interior.card`), `AllAxis` (size `4 * Axis.card`),
  -- and `AllDiag` (size `4 * Diag.card`)
  let AllAxis := All.filter (fun z => z.1 = 0 ∨ z.2 = 0)
  let AllDiag := All.filter (fun z => z.1.natAbs = z.2.natAbs)
  let AllInt := All.filter (fun z => z.1 ≠ 0 ∧ z.2 ≠ 0 ∧ z.1.natAbs ≠ z.2.natAbs)
  have hAll_card : All.card = AllInt.card + AllAxis.card + AllDiag.card := by
    have hunion : All = AllInt ∪ (AllAxis ∪ AllDiag) := by
      ext z
      simp only [Finset.mem_union, AllInt, AllAxis, AllDiag, Finset.mem_filter]
      constructor
      · intro hz
        by_cases hax : z.1 = 0 ∨ z.2 = 0
        · exact Or.inr (Or.inl ⟨hz, hax⟩)
        · push Not at hax
          by_cases hdg : z.1.natAbs = z.2.natAbs
          · exact Or.inr (Or.inr ⟨hz, hdg⟩)
          · exact Or.inl ⟨hz, hax.1, hax.2, hdg⟩
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    have hd1 : Disjoint AllAxis AllDiag := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [AllAxis, AllDiag, All, Finset.mem_filter] at hz1 hz2
      have hgn0 := hz1.1.2.1
      unfold gnorm at hgn0
      rcases hz1.2 with h1 | h2
      · rw [h1] at hz2 hgn0; simp at hz2; rw [← hz2.2] at hgn0; simp at hgn0
      · rw [h2] at hz2 hgn0; simp at hz2; rw [hz2.2] at hgn0; simp at hgn0
    have hd2 : Disjoint AllInt (AllAxis ∪ AllDiag) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_union, AllInt, AllAxis, AllDiag, Finset.mem_filter] at hz1 hz2
      rcases hz2 with ⟨_, h1 | h2⟩ | ⟨_, h3⟩
      · exact hz1.2.1 h1
      · exact hz1.2.2.1 h2
      · exact hz1.2.2.2 h3
    rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
    omega
  -- Bijection `(Fin 4 × Axis) ≃ AllAxis`
  have hAllAxis_card : AllAxis.card = 4 * Axis.card := by
    have h4 : 4 * Axis.card = ((Finset.univ : Finset (Fin 4)) ×ˢ Axis).card := by
      simp [Finset.card_product]
    rw [h4]
    symm
    let φ : Fin 4 × ℕ → ℤ × ℤ := fun ⟨i, k⟩ =>
      match i with
      | ⟨0, _⟩ => ((k : ℤ), 0)
      | ⟨1, _⟩ => (-(k : ℤ), 0)
      | ⟨2, _⟩ => (0, (k : ℤ))
      | ⟨3, _⟩ => (0, -(k : ℤ))
    refine Finset.card_bij (fun p _ => φ p) ?_ ?_ ?_
    · rintro ⟨i, k⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Axis,
        Finset.mem_filter, Finset.mem_Icc] at hp
      have hgn : gnorm (φ (i, k)) = k ^ 2 := by
        fin_cases i <;> unfold φ gnorm <;> simp
      simp only [AllAxis, All, Finset.mem_filter]
      refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hp.2),
        by rw [hgn]; exact Nat.pow_pos hp.1.1, hgn ▸ hp.2⟩, ?_⟩
      fin_cases i <;> simp [φ]
    · rintro ⟨i₁, k₁⟩ hp₁ ⟨i₂, k₂⟩ hp₂ heq
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Axis,
        Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      have h1 := congr_arg Prod.fst heq
      have h2 := congr_arg Prod.snd heq
      fin_cases i₁ <;> fin_cases i₂ <;> simp only [φ] at h1 h2
      all_goals first | omega | (exact Prod.ext rfl (by omega))
    · intro z hz
      simp only [AllAxis, All, Finset.mem_filter] at hz
      have hgn0 := hz.1.2.1
      rcases hz.2 with hx0 | hy0
      · have hgn : gnorm z = z.2.natAbs ^ 2 := by unfold gnorm; simp [hx0]
        have hypos : 0 < z.2.natAbs := by
          by_contra h0; have : z.2.natAbs = 0 := by omega
          rw [hgn, this] at hgn0; simp at hgn0
        have hle : z.2.natAbs ≤ M :=
          le_trans (Nat.le_self_pow (by norm_num) _) (hgn ▸ hP _ hz.1.2.2)
        have hmem : z.2.natAbs ∈ Axis := by
          simp only [Axis, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hypos, hle⟩, hgn ▸ hz.1.2.2⟩
        by_cases hpos : 0 ≤ z.2
        · refine ⟨(⟨2, by omega⟩, z.2.natAbs), Finset.mem_product.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩
          exact Prod.ext hx0.symm (by dsimp [φ]; omega)
        · refine ⟨(⟨3, by omega⟩, z.2.natAbs), Finset.mem_product.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩
          exact Prod.ext hx0.symm (by dsimp [φ]; omega)
      · have hgn : gnorm z = z.1.natAbs ^ 2 := by unfold gnorm; simp [hy0]
        have hxpos : 0 < z.1.natAbs := by
          by_contra h0; have : z.1.natAbs = 0 := by omega
          rw [hgn, this] at hgn0; simp at hgn0
        have hle : z.1.natAbs ≤ M :=
          le_trans (Nat.le_self_pow (by norm_num) _) (hgn ▸ hP _ hz.1.2.2)
        have hmem : z.1.natAbs ∈ Axis := by
          simp only [Axis, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hxpos, hle⟩, hgn ▸ hz.1.2.2⟩
        by_cases hpos : 0 ≤ z.1
        · refine ⟨(⟨0, by omega⟩, z.1.natAbs), Finset.mem_product.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩
          exact Prod.ext (by dsimp [φ]; omega) hy0.symm
        · refine ⟨(⟨1, by omega⟩, z.1.natAbs), Finset.mem_product.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩
          exact Prod.ext (by dsimp [φ]; omega) hy0.symm
  -- Bijection `(Bool × Bool × Diag) ≃ AllDiag`
  have hAllDiag_card : AllDiag.card = 4 * Diag.card := by
    have h4 : 4 * Diag.card =
        (((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)) ×ˢ Diag).card := by
      simp [Finset.card_product]
    rw [h4]
    symm
    let sgn : Bool → ℤ → ℤ := fun b x => if b then x else -x
    let ψ : (Bool × Bool) × ℕ → ℤ × ℤ := fun ⟨⟨bx, by_⟩, k⟩ => (sgn bx k, sgn by_ k)
    refine Finset.card_bij (fun p _ => ψ p) ?_ ?_ ?_
    · rintro ⟨⟨bx, by_⟩, k⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Diag,
        Finset.mem_filter, Finset.mem_Icc] at hp
      have hgn : gnorm (ψ ((bx, by_), k)) = 2 * k ^ 2 := by
        cases bx <;> cases by_ <;> unfold ψ sgn gnorm <;> simp <;> ring
      simp only [AllDiag, All, Finset.mem_filter]
      refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hp.2),
        by rw [hgn]; exact Nat.mul_pos (by norm_num) (Nat.pow_pos hp.1.1), hgn ▸ hp.2⟩, ?_⟩
      cases bx <;> cases by_ <;> simp [ψ, sgn]
    · rintro ⟨⟨bx₁, by₁⟩, k₁⟩ hp₁ ⟨⟨bx₂, by₂⟩, k₂⟩ hp₂ heq
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Diag,
        Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      have h1 : sgn bx₁ k₁ = sgn bx₂ k₂ := congr_arg Prod.fst heq
      have h2 : sgn by₁ k₁ = sgn by₂ k₂ := congr_arg Prod.snd heq
      have hk : k₁ = k₂ := by
        have hab := congr_arg Int.natAbs h1
        cases bx₁ <;> cases bx₂ <;> simp [sgn] at hab <;> exact hab
      have hbx : bx₁ = bx₂ := by
        cases bx₁ <;> cases bx₂ <;> simp [sgn] at h1 <;> first | rfl | omega
      have hby : by₁ = by₂ := by
        cases by₁ <;> cases by₂ <;> simp [sgn] at h2 <;> first | rfl | omega
      exact Prod.ext (Prod.ext hbx hby) hk
    · intro z hz
      simp only [AllDiag, All, Finset.mem_filter] at hz
      have hgn : gnorm z = 2 * z.1.natAbs ^ 2 := by
        unfold gnorm; rw [← hz.2]; ring
      have hpos : 0 < z.1.natAbs := by
        have hgn0 := hz.1.2.1
        by_contra h0; have : z.1.natAbs = 0 := by omega
        rw [hgn, this] at hgn0; simp at hgn0
      have hle : z.1.natAbs ≤ M := by
        have hsq : z.1.natAbs ^ 2 ≤ M := le_trans (by omega : z.1.natAbs ^ 2 ≤ 2 * z.1.natAbs ^ 2)
          (hgn ▸ hP _ hz.1.2.2)
        exact le_trans (Nat.le_self_pow (by norm_num) _) hsq
      have hmem : z.1.natAbs ∈ Diag := by
        simp only [Diag, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hpos, hle⟩, hgn ▸ hz.1.2.2⟩
      refine ⟨((decide (0 ≤ z.1), decide (0 ≤ z.2)), z.1.natAbs),
        Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hmem⟩, ?_⟩
      have hax : (z.1.natAbs : ℤ) = (z.2.natAbs : ℤ) := by exact_mod_cast hz.2
      have h1 : (z.1.natAbs : ℤ) = if 0 ≤ z.1 then z.1 else -z.1 := by split_ifs <;> omega
      have h2 : (z.2.natAbs : ℤ) = if 0 ≤ z.2 then z.2 else -z.2 := by split_ifs <;> omega
      dsimp [ψ, sgn]
      by_cases hx : 0 ≤ z.1 <;> by_cases hy : 0 ≤ z.2
      · simp only [hx, hy, ↓reduceIte, decide_true] at h1 h2 ⊢; exact Prod.ext h1 (hax.trans h2)
      · simp only [hx, hy, ↓reduceIte, decide_true, decide_false, Bool.false_eq_true] at h1 h2 ⊢
        exact Prod.ext h1 (by omega)
      · simp only [hx, hy, ↓reduceIte, decide_true, decide_false, Bool.false_eq_true] at h1 h2 ⊢
        exact Prod.ext (by omega) (hax.trans h2)
      · simp only [hx, hy, ↓reduceIte, decide_false, Bool.false_eq_true] at h1 h2 ⊢
        exact Prod.ext (by omega) (by omega)
  -- Bijection `(Bool × Bool × Bool × Interior) ≃ AllInt`
  have hAllInt_card : AllInt.card = 8 * Interior.card := by
    have h8 : 8 * Interior.card =
        ((((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)) ×ˢ
          (Finset.univ : Finset Bool)) ×ˢ Interior).card := by
      simp [Finset.card_product]
    rw [h8]
    symm
    let sgn : Bool → ℤ → ℤ := fun b x => if b then x else -x
    let ρ : ((Bool × Bool) × Bool) × (ℤ × ℤ) → ℤ × ℤ := fun ⟨⟨⟨bx, by_⟩, sw⟩, z⟩ =>
      if sw then (sgn bx z.1, sgn by_ z.2) else (sgn bx z.2, sgn by_ z.1)
    have hsgn_abs : ∀ b x, (sgn b x).natAbs = x.natAbs := by
      intro b x; cases b <;> simp [sgn]
    have hsgn_pos : ∀ b {x : ℤ}, 0 < x → (0 < sgn b x ↔ b = true) := by
      intro b x hx; cases b <;> simp [sgn] <;> omega
    refine Finset.card_bij (fun p _ => ρ p) ?_ ?_ ?_
    · rintro ⟨⟨⟨bx, by_⟩, sw⟩, z⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Interior, W,
        Finset.mem_filter] at hp
      have hgn : gnorm (ρ (((bx, by_), sw), z)) = gnorm z := by
        cases bx <;> cases by_ <;> cases sw <;> unfold ρ sgn gnorm <;> simp [add_comm]
      have hpos2 : 0 < z.2 := hp.2.1
      have hlt : z.2 < z.1 := hp.2.2
      simp only [AllInt, All, Finset.mem_filter]
      refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hp.1.2.2), hgn ▸ hp.1.2.1.2.2, hgn ▸ hp.1.2.2⟩, ?_⟩
      cases bx <;> cases by_ <;> cases sw <;> simp [ρ, sgn] <;> omega
    · rintro ⟨⟨⟨bx₁, by₁⟩, sw₁⟩, z₁⟩ hp₁ ⟨⟨⟨bx₂, by₂⟩, sw₂⟩, z₂⟩ hp₂ heq
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Interior, W,
        Finset.mem_filter] at hp₁ hp₂
      have h1a : 0 < z₁.2 := hp₁.2.1
      have h1b : z₁.2 < z₁.1 := hp₁.2.2
      have h2a : 0 < z₂.2 := hp₂.2.1
      have h2b : z₂.2 < z₂.1 := hp₂.2.2
      have hfst := congr_arg Prod.fst heq
      have hsnd := congr_arg Prod.snd heq
      have habs1 := congr_arg Int.natAbs hfst
      have habs2 := congr_arg Int.natAbs hsnd
      have hsw : sw₁ = sw₂ := by
        cases sw₁ <;> cases sw₂
        · rfl
        · simp [ρ, hsgn_abs] at habs1 habs2; omega
        · simp [ρ, hsgn_abs] at habs1 habs2; omega
        · rfl
      subst hsw
      cases sw₁
      · simp only [ρ, Bool.false_eq_true, ↓reduceIte] at hfst hsnd habs1 habs2
        rw [hsgn_abs, hsgn_abs] at habs1 habs2
        have hz : z₁ = z₂ := Prod.ext (by omega) (by omega)
        have hbx : bx₁ = bx₂ := by
          cases bx₁ <;> cases bx₂ <;> simp [sgn] at hfst <;> first | rfl | omega
        have hby : by₁ = by₂ := by
          cases by₁ <;> cases by₂ <;> simp [sgn] at hsnd <;> first | rfl | omega
        exact Prod.ext (Prod.ext (Prod.ext hbx hby) rfl) hz
      · simp only [ρ, ↓reduceIte] at hfst hsnd habs1 habs2
        rw [hsgn_abs, hsgn_abs] at habs1 habs2
        have hz : z₁ = z₂ := Prod.ext (by omega) (by omega)
        have hbx : bx₁ = bx₂ := by
          cases bx₁ <;> cases bx₂ <;> simp [sgn] at hfst <;> first | rfl | omega
        have hby : by₁ = by₂ := by
          cases by₁ <;> cases by₂ <;> simp [sgn] at hsnd <;> first | rfl | omega
        exact Prod.ext (Prod.ext (Prod.ext hbx hby) rfl) hz
    · intro z hz
      simp only [AllInt, All, Finset.mem_filter] at hz
      have hx0 : z.1 ≠ 0 := hz.2.1
      have hy0 : z.2 ≠ 0 := hz.2.2.1
      have hne : z.1.natAbs ≠ z.2.natAbs := hz.2.2.2
      have h1 : (z.1.natAbs : ℤ) = if 0 ≤ z.1 then z.1 else -z.1 := by split_ifs <;> omega
      have h2 : (z.2.natAbs : ℤ) = if 0 ≤ z.2 then z.2 else -z.2 := by split_ifs <;> omega
      by_cases hgt : z.2.natAbs < z.1.natAbs
      · let w : ℤ × ℤ := ((z.1.natAbs : ℤ), (z.2.natAbs : ℤ))
        have hgn : gnorm w = gnorm z := by
          unfold w gnorm; simp only [Int.natAbs_natCast]
        have hw : w ∈ Interior := by
          simp only [Interior, W, Finset.mem_filter]
          refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hz.1.2.2),
            ⟨by dsimp [w]; omega, by dsimp [w]; omega, hgn ▸ hz.1.2.1⟩,
            hgn ▸ hz.1.2.2⟩, ⟨by dsimp [w]; omega, by dsimp [w]; omega⟩⟩
        refine ⟨(((decide (0 ≤ z.1), decide (0 ≤ z.2)), true), w),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, Finset.mem_univ _⟩, hw⟩, ?_⟩
        dsimp [ρ, sgn, w]
        by_cases hx : 0 ≤ z.1 <;> by_cases hy : 0 ≤ z.2
        · simp only [hx, hy, ↓reduceIte, decide_true] at h1 h2 ⊢; exact Prod.ext h1 h2
        · simp only [hx, hy, ↓reduceIte, decide_true, decide_false, Bool.false_eq_true] at h1 h2 ⊢
          exact Prod.ext h1 (by omega)
        · simp only [hx, hy, ↓reduceIte, decide_true, decide_false, Bool.false_eq_true] at h1 h2 ⊢
          exact Prod.ext (by omega) h2
        · simp only [hx, hy, ↓reduceIte, decide_false, Bool.false_eq_true] at h1 h2 ⊢
          exact Prod.ext (by omega) (by omega)
      · have hlt : z.1.natAbs < z.2.natAbs := by omega
        let w : ℤ × ℤ := ((z.2.natAbs : ℤ), (z.1.natAbs : ℤ))
        have hgn : gnorm w = gnorm z := by
          unfold w gnorm; simp only [Int.natAbs_natCast]; exact add_comm _ _
        have hw : w ∈ Interior := by
          simp only [Interior, W, Finset.mem_filter]
          refine ⟨⟨mem_intBox_of_gnorm_le (hgn ▸ hP _ hz.1.2.2),
            ⟨by dsimp [w]; omega, by dsimp [w]; omega, hgn ▸ hz.1.2.1⟩,
            hgn ▸ hz.1.2.2⟩, ⟨by dsimp [w]; omega, by dsimp [w]; omega⟩⟩
        refine ⟨(((decide (0 ≤ z.1), decide (0 ≤ z.2)), false), w),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, Finset.mem_univ _⟩, hw⟩, ?_⟩
        dsimp [ρ, sgn, w]
        by_cases hx : 0 ≤ z.1 <;> by_cases hy : 0 ≤ z.2
        · simp only [hx, hy, ↓reduceIte, decide_true] at h1 h2 ⊢; exact Prod.ext h1 h2
        · simp only [hx, hy, ↓reduceIte, decide_true, decide_false, Bool.false_eq_true] at h1 h2 ⊢
          exact Prod.ext h1 (by omega)
        · simp only [hx, hy, ↓reduceIte, decide_true, decide_false, Bool.false_eq_true] at h1 h2 ⊢
          exact Prod.ext (by omega) h2
        · simp only [hx, hy, ↓reduceIte, decide_false, Bool.false_eq_true] at h1 h2 ⊢
          exact Prod.ext (by omega) (by omega)
  omega

/-- Upper bound `4 * #{1 ≤ k | k² ≤ M} + 4 * #{1 ≤ k | 2 k² ≤ M} ≤ 7 √M`. -/
lemma axis_diag_bound (M : ℕ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ k, P k → k ≤ M) :
    let Axis := (Finset.Icc 1 M).filter (fun k => P (k ^ 2))
    let Diag := (Finset.Icc 1 M).filter (fun k => P (2 * k ^ 2))
    4 * (Axis.card : ℝ) + 4 * (Diag.card : ℝ) ≤ 7 * Real.sqrt (M : ℝ) := by
  intro Axis Diag
  have hAxis : (Axis.card : ℝ) ≤ Real.sqrt (M : ℝ) := by
    have hsub : Axis ⊆ Finset.Icc 1 (Nat.floor (Real.sqrt (M : ℝ))) := by
      intro k hk
      simp only [Axis, Finset.mem_filter, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]
      refine ⟨hk.1.1, Nat.le_floor ?_⟩
      have hsq : (k : ℝ) ^ 2 ≤ (M : ℝ) := by exact_mod_cast hP _ hk.2
      exact Real.le_sqrt_of_sq_le hsq
    calc
      (Axis.card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor (Real.sqrt (M : ℝ)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor (Real.sqrt (M : ℝ)) : ℝ) := by simp
      _ ≤ Real.sqrt (M : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hDiag : (Diag.card : ℝ) ≤ Real.sqrt ((M : ℝ) / 2) := by
    have hsub : Diag ⊆ Finset.Icc 1 (Nat.floor (Real.sqrt ((M : ℝ) / 2))) := by
      intro k hk
      simp only [Diag, Finset.mem_filter, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]
      refine ⟨hk.1.1, Nat.le_floor ?_⟩
      have hsq : 2 * (k : ℝ) ^ 2 ≤ (M : ℝ) := by exact_mod_cast hP _ hk.2
      exact Real.le_sqrt_of_sq_le (by linarith)
    calc
      (Diag.card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor (Real.sqrt ((M : ℝ) / 2)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor (Real.sqrt ((M : ℝ) / 2)) : ℝ) := by simp
      _ ≤ Real.sqrt ((M : ℝ) / 2) := Nat.floor_le (Real.sqrt_nonneg _)
  have h4sq : 4 * Real.sqrt ((M : ℝ) / 2) ≤ 3 * Real.sqrt (M : ℝ) := by
    have h1 : (4 * Real.sqrt ((M : ℝ) / 2)) ^ 2 = 8 * (M : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have h2 : (3 * Real.sqrt (M : ℝ)) ^ 2 = 9 * (M : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
    have hpos1 : 0 ≤ 4 * Real.sqrt ((M : ℝ) / 2) := by positivity
    have hpos2 : 0 ≤ 3 * Real.sqrt (M : ℝ) := by positivity
    nlinarith
  linarith

/-- **Proposition B (Rank–Norm Bound Accounting for Norm Ties):**
For every `n ≥ 1`, letting `N = N(z_n)`, we have `|n - π N / 8| ≤ 2 √N`. -/
theorem rank_norm_bound {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ) - Real.pi * (gnorm (a401897_z n) : ℝ) / 8| ≤
      2 * Real.sqrt (gnorm (a401897_z n) : ℝ) := by
  set z := a401897_z n
  set N := gnorm z
  have hz : InWedge z := a401897_z_inWedge hn
  have hN_pos : 0 < N := hz.2.2
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
  have hR_ge_one : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hN_ge_one
  have hR_pos : 0 < Real.sqrt (N : ℝ) := by linarith
  have hR_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (by linarith)
  have hsand := rank_sandwich hn
  -- Relate `All_le` to `closedDiskLattice 0 √N` and `All_lt` to `openDiskLattice 0 √N`
  have hAll_le_card :
      ((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w ≤ N)).card + 1 =
        (closedDiskLattice 0 (Real.sqrt (N : ℝ))).card := by
    have hset : insert ((0 : ℤ), (0 : ℤ))
        ((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w ≤ N)) =
        closedDiskLattice 0 (Real.sqrt (N : ℝ)) := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_filter, mem_closedDiskLattice]
      rw [dist_zero_right]
      have hle_iff : ‖latPt w‖ ≤ Real.sqrt (N : ℝ) ↔ gnorm w ≤ N := by
        constructor
        · intro h
          have hsq : ‖latPt w‖ ^ 2 ≤ (Real.sqrt (N : ℝ)) ^ 2 := by nlinarith [norm_nonneg (latPt w)]
          rw [norm_latPt_sq, hR_sq] at hsq
          exact_mod_cast hsq
        · intro h
          have hsq : ‖latPt w‖ ^ 2 ≤ (Real.sqrt (N : ℝ)) ^ 2 := by
            rw [norm_latPt_sq, hR_sq]; exact_mod_cast h
          nlinarith [norm_nonneg (latPt w)]
      rw [hle_iff]
      constructor
      · rintro (rfl | ⟨_, _, hle⟩)
        · unfold gnorm; simp
        · exact hle
      · intro hle
        by_cases h0 : w = (0, 0)
        · exact Or.inl h0
        · right
          refine ⟨mem_intBox_of_gnorm_le hle, ?_, hle⟩
          unfold gnorm
          by_contra hc
          have h1 : w.1.natAbs ^ 2 = 0 := by omega
          have h2 : w.2.natAbs ^ 2 = 0 := by omega
          have hw1 : w.1 = 0 := Int.natAbs_eq_zero.mp (sq_eq_zero_iff.mp h1)
          have hw2 : w.2 = 0 := Int.natAbs_eq_zero.mp (sq_eq_zero_iff.mp h2)
          exact h0 (Prod.ext hw1 hw2)
    have hnot : ((0 : ℤ), (0 : ℤ)) ∉ (intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w ≤ N) := by
      simp [gnorm]
    rw [← hset, Finset.card_insert_of_notMem hnot]
  have hAll_lt_card :
      ((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w < N)).card + 1 =
        (openDiskLattice 0 (Real.sqrt (N : ℝ))).card := by
    have hset : insert ((0 : ℤ), (0 : ℤ))
        ((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w < N)) =
        openDiskLattice 0 (Real.sqrt (N : ℝ)) := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_filter, mem_openDiskLattice]
      rw [dist_zero_right]
      have hlt_iff : ‖latPt w‖ < Real.sqrt (N : ℝ) ↔ gnorm w < N := by
        constructor
        · intro h
          have hsq : ‖latPt w‖ ^ 2 < (Real.sqrt (N : ℝ)) ^ 2 := by nlinarith [norm_nonneg (latPt w)]
          rw [norm_latPt_sq, hR_sq] at hsq
          exact_mod_cast hsq
        · intro h
          have hsq : ‖latPt w‖ ^ 2 < (Real.sqrt (N : ℝ)) ^ 2 := by
            rw [norm_latPt_sq, hR_sq]; exact_mod_cast h
          nlinarith [norm_nonneg (latPt w)]
      rw [hlt_iff]
      constructor
      · rintro (rfl | ⟨_, _, hlt⟩)
        · unfold gnorm; simpa using hN_pos
        · exact hlt
      · intro hlt
        by_cases h0 : w = (0, 0)
        · exact Or.inl h0
        · right
          refine ⟨mem_intBox_of_gnorm_le (le_of_lt hlt), ?_, hlt⟩
          unfold gnorm
          by_contra hc
          have h1 : w.1.natAbs ^ 2 = 0 := by omega
          have h2 : w.2.natAbs ^ 2 = 0 := by omega
          have hw1 : w.1 = 0 := Int.natAbs_eq_zero.mp (sq_eq_zero_iff.mp h1)
          have hw2 : w.2 = 0 := Int.natAbs_eq_zero.mp (sq_eq_zero_iff.mp h2)
          exact h0 (Prod.ext hw1 hw2)
    have hnot : ((0 : ℤ), (0 : ℤ)) ∉ (intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w < N) := by
      simp [gnorm]
    rw [← hset, Finset.card_insert_of_notMem hnot]
  -- Apply dihedral identity + shifted Gauss circle bounds
  have hdih_le := dihedral_wedge_identity N (fun k => k ≤ N) (fun _ h => h)
  have hdih_lt := dihedral_wedge_identity N (fun k => k < N) (fun _ h => le_of_lt h)
  have hax_le := axis_diag_bound N (fun k => k ≤ N) (fun _ h => h)
  have hgauss_closed := shifted_gauss_circle_closed 0 hR_pos
  have hgauss_open := shifted_gauss_circle_open 0 hR_pos
  rw [hR_sq] at hgauss_closed hgauss_open
  -- Numeric constants: `π < 4` and `√2 < 1.42`
  have hpi_lt : Real.pi < 4 := Real.pi_lt_four
  have hsqrt2_lt : Real.sqrt 2 < 1.42 := by
    have : Real.sqrt 2 ^ 2 < (1.42 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpisq_lt : Real.pi * Real.sqrt 2 < 4 * 1.42 :=
    mul_lt_mul' hpi_lt.le hsqrt2_lt hsqrt2_pos.le (by norm_num)
  have hgauss_err : Real.pi * (Real.sqrt 2 * Real.sqrt (N : ℝ) + 1 / 2) ≤ 8 * Real.sqrt (N : ℝ) := by
    nlinarith [hR_ge_one, hpisq_lt, hpi_lt]
  -- Upper bound `n ≤ π N / 8 + 2 √N`
  have hupper : (n : ℝ) ≤ Real.pi * (N : ℝ) / 8 + 2 * Real.sqrt (N : ℝ) := by
    have hn_le : (n : ℝ) ≤ ((wedgeLe N).card : ℝ) := by exact_mod_cast hsand.2
    have hdih_r : 8 * ((wedgeLe N).card : ℝ) =
        (((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w ≤ N)).card : ℝ) +
          4 * (((Finset.Icc 1 N).filter (fun k => k ^ 2 ≤ N)).card : ℝ) +
          4 * (((Finset.Icc 1 N).filter (fun k => 2 * k ^ 2 ≤ N)).card : ℝ) := by
      exact_mod_cast hdih_le
    have hall_r : (((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w ≤ N)).card : ℝ) + 1 =
        ((closedDiskLattice 0 (Real.sqrt (N : ℝ))).card : ℝ) := by
      exact_mod_cast hAll_le_card
    have hcl_up := (abs_le.mp hgauss_closed).2
    linarith
  -- Lower bound `π N / 8 - 2 √N ≤ n`
  have hlower : Real.pi * (N : ℝ) / 8 - 2 * Real.sqrt (N : ℝ) ≤ (n : ℝ) := by
    have hn_ge : ((wedgeLtSet N).card : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hsand.1
    have hdih_r : 8 * ((wedgeLtSet N).card : ℝ) =
        (((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w < N)).card : ℝ) +
          4 * (((Finset.Icc 1 N).filter (fun k => k ^ 2 < N)).card : ℝ) +
          4 * (((Finset.Icc 1 N).filter (fun k => 2 * k ^ 2 < N)).card : ℝ) := by
      exact_mod_cast hdih_lt
    have hall_r : (((intBox N).filter (fun w => 0 < gnorm w ∧ gnorm w < N)).card : ℝ) + 1 =
        ((openDiskLattice 0 (Real.sqrt (N : ℝ))).card : ℝ) := by
      exact_mod_cast hAll_lt_card
    have hop_lo := (abs_le.mp hgauss_open).1
    have hnonneg1 : (0 : ℝ) ≤ (((Finset.Icc 1 N).filter (fun k => k ^ 2 < N)).card : ℝ) :=
      Nat.cast_nonneg _
    have hnonneg2 : (0 : ℝ) ≤ (((Finset.Icc 1 N).filter (fun k => 2 * k ^ 2 < N)).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### Section 5: Asymptotic Resolution of Karan Sharma's OEIS A401897 Conjecture -/

/-- Norm `N(z_n)` diverges to `+∞` as `n → ∞`. -/
lemma tendsto_gnorm_a401897_z_atTop :
    Tendsto (fun n : ℕ => (gnorm (a401897_z n) : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨Nat.ceil (Real.pi * max B 1 / 8 + 2 * Real.sqrt (max B 1)) + 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hrb := (abs_le.mp (rank_norm_bound hn1)).2
  by_contra hlt
  push Not at hlt
  have hNle : (gnorm (a401897_z n) : ℝ) ≤ max B 1 := le_trans (le_of_lt hlt) (le_max_left _ _)
  have hsq : Real.sqrt (gnorm (a401897_z n) : ℝ) ≤ Real.sqrt (max B 1) :=
    Real.sqrt_le_sqrt hNle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn_le : (n : ℝ) ≤ Real.pi * max B 1 / 8 + 2 * Real.sqrt (max B 1) := by nlinarith
  have hceil : Real.pi * max B 1 / 8 + 2 * Real.sqrt (max B 1) < (n : ℝ) := by
    have h1 : (Nat.ceil (Real.pi * max B 1 / 8 + 2 * Real.sqrt (max B 1)) : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith [Nat.le_ceil (Real.pi * max B 1 / 8 + 2 * Real.sqrt (max B 1))]
  linarith

/-- Elementary decay `log(2 √x) / √x → 0` as `x → ∞`. -/
lemma tendsto_log_two_sqrt_div_sqrt :
    Tendsto (fun x : ℝ => Real.log (2 * Real.sqrt x) / Real.sqrt x) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ ?_ (a := fun x : ℝ => 4 / Real.sqrt (Real.sqrt x) + Real.log 2 / Real.sqrt x)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hsqx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hsqx_ge1 : 1 ≤ Real.sqrt x := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    have hq_pos : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hsqx_pos
    have hlog_ge0 : 0 ≤ Real.log (2 * Real.sqrt x) :=
      Real.log_nonneg (by linarith)
    have hlog_split : Real.log (2 * Real.sqrt x) = Real.log 2 + Real.log (Real.sqrt x) :=
      Real.log_mul (by norm_num) hsqx_pos.ne'
    have hlog_sq : Real.log (Real.sqrt x) = 2 * Real.log (Real.sqrt (Real.sqrt x)) := by
      have heq : Real.sqrt x = (Real.sqrt (Real.sqrt x)) ^ 2 :=
        (Real.sq_sqrt hsqx_pos.le).symm
      conv_lhs => rw [heq]
      rw [Real.log_pow]
      push_cast
      rfl
    have hlog_le : Real.log (Real.sqrt (Real.sqrt x)) ≤ Real.sqrt (Real.sqrt x) := by
      linarith [Real.log_le_sub_one_of_pos hq_pos]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog_ge0 hsqx_pos.le), hlog_split, add_div]
    have hpart : Real.log (Real.sqrt x) / Real.sqrt x ≤ 4 / Real.sqrt (Real.sqrt x) := by
      rw [hlog_sq]
      calc
        2 * Real.log (Real.sqrt (Real.sqrt x)) / Real.sqrt x
            ≤ 2 * Real.sqrt (Real.sqrt x) / Real.sqrt x := by
          exact div_le_div_of_nonneg_right (by linarith) hsqx_pos.le
        _ = 2 / Real.sqrt (Real.sqrt x) := by
          rw [div_eq_div_iff hsqx_pos.ne' hq_pos.ne']
          nlinarith [Real.mul_self_sqrt hsqx_pos.le]
        _ ≤ 4 / Real.sqrt (Real.sqrt x) := by
          exact div_le_div_of_nonneg_right (by norm_num) hq_pos.le
    linarith
  · have hsq_inf : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨max b 0 ^ 2, fun x hx => ?_⟩
      calc
        b ≤ max b 0 := le_max_left _ _
        _ = Real.sqrt (max b 0 ^ 2) := (Real.sqrt_sq (le_max_right b 0)).symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    have hq_inf : Tendsto (fun x : ℝ => Real.sqrt (Real.sqrt x)) atTop atTop :=
      hsq_inf.comp hsq_inf
    have h1 : Tendsto (fun x : ℝ => (4 : ℝ) / Real.sqrt (Real.sqrt x)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := (4 : ℝ))).mul (tendsto_inv_atTop_zero.comp hq_inf)
    have h2 : Tendsto (fun x : ℝ => Real.log 2 / Real.sqrt x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := Real.log 2)).mul (tendsto_inv_atTop_zero.comp hsq_inf)
    simpa using h1.add h2

/-- **Main Theorem (Resolution of Karan Sharma's OEIS A401897 Conjecture):**
`a(n) ~ 48 n / π²` as `n → ∞`. -/
theorem sharma_a401897_asymptotic :
    Tendsto (fun n : ℕ => (a401897 n : ℝ) / (48 * (n : ℝ) / Real.pi ^ 2))
      atTop (nhds 1) := by
  let Nseq : ℕ → ℝ := fun n => (gnorm (a401897_z n) : ℝ)
  have hN_inf : Tendsto Nseq atTop atTop := tendsto_gnorm_a401897_z_atTop
  have hsq_inf : Tendsto (fun n : ℕ => Real.sqrt (Nseq n)) atTop atTop := by
    refine (?_ : Tendsto Real.sqrt atTop atTop).comp hN_inf
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max b 0 ^ 2, fun x hx => ?_⟩
    calc
      b ≤ max b 0 := le_max_left _ _
      _ = Real.sqrt (max b 0 ^ 2) := (Real.sqrt_sq (le_max_right b 0)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  -- Ratio 1: `a(n) / (6 N(z_n) / π) → 1`
  have hnum : Tendsto (fun n : ℕ => (a401897 n : ℝ) / (6 * Nseq n / Real.pi)) atTop (nhds 1) := by
    have hdiff : Tendsto (fun n : ℕ => (a401897 n : ℝ) / (6 * Nseq n / Real.pi) - 1) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ ?_
        (a := fun n : ℕ => (Real.pi ^ 2 / 6) *
          ((2 + Real.sqrt 2) / Real.sqrt (Nseq n) +
            Real.sqrt 2 * (Real.log (2 * Real.sqrt (Nseq n)) / Real.sqrt (Nseq n))))
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hz : 0 < gnorm (a401897_z n) := (a401897_z_inWedge hn).2.2
        have hNpos : 0 < Nseq n := Nat.cast_pos.mpr hz
        have hRpos : 0 < Real.sqrt (Nseq n) := Real.sqrt_pos.mpr hNpos
        have hpi : 0 < Real.pi := Real.pi_pos
        have hdenom : 0 < 6 * Nseq n / Real.pi := by positivity
        have huv := uniform_visibility_bound hz
        rw [Real.norm_eq_abs]
        have hrew : (a401897 n : ℝ) / (6 * Nseq n / Real.pi) - 1 =
            ((visibleCount (a401897_z n) : ℝ) - 6 * Nseq n / Real.pi) / (6 * Nseq n / Real.pi) := by
          unfold a401897
          field_simp
        rw [hrew, abs_div, abs_of_pos hdenom]
        calc
          |(visibleCount (a401897_z n) : ℝ) - 6 * Nseq n / Real.pi| / (6 * Nseq n / Real.pi)
              ≤ (Real.pi * Real.sqrt (Nseq n) *
                  (2 + Real.sqrt 2 + Real.sqrt 2 * Real.log (2 * Real.sqrt (Nseq n)))) /
                  (6 * Nseq n / Real.pi) :=
            div_le_div_of_nonneg_right huv hdenom.le
          _ = (Real.pi ^ 2 / 6) *
                ((2 + Real.sqrt 2) / Real.sqrt (Nseq n) +
                  Real.sqrt 2 * (Real.log (2 * Real.sqrt (Nseq n)) / Real.sqrt (Nseq n))) := by
            have hdiv : Real.sqrt (Nseq n) / Nseq n = 1 / Real.sqrt (Nseq n) := by
              rw [div_eq_div_iff hNpos.ne' hRpos.ne', one_mul, Real.mul_self_sqrt hNpos.le]
            calc
              (Real.pi * Real.sqrt (Nseq n) *
                  (2 + Real.sqrt 2 + Real.sqrt 2 * Real.log (2 * Real.sqrt (Nseq n)))) /
                  (6 * Nseq n / Real.pi)
                  = (Real.pi ^ 2 / 6) * (Real.sqrt (Nseq n) / Nseq n) *
                      (2 + Real.sqrt 2 + Real.sqrt 2 * Real.log (2 * Real.sqrt (Nseq n))) := by
                field_simp
              _ = (Real.pi ^ 2 / 6) * (1 / Real.sqrt (Nseq n)) *
                      (2 + Real.sqrt 2 + Real.sqrt 2 * Real.log (2 * Real.sqrt (Nseq n))) := by
                rw [hdiv]
              _ = (Real.pi ^ 2 / 6) *
                    ((2 + Real.sqrt 2) / Real.sqrt (Nseq n) +
                      Real.sqrt 2 * (Real.log (2 * Real.sqrt (Nseq n)) / Real.sqrt (Nseq n))) := by
                ring
      · have h1 : Tendsto (fun n : ℕ => (2 + Real.sqrt 2) / Real.sqrt (Nseq n)) atTop (nhds 0) := by
          simpa [div_eq_mul_inv] using
            (tendsto_const_nhds (x := 2 + Real.sqrt 2)).mul (tendsto_inv_atTop_zero.comp hsq_inf)
        have h2 : Tendsto (fun n : ℕ =>
            Real.sqrt 2 * (Real.log (2 * Real.sqrt (Nseq n)) / Real.sqrt (Nseq n))) atTop (nhds 0) := by
          simpa using
            (tendsto_const_nhds (x := Real.sqrt 2)).mul (tendsto_log_two_sqrt_div_sqrt.comp hN_inf)
        simpa using (tendsto_const_nhds (x := Real.pi ^ 2 / 6)).mul (h1.add h2)
    simpa using hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
  -- Ratio 2: `n / (π N(z_n) / 8) → 1`
  have hden : Tendsto (fun n : ℕ => (n : ℝ) / (Real.pi * Nseq n / 8)) atTop (nhds 1) := by
    have hdiff : Tendsto (fun n : ℕ => (n : ℝ) / (Real.pi * Nseq n / 8) - 1) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ ?_ (a := fun n : ℕ => (16 / Real.pi) / Real.sqrt (Nseq n))
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hz : 0 < gnorm (a401897_z n) := (a401897_z_inWedge hn).2.2
        have hNpos : 0 < Nseq n := Nat.cast_pos.mpr hz
        have hRpos : 0 < Real.sqrt (Nseq n) := Real.sqrt_pos.mpr hNpos
        have hpi : 0 < Real.pi := Real.pi_pos
        have hdenom : 0 < Real.pi * Nseq n / 8 := by positivity
        have hrb := rank_norm_bound hn
        rw [Real.norm_eq_abs]
        have hrew : (n : ℝ) / (Real.pi * Nseq n / 8) - 1 =
            ((n : ℝ) - Real.pi * Nseq n / 8) / (Real.pi * Nseq n / 8) := by
          field_simp
        rw [hrew, abs_div, abs_of_pos hdenom]
        calc
          |(n : ℝ) - Real.pi * Nseq n / 8| / (Real.pi * Nseq n / 8)
              ≤ (2 * Real.sqrt (Nseq n)) / (Real.pi * Nseq n / 8) :=
            div_le_div_of_nonneg_right hrb hdenom.le
          _ = (16 / Real.pi) / Real.sqrt (Nseq n) := by
            have hdiv : Real.sqrt (Nseq n) / Nseq n = 1 / Real.sqrt (Nseq n) := by
              rw [div_eq_div_iff hNpos.ne' hRpos.ne', one_mul, Real.mul_self_sqrt hNpos.le]
            calc
              (2 * Real.sqrt (Nseq n)) / (Real.pi * Nseq n / 8)
                  = (16 / Real.pi) * (Real.sqrt (Nseq n) / Nseq n) := by field_simp; ring
              _ = (16 / Real.pi) * (1 / Real.sqrt (Nseq n)) := by rw [hdiv]
              _ = (16 / Real.pi) / Real.sqrt (Nseq n) := by ring
      · simpa [div_eq_mul_inv] using
          (tendsto_const_nhds (x := 16 / Real.pi)).mul (tendsto_inv_atTop_zero.comp hsq_inf)
    simpa using hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
  -- Combine Ratio 1 / Ratio 2 = `a(n) / (48 n / π²)`
  have hquot : Tendsto (fun n : ℕ =>
      ((a401897 n : ℝ) / (6 * Nseq n / Real.pi)) / ((n : ℝ) / (Real.pi * Nseq n / 8)))
      atTop (nhds (1 / 1)) :=
    hnum.div hden one_ne_zero
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hNpos : (Nseq n) ≠ 0 := (Nat.cast_pos.mpr (a401897_z_inWedge hn).2.2).ne'
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega : 0 < n)).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end SharmaA401897
