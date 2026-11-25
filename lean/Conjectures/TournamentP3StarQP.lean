import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

/-! # Distance-two convexity in tournaments -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TournamentP3StarQP

structure Tournament (V : Type*) where
  adj : V → V → Prop
  irrefl : ∀ v, ¬ adj v v
  asymm : ∀ {v w}, adj v w → ¬ adj w v
  trichotomous : ∀ {v w}, v ≠ w → adj v w ∨ adj w v
  decidableAdj : DecidableRel adj

attribute [instance] Tournament.decidableAdj

variable {V : Type*} [Fintype V] [DecidableEq V]

def P3StarInterval (T : Tournament V) (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun v =>
    ∃ u ∈ S, ∃ w ∈ S, T.adj u v ∧ T.adj v w ∧ T.adj w u)

def HasP3StarIntervalSet (T : Tournament V) (D F : Finset V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ k ∧ D ⊆ P3StarInterval T (S ∪ F)

variable (T : Tournament V)

@[simp] theorem mem_interval {S : Finset V} {v : V} :
    v ∈ P3StarInterval T S ↔
      v ∈ S ∨ ∃ u ∈ S, ∃ w ∈ S, T.adj u v ∧ T.adj v w ∧ T.adj w u := by
  simp [P3StarInterval]

theorem interval_mono {S S' : Finset V} (h : S ⊆ S') :
    P3StarInterval T S ⊆ P3StarInterval T S' := by
  intro v hv
  rw [mem_interval] at hv ⊢
  rcases hv with hv | ⟨u, hu, w, hw, huv, hvw, hwu⟩
  · exact Or.inl (h hv)
  · exact Or.inr ⟨u, h hu, w, h hw, huv, hvw, hwu⟩

def cov (U : Finset V) (u w : V) : Finset V :=
  U.filter (fun v => T.adj u v ∧ T.adj v w)

def out (U : Finset V) (x : V) : Finset V := U.filter (T.adj x)

def f (U : Finset V) (x : V) : ℕ := (out T U x).card

def LowCoverage (U : Finset V) (r : ℕ) : Prop :=
  ∀ w u, T.adj w u → (cov T U u w).card * r < U.card

variable {T} {U : Finset V} {r : ℕ}

theorem lemmaA_lipschitz (h : LowCoverage T U r) {w u : V} (hwu : T.adj w u) :
    f T U u - f T U w ≤ (cov T U u w).card ∧
      f T U u * r < f T U w * r + U.card := by
  have hs : out T U u \ out T U w ⊆ cov T U u w := by
    intro v hv
    simp only [Finset.mem_sdiff, out, cov, Finset.mem_filter] at hv ⊢
    obtain ⟨⟨hv, huv⟩, hn⟩ := hv
    refine ⟨hv, huv, ?_⟩
    have hne : w ≠ v := fun e => T.asymm hwu (e ▸ huv)
    exact (T.trichotomous hne).resolve_left (fun h' => hn ⟨hv, h'⟩)
  have hd := Finset.card_le_card hs
  have hc := Finset.card_sdiff_add_card_eq_card (t := out T U u) (s := out T U u ∩ out T U w)
    Finset.inter_subset_left
  have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := out T U u) (s₂ := out T U w))
  have he : out T U u \ (out T U u ∩ out T U w) = out T U u \ out T U w := by
    ext v
    simp
  rw [he] at hc
  have hb : f T U u ≤ f T U w + (cov T U u w).card := by unfold f; omega
  refine ⟨by omega, ?_⟩
  have hm := Nat.mul_le_mul_right r hb
  rw [Nat.add_mul] at hm
  have hh := h w u hwu
  omega

/-- The bottom band includes degree zero. -/
def bandIndex (T : Tournament V) (U : Finset V) (r : ℕ) (x : V) : ℕ :=
  r - (f T U x * r - 1) / U.card

def C (T : Tournament V) (U : Finset V) (r i : ℕ) : Finset V :=
  Finset.univ.filter (fun x => 1 ≤ i ∧ i ≤ r ∧ bandIndex T U r x = i)

theorem bandIndex_le (x : V) : bandIndex T U r x ≤ r := Nat.sub_le _ _

theorem bandIndex_pos (hr : 0 < r) (x : V) : 1 ≤ bandIndex T U r x := by
  unfold bandIndex
  by_cases hm : U.card = 0
  · simp [hm]; omega
  have hf : f T U x ≤ U.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hmul := Nat.mul_le_mul_right r hf
  have hlt : f T U x * r - 1 < r * U.card := by
    rw [Nat.mul_comm r]
    have hp := Nat.mul_pos (Nat.pos_of_ne_zero hm) hr
    omega
  have := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hm)).2 hlt
  omega

theorem mem_band_iff {i : ℕ} {x : V} (hm : 0 < U.card) :
    x ∈ C T U r i ↔ 1 ≤ i ∧ i ≤ r ∧
      (i = r ∨ (r - i) * U.card < f T U x * r) ∧
      f T U x * r ≤ (r - i + 1) * U.card := by
  simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hir, h⟩
    have he : (f T U x * r - 1) / U.card = r - i := by
      unfold bandIndex at h
      omega
    have hu := (Nat.div_lt_iff_lt_mul hm).1
      (show (f T U x * r - 1) / U.card < r - i + 1 by omega)
    have hl := (Nat.le_div_iff_mul_le hm).1
      (show r - i ≤ (f T U x * r - 1) / U.card by omega)
    refine ⟨hi, hir, ?_, ?_⟩
    · by_cases e : i = r
      · exact Or.inl e
      exact Or.inr (by have := Nat.mul_pos (show 0 < r - i by omega) hm; omega)
    · omega
  · rintro ⟨hi, hir, hl, hu⟩
    have hp := Nat.mul_pos (show 0 < r - i + 1 by omega) hm
    have ha := (Nat.div_lt_iff_lt_mul hm).2
      (show f T U x * r - 1 < (r - i + 1) * U.card by omega)
    have hb : r - i ≤ (f T U x * r - 1) / U.card := by
      apply (Nat.le_div_iff_mul_le hm).2
      rcases hl with rfl | hl
      · simp
      · omega
    unfold bandIndex
    omega

theorem mem_own_band (hr : 0 < r) (x : V) :
    x ∈ C T U r (bandIndex T U r x) := by
  simp [C, bandIndex_pos hr x, bandIndex_le x]

theorem lemmaB_forward (h : LowCoverage T U r) (hm : 0 < U.card)
    {i j : ℕ} {x y : V} (_hi : 1 ≤ i) (hij : i + 2 ≤ j) (hj : j ≤ r)
    (hx : x ∈ C T U r i) (hy : y ∈ C T U r j) : T.adj x y := by
  have hne : x ≠ y := by
    intro e
    subst y
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    omega
  rcases T.trichotomous hne with hxy | hyx
  · exact hxy
  have hl := (mem_band_iff hm).1 hx |>.2.2.1.resolve_left (by omega)
  have hu := (mem_band_iff hm).1 hy |>.2.2.2
  have hc := Nat.mul_le_mul_right U.card (show r - j + 1 + 1 ≤ r - i by omega)
  rw [Nat.add_mul, Nat.one_mul] at hc
  have ha := (lemmaA_lipschitz h hyx).2
  omega

private theorem arc_index (h : LowCoverage T U r) (hm : 0 < U.card) (hr : 0 < r)
    {x y : V} (hxy : T.adj x y) : bandIndex T U r x ≤ bandIndex T U r y + 1 := by
  by_contra! hn
  exact T.asymm hxy (lemmaB_forward h hm (bandIndex_pos hr y) hn (bandIndex_le x)
    (mem_own_band hr y) (mem_own_band hr x))

theorem lemmaE_triangle_radius (h : LowCoverage T U r) (hm : 0 < U.card)
    {i : ℕ} {u v w : V} (hv : v ∈ C T U r i)
    (huv : T.adj u v) (hvw : T.adj v w) (hwu : T.adj w u) :
    (bandIndex T U r u ≤ i + 2 ∧ i ≤ bandIndex T U r u + 2) ∧
    (bandIndex T U r w ≤ i + 2 ∧ i ≤ bandIndex T U r w + 2) := by
  simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hr : 0 < r := by omega
  have h₁ := arc_index h hm hr huv
  have h₂ := arc_index h hm hr hvw
  have h₃ := arc_index h hm hr hwu
  omega

theorem lemmaC_decoupling (h : LowCoverage T U r) (hm : 0 < U.card)
    {t : ℕ} (ht : 2 ≤ t) (htr : t ≤ r - 4) {u v w : V}
    (huv : T.adj u v) (hvw : T.adj v w) (hwu : T.adj w u) :
    let i := bandIndex T U r v
    let j := bandIndex T U r u
    let l := bandIndex T U r w
    (i ≤ t + 1 → j ≤ t + 3 ∧ l ≤ t + 3) ∧
    (t + 2 ≤ i → t ≤ j ∧ t ≤ l) := by
  have hr : 0 < r := by omega
  have he := lemmaE_triangle_radius h hm (mem_own_band hr v) huv hvw hwu
  dsimp
  omega



variable (T) in
/-- Reversing each arc exchanges out-degree and in-degree. -/
def reverse : Tournament V where
  adj x y := T.adj y x
  irrefl := T.irrefl
  asymm h := T.asymm h
  trichotomous h := (T.trichotomous h).symm
  decidableAdj _ _ := T.decidableAdj _ _

private theorem degreeSum (B : Finset V) :
    (∑ x ∈ B, f T B x) + (∑ x ∈ B, f T B x) = B.card * (B.card - 1) := by
  have he (x : V) : f T B x = ∑ y ∈ B, if T.adj x y then 1 else 0 := by
    simp [f, out]
  simp_rw [he]
  conv_lhs =>
    arg 1
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_const_nat
  intro x hx
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ y ∈ B, if x = y then (0 : ℕ) else 1 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : x = y
      · subst y
        simp [T.irrefl]
      · rcases T.trichotomous h with hxy | hyx
        · simp [h, hxy, T.asymm hxy]
        · simp [h, hyx, T.asymm hyx]
    _ = B.card - 1 := by
      have he (y : V) : (if x = y then 0 else 1 : ℕ) = if x ≠ y then 1 else 0 := by
        by_cases h : x = y <;> simp [h]
      simp_rw [he, Finset.sum_boole, Finset.filter_ne, Finset.card_erase_of_mem hx]
      rfl

private theorem degreeComplement {B : Finset V} {x : V} (hx : x ∈ B) :
    f T B x + f (reverse T) B x + 1 = B.card := by
  have hfilter :
      (B.erase x).filter (fun y => ¬ T.adj x y) = out (reverse T) B x := by
    ext y
    change y ∈ (B.erase x).filter _ ↔ y ∈ B.filter (fun z => T.adj z x)
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hy⟩, hn⟩
      exact ⟨hy, (T.trichotomous hne.symm).resolve_left hn⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨fun he => T.irrefl x (he ▸ h), hy⟩, T.asymm h⟩
  have hout : (B.erase x).filter (T.adj x) = out T B x := by
    ext y
    simp only [out, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨⟨_, hy⟩, ha⟩ => ⟨hy, ha⟩,
      fun ⟨hy, ha⟩ => ⟨⟨fun he => T.irrefl x (he ▸ ha), hy⟩, ha⟩⟩
  have h := Finset.card_filter_add_card_filter_not (s := B.erase x) (p := T.adj x)
  rw [hfilter, hout] at h
  rw [Finset.card_erase_of_mem hx] at h
  have hp := Finset.card_pos.mpr ⟨x, hx⟩
  unfold f
  omega

private theorem largeDegree (low : LowCoverage T U r) (hsize : r < 2 * U.card)
    {B : Finset V} (hBU : B ⊆ U) (hB : B.Nonempty) :
    ∃ x ∈ B, B.card * r < f T B x * r + 2 * U.card := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image B (f T B) hB
  let I := out (reverse T) B x
  let O := out T B x
  have hdeg := degreeComplement (T := T) hx
  change O.card + I.card + 1 = B.card at hdeg
  refine ⟨x, hx, ?_⟩
  suffices hi : (I.card + 1) * r < 2 * U.card by
    rw [← hdeg, show O.card + I.card + 1 = O.card + (I.card + 1) by omega, Nat.add_mul]
    exact Nat.add_lt_add_left hi _
  by_cases hI : I.Nonempty
  · obtain ⟨y, hy, hlarge⟩ := Finset.exists_max_image I (f T I) hI
    have hpair := degreeSum (T := T) I
    have hsum : (∑ z ∈ I, f T I z) ≤ I.card * f T I y := by
      calc
        _ ≤ ∑ _ ∈ I, f T I y := Finset.sum_le_sum hlarge
        _ = _ := Finset.sum_const_nat (fun _ _ => rfl)
    have hpos := Finset.card_pos.mpr hI
    have hbound : I.card - 1 ≤ 2 * f T I y := by
      apply Nat.le_of_mul_le_mul_left _ hpos
      rw [Nat.mul_left_comm]
      omega
    have hy' : y ∈ B ∧ T.adj y x := Finset.mem_filter.mp hy
    have hyx := hy'.2
    have hs : (out T I y ∪ out T O y) ⊆ out T B y := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz <;>
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1,
          (Finset.mem_filter.mp hz).2⟩
    have hj : Disjoint (out T I y) (out T O y) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact T.asymm (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hz').1).2
    have hxn : x ∉ out T I y ∪ out T O y := by
      intro hh
      rcases Finset.mem_union.mp hh with hh | hh <;>
        exact T.irrefl x (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2
    have hcard := Finset.card_le_card
      (Finset.insert_subset (Finset.mem_filter.mpr ⟨hx, hyx⟩) hs)
    rw [Finset.card_insert_of_notMem hxn, Finset.card_union_of_disjoint hj] at hcard
    change f T I y + (out T O y).card + 1 ≤ f T B y at hcard
    have hpart : (out T O y).card + (cov T B x y).card = O.card := by
      have hp := Finset.card_filter_add_card_filter_not (s := O) (p := T.adj y)
      have he : O.filter (fun z => ¬ T.adj y z) = cov T B x y := by
        ext z
        simp only [Finset.mem_filter, O, out, cov]
        constructor
        · rintro ⟨⟨hz, hxz⟩, hn⟩
          have hn' : y ≠ z := fun e => T.asymm hyx (e ▸ hxz)
          exact ⟨hz, hxz, (T.trichotomous hn').resolve_left hn⟩
        · rintro ⟨hz, hxz, hzy⟩
          exact ⟨⟨hz, hxz⟩, T.asymm hzy⟩
      rwa [he] at hp
    have hle := hmax y hy'.1
    change f T B y ≤ O.card at hle
    have hsub : cov T B x y ⊆ cov T U x y :=
      Finset.filter_subset_filter _ hBU
    have hm := Nat.mul_le_mul_right r (Finset.card_le_card hsub)
    have hc := low y x hyx
    have hlin : I.card + 1 ≤ 2 * (cov T B x y).card := by omega
    have hmul := Nat.mul_le_mul_right r hlin
    rw [Nat.mul_assoc] at hmul
    omega
  · have : I.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hI)
    simpa [this] using hsize

private theorem reverse_low (h : LowCoverage T U r) : LowCoverage (reverse T) U r := by
  intro w u hwu
  have he : cov (reverse T) U u w = cov T U w u := by
    ext x
    simp [cov, reverse, and_comm]
  rw [he]
  exact h u w hwu

private theorem smallDegree (low : LowCoverage T U r) (hsize : r < 2 * U.card)
    {A : Finset V} (hAU : A ⊆ U) (hA : A.Nonempty) :
    ∃ x ∈ A, f T A x * r < 2 * U.card := by
  obtain ⟨x, hx, hl⟩ := largeDegree (reverse_low low) hsize hAU hA
  have he := degreeComplement (T := T) hx
  rw [← he, Nat.add_mul, Nat.add_mul, Nat.one_mul] at hl
  exact ⟨x, hx, by omega⟩

private theorem splitDegrees (low : LowCoverage T U r) (hsize : r < 2 * U.card)
    {A B : Finset V} (he : A ∪ B = U) (hab : ∀ x ∈ A, ∀ y ∈ B, T.adj x y) :
    (A.Nonempty → ∃ x ∈ A, f T U x * r < B.card * r + 2 * U.card) ∧
    (B.Nonempty → ∃ y ∈ B, B.card * r < f T U y * r + 2 * U.card) := by
  have hA : A ⊆ U := he ▸ Finset.subset_union_left
  have hB : B ⊆ U := he ▸ Finset.subset_union_right
  constructor
  · intro ha
    obtain ⟨x, hx, hl⟩ := smallDegree low hsize hA ha
    have hs : out T U x = out T A x ∪ B := by
      ext y
      rw [← he]
      simp only [out, Finset.mem_filter, Finset.mem_union]
      exact ⟨fun ⟨hu, hxy⟩ => hu.elim (fun h => Or.inl ⟨h, hxy⟩) Or.inr,
        fun h => h.elim (fun ⟨hy, hxy⟩ => ⟨Or.inl hy, hxy⟩)
          (fun hy => ⟨Or.inr hy, hab x hx y hy⟩)⟩
    have hd : Disjoint (out T A x) B := by
      exact Finset.disjoint_left.mpr (fun y hy hy' =>
        T.irrefl y (hab y (Finset.mem_filter.mp hy).1 y hy'))
    refine ⟨x, hx, ?_⟩
    unfold f at hl ⊢
    rw [hs, Finset.card_union_of_disjoint hd, Nat.add_mul]
    omega
  · intro hb
    obtain ⟨y, hy, hl⟩ := largeDegree low hsize hB hb
    have hs : out T U y = out T B y := by
      ext x
      rw [← he]
      simp only [out, Finset.mem_filter, Finset.mem_union]
      exact ⟨fun ⟨hu, hyx⟩ => ⟨hu.resolve_left (fun hx => T.asymm hyx (hab x hx y hy)), hyx⟩,
        fun ⟨hx, hyx⟩ => ⟨Or.inr hx, hyx⟩⟩
    exact ⟨y, hy, by simpa only [f, hs] using hl⟩



private def bandRange (T : Tournament V) (U : Finset V) (r : ℕ)
    (X : Finset V) (a b : ℕ) : Finset V :=
  X.filter (fun x => a ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ b)

private theorem noWideSplit (low : LowCoverage T U r) (hr : 0 < r) (hm : r < 2 * U.card)
    {a b : ℕ} (hab : a + 5 ≤ b) (hbr : b ≤ r)
    (ha : (bandRange T U r U 1 a).Nonempty)
    (hb : (bandRange T U r U b r).Nonempty)
    (hgap : ∀ x ∈ U, bandIndex T U r x ≤ a ∨ b ≤ bandIndex T U r x) : False := by
  have hp : 0 < U.card := by omega
  let A := bandRange T U r U 1 a
  let B := bandRange T U r U b r
  have he : A ∪ B = U := by
    ext x
    simp only [A, B, bandRange, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      exact (hgap x hx).elim
        (fun h => Or.inl ⟨hx, bandIndex_pos hr x, h⟩)
        (fun h => Or.inr ⟨hx, h, bandIndex_le x⟩)
  have harc (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) : T.adj x y := by
    have h₁ := (Finset.mem_filter.mp hx).2.2
    have h₂ := (Finset.mem_filter.mp hy).2.1
    exact lemmaB_forward low hp (bandIndex_pos hr x) (by omega) (bandIndex_le y)
      (mem_own_band hr x) (mem_own_band hr y)
  have hd := splitDegrees low hm he harc
  obtain ⟨x, hx, hxf⟩ := hd.1 ha
  obtain ⟨y, hy, hyf⟩ := hd.2 hb
  have h₁ := (Finset.mem_filter.mp hx).2.2
  have h₂ := (Finset.mem_filter.mp hy).2.1
  have hl := (mem_band_iff hp).1 (mem_own_band (T := T) (U := U) hr x) |>.2.2.1.resolve_left (by omega)
  have hu := (mem_band_iff hp).1 (mem_own_band (T := T) (U := U) hr y) |>.2.2.2
  have hmul := Nat.mul_le_mul_right U.card
    (show r - bandIndex T U r y + 1 + 4 ≤ r - bandIndex T U r x by
      have := bandIndex_le (T := T) (U := U) (r := r) y
      omega)
  rw [Nat.add_mul] at hmul
  omega

theorem lemmaD_empty_gap (low : LowCoverage T U r) (hr : 6 ≤ r) (hm : 2 * U.card > r) :
    (∃ x ∈ U, x ∈ C T U r 1 ∪ C T U r 2) ∧
    (∃ x ∈ U, x ∈ C T U r (r - 1) ∪ C T U r r) ∧
    (∀ a b, (U ∩ C T U r a).Nonempty → (U ∩ C T U r b).Nonempty →
      (∀ i, a < i → i < b → U ∩ C T U r i = ∅) → b - a - 1 ≤ 3) ∧
    (∀ j, 1 ≤ j → j + 3 ≤ r → ∃ x ∈ U,
      j ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ j + 3) := by
  have hp : 0 < U.card := by omega
  have hr' : 0 < r := by omega
  have hn := Finset.card_pos.mp hp
  obtain ⟨x, hx, hxf⟩ := largeDegree low hm (fun _ h => h : U ⊆ U) hn
  obtain ⟨y, hy, hyf⟩ := smallDegree low hm (fun _ h => h : U ⊆ U) hn
  have hxl : bandIndex T U r x ≤ 2 := by
    by_contra! h
    have hu := (mem_band_iff hp).1 (mem_own_band (T := T) (U := U) hr' x) |>.2.2.2
    have hh := Nat.mul_le_mul_right U.card
      (show r - bandIndex T U r x + 1 + 2 ≤ r by omega)
    rw [Nat.add_mul, Nat.mul_comm r] at hh
    omega
  have hyl : r - 1 ≤ bandIndex T U r y := by
    by_contra! h
    have hl := (mem_band_iff hp).1 (mem_own_band (T := T) (U := U) hr' y) |>.2.2.1.resolve_left (by omega)
    have hh := Nat.mul_le_mul_right U.card
      (show 2 ≤ r - bandIndex T U r y by omega)
    omega
  refine ⟨⟨x, hx, ?_⟩, ⟨y, hy, ?_⟩, ?_, ?_⟩
  · have hpx := bandIndex_pos (T := T) (U := U) hr' x
    have he : bandIndex T U r x = 1 ∨ bandIndex T U r x = 2 := by omega
    simp only [Finset.mem_union, C, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with h | h
    · exact Or.inl ⟨by omega, by omega, h⟩
    · exact Or.inr ⟨by omega, by omega, h⟩
  · have hpy := bandIndex_le (T := T) (U := U) (r := r) y
    have he : bandIndex T U r y = r - 1 ∨ bandIndex T U r y = r := by omega
    simp only [Finset.mem_union, C, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with h | h
    · exact Or.inl ⟨by omega, by omega, h⟩
    · exact Or.inr ⟨by omega, le_rfl, h⟩
  · rintro a b ⟨v, hv⟩ ⟨w, hw⟩ hgap
    obtain ⟨hvU, hv⟩ := Finset.mem_inter.mp hv
    obtain ⟨hwU, hw⟩ := Finset.mem_inter.mp hw
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
    by_contra! h
    refine noWideSplit low hr' hm (by omega : a + 5 ≤ b) hw.2.1 ⟨v, ?_⟩ ⟨w, ?_⟩ ?_
    · exact Finset.mem_filter.mpr ⟨hvU, by omega⟩
    · exact Finset.mem_filter.mpr ⟨hwU, by omega⟩
    · intro z hz
      by_contra! hh
      have hz' := Finset.mem_inter.mpr ⟨hz, mem_own_band (T := T) (U := U) hr' z⟩
      rw [hgap _ hh.1 hh.2] at hz'
      exact Finset.notMem_empty _ hz'
  · intro j hj hjr
    by_contra! h
    have hgap (z : V) (hz : z ∈ U) :
        bandIndex T U r z ≤ j - 1 ∨ j + 4 ≤ bandIndex T U r z := by
      by_cases hjz : j ≤ bandIndex T U r z
      · have := h z hz hjz
        omega
      · omega
    have hxa : bandIndex T U r x ≤ j - 1 := (hgap x hx).resolve_right (by omega)
    have hyb : j + 4 ≤ bandIndex T U r y := (hgap y hy).resolve_left (by omega)
    have hyR := bandIndex_le (T := T) (U := U) (r := r) y
    exact noWideSplit low hr' hm (by omega : j - 1 + 5 ≤ j + 4) (by omega)
      ⟨x, Finset.mem_filter.mpr ⟨hx, bandIndex_pos hr' x, hxa⟩⟩
      ⟨y, Finset.mem_filter.mpr ⟨hy, hyb, hyR⟩⟩ hgap



def ell (n : ℕ) : ℕ := Nat.log 2 n + 1

def K0 (n : ℕ) : ℕ := 8000 * ell n

private theorem ell_pos (n : ℕ) : 0 < ell n := Nat.succ_pos _

private theorem lt_two_pow_ell (n : ℕ) : n < 2 ^ ell n :=
  Nat.lt_pow_succ_log_self (by decide) _

/-- A cardinal that falls by a factor of at most (r - 1)/r fits this many further steps. -/
private def Fits (r a fuel : ℕ) : Prop := a * (r - 1) ^ fuel < r ^ fuel

private theorem fits_init {r a n : ℕ} (hr : 2 ≤ r) (ha : a ≤ n) :
    Fits r a (r * ell n) := by
  have hb := pow_add_mul_le_add_pow (R := ℕ) (a := r - 1) (b := 1)
    (Nat.zero_le _) (Nat.zero_le _) r
  simp only [Nat.mul_one, show r - 1 + 1 = r by omega] at hb
  have he : (r - 1) ^ r ≤ r * (r - 1) ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    exact Nat.mul_le_mul (Nat.le_refl _) (by omega) |>.trans_eq (Nat.mul_comm _ _)
  have hh : 2 * (r - 1) ^ r ≤ r ^ r := by
    rw [Nat.two_mul]
    exact (Nat.add_le_add_left he _).trans hb
  have hp := Nat.pow_le_pow_left hh (ell n)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hp
  have hlt := ha.trans_lt (lt_two_pow_ell n)
  have hpos := Nat.pow_pos (n := r * ell n) (show 0 < r - 1 by omega)
  exact (Nat.mul_lt_mul_of_pos_right hlt hpos).trans_le hp

private theorem fits_step {r a b d : ℕ} (h : Fits r a (d + 1))
    (hd : b * r ≤ a * (r - 1)) : Fits r b d := by
  unfold Fits at *
  have hm := Nat.mul_le_mul_right ((r - 1) ^ d) hd
  rw [Nat.mul_right_comm b, Nat.mul_assoc a, ← pow_succ'] at hm
  rw [pow_succ] at h
  by_contra! hb
  exact (Nat.not_lt_of_ge (Nat.mul_le_mul_right r hb)) (hm.trans_lt h)

private def pairs (xs : List V) : List (V × V) :=
  xs.flatMap (fun x => xs.map (fun y => (x, y)))

private theorem mem_pairs {xs : List V} {a b : V} :
    (a, b) ∈ pairs xs ↔ a ∈ xs ∧ b ∈ xs := by simp [pairs]

private theorem pairs_length (xs : List V) : (pairs xs).length = xs.length * xs.length := by
  have he (ys : List V) :
      (ys.flatMap (fun x => xs.map (fun y => (x, y)))).length = ys.length * xs.length := by
    induction ys with
    | nil => simp
    | cons y ys ih => simp [ih, Nat.add_mul, Nat.add_comm]
  exact he xs

private def heavy (T : Tournament V) (U : Finset V) (r : ℕ) (p : V × V) : Bool :=
  let a := (cov T U p.2 p.1).card
  decide (U.card ≤ a * r ∧ T.adj p.1 p.2)

private def heavyArc (T : Tournament V) (ps : List (V × V)) (U : Finset V) (r : ℕ) :
    Option (V × V) :=
  (ps.filter (heavy T U r)).head?

private theorem heavyArc_some {ps : List (V × V)} {p : V × V}
    (h : heavyArc T ps U r = some p) :
    T.adj p.1 p.2 ∧ U.card ≤ (cov T U p.2 p.1).card * r := by
  obtain ⟨rest, he⟩ := List.head?_eq_some_iff.mp h
  have hm : p ∈ ps.filter (heavy T U r) := by rw [he]; simp
  simpa [heavy, and_comm] using (List.mem_filter.mp hm).2

private theorem heavyArc_none {ps : List (V × V)} (hall : ∀ w u : V, (w, u) ∈ ps)
    (h : heavyArc T ps U r = none) : LowCoverage T U r := by
  intro w u hwu
  have he := List.head?_eq_none_iff.mp h
  by_contra! hc
  have hm : (w, u) ∈ ps.filter (heavy T U r) := by simp [heavy, hall, hwu, hc]
  simp [he] at hm

private def pick (p : V × V) : Finset V := {p.1, p.2}

private def trim (T : Tournament V) (U : Finset V) (p : V × V) : Finset V :=
  U \ (pick p ∪ cov T U p.2 p.1)

private theorem trim_sub (p : V × V) : trim T U p ⊆ U := Finset.sdiff_subset

private theorem trim_decay {p : V × V} (hr : 1 ≤ r)
    (hh : U.card ≤ (cov T U p.2 p.1).card * r) :
    (trim T U p).card * r ≤ U.card * (r - 1) := by
  have hs : trim T U p ⊆ U \ cov T U p.2 p.1 := by
    intro x hx
    obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hx, fun hc => hn (Finset.mem_union_right _ hc)⟩
  have hsub := Finset.card_le_card hs
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _ :
    cov T U p.2 p.1 ⊆ U)
  change (U \ cov T U p.2 p.1).card + (cov T U p.2 p.1).card = U.card at hc
  have hm := Nat.mul_le_mul_right r (show (trim T U p).card +
    (cov T U p.2 p.1).card ≤ U.card by omega)
  rw [Nat.add_mul] at hm
  have he : U.card * (r - 1) + U.card = U.card * r := by
    rw [← Nat.mul_succ, show (r - 1).succ = r by omega]
  omega

private theorem trim_cover {p : V × V} (hp : T.adj p.1 p.2) :
    U ⊆ trim T U p ∪ P3StarInterval T (pick p) := by
  intro x hx
  rw [Finset.mem_union]
  by_cases ht : x ∈ trim T U p
  · exact Or.inl ht
  refine Or.inr ?_
  have hm : x ∈ pick p ∪ cov T U p.2 p.1 := by
    by_contra! hn
    exact ht (Finset.mem_sdiff.mpr ⟨hx, hn⟩)
  rcases Finset.mem_union.mp hm with hm | hm
  · exact (mem_interval T).2 (Or.inl hm)
  · obtain ⟨_, h₁, h₂⟩ := Finset.mem_filter.mp hm
    exact (mem_interval T).2 (Or.inr ⟨p.2, by simp [pick], p.1, by simp [pick], h₁, h₂, hp⟩)

private structure GreedyResult (V : Type*) where
  chosen : Finset V
  residual : Finset V
  steps : ℕ

/-- Each visit charges the fuel and empty checks. The arc scan visits every ordered pair
and, for each pair, scans the residual set to compute its coverage. -/
private def greedy (T : Tournament V) (ps : List (V × V)) (r : ℕ) :
    (fuel : ℕ) → Finset V → GreedyResult V
  | 0, U => ⟨∅, U, 1⟩
  | d + 1, U =>
    if U = ∅ then ⟨∅, U, 2⟩
    else
      let scan := 3 + ps.length * (U.card + 1)
      match heavyArc T ps U r with
      | none => ⟨∅, U, scan⟩
      | some p =>
        let g := greedy T ps r d (trim T U p)
        ⟨pick p ∪ g.chosen, g.residual, scan + 2 * U.card + 3 + g.steps⟩

private theorem greedy_spec {ps : List (V × V)} (hall : ∀ w u : V, (w, u) ∈ ps)
    (hr : 1 ≤ r) (d : ℕ) (U : Finset V) (hf : Fits r U.card d) :
    let g := greedy T ps r d U
    g.chosen.card ≤ 2 * d ∧ g.residual ⊆ U ∧
      (g.residual = ∅ ∨ LowCoverage T g.residual r) ∧
      U ⊆ g.residual ∪ P3StarInterval T g.chosen := by
  induction d generalizing U with
  | zero =>
    have he : U = ∅ := Finset.card_eq_zero.mp (by simpa [Fits] using hf)
    simp [greedy, he]
  | succ d ih =>
    by_cases he : U = ∅
    · simp [greedy, he]
    cases ha : heavyArc T ps U r with
    | none =>
      simp [greedy, he, ha, heavyArc_none hall ha, Finset.subset_union_left]
    | some p =>
      have hp := heavyArc_some ha
      have hf' := fits_step hf (trim_decay hr hp.2)
      obtain ⟨hc, hs, hl, hv⟩ := ih (trim T U p) hf'
      simp only [greedy, if_neg he, ha]
      have hb : (pick p).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      have hcard := Finset.card_union_le (pick p) (greedy T ps r d (trim T U p)).chosen
      refine ⟨by omega, fun _ hx => trim_sub p (hs hx), hl, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (trim_cover hp.1 hx) with hx | hx
      · rcases Finset.mem_union.mp (hv hx) with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (interval_mono T Finset.subset_union_right hx)
      · exact Finset.mem_union_right _ (interval_mono T Finset.subset_union_left hx)



private def windowStart (r q : ℕ) : ℕ := (r + 2) / 3 + 4 * q
private def windowCount (r : ℕ) : ℕ := ((2 * r) / 3 - 4 - (r + 2) / 3) / 4 + 1
private def windowBudget (k r : ℕ) : ℕ := 15 * k / r
private def dropBudget (r : ℕ) : ℕ := (r + 29) / 30

private theorem window_bounds {r q : ℕ} (hr : 200 ≤ r) (hq : q < windowCount r) :
    r ≤ 3 * windowStart r q ∧ windowStart r q + 4 ≤ (2 * r) / 3 := by
  unfold windowCount windowStart at *
  omega

private theorem bandRange_sum (S : Finset V) (a b : ℕ → ℕ) (q : ℕ)
    (h : ∀ i j, i < j → b i < a j) :
    (∑ i ∈ Finset.range q, (bandRange T U r S (a i) (b i)).card) ≤ S.card := by
  have hd : (↑(Finset.range q) : Set ℕ).PairwiseDisjoint
      (fun i => bandRange T U r S (a i) (b i)) := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨_, hvi, hivi⟩ := Finset.mem_filter.mp hv
    obtain ⟨_, hvj, hjvj⟩ := Finset.mem_filter.mp hw
    rcases lt_or_gt_of_ne hne with hh | hh
    · have := h i j hh
      omega
    · have := h j i hh
      omega
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ _ => Finset.filter_subset _ _))

private theorem light_window {S : Finset V} {k : ℕ} (hr : 200 ≤ r) (hk : S.card ≤ k) :
    ∃ q < windowCount r,
      (bandRange T U r S (windowStart r q) (windowStart r q + 3)).card ≤ windowBudget k r := by
  let Q := windowCount r
  let s := windowBudget k r
  have hrQ : r ≤ 15 * Q := by
    unfold Q windowCount
    omega
  have hsum := (bandRange_sum (T := T) (U := U) (r := r) S
    (windowStart r) (fun q => windowStart r q + 3) Q
    (by intro i j hij; unfold windowStart; omega)).trans hk
  by_contra! h
  have hmul : Q * (s + 1) ≤ k := calc
    _ = ∑ _ ∈ Finset.range Q, (s + 1) :=
      by rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      exact h q (Finset.mem_range.mp hq)
    _ ≤ _ := hsum
  have hdiv : 15 * k < (s + 1) * r :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < r)).1 (Nat.lt_succ_self _)
  have hm := Nat.mul_le_mul_left (s + 1) hrQ
  have hk' := Nat.mul_le_mul_left 15 hmul
  rw [Nat.mul_comm Q, ← Nat.mul_assoc, Nat.mul_comm 15 (s + 1), Nat.mul_assoc] at hk'
  omega

private theorem localWitness {D F S : Finset V} (h : LowCoverage T U r)
    (hr : 0 < r) (hm : 0 < U.card) (hU : U ⊆ D \ P3StarInterval T F)
    (hS : D ⊆ P3StarInterval T (S ∪ F)) {v : V} (hv : v ∈ U) :
    ∃ x ∈ S, bandIndex T U r x ≤ bandIndex T U r v + 2 ∧
      bandIndex T U r v ≤ bandIndex T U r x + 2 := by
  have ⟨hvD, hvF⟩ := Finset.mem_sdiff.mp (hU hv)
  have hn : v ∉ F := fun hv => hvF ((mem_interval T).2 (Or.inl hv))
  rcases (mem_interval T).1 (hS hvD) with hv' | ⟨u, hu, w, hw, huv, hvw, hwu⟩
  · exact ⟨v, (Finset.mem_union.mp hv').resolve_right hn, by omega, by omega⟩
  · have he := lemmaE_triangle_radius h hm (mem_own_band hr v) huv hvw hwu
    rcases Finset.mem_union.mp hu with huS | huF
    · exact ⟨u, huS, he.1⟩
    rcases Finset.mem_union.mp hw with hwS | hwF
    · exact ⟨w, hwS, he.2⟩
    exact (hvF ((mem_interval T).2 (Or.inr ⟨u, huF, w, hwF, huv, hvw, hwu⟩))).elim

private theorem countBlocks {D F S : Finset V} (low : LowCoverage T U r)
    (hr : 6 ≤ r) (hm : r < 2 * U.card) (hU : U ⊆ D \ P3StarInterval T F)
    (hS : D ⊆ P3StarInterval T (S ∪ F)) {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ r) :
    (b + 1 - a) / 8 ≤ (bandRange T U r S a b).card := by
  let q := (b + 1 - a) / 8
  let A := bandRange T U r S a b
  have hsum := bandRange_sum (T := T) (U := U) (r := r) A
    (fun i => a + 8 * i) (fun i => a + 8 * i + 7) q
    (by intro i j hij; omega)
  have hn := (lemmaD_empty_gap low hr hm).2.2.2
  have hp (i : ℕ) (hi : i ∈ Finset.range q) :
      1 ≤ (bandRange T U r A (a + 8 * i) (a + 8 * i + 7)).card := by
    have hi' : i < (b + 1 - a) / 8 := Finset.mem_range.mp hi
    have hlast : a + 8 * i + 7 ≤ b := by omega
    obtain ⟨v, hv, hv₁, hv₂⟩ := hn (a + 8 * i + 2) (by omega) (by omega)
    obtain ⟨x, hx, h₁, h₂⟩ := localWitness low (by omega) (by omega) hU hS hv
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hx, by omega, by omega⟩, by omega, by omega⟩⟩
  calc
    q = ∑ _ ∈ Finset.range q, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum hp
    _ ≤ _ := hsum

private def demandLeft (T : Tournament V) (U D : Finset V) (r t : ℕ) : Finset V :=
  D.filter (fun x => bandIndex T U r x ≤ t + 1)

private def demandRight (T : Tournament V) (U D : Finset V) (r t : ℕ) : Finset V :=
  D.filter (fun x => t + 2 ≤ bandIndex T U r x)

private theorem restrictInterval {D F S : Finset V} (keep : V → Prop) [DecidablePred keep]
    (hS : D ⊆ P3StarInterval T (S ∪ F))
    (hkeep : ∀ v ∈ D, keep v)
    (htri : ∀ v ∈ D, ∀ u w, T.adj u v → T.adj v w → T.adj w u → keep u ∧ keep w) :
    D ⊆ P3StarInterval T (S.filter keep ∪ F) := by
  intro v hv
  have hm (x : V) (hx : x ∈ S ∪ F) (hk : keep x) : x ∈ S.filter keep ∪ F :=
    Finset.mem_union.mpr ((Finset.mem_union.mp hx).imp (fun h => Finset.mem_filter.mpr ⟨h, hk⟩) id)
  apply (mem_interval T).2
  rcases (mem_interval T).1 (hS hv) with h | ⟨u, hu, w, hw, huv, hvw, hwu⟩
  · exact Or.inl (hm v h (hkeep v hv))
  · have hk := htri v hv u w huv hvw hwu
    exact Or.inr ⟨u, hm u hu hk.1, w, hm w hw hk.2, huv, hvw, hwu⟩

private theorem split_certificate {D F S : Finset V} {k : ℕ}
    (low : LowCoverage T U r) (hr : 200 ≤ r) (hm : r < 2 * U.card)
    (hU : U ⊆ D \ P3StarInterval T F) (hcard : S.card ≤ k)
    (hS : D ⊆ P3StarInterval T (S ∪ F)) :
    ∃ q < windowCount r, ∃ W : Finset V, ∃ kl kr : ℕ,
      W ⊆ bandRange T U r Finset.univ (windowStart r q) (windowStart r q + 3) ∧
      W.card ≤ windowBudget k r ∧ kl + W.card + kr ≤ k ∧
      kl ≤ k - dropBudget r ∧ kr ≤ k - dropBudget r ∧
      HasP3StarIntervalSet T (demandLeft T U D r (windowStart r q)) (F ∪ W) kl ∧
      HasP3StarIntervalSet T (demandRight T U D r (windowStart r q)) (F ∪ W) kr := by
  obtain ⟨q, hq, hw⟩ := light_window (T := T) (U := U) hr hcard
  let t := windowStart r q
  let L := bandRange T U r S 1 (t - 1)
  let W := bandRange T U r S t (t + 3)
  let R := bandRange T U r S (t + 4) r
  have hwin : r ≤ 3 * t ∧ t + 4 ≤ (2 * r) / 3 := window_bounds hr hq
  have hL := countBlocks low (by omega) hm hU hS (a := 1) (b := t - 1) (by omega) (by omega)
  have hR := countBlocks low (by omega) hm hU hS (a := t + 4) (b := r) (by omega) (by omega)
  change (t - 1 + 1 - 1) / 8 ≤ L.card at hL
  change (r + 1 - (t + 4)) / 8 ≤ R.card at hR
  have hl : dropBudget r ≤ L.card := by unfold dropBudget; omega
  have hr' : dropBudget r ≤ R.card := by unfold dropBudget; omega
  have hidx (x : V) : 1 ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ r :=
    ⟨bandIndex_pos (by omega) x, bandIndex_le x⟩
  have hleft : S.filter (fun x => bandIndex T U r x ≤ t + 3) = L ∪ W := by
    ext x
    have ⟨h₁, h₂⟩ := hidx x
    have he : ((1 ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ t - 1) ∨
        (t ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ t + 3)) ↔
          bandIndex T U r x ≤ t + 3 := by omega
    simp only [L, W, bandRange, Finset.mem_filter, Finset.mem_union, ← and_or_left, he]
  have hright : S.filter (fun x => ¬ bandIndex T U r x ≤ t + 3) = R := by
    ext x
    have ⟨h₁, h₂⟩ := hidx x
    have he : (t + 4 ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ r) ↔
        ¬ bandIndex T U r x ≤ t + 3 := by omega
    simp only [R, bandRange, Finset.mem_filter, he]
  have hpart := Finset.card_filter_add_card_filter_not (s := S)
    (p := fun x => bandIndex T U r x ≤ t + 3)
  rw [hleft, hright, Finset.card_union_of_disjoint] at hpart
  swap
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    have h₁ := (Finset.mem_filter.mp hx).2.2
    have h₂ := (Finset.mem_filter.mp hx').2.1
    omega
  refine ⟨q, hq, W, L.card, R.card, Finset.filter_subset_filter _ (Finset.subset_univ _),
    hw, by omega, by omega, by omega, ?_, ?_⟩
  · have hcov := restrictInterval (T := T) (S := S) (F := F)
      (D := demandLeft T U D r t) (fun x => bandIndex T U r x ≤ t + 3)
      (fun _ hx => hS (Finset.mem_filter.mp hx).1)
      (fun _ hx => by have := (Finset.mem_filter.mp hx).2; omega)
      (fun v hv u w huv hvw hwu => (lemmaC_decoupling low (by omega)
        (t := t) (by omega) (by omega) huv hvw hwu).1 (Finset.mem_filter.mp hv).2)
    rw [hleft] at hcov
    exact ⟨L, le_rfl, by simpa only [Finset.union_assoc, Finset.union_comm W F] using hcov⟩
  · have he : S.filter (fun x => t ≤ bandIndex T U r x) = R ∪ W := by
      ext x
      have ⟨h₁, h₂⟩ := hidx x
      have he : ((t + 4 ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ r) ∨
          (t ≤ bandIndex T U r x ∧ bandIndex T U r x ≤ t + 3)) ↔
            t ≤ bandIndex T U r x := by omega
      simp only [R, W, bandRange, Finset.mem_filter, Finset.mem_union, ← and_or_left, he]
    have hcov := restrictInterval (T := T) (S := S) (F := F)
      (D := demandRight T U D r t) (fun x => t ≤ bandIndex T U r x)
      (fun _ hx => hS (Finset.mem_filter.mp hx).1)
      (fun _ hx => by have := (Finset.mem_filter.mp hx).2; omega)
      (fun v hv u w huv hvw hwu => (lemmaC_decoupling low (by omega)
        (t := t) (by omega) (by omega) huv hvw hwu).2 (Finset.mem_filter.mp hv).2)
    rw [he] at hcov
    exact ⟨R, le_rfl, by simpa only [Finset.union_assoc, Finset.union_comm W F] using hcov⟩



private abbrev Result := Bool × ℕ

/-- Visit every item. The second component charges each list cell and the final empty check. -/
private def scan {A : Type*} (test : A → Result) : List A → Result
  | [] => (false, 1)
  | a :: as =>
    let x := test a
    let y := scan test as
    (x.1 || y.1, 1 + x.2 + y.2)

private theorem scan_true {A : Type*} (test : A → Result) (as : List A) :
    (scan test as).1 = true ↔ ∃ a ∈ as, (test a).1 = true := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
    simp only [scan, Bool.or_eq_true, ih, List.mem_cons]
    exact ⟨fun h => h.elim (fun h' => ⟨a, Or.inl rfl, h'⟩)
      (fun ⟨b, hb, h'⟩ => ⟨b, Or.inr hb, h'⟩),
      fun ⟨b, hb, h'⟩ => hb.elim (fun e => Or.inl (e ▸ h'))
        (fun hb' => Or.inr ⟨b, hb', h'⟩)⟩

private def candidates (xs : List V) : ℕ → List (Finset V) × ℕ
  | 0 => ([∅], 1)
  | d + 1 =>
    let p := candidates xs d
    (p.1.flatMap (fun S => S :: xs.map (fun x => insert x S)),
      p.2 + 1 + p.1.length * (xs.length + 2))

private theorem candidates_spec (xs : List V) (d : ℕ) (S : Finset V) :
    S ∈ (candidates xs d).1 ↔ S.card ≤ d ∧ ∀ x ∈ S, x ∈ xs := by
  induction d generalizing S with
  | zero =>
    simp only [candidates, List.mem_singleton, Nat.le_zero, Finset.card_eq_zero,
      iff_self_and]
    rintro rfl
    simp
  | succ d ih =>
    simp only [candidates, List.mem_flatMap, List.mem_cons, List.mem_map, ih]
    constructor
    · rintro ⟨A, ⟨hd, ha⟩, rfl | ⟨x, hx, rfl⟩⟩
      · exact ⟨by omega, ha⟩
      · refine ⟨(Finset.card_insert_le _ _).trans (by omega), ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact ha y hy
    · rintro ⟨hd, ha⟩
      by_cases h : S.card ≤ d
      · exact ⟨S, ⟨h, ha⟩, Or.inl rfl⟩
      have hp : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hp
      refine ⟨S.erase x, ⟨?_, fun y hy => ha y (Finset.mem_of_mem_erase hy)⟩,
        Or.inr ⟨x, ha x hx, Finset.insert_erase hx⟩⟩
      rw [Finset.card_erase_of_mem hx]
      omega

private theorem candidates_length (xs : List V) (d : ℕ) :
    (candidates xs d).1.length = (xs.length + 1) ^ d := by
  have hflat (as : List (Finset V)) :
      (as.flatMap (fun S => S :: xs.map (fun x => insert x S))).length =
        as.length * (xs.length + 1) := by
    induction as with
    | nil => simp
    | cons a as ih => simp [ih, Nat.add_mul]; omega
  induction d with
  | zero => simp [candidates]
  | succ d ih => simp only [candidates, hflat, ih, pow_succ]

private def checkedInterval (T : Tournament V) (ps : List (V × V)) (S : Finset V) : Finset V :=
  S ∪ (Finset.univ \ S).filter (fun v =>
    (!(ps.filter (fun (u, w) =>
      decide (u ∈ S ∧ w ∈ S ∧ T.adj u v ∧ T.adj v w ∧ T.adj w u))).isEmpty) = true)

private theorem checkedInterval_eq {ps : List (V × V)} (hall : ∀ u w : V, (u, w) ∈ ps)
    (S : Finset V) : checkedInterval T ps S = P3StarInterval T S := by
  ext v
  rw [mem_interval]
  by_cases hv : v ∈ S
  · simp [checkedInterval, hv]
  simp only [checkedInterval, Finset.mem_union, hv, false_or, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_univ, not_false_eq_true, and_self, true_and,
    Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨u, w⟩ := p
    have he := (List.mem_filter.mp hp).2
    simp only [decide_eq_true_eq] at he
    exact ⟨u, he.1, w, he.2⟩
  · rintro ⟨u, hu, w, hw, huv, hvw, hwu⟩ he
    have hp : (u, w) ∈ ps.filter (fun (u, w) =>
        decide (u ∈ S ∧ w ∈ S ∧ T.adj u v ∧ T.adj v w ∧ T.adj w u)) := by
      simp [hall, hu, hw, huv, hvw, hwu]
    rw [he] at hp
    exact List.not_mem_nil hp

private def intervalSteps (n : ℕ) (ps : List (V × V)) (S : Finset V) : ℕ :=
  3 + n + (n - S.card) * (ps.length + 2)

private def verify (T : Tournament V) (ps : List (V × V)) (D S : Finset V) : Result :=
  let I := checkedInterval T ps S
  let bad := D.filter (fun v => v ∉ I)
  (decide (bad = ∅), intervalSteps (Fintype.card V) ps S + D.card + 2)

private theorem verify_true {ps : List (V × V)} (hall : ∀ u w : V, (u, w) ∈ ps)
    (D S : Finset V) : (verify T ps D S).1 = true ↔ D ⊆ P3StarInterval T S := by
  simp only [verify, decide_eq_true_eq, checkedInterval_eq hall, Finset.filter_eq_empty_iff,
    Finset.subset_iff, not_not]

private def bandParameter (n k : ℕ) : ℕ := k / (40 * ell n)

private def depthParameter (n : ℕ) : ℕ := 1230 * ell n

private theorem parameters {n k : ℕ} (hk : K0 n < k) :
    let r := bandParameter n k
    200 ≤ r ∧ r * (40 * ell n) ≤ k ∧ k ≤ r * (41 * ell n) := by
  let l := ell n
  let r := bandParameter n k
  have hl : 0 < l := ell_pos n
  have hp : 0 < 40 * l := by omega
  have hlow : 8000 * l < k := hk
  have hr : 200 ≤ r := (Nat.le_div_iff_mul_le hp).2 (by omega)
  have h₁ : r * (40 * l) ≤ k := Nat.div_mul_le_self _ _
  have h₂ : k < (r + 1) * (40 * l) :=
    (Nat.div_lt_iff_lt_mul hp).1 (Nat.lt_succ_self _)
  change 200 ≤ r ∧ r * (40 * l) ≤ k ∧ k ≤ r * (41 * l)
  refine ⟨hr, h₁, ?_⟩
  have hmul := Nat.mul_le_mul_right l (show 40 * (r + 1) ≤ 41 * r by omega)
  simpa only [Nat.mul_assoc, Nat.mul_comm 40 r, Nat.mul_comm 41 r,
    Nat.mul_comm 40 (r + 1)] using (h₂.le.trans (by
      simpa only [← Nat.mul_assoc, Nat.mul_comm (r + 1) 40, Nat.mul_comm r 41] using hmul))

private theorem childFits {n k r k' d : ℕ} (hk : K0 n < k)
    (hr : r = bandParameter n k) (hf : Fits (depthParameter n) k (d + 1))
    (hchild : k' ≤ k - dropBudget r) :
    Fits (depthParameter n) k' d := by
  subst r
  let r := bandParameter n k
  let c := depthParameter n
  have ⟨h200, hrk, hkr⟩ := parameters hk
  change k ≤ r * (41 * ell n) at hkr
  change k' ≤ k - dropBudget r at hchild
  have hc : 1 ≤ c := by unfold c depthParameter; have := ell_pos n; omega
  have hdrop : r ≤ dropBudget r * 30 := by unfold dropBudget; omega
  have hd := Nat.mul_le_mul_right (41 * ell n) hdrop
  rw [Nat.mul_assoc, show 30 * (41 * ell n) = c by unfold c depthParameter; omega] at hd
  have hδ : dropBudget r ≤ k := by
    have hrle : r ≤ k := Nat.div_le_self _ _
    unfold dropBudget
    omega
  have hmul := Nat.mul_le_mul_right c (show k' + dropBudget r ≤ k by omega)
  rw [Nat.add_mul] at hmul
  have he : k * (c - 1) + k = k * c := by
    rw [← Nat.mul_succ, show (c - 1).succ = c by omega]
  apply fits_step hf
  change k' * c ≤ k * (c - 1)
  omega

private def branchOK (k r w kl kr : ℕ) : Prop :=
  kl + w + kr ≤ k ∧ kl ≤ k - dropBudget r ∧ kr ≤ k - dropBudget r

private instance (k r w kl kr : ℕ) : Decidable (branchOK k r w kl kr) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private def addSteps (s : ℕ) (x : Result) : Result := (x.1, s + x.2)

/-- The clock bounds the depth of multiplicatively decreasing budgets. -/
private def solveOn (T : Tournament V) (xs : List V) (ps : List (V × V)) :
    (fuel : ℕ) → Finset V → Finset V → ℕ → Result
  | d, D, F, k =>
    let n := Fintype.card V
    if n ≤ k then (true, 1)
    else if k ≤ K0 n then
      let cs := candidates xs k
      addSteps (2 + cs.2) (scan (fun S => addSteps 1 (verify T ps D (S ∪ F))) cs.1)
    else
      let r := bandParameter n k
      let U := D \ checkedInterval T ps F
      let g := greedy T ps r (r * ell n) U
      let initial := 5 + intervalSteps n ps F + D.card + g.steps
      if g.chosen.card + g.residual.card ≤ k then (true, initial)
      else
        match d with
        | 0 => (false, initial + 1)
        | d + 1 =>
          addSteps (initial + 1 + windowCount r) <| scan (fun q =>
            let t := windowStart r q
            let A := xs.filter (fun v =>
              decide (t ≤ bandIndex T g.residual r v ∧ bandIndex T g.residual r v ≤ t + 3))
            let dl := demandLeft T g.residual D r t
            let dr := demandRight T g.residual D r t
            let cs := candidates A (windowBudget k r)
            addSteps (4 + (2 * D.card + xs.length) * (g.residual.card + 1) + cs.2) <|
              scan (fun W =>
                let fixed := F ∪ W
                let budgets := List.range (k + 1)
                addSteps (k + 2) <| scan (fun kl => scan (fun kr =>
                  if branchOK k r W.card kl kr then
                    let left := solveOn T xs ps d dl fixed kl
                    let right := solveOn T xs ps d dr fixed kr
                    (left.1 && right.1, 5 + left.2 + right.2)
                  else (false, 4)) budgets) budgets) cs.1) (List.range (windowCount r))
termination_by fuel => fuel

/-- Run the counted solver with a vertex enumeration. The Boolean is independent of
permutation for a complete enumeration. The cost charges recursive calls, candidate generation,
loop visits, and checks at the level of the algorithm. Adjacency queries, natural arithmetic,
and primitive finite-set operations use unit charges in this work model. -/
def solveWithCost (T : Tournament V) (xs : List V) (D F : Finset V) (k : ℕ) : Result :=
  let n := Fintype.card V
  if n ≤ k then (true, 1)
  else
    let ps := pairs xs
    addSteps (2 + xs.length + ps.length)
      (solveOn T xs ps (depthParameter n * ell n) D F k)



private theorem budget_all (T : Tournament V) (D F : Finset V) {k : ℕ}
    (h : Fintype.card V ≤ k) : HasP3StarIntervalSet T D F k :=
  ⟨Finset.univ, h, fun _ _ => (mem_interval T).2
    (Or.inl (Finset.mem_union_left _ (Finset.mem_univ _)))⟩

private theorem greedy_yes {D F A U : Finset V} {k : ℕ}
    (hc : A.card + U.card ≤ k) (h : D \ P3StarInterval T F ⊆ U ∪ P3StarInterval T A) :
    HasP3StarIntervalSet T D F k := by
  refine ⟨A ∪ U, (Finset.card_union_le _ _).trans hc, ?_⟩
  intro x hx
  by_cases hf : x ∈ P3StarInterval T F
  · exact interval_mono T Finset.subset_union_right hf
  rcases Finset.mem_union.mp (h (Finset.mem_sdiff.mpr ⟨hx, hf⟩)) with hU | hA
  · exact (mem_interval T).2 (Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ hU)))
  · exact interval_mono T (Finset.subset_union_left.trans Finset.subset_union_left) hA

private theorem merge_subproblems {D F W : Finset V} {t kl kr k : ℕ}
    (hk : kl + W.card + kr ≤ k)
    (hL : HasP3StarIntervalSet T (demandLeft T U D r t) (F ∪ W) kl)
    (hR : HasP3StarIntervalSet T (demandRight T U D r t) (F ∪ W) kr) :
    HasP3StarIntervalSet T D F k := by
  obtain ⟨L, hcL, hL⟩ := hL
  obtain ⟨R, hcR, hR⟩ := hR
  refine ⟨L ∪ W ∪ R, ?_, ?_⟩
  · have h₁ := Finset.card_union_le L W
    have h₂ := Finset.card_union_le (L ∪ W) R
    omega
  intro x hx
  by_cases hi : bandIndex T U r x ≤ t + 1
  · have h := hL (Finset.mem_filter.mpr ⟨hx, hi⟩)
    apply interval_mono T _ h
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    tauto
  · have h := hR (Finset.mem_filter.mpr ⟨hx, show t + 2 ≤ bandIndex T U r x by omega⟩)
    apply interval_mono T _ h
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    tauto

private theorem solveOn_correct {xs : List V} (hall : ∀ v : V, v ∈ xs)
    {ps : List (V × V)} (hps : ∀ u w : V, (u, w) ∈ ps) (d : ℕ)
    (D F : Finset V) (k : ℕ) (hf : Fits (depthParameter (Fintype.card V)) k d) :
    (solveOn T xs ps d D F k).1 = true ↔ HasP3StarIntervalSet T D F k := by
  induction d using Nat.strong_induction_on generalizing D F k with
  | h d ih =>
    rw [solveOn]
    dsimp only
    let n := Fintype.card V
    by_cases hn : n ≤ k
    · rw [if_pos hn]
      exact ⟨fun _ => budget_all T D F hn, fun _ => rfl⟩
    rw [if_neg hn]
    by_cases hk : k ≤ K0 n
    · rw [if_pos hk]
      simp only [addSteps, scan_true, candidates_spec, verify_true hps, HasP3StarIntervalSet]
      exact ⟨fun ⟨S, hc, h⟩ => ⟨S, hc.1, h⟩,
        fun ⟨S, hc, h⟩ => ⟨S, ⟨hc, fun x _ => hall x⟩, h⟩⟩
    rw [if_neg hk]
    have hk' : K0 n < k := Nat.lt_of_not_ge hk
    let r := bandParameter n k
    let base := D \ checkedInterval T ps F
    let g := greedy T ps r (r * ell n) base
    obtain ⟨hr, hrk, _⟩ := parameters hk'
    change 200 ≤ r at hr
    change r * (40 * ell n) ≤ k at hrk
    have hbase : base = D \ P3StarInterval T F := by
      unfold base
      rw [checkedInterval_eq hps]
    have hcount : base.card ≤ n := Finset.card_le_univ _
    have hgf := fits_init (by omega : 2 ≤ r) hcount
    obtain ⟨hgc, hsub, hlow, hcov⟩ := greedy_spec hps (by omega : 1 ≤ r) (r * ell n) base hgf
    change g.chosen.card ≤ 2 * (r * ell n) at hgc
    change g.residual ⊆ base at hsub
    change g.residual = ∅ ∨ LowCoverage T g.residual r at hlow
    change base ⊆ g.residual ∪ P3StarInterval T g.chosen at hcov
    by_cases hg : g.chosen.card + g.residual.card ≤ k
    · rw [if_pos hg]
      have h := greedy_yes hg (hbase ▸ hcov)
      exact ⟨fun _ => h, fun _ => rfl⟩
    rw [if_neg hg]
    have hmul : 40 * (r * ell n) ≤ k := by
      simpa only [← Nat.mul_assoc, Nat.mul_comm r 40] using hrk
    have hrl : r ≤ r * ell n := by
      have h := Nat.mul_le_mul_left r (show 1 ≤ ell n from ell_pos n)
      simpa using h
    have hm : r < 2 * g.residual.card := by omega
    have hne : g.residual ≠ ∅ := by
      intro he
      rw [he, Finset.card_empty] at hm
      omega
    have low := hlow.resolve_left hne
    cases d with
    | zero =>
      have hzero : k = 0 := by simpa [Fits] using hf
      omega
    | succ d =>
      simp only [addSteps, scan_true, List.mem_range]
      constructor
      · rintro ⟨q, hq, W, hW, kl, hkl, kr, hkr, hb⟩
        by_cases h : branchOK k r W.card kl kr
        · rw [if_pos h, Bool.and_eq_true] at hb
          exact merge_subproblems h.1
            ((ih d (Nat.lt_succ_self _) _ _ _ (childFits hk' rfl hf h.2.1)).1 hb.1)
            ((ih d (Nat.lt_succ_self _) _ _ _ (childFits hk' rfl hf h.2.2)).1 hb.2)
        · rw [if_neg h] at hb
          contradiction
      · rintro ⟨S, hS, hv⟩
        obtain ⟨q, hq, W, kl, kr, hW, hsw, hsum, hkl, hkr, hl, hrr⟩ :=
          split_certificate low hr hm (hbase ▸ hsub) hS hv
        refine ⟨q, hq, W, ?_, kl, by omega, kr, by omega, ?_⟩
        · apply (candidates_spec _ _ _).2
          refine ⟨hsw, fun x hx => List.mem_filter.mpr ⟨hall x, ?_⟩⟩
          exact decide_eq_true ((Finset.mem_filter.mp (hW hx)).2)
        · have hb : branchOK k r W.card kl kr := ⟨hsum, hkl, hkr⟩
          rw [if_pos hb, Bool.and_eq_true]
          exact ⟨(ih d (Nat.lt_succ_self _) _ _ _ (childFits hk' rfl hf hkl)).2 hl,
            (ih d (Nat.lt_succ_self _) _ _ _ (childFits hk' rfl hf hkr)).2 hrr⟩

theorem solveWithCost_correct {xs : List V} (hall : ∀ v : V, v ∈ xs)
    (D F : Finset V) (k : ℕ) :
    (solveWithCost T xs D F k).1 = true ↔ HasP3StarIntervalSet T D F k := by
  unfold solveWithCost
  dsimp only
  by_cases hn : Fintype.card V ≤ k
  · rw [if_pos hn]
    exact ⟨fun _ => budget_all T D F hn, fun _ => rfl⟩
  rw [if_neg hn]
  have hr : 2 ≤ depthParameter (Fintype.card V) := by
    unfold depthParameter
    have := ell_pos (Fintype.card V)
    omega
  exact solveOn_correct hall (fun u w => mem_pairs.mpr ⟨hall u, hall w⟩) _ D F k
    (fits_init hr (Nat.le_of_lt (Nat.lt_of_not_ge hn)))

private theorem proofFun_heq {P Q : Prop} {a b : Bool} (he : P ↔ Q) (h : P → a = b) :
    HEq (fun _ : P => a) (fun _ : Q => b) := by
  have e := propext he
  subst Q
  exact heq_of_eq (funext h)

private def solveMultiset (T : Tournament V) (D F : Finset V) (k : ℕ) (M : Multiset V) :
    (∀ v : V, v ∈ M) → Bool :=
  Quotient.hrecOn (motive := fun M : Multiset V => (∀ v : V, v ∈ M) → Bool) M
    (fun (xs : List V) _ => (solveWithCost T xs D F k).1) (by
      intro a b h
      change a.Perm b at h
      apply proofFun_heq
      · exact ⟨fun ha v => Multiset.mem_coe.mpr (h.mem_iff.mp (Multiset.mem_coe.mp (ha v))),
          fun hb v => Multiset.mem_coe.mpr (h.mem_iff.mpr (Multiset.mem_coe.mp (hb v)))⟩
      · intro ha
        have ha' : ∀ v : V, v ∈ a := fun v => Multiset.mem_coe.mp (ha v)
        have hb' : ∀ v : V, v ∈ b := fun v => h.mem_iff.mp (ha' v)
        rw [Bool.eq_iff_iff, solveWithCost_correct ha', solveWithCost_correct hb'])

/-- Run the algorithm on the list underlying the finite type. The proof that this list
contains all vertices is erased, and the decision respects permutation of the list. -/
def solve (T : Tournament V) (D F : Finset V) (k : ℕ) : Bool :=
  solveMultiset T D F k (Finset.univ : Finset V).val (fun x => Finset.mem_univ x)

theorem solve_correct (D F : Finset V) (k : ℕ) :
    solve T D F k = true ↔ HasP3StarIntervalSet T D F k := by
  have h (M : Multiset V) (hall : ∀ v : V, v ∈ M) :
      solveMultiset T D F k M hall = true ↔ HasP3StarIntervalSet T D F k := by
    induction M using Quotient.inductionOn with
    | h xs =>
      have hx : ∀ v : V, v ∈ xs := fun v => Multiset.mem_coe.mp (hall v)
      change (solveWithCost T xs D F k).1 = true ↔ _
      exact solveWithCost_correct hx D F k
  exact h (Finset.univ : Finset V).val (fun x => Finset.mem_univ x)

theorem solveWithCost_eq_solve {xs : List V} (hall : ∀ v : V, v ∈ xs)
    (D F : Finset V) (k : ℕ) : (solveWithCost T xs D F k).1 = solve T D F k :=
  Bool.eq_iff_iff.mpr ((solveWithCost_correct hall D F k).trans (solve_correct D F k).symm)

theorem solve_sound {D F : Finset V} {k : ℕ} (h : solve T D F k = true) :
    HasP3StarIntervalSet T D F k := (solve_correct (T := T) D F k).1 h

theorem solve_complete {D F : Finset V} {k : ℕ} (h : HasP3StarIntervalSet T D F k) :
    solve T D F k = true := (solve_correct (T := T) D F k).2 h

theorem solve_iff_full (k : ℕ) : solve T Finset.univ ∅ k = true ↔
    ∃ S : Finset V, S.card ≤ k ∧ P3StarInterval T S = Finset.univ := by
  rw [solve_correct]
  simp only [HasP3StarIntervalSet, Finset.union_empty]
  apply exists_congr
  intro S
  rw [Finset.univ_subset_iff]



private theorem scan_steps {A : Type*} (test : A → Result) (xs : List A) (M : ℕ)
    (h : ∀ x ∈ xs, (test x).2 ≤ M) :
    (scan test xs).2 ≤ (xs.length + 1) * (M + 1) := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [scan, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem work_mono {A d e Z x : ℕ} (hA : 0 < A) (hde : d ≤ e)
    (h : x ≤ A ^ d * Z) : x ≤ A ^ e * Z :=
  h.trans (Nat.mul_le_mul_right Z (Nat.pow_le_pow_right hA hde))

private theorem work_one {A d Z x : ℕ} (hZ : 1 ≤ Z) (h : x ≤ A ^ d) :
    x ≤ A ^ d * Z := h.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A ^ d) hZ)

private theorem work_add {A d Z x y : ℕ} (hA : 2 ≤ A) (hx : x ≤ A ^ d * Z)
    (hy : y ≤ A ^ d * Z) : x + y ≤ A ^ (d + 1) * Z := by
  rw [pow_succ', Nat.mul_assoc]
  exact (Nat.add_le_add hx hy).trans (by rw [← Nat.two_mul]; exact Nat.mul_le_mul_right _ hA)

private theorem work_scan {α : Type*} {A d e Z : ℕ} (hA : 2 ≤ A) (hZ : 1 ≤ Z)
    (test : α → Result) (xs : List α) (hlen : xs.length + 1 ≤ A ^ d)
    (ht : ∀ x ∈ xs, (test x).2 ≤ A ^ e * Z) :
    (scan test xs).2 ≤ A ^ (d + (e + 1)) * Z := by
  have hpos : 1 ≤ A ^ e * Z :=
    Nat.mul_pos (Nat.pow_pos (by omega)) hZ
  have h₂ : A ^ e * Z + 1 ≤ A ^ (e + 1) * Z :=
    work_add hA (Nat.le_refl _) hpos
  calc
    _ ≤ (xs.length + 1) * (A ^ e * Z + 1) := scan_steps _ _ _ ht
    _ ≤ A ^ d * (A ^ (e + 1) * Z) := Nat.mul_le_mul hlen h₂
    _ = _ := by rw [← Nat.mul_assoc, ← pow_add]

private theorem candidate_steps {A : ℕ} (hA : 2 ≤ A) (xs : List V)
    (hxs : xs.length + 2 ≤ A) (d : ℕ) :
    (candidates xs d).2 ≤ A ^ (d + 2) := by
  have hpos : 0 < A := by omega
  induction d with
  | zero => simpa [candidates] using (Nat.succ_le_of_lt (Nat.pow_pos (n := 2) hpos))
  | succ d ih =>
    simp only [candidates, candidates_length]
    have hlen := Nat.pow_le_pow_left (show xs.length + 1 ≤ A by omega) d
    have hg := Nat.mul_le_mul hlen hxs
    rw [← pow_succ] at hg
    have h₁ : (xs.length + 1) ^ d * (xs.length + 2) + 1 ≤ A ^ (d + 2) :=
      by simpa only [Nat.mul_one] using
        (work_add hA (show (xs.length + 1) ^ d * (xs.length + 2) ≤ A ^ (d + 1) * 1
          by simpa using hg)
          (show 1 ≤ A ^ (d + 1) * 1 by simpa using Nat.succ_le_of_lt (Nat.pow_pos (n := d + 1) hpos)))
    have he := work_add hA
      (show (candidates xs d).2 ≤ A ^ (d + 2) * 1 by simpa using ih)
      (show (xs.length + 1) ^ d * (xs.length + 2) + 1 ≤ A ^ (d + 2) * 1 by simpa using h₁)
    rw [Nat.mul_one] at he
    change _ ≤ A ^ (d + 2 + 1)
    omega

private theorem candidate_length_bound {A : ℕ} (hA : 2 ≤ A) (xs : List V)
    (hxs : xs.length + 1 ≤ A) (d : ℕ) :
    (candidates xs d).1.length + 1 ≤ A ^ (d + 1) := by
  rw [candidates_length]
  have hp := Nat.pow_le_pow_left hxs d
  exact (Nat.add_le_add hp (Nat.succ_le_of_lt (Nat.pow_pos (n := d) (show 0 < A by omega)))).trans (by
    rw [pow_succ', ← Nat.two_mul]
    exact Nat.mul_le_mul_right _ hA)

private theorem greedy_steps {ps : List (V × V)} {r : ℕ} (n d : ℕ) (U : Finset V)
    (hU : U.card ≤ n) :
    (greedy T ps r d U).steps ≤ (d + 1) * (8 + (ps.length + 3) * (n + 1)) := by
  induction d generalizing U with
  | zero => simp [greedy]; omega
  | succ d ih =>
    let M := 8 + (ps.length + 3) * (n + 1)
    change (greedy T ps r (d + 1) U).steps ≤ (d + 1 + 1) * M
    have hM : 3 + ps.length * (U.card + 1) + 2 * U.card + 3 ≤ M := by
      have h := Nat.mul_le_mul_left ps.length (show U.card + 1 ≤ n + 1 by omega)
      unfold M
      rw [Nat.add_mul]
      omega
    rw [Nat.add_mul, Nat.one_mul, greedy]
    by_cases he : U = ∅
    · simp [he]
      omega
    rw [if_neg he]
    cases h : heavyArc T ps U r with
    | none => simp only; omega
    | some p =>
      have hU' := (Finset.card_le_card (trim_sub (T := T) (U := U) p)).trans hU
      have hb := ih _ hU'
      change (greedy T ps r d (trim T U p)).steps ≤ (d + 1) * M at hb
      simp only
      omega

private theorem windowCount_le {r : ℕ} (hr : 200 ≤ r) : windowCount r + 1 ≤ r + 1 := by
  unfold windowCount
  omega

private theorem windowBudget_le {n k : ℕ} (hk : K0 n < k) :
    windowBudget k (bandParameter n k) ≤ K0 n := by
  have hparam := (parameters hk).2.2
  have hmul := Nat.mul_le_mul_left 15 hparam
  apply Nat.div_le_of_le_mul
  refine hmul.trans ?_
  rw [Nat.mul_left_comm]
  apply Nat.mul_le_mul_left
  unfold K0
  rw [← Nat.mul_assoc]
  omega

private theorem intervalSteps_le {n : ℕ} (ps : List (V × V)) (hps : ps.length ≤ n * n)
    (S : Finset V) : intervalSteps n ps S ≤ (n + 2) ^ 4 := by
  have h := Nat.mul_le_mul (Nat.sub_le n S.card) (Nat.add_le_add_right hps 2)
  unfold intervalSteps
  have hp : 3 + n + n * (n * n + 2) ≤ (n + 2) ^ 4 := by
    nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 4)]
  omega

private theorem verify_steps_le {ps : List (V × V)}
    (hps : ps.length ≤ Fintype.card V * Fintype.card V) (D S : Finset V) :
    (addSteps 1 (verify T ps D S)).2 ≤ (Fintype.card V + 2) ^ 5 := by
  let n := Fintype.card V
  have hD : D.card ≤ n := Finset.card_le_univ _
  have hI : intervalSteps n ps S ≤ (n + 2) ^ 4 := intervalSteps_le ps hps S
  change 1 + (intervalSteps n ps S + D.card + 2) ≤ (n + 2) ^ 5
  have hp : (n + 2) ^ 4 + n + 3 ≤ (n + 2) ^ 5 := by
    nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3),
      Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 5)]
  omega

private theorem initial_steps_le {n r k : ℕ} {ps : List (V × V)}
    (hn : k < n) (hr : 200 ≤ r) (hrk : r * (40 * ell n) ≤ k) (hps : ps.length ≤ n * n)
    (D F U : Finset V) (hD : D.card ≤ n) (hU : U.card ≤ n) :
    5 + intervalSteps n ps F + D.card + (greedy T ps r (r * ell n) U).steps + 1 +
      windowCount r ≤ (n + 2) ^ 7 := by
  have hm : 40 * (r * ell n) ≤ k := by
    simpa only [← Nat.mul_assoc, Nat.mul_comm r 40] using hrk
  have hrl : r ≤ r * ell n := by
    simpa using Nat.mul_le_mul_left r (show 1 ≤ ell n from ell_pos n)
  have hg := greedy_steps (T := T) (r := r) (ps := ps) n (r * ell n) U hU
  have hb : (greedy T ps r (r * ell n) U).steps ≤ (n + 2) ^ 5 := by
    refine hg.trans ?_
    have h₁ := Nat.mul_le_mul_right (n + 1) (Nat.add_le_add_right hps 3)
    have h₂ := Nat.mul_le_mul (show r * ell n + 1 ≤ n + 1 by omega)
      (Nat.add_le_add_left h₁ 8)
    refine h₂.trans ?_
    nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3),
      Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 5)]
  have hI := intervalSteps_le ps hps F
  have hQ := windowCount_le hr
  have hp : 5 + (n + 2) ^ 4 + n + (n + 2) ^ 5 + 1 + n ≤ (n + 2) ^ 7 := by
    nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3),
      Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 5), Nat.zero_le (n ^ 6), Nat.zero_le (n ^ 7)]
  omega



private def workBase (n : ℕ) : ℕ := (n + 2) ^ (K0 n + 20)

private theorem solveOn_steps {xs : List V} {ps : List (V × V)}
    (hxs : xs.length ≤ Fintype.card V) (hps : ps.length ≤ Fintype.card V * Fintype.card V)
    (d : ℕ) (D F : Finset V) (k : ℕ) :
    (solveOn T xs ps d D F k).2 ≤ workBase (Fintype.card V) ^ (d + 1) := by
  induction d using Nat.strong_induction_on generalizing D F k with
  | h d ih =>
    let n := Fintype.card V
    let A := n + 2
    let K := K0 n
    let Z := workBase n ^ d
    have hA : 2 ≤ A := by unfold A; omega
    have hApos : 0 < A := by omega
    have hZ : 1 ≤ Z := Nat.pow_pos (Nat.pow_pos hApos)
    have hw : workBase n ^ (d + 1) = A ^ (K + 20) * Z := pow_succ' _ _
    rw [solveOn]
    dsimp only
    by_cases hn : n ≤ k
    · rw [if_pos hn]
      exact Nat.pow_pos (Nat.pow_pos hApos)
    rw [if_neg hn, hw]
    have hn' : k < n := by omega
    have hconst {i e : ℕ} (hi : i ≤ A) (he : 1 ≤ e) : i ≤ A ^ e * Z :=
      work_mono (d := 1) hApos he (work_one hZ
        (by simpa only [pow_one] using hi : i ≤ A ^ 1))
    by_cases hk : k ≤ K
    · rw [if_pos hk]
      simp only [addSteps]
      apply work_mono (d := k + 8) hApos (by omega)
      apply work_add hA (d := k + 7)
      · apply work_mono (d := k + 3) hApos (by omega)
        exact work_add hA (hconst hA (by omega)) (work_one hZ
          (candidate_steps hA xs (by unfold A; omega) k))
      · apply work_scan (d := k + 1) (e := 5) hA hZ
        · exact candidate_length_bound hA xs (by unfold A; omega) k
        · intro S _
          exact work_one hZ (verify_steps_le hps D (S ∪ F))
    rw [if_neg hk]
    have hk' : K0 n < k := by omega
    let r := bandParameter n k
    let U := D \ checkedInterval T ps F
    let g := greedy T ps r (r * ell n) U
    let I := 5 + intervalSteps n ps F + D.card + g.steps
    let Q := windowCount r
    let s := windowBudget k r
    have ⟨hr, hrk, _⟩ := parameters hk'
    change 200 ≤ r at hr
    change r * (40 * ell n) ≤ k at hrk
    have hrle : r ≤ n := (Nat.div_le_self _ _).trans hn'.le
    have hD : D.card ≤ n := Finset.card_le_univ _
    have hU : U.card ≤ n := Finset.card_le_univ _
    have hG : g.residual.card ≤ n := Finset.card_le_univ _
    have hI : I + 1 + Q ≤ A ^ 7 := initial_steps_le hn' hr hrk hps D F U hD hU
    have hQ : Q + 1 ≤ A ^ 1 := by
      rw [pow_one]
      have := windowCount_le hr
      unfold Q A
      omega
    have hQ' : (List.range Q).length + 1 ≤ A ^ 1 := by
      simpa only [List.length_range] using hQ
    have hsK : s ≤ K := windowBudget_le hk'
    by_cases hg : g.chosen.card + g.residual.card ≤ k
    · rw [if_pos hg]
      exact work_mono (d := 7) hApos (by omega) (work_one hZ (by omega : I ≤ A ^ 7))
    rw [if_neg hg]
    cases d with
    | zero =>
      exact work_mono (d := 7) hApos (by omega) (work_one hZ (by omega : I + 1 ≤ A ^ 7))
    | succ d =>
      simp only [addSteps]
      apply work_mono (d := (1 + (K + 11 + 1)) + 1) hApos (by omega)
      apply work_add hA
      · exact work_mono (d := 7) hApos (by omega) (work_one hZ hI)
      · apply work_scan (d := 1) (e := K + 11) hA hZ _ _ hQ'
        intro q _
        let t := windowStart r q
        let xs' := xs.filter (fun v =>
          decide (t ≤ bandIndex T g.residual r v ∧ bandIndex T g.residual r v ≤ t + 3))
        have hxs' : xs'.length ≤ n := (List.length_filter_le _ _).trans hxs
        have hPrep : 4 + (2 * D.card + xs.length) * (g.residual.card + 1) ≤ A ^ 4 := by
          have hP := Nat.mul_le_mul (show 2 * D.card + xs.length ≤ 3 * n by omega)
            (show g.residual.card + 1 ≤ n + 1 by omega)
          have hPoly : 4 + 3 * n * (n + 1) ≤ A ^ 4 := by
            unfold A
            nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 4)]
          omega
        apply work_add hA (d := K + 10)
        · apply work_mono (d := K + 5) hApos (by omega)
          apply work_add hA
          · exact work_mono (d := 4) hApos (by omega) (work_one hZ hPrep)
          · exact work_mono (d := s + 2) hApos (by omega) (work_one hZ
              (candidate_steps hA xs' (by unfold A; omega) s))
        · apply work_scan (d := K + 1) (e := 8) hA hZ
          · exact (candidate_length_bound hA xs' (by unfold A; omega) s).trans
              (Nat.pow_le_pow_right hApos (by omega))
          · intro W _
            apply work_add hA (d := 7)
            · exact hconst (by unfold A; omega) (by omega)
            · apply work_scan (d := 1) (e := 5) hA hZ
              · simp only [List.length_range, pow_one]
                unfold A
                omega
              · intro kl _
                apply work_scan (d := 1) (e := 3) hA hZ
                · simp only [List.length_range, pow_one]
                  unfold A
                  omega
                · intro kr _
                  by_cases hb : branchOK k r W.card kl kr
                  · rw [if_pos hb]
                    have hL := ih d (Nat.lt_succ_self _) (demandLeft T g.residual D r t) (F ∪ W) kl
                    have hR := ih d (Nat.lt_succ_self _) (demandRight T g.residual D r t) (F ∪ W) kr
                    change _ ≤ Z at hL hR
                    have h₇ : 7 ≤ A ^ 3 := (by decide : 7 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hA 3)
                    have hbnd := Nat.mul_le_mul_right Z h₇
                    change 5 + (solveOn T xs ps d (demandLeft T g.residual D r t) (F ∪ W) kl).2 +
                      (solveOn T xs ps d (demandRight T g.residual D r t) (F ∪ W) kr).2 ≤ _
                    omega
                  · rw [if_neg hb]
                    exact work_one hZ ((by decide : 4 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hA 3))

theorem solveWithCost_quasipolynomial {xs : List V} (hxs : xs.length ≤ Fintype.card V)
    (D F : Finset V) (k : ℕ) :
    (solveWithCost T xs D F k).2 ≤ 2 ^ (20000000 * ell (Fintype.card V) ^ 4) := by
  let n := Fintype.card V
  let l := ell n
  let d := depthParameter n * l
  let A := n + 2
  let K := K0 n
  have hA : 2 ≤ A := by unfold A; omega
  have hApos : 0 < A := by omega
  have hl : 1 ≤ l := ell_pos n
  have h₁ : A ≤ 2 ^ (l + 1) := by
    have hp : n < 2 ^ l := lt_two_pow_ell n
    have hpow : 1 ≤ 2 ^ l := Nat.pow_pos (by decide)
    unfold A
    rw [pow_succ', Nat.two_mul]
    omega
  unfold solveWithCost
  dsimp only
  by_cases hn : n ≤ k
  · rw [if_pos hn]
    exact Nat.pow_pos (by decide)
  rw [if_neg hn]
  have hps : (pairs xs).length ≤ n * n := by
    rw [pairs_length]
    exact Nat.mul_le_mul hxs hxs
  have hb := solveOn_steps (T := T) hxs hps d D F k
  have hroot : 2 + xs.length + (pairs xs).length ≤ A ^ 2 := by
    have h : 2 + n + n * n ≤ A ^ 2 := by unfold A; nlinarith [Nat.zero_le n]
    change xs.length ≤ n at hxs
    omega
  have he : workBase n ^ (d + 1) = A ^ ((K + 20) * (d + 1)) := by
    unfold workBase
    exact (pow_mul _ _ _).symm
  let e := (K + 20) * (d + 1)
  have he₂ : 2 ≤ e := by
    have h := Nat.mul_le_mul (show 2 ≤ K + 20 by omega) (show 1 ≤ d + 1 by omega)
    unfold e
    omega
  have B : (solveOn T xs (pairs xs) d D F k).2 ≤ A ^ e := by
    exact hb.trans_eq he
  have H : 2 + xs.length + (pairs xs).length +
      (solveOn T xs (pairs xs) d D F k).2 ≤ A ^ (e + 1) := by
    simpa only [Nat.mul_one] using (work_add hA
      (show 2 + xs.length + (pairs xs).length ≤ A ^ e * 1 by
        rw [Nat.mul_one]
        exact hroot.trans (Nat.pow_le_pow_right hApos he₂))
      (show (solveOn T xs (pairs xs) d D F k).2 ≤ A ^ e * 1 by simpa only [Nat.mul_one]))
  change _ ≤ 2 ^ (20000000 * l ^ 4)
  refine H.trans ?_
  refine (Nat.pow_le_pow_left h₁ (e + 1)).trans ?_
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  have hK : K = 8000 * l := rfl
  have hd : d = 1230 * l ^ 2 := by unfold d depthParameter l; ring
  have he' : e = (8000 * l + 20) * (1230 * l ^ 2 + 1) := by unfold e; rw [hK, hd]
  rw [he']
  have h₂ : l ≤ l ^ 2 := by nlinarith [Nat.mul_le_mul_left l hl]
  have h₃ : l ^ 2 ≤ l ^ 3 := by nlinarith [Nat.mul_le_mul_left (l ^ 2) hl]
  have h₄ : l ^ 3 ≤ l ^ 4 := by nlinarith [Nat.mul_le_mul_left (l ^ 3) hl]
  nlinarith

/-- Select a representative only to report one execution's work. The uniform bound
applies to every representative of the finite type's vertex list. -/
noncomputable def solveCost (T : Tournament V) (D F : Finset V) (k : ℕ) : ℕ :=
  (solveWithCost T (Finset.univ : Finset V).val.toList D F k).2

theorem solveCost_quasipolynomial :
    ∃ C : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W]
      (T : Tournament W) (D F : Finset W) (k : ℕ),
      solveCost T D F k ≤ 2 ^ (C * (Nat.log 2 (Fintype.card W) + 1) ^ 4) := by
  refine ⟨20000000, ?_⟩
  intro W _ _ T D F k
  apply solveWithCost_quasipolynomial
  rw [Multiset.length_toList]
  exact le_rfl



abbrev Thm41Vertex (W : Type*) := W ⊕ W ⊕ Fin 3

private def specialArc (a b : Fin 3) : Prop := b.val = (a.val + 1) % 3

private instance (a b : Fin 3) : Decidable (specialArc a b) :=
  inferInstanceAs (Decidable (_ = _))

private theorem special_irrefl : ∀ a : Fin 3, ¬ specialArc a a := by decide
private theorem special_asymm : ∀ a b : Fin 3, specialArc a b → ¬ specialArc b a := by decide
private theorem special_trichotomous : ∀ a b : Fin 3, a ≠ b → specialArc a b ∨ specialArc b a := by decide

private def thm41Adj {W : Type*} (T : Tournament W) : Thm41Vertex W → Thm41Vertex W → Prop
  | .inl a, .inl b => T.adj a b
  | .inl a, .inr (.inl b) => a = b ∨ T.adj a b
  | .inr (.inl a), .inl b => T.adj a b
  | .inr (.inl a), .inr (.inl b) => T.adj a b
  | .inl _, .inr (.inr b) => b ≠ 0
  | .inr (.inr a), .inl _ => a = 0
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inr (.inl _) => False
  | .inr (.inr a), .inr (.inr b) => specialArc a b

/-- The two copies and the directed three-cycle in Theorem 4.1. -/
def thm41Tournament (T : Tournament V) : Tournament (Thm41Vertex V) where
  adj := thm41Adj T
  irrefl := by
    rintro (a | a | a)
    · exact T.irrefl a
    · exact T.irrefl a
    · exact special_irrefl a
  asymm := by
    rintro (a | a | a) (b | b | b) h
    · exact T.asymm h
    · rcases h with h | h
      · subst b
        exact T.irrefl a
      · exact T.asymm h
    · exact h
    · intro hb
      rcases hb with hb | hb
      · subst b
        exact T.irrefl a h
      · exact T.asymm h hb
    · exact T.asymm h
    · exact id
    · intro hb
      exact hb h
    · exact h.elim
    · exact special_asymm a b h
  trichotomous := by
    rintro (a | a | a) (b | b | b) h
    · exact T.trichotomous (fun he => h (congrArg Sum.inl he))
    · by_cases he : a = b
      · exact Or.inl (Or.inl he)
      · exact (T.trichotomous he).imp Or.inr id
    · exact ne_or_eq b 0
    · by_cases he : b = a
      · exact Or.inr (Or.inl he)
      · exact (T.trichotomous (Ne.symm he)).imp id Or.inr
    · exact T.trichotomous (fun he => h (congrArg (fun x => Sum.inr (Sum.inl x)) he))
    · exact Or.inl trivial
    · exact eq_or_ne a 0
    · exact Or.inr trivial
    · exact special_trichotomous a b
        (fun he => h (congrArg (fun x => Sum.inr (Sum.inr x)) he))
  decidableAdj := by
    rintro (a | a | a) (b | b | b) <;> unfold thm41Adj <;> infer_instance

theorem thm41_strongly_connected [Nonempty V] (T : Tournament V)
    (u v : Thm41Vertex V) : Relation.ReflTransGen (thm41Tournament T).adj u v := by
  let x : Thm41Vertex V := .inr (.inr 0)
  let y : Thm41Vertex V := .inr (.inr 1)
  let z : Thm41Vertex V := .inr (.inr 2)
  let Reach := Relation.ReflTransGen (thm41Tournament T).adj
  have one {a b} (h : (thm41Tournament T).adj a b) : Reach a b :=
    Relation.ReflTransGen.single h
  have hxy : Reach x y := one (show specialArc 0 1 by decide)
  have hyz : Reach y z := one (show specialArc 1 2 by decide)
  have hzx : Reach z x := one (show specialArc 2 0 by decide)
  have hpaths (a : Thm41Vertex V) : Reach a x ∧ Reach x a := by
    rcases a with a | a | a
    · have hto : Reach x (.inl a) := one (show (0 : Fin 3) = 0 from rfl)
      have hmid : Reach (.inl a) (.inr (.inl a)) := one (Or.inl rfl)
      have hback : Reach (.inr (.inl a)) x := one trivial
      exact ⟨hmid.trans hback, hto⟩
    · have hto : Reach x (.inl a) := one (show (0 : Fin 3) = 0 from rfl)
      have hmid : Reach (.inl a) (.inr (.inl a)) := one (Or.inl rfl)
      exact ⟨one trivial, hto.trans hmid⟩
    · fin_cases a
      · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · exact ⟨hyz.trans hzx, hxy⟩
      · exact ⟨hzx, hxy.trans hyz⟩
  exact (hpaths u).1.trans (hpaths v).2

end TournamentP3StarQP

#print axioms TournamentP3StarQP.lemmaA_lipschitz
#print axioms TournamentP3StarQP.lemmaB_forward
#print axioms TournamentP3StarQP.lemmaE_triangle_radius
#print axioms TournamentP3StarQP.lemmaC_decoupling
#print axioms TournamentP3StarQP.lemmaD_empty_gap
#print axioms TournamentP3StarQP.solve_sound
#print axioms TournamentP3StarQP.solve_complete
#print axioms TournamentP3StarQP.solve_iff_full
#print axioms TournamentP3StarQP.solveWithCost_eq_solve
#print axioms TournamentP3StarQP.solveWithCost_quasipolynomial
#print axioms TournamentP3StarQP.solveCost_quasipolynomial
#print axioms TournamentP3StarQP.thm41_strongly_connected

