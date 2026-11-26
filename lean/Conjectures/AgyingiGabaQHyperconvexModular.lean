import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.ModularLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Resolution of Agyingi–Gaba Question `q:modular` (`arXiv:2611.32417v1`)

This file completely formalizes both parts of Question `q:modular` from
C. A. Agyingi and Y. U. Gaba, *Smyth completeness and nonexpansive iteration
in q-hyperconvex T₀-quasi-metric spaces* (`arXiv:2611.32417v1`, 25 Nov 2026):

1. Let `X = [0, 1]³` with `q(g, h) = max_{k} max(h_k - g_k, 0)` and
   specialization order `g ≤_q h ↔ q(g, h) = 0 ↔ ∀ k, h_k ≤ g_k`.
   Let `Y = {g ∈ [0, 1]³ : the two largest coordinates of g coincide}`
   (the Isbell-hull of the equilateral three-point space).
   We prove:
   - `Y_isQHyperconvex`: `(Y, q)` is `q`-hyperconvex (boundedness and `T₀` separation are proved in `qdist_le_one` and `qdist_T0`).
   - `Y_isModularLattice`: `(Y, ≤_q)` is a modular lattice (`IsModularLattice YSpec`).
   - `Y_not_distributive`: `(Y, ≤_q)` is not distributive (explicit `M₃` sublattice).
   - `Y_no_N5_sublattice`: `N₅` does not occur as a sublattice of `(Y, ≤_q)`.

2. Let `S = {g ∈ [0, 1]³ : g₂ ≤ max g₀ g₁}`.
   We prove:
   - `S_isQHyperconvex`: `(S, q)` is a bounded, `T₀`, `q`-hyperconvex quasi-metric space.
   - `S_has_N5_sublattice`: `(S, ≤_q)` contains an explicit `N₅` sublattice
     (hence is non-modular).

3. `agyingi_gaba_question_modular_resolution`: combined master theorem.
-/

namespace AgyingiGabaQHyperconvexModular

/-! ### 1. Carrier `[0, 1]³`, quasi-metric `q`, and `q`-hyperconvexity -/

/-- Points of `ℝ³` represented as `Fin 3 → ℝ`. -/
abbrev R3 := Fin 3 → ℝ

/-- Unit cube `[0, 1]³`. -/
def InCube (g : R3) : Prop :=
  ∀ k : Fin 3, 0 ≤ g k ∧ g k ≤ 1

/-- Quasi-metric `q(g, h) = max_{k ∈ {0,1,2}} max(h k - g k, 0)`. -/
def qdist (g h : R3) : ℝ :=
  max (max (h 0 - g 0) 0) (max (max (h 1 - g 1) 0) (max (h 2 - g 2) 0))

lemma qdist_nonneg (g h : R3) : 0 ≤ qdist g h := by
  unfold qdist
  exact le_trans (le_max_right _ _) (le_max_left _ _)

lemma qdist_self (g : R3) : qdist g g = 0 := by
  unfold qdist
  simp

lemma qdist_le_iff {g h : R3} {r : ℝ} (hr : 0 ≤ r) :
    qdist g h ≤ r ↔ ∀ k : Fin 3, h k - g k ≤ r := by
  unfold qdist
  constructor
  · intro hle k
    fin_cases k
    · exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hle)
    · exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hle))
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hle))
  · intro hk
    refine max_le (max_le (hk 0) hr) (max_le (max_le (hk 1) hr) (max_le (hk 2) hr))

lemma qdist_triangle (x y z : R3) : qdist x z ≤ qdist x y + qdist y z := by
  have hnn : 0 ≤ qdist x y + qdist y z := add_nonneg (qdist_nonneg x y) (qdist_nonneg y z)
  rw [qdist_le_iff hnn]
  intro k
  have h1 : y k - x k ≤ qdist x y := (qdist_le_iff (qdist_nonneg x y)).mp le_rfl k
  have h2 : z k - y k ≤ qdist y z := (qdist_le_iff (qdist_nonneg y z)).mp le_rfl k
  linarith

lemma qdist_eq_zero_iff (g h : R3) : qdist g h = 0 ↔ ∀ k : Fin 3, h k ≤ g k := by
  constructor
  · intro h0 k
    have hle := (qdist_le_iff le_rfl).mp (le_of_eq h0) k
    linarith
  · intro hk
    refine le_antisymm ?_ (qdist_nonneg g h)
    rw [qdist_le_iff le_rfl]
    intro k
    linarith [hk k]

/-- `T₀` separation property for `qdist`. -/
lemma qdist_T0 {g h : R3} (h1 : qdist g h = 0) (h2 : qdist h g = 0) : g = h := by
  rw [qdist_eq_zero_iff] at h1 h2
  funext k
  exact le_antisymm (h2 k) (h1 k)

/-- Boundedness of `qdist` on `[0, 1]³`. -/
lemma qdist_le_one {g h : R3} (hg : InCube g) (hh : InCube h) : qdist g h ≤ 1 := by
  rw [qdist_le_iff (by norm_num)]
  intro k
  linarith [(hg k).1, (hh k).2]

/-- Definition of a `q`-hyperconvex subset `F ⊆ [0, 1]³` (for arbitrary index types `ι`):
every compatible family of double balls has a common point in `F`. -/
def IsQHyperconvex (F : Set R3) : Prop :=
  ∀ {ι : Type} (y : ι → R3) (r s : ι → ℝ),
    (∀ i, y i ∈ F) →
    (∀ i, 0 ≤ r i) →
    (∀ i, 0 ≤ s i) →
    (∀ i j, qdist (y i) (y j) ≤ r i + s j) →
    ∃ z ∈ F, ∀ i, qdist (y i) z ≤ r i ∧ qdist z (y i) ≤ s i

/-- Helper: `max` and `min` of the 3 coordinates of `g : R3`. -/
def max3 (g : R3) : ℝ := max (g 0) (max (g 1) (g 2))
def min3 (g : R3) : ℝ := min (g 0) (min (g 1) (g 2))

/-- Coordinatewise maximum and minimum on `R3`. -/
def cmax (g h : R3) : R3 := fun k => max (g k) (h k)
def cmin (g h : R3) : R3 := fun k => min (g k) (h k)

/-! ### 2. Subspaces `Y` and `S` and their deflationary retractions -/

/-- `Y = {g ∈ [0, 1]³ : the two largest coordinates of g coincide}`. -/
def InY (g : R3) : Prop :=
  InCube g ∧
    ((g 0 = g 1 ∧ g 2 ≤ g 0) ∨
     (g 0 = g 2 ∧ g 1 ≤ g 0) ∨
     (g 1 = g 2 ∧ g 0 ≤ g 1))

/-- `S = {g ∈ [0, 1]³ : g 2 ≤ max (g 0) (g 1)}`. -/
def InS (g : R3) : Prop :=
  InCube g ∧ g 2 ≤ max (g 0) (g 1)

/-- Retraction `ρ_Y(g)_k = min(g_k, max_{j ≠ k} g_j)`. -/
def rhoY (g : R3) : R3
  | ⟨0, _⟩ => min (g 0) (max (g 1) (g 2))
  | ⟨1, _⟩ => min (g 1) (max (g 0) (g 2))
  | ⟨2, _⟩ => min (g 2) (max (g 0) (g 1))

/-- Retraction `ρ_S(g) = (g 0, g 1, min (g 2) (max (g 0) (g 1)))`. -/
def rhoS (g : R3) : R3
  | ⟨0, _⟩ => g 0
  | ⟨1, _⟩ => g 1
  | ⟨2, _⟩ => min (g 2) (max (g 0) (g 1))

private lemma rhoY_0 (g : R3) : rhoY g 0 = min (g 0) (max (g 1) (g 2)) := rfl
private lemma rhoY_1 (g : R3) : rhoY g 1 = min (g 1) (max (g 0) (g 2)) := rfl
private lemma rhoY_2 (g : R3) : rhoY g 2 = min (g 2) (max (g 0) (g 1)) := rfl

private lemma rhoS_0 (g : R3) : rhoS g 0 = g 0 := rfl
private lemma rhoS_1 (g : R3) : rhoS g 1 = g 1 := rfl
private lemma rhoS_2 (g : R3) : rhoS g 2 = min (g 2) (max (g 0) (g 1)) := rfl

lemma rhoY_le (g : R3) (k : Fin 3) : rhoY g k ≤ g k := by
  fin_cases k <;> exact min_le_left _ _

lemma rhoY_mono {g h : R3} (hgh : ∀ k, g k ≤ h k) (k : Fin 3) : rhoY g k ≤ rhoY h k := by
  fin_cases k
  · exact min_le_min (hgh 0) (max_le_max (hgh 1) (hgh 2))
  · exact min_le_min (hgh 1) (max_le_max (hgh 0) (hgh 2))
  · exact min_le_min (hgh 2) (max_le_max (hgh 0) (hgh 1))

lemma rhoY_inY {g : R3} (hg : InCube g) : InY (rhoY g) := by
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · exact ⟨le_min (hg 0).1 (le_trans (hg 1).1 (le_max_left _ _)),
        le_trans (min_le_left _ _) (hg 0).2⟩
    · exact ⟨le_min (hg 1).1 (le_trans (hg 0).1 (le_max_left _ _)),
        le_trans (min_le_left _ _) (hg 1).2⟩
    · exact ⟨le_min (hg 2).1 (le_trans (hg 0).1 (le_max_left _ _)),
        le_trans (min_le_left _ _) (hg 2).2⟩
  · rcases le_total (g 0) (g 1) with h01 | h10
    · rcases le_total (g 1) (g 2) with h12 | h21
      · -- g 0 ≤ g 1 ≤ g 2
        right; right
        simp only [rhoY_0, rhoY_1, rhoY_2, max_eq_right h12, max_eq_right (le_trans h01 h12),
          max_eq_right h01, min_eq_left h12, min_eq_right h12]
        exact ⟨trivial, le_trans (min_le_left _ _) h01⟩
      · rcases le_total (g 0) (g 2) with h02 | h20
        · -- g 0 ≤ g 2 ≤ g 1
          right; right
          simp only [rhoY_0, rhoY_1, rhoY_2, max_eq_left h21, max_eq_right h02,
            max_eq_right h01, min_eq_left h01, min_eq_right h21, min_eq_left h21]
          exact ⟨trivial, h02⟩
        · -- g 2 ≤ g 0 ≤ g 1
          left
          simp only [rhoY_0, rhoY_1, rhoY_2, max_eq_left h21, max_eq_left h20,
            max_eq_right h01, min_eq_left h01, min_eq_right h01, min_eq_left (le_trans h20 h01)]
          exact ⟨trivial, h20⟩
    · rcases le_total (g 0) (g 2) with h02 | h20
      · -- g 1 ≤ g 0 ≤ g 2
        right; left
        simp only [rhoY_0, rhoY_1, rhoY_2, max_eq_right (le_trans h10 h02), max_eq_right h02,
          max_eq_left h10, min_eq_left h02, min_eq_left (le_trans h10 h02), min_eq_right h02]
        exact ⟨trivial, h10⟩
      · rcases le_total (g 1) (g 2) with h12 | h21
        · -- g 1 ≤ g 2 ≤ g 0
          right; left
          simp only [rhoY_0, rhoY_1, rhoY_2, max_eq_right h12, max_eq_left h20,
            max_eq_left h10, min_eq_right h20, min_eq_left (le_trans h12 h20), min_eq_left h20]
          exact ⟨trivial, h12⟩
        · -- g 2 ≤ g 1 ≤ g 0
          left
          simp only [rhoY_0, rhoY_1, rhoY_2, max_eq_left h21, max_eq_left h20,
            max_eq_left h10, min_eq_right h10, min_eq_left h10, min_eq_left (le_trans h21 h10)]
          exact ⟨trivial, h21⟩

lemma rhoY_fix {g : R3} (hg : InY g) : rhoY g = g := by
  funext k
  rcases hg.2 with ⟨h01, h20⟩ | ⟨h02, h10⟩ | ⟨h12, h01⟩
  · match k with
    | ⟨0, _⟩ => exact min_eq_left (le_trans (le_of_eq h01) (le_max_left _ _))
    | ⟨1, _⟩ => exact min_eq_left (le_trans (le_of_eq h01.symm) (le_max_left _ _))
    | ⟨2, _⟩ => exact min_eq_left (le_trans h20 (le_max_left _ _))
  · match k with
    | ⟨0, _⟩ => exact min_eq_left (le_trans (le_of_eq h02) (le_max_right _ _))
    | ⟨1, _⟩ => exact min_eq_left (le_trans h10 (le_max_left _ _))
    | ⟨2, _⟩ => exact min_eq_left (le_trans (le_of_eq h02.symm) (le_max_left _ _))
  · match k with
    | ⟨0, _⟩ => exact min_eq_left (le_trans h01 (le_max_left _ _))
    | ⟨1, _⟩ => exact min_eq_left (le_trans (le_of_eq h12) (le_max_right _ _))
    | ⟨2, _⟩ => exact min_eq_left (le_trans (le_of_eq h12.symm) (le_max_right _ _))

lemma cmax_inCube {g h : R3} (hg : InCube g) (hh : InCube h) : InCube (cmax g h) := fun k =>
  ⟨le_trans (hg k).1 (le_max_left _ _), max_le (hg k).2 (hh k).2⟩

lemma cmin_inCube {g h : R3} (hg : InCube g) (hh : InCube h) : InCube (cmin g h) := fun k =>
  ⟨le_min (hg k).1 (hh k).1, le_trans (min_le_left _ _) (hg k).2⟩

lemma cmax_inY {g h : R3} (hg : InY g) (hh : InY h) : InY (cmax g h) := by
  have hfix : rhoY (cmax g h) = cmax g h := by
    funext k
    refine le_antisymm (rhoY_le _ k) ?_
    have h1 : g k ≤ rhoY (cmax g h) k :=
      calc g k = rhoY g k := (congr_fun (rhoY_fix hg) k).symm
        _ ≤ rhoY (cmax g h) k := rhoY_mono (fun j => le_max_left _ _) k
    have h2 : h k ≤ rhoY (cmax g h) k :=
      calc h k = rhoY h k := (congr_fun (rhoY_fix hh) k).symm
        _ ≤ rhoY (cmax g h) k := rhoY_mono (fun j => le_max_right _ _) k
    exact max_le h1 h2
  rw [← hfix]
  exact rhoY_inY (cmax_inCube hg.1 hh.1)

lemma rhoS_le (g : R3) (k : Fin 3) : rhoS g k ≤ g k := by
  fin_cases k
  · exact le_rfl
  · exact le_rfl
  · exact min_le_left _ _

lemma rhoS_mono {g h : R3} (hgh : ∀ k, g k ≤ h k) (k : Fin 3) : rhoS g k ≤ rhoS h k := by
  fin_cases k
  · exact hgh 0
  · exact hgh 1
  · exact min_le_min (hgh 2) (max_le_max (hgh 0) (hgh 1))

lemma rhoS_inS {g : R3} (hg : InCube g) : InS (rhoS g) := by
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · exact hg 0
    · exact hg 1
    · exact ⟨le_min (hg 2).1 (le_trans (hg 0).1 (le_max_left _ _)),
        le_trans (min_le_left _ _) (hg 2).2⟩
  · exact min_le_right _ _

lemma rhoS_fix {g : R3} (hg : InS g) : rhoS g = g := by
  funext k
  fin_cases k
  · rfl
  · rfl
  · exact min_eq_left hg.2

lemma cmax_inS {g h : R3} (hg : InS g) (hh : InS h) : InS (cmax g h) := by
  refine ⟨cmax_inCube hg.1 hh.1, ?_⟩
  simp only [cmax]
  refine max_le ?_ ?_
  · exact le_trans hg.2 (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact le_trans hh.2 (max_le_max (le_max_right _ _) (le_max_right _ _))

/-! ### 3. Specialization order lattices `(YSpec, ≤_q)` and `(SSpec, ≤_q)` -/

/-- The space `Y` equipped with its specialization order `≤_q` (`g ≤_q h ↔ q(g, h) = 0`). -/
@[ext]
structure YSpec where
  val : R3
  prop : InY val

/-- The space `S` equipped with its specialization order `≤_q` (`g ≤_q h ↔ q(g, h) = 0`). -/
@[ext]
structure SSpec where
  val : R3
  prop : InS val

instance : LE YSpec where
  le g h := qdist g.val h.val = 0

lemma YSpec.le_iff_coord (g h : YSpec) : g ≤ h ↔ ∀ k : Fin 3, h.val k ≤ g.val k :=
  qdist_eq_zero_iff g.val h.val

instance : PartialOrder YSpec where
  le_refl g := qdist_self g.val
  le_trans a b c hab hbc := by
    rw [YSpec.le_iff_coord] at hab hbc ⊢
    intro k; exact le_trans (hbc k) (hab k)
  le_antisymm a b hab hba := YSpec.ext (qdist_T0 hab hba)

instance : Lattice YSpec where
  sup g h := ⟨rhoY (cmin g.val h.val), rhoY_inY (cmin_inCube g.prop.1 h.prop.1)⟩
  inf g h := ⟨cmax g.val h.val, cmax_inY g.prop h.prop⟩
  le_sup_left g h := by
    rw [YSpec.le_iff_coord]; intro k
    exact le_trans (rhoY_le _ k) (min_le_left _ _)
  le_sup_right g h := by
    rw [YSpec.le_iff_coord]; intro k
    exact le_trans (rhoY_le _ k) (min_le_right _ _)
  sup_le a b c hac hbc := by
    rw [YSpec.le_iff_coord] at hac hbc ⊢
    intro k
    have hmin : ∀ j, c.val j ≤ cmin a.val b.val j := fun j => le_min (hac j) (hbc j)
    simpa [rhoY_fix c.prop] using rhoY_mono hmin k
  inf_le_left g h := by
    rw [YSpec.le_iff_coord]; intro k; exact le_max_left _ _
  inf_le_right g h := by
    rw [YSpec.le_iff_coord]; intro k; exact le_max_right _ _
  le_inf a b c hab hac := by
    rw [YSpec.le_iff_coord] at hab hac ⊢
    intro k; exact max_le (hab k) (hac k)

instance : LE SSpec where
  le g h := qdist g.val h.val = 0

lemma SSpec.le_iff_coord (g h : SSpec) : g ≤ h ↔ ∀ k : Fin 3, h.val k ≤ g.val k :=
  qdist_eq_zero_iff g.val h.val

instance : PartialOrder SSpec where
  le_refl g := qdist_self g.val
  le_trans a b c hab hbc := by
    rw [SSpec.le_iff_coord] at hab hbc ⊢
    intro k; exact le_trans (hbc k) (hab k)
  le_antisymm a b hab hba := SSpec.ext (qdist_T0 hab hba)

instance : Lattice SSpec where
  sup g h := ⟨rhoS (cmin g.val h.val), rhoS_inS (cmin_inCube g.prop.1 h.prop.1)⟩
  inf g h := ⟨cmax g.val h.val, cmax_inS g.prop h.prop⟩
  le_sup_left g h := by
    rw [SSpec.le_iff_coord]; intro k
    exact le_trans (rhoS_le _ k) (min_le_left _ _)
  le_sup_right g h := by
    rw [SSpec.le_iff_coord]; intro k
    exact le_trans (rhoS_le _ k) (min_le_right _ _)
  sup_le a b c hac hbc := by
    rw [SSpec.le_iff_coord] at hac hbc ⊢
    intro k
    have hmin : ∀ j, c.val j ≤ cmin a.val b.val j := fun j => le_min (hac j) (hbc j)
    simpa [rhoS_fix c.prop] using rhoS_mono hmin k
  inf_le_left g h := by
    rw [SSpec.le_iff_coord]; intro k; exact le_max_left _ _
  inf_le_right g h := by
    rw [SSpec.le_iff_coord]; intro k; exact le_max_right _ _
  le_inf a b c hab hac := by
    rw [SSpec.le_iff_coord] at hab hac ⊢
    intro k; exact max_le (hab k) (hac k)

/-! ### 4. Theorem A: `(YSpec, ≤_q)` is modular, non-distributive, and `N₅`-free -/

/-- Valuation `v(g) = max g + min g`. -/
def valV (g : R3) : ℝ := max3 g + min3 g

/-- Key overlap identity on `Y`: `max_k min(g_k, h_k) = min(max g, max h)`. -/
lemma max3_cmin_eq_min_max3 {g h : R3} (hg : InY g) (hh : InY h) :
    max3 (cmin g h) = min (max3 g) (max3 h) := by
  refine le_antisymm ?_ ?_
  · unfold max3 cmin
    refine max_le ?_ (max_le ?_ ?_)
    · exact min_le_min (le_max_left _ _) (le_max_left _ _)
    · exact min_le_min (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact min_le_min (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _))
  · -- Each of `g, h` achieves its maximum on a 2-element subset of `{0,1,2}`;
    -- any two 2-element subsets overlap at some coordinate `k`.
    have hmax_of : ∀ x : R3,
        (x 0 = x 1 ∧ x 2 ≤ x 0 → max3 x = x 0) ∧
        (x 0 = x 2 ∧ x 1 ≤ x 0 → max3 x = x 0) ∧
        (x 1 = x 2 ∧ x 0 ≤ x 1 → max3 x = x 1) := by
      intro x
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨h01, h20⟩; unfold max3; rw [← h01, max_eq_left h20, max_self]
      · rintro ⟨h02, h10⟩; unfold max3; rw [← h02, max_eq_right h10, max_self]
      · rintro ⟨h12, h01⟩; unfold max3; rw [← h12, max_self, max_eq_right h01]
    rcases hg.2 with hga | hgb | hgc <;> rcases hh.2 with hha | hhb | hhc
    · -- both attain max at 0 (and 1)
      rw [(hmax_of g).1 hga, (hmax_of h).1 hha]
      exact le_max_left _ _
    · -- overlap at 0
      rw [(hmax_of g).1 hga, (hmax_of h).2.1 hhb]
      exact le_max_left _ _
    · -- overlap at 1
      rw [(hmax_of g).1 hga, (hmax_of h).2.2 hhc, hga.1]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · -- overlap at 0
      rw [(hmax_of g).2.1 hgb, (hmax_of h).1 hha]
      exact le_max_left _ _
    · -- overlap at 0
      rw [(hmax_of g).2.1 hgb, (hmax_of h).2.1 hhb]
      exact le_max_left _ _
    · -- overlap at 2
      rw [(hmax_of g).2.1 hgb, (hmax_of h).2.2 hhc, hgb.1, hhc.1]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    · -- overlap at 1
      rw [(hmax_of g).2.2 hgc, (hmax_of h).1 hha, hha.1]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · -- overlap at 2
      rw [(hmax_of g).2.2 hgc, (hmax_of h).2.1 hhb, hgc.1, hhb.1]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    · -- overlap at 1
      rw [(hmax_of g).2.2 hgc, (hmax_of h).2.2 hhc]
      exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- Formula `valV (rhoY x) = x 0 + x 1 + x 2 - max3 x` for every `x : R3`. -/
lemma valV_rhoY (x : R3) : valV (rhoY x) = x 0 + x 1 + x 2 - max3 x := by
  unfold valV max3 min3
  simp only [rhoY_0, rhoY_1, rhoY_2, max_def, min_def]
  split_ifs <;> linarith

lemma valV_of_inY {g : R3} (hg : InY g) : valV g = g 0 + g 1 + g 2 - max3 g := by
  have h := valV_rhoY g
  rwa [rhoY_fix hg] at h

/-- Valuation identity on `(YSpec, ≤_q)`: `v(g ⊔ h) + v(g ⊓ h) = v(g) + v(h)`. -/
lemma valV_valuation (g h : YSpec) :
    valV (g ⊔ h).val + valV (g ⊓ h).val = valV g.val + valV h.val := by
  change valV (rhoY (cmin g.val h.val)) + valV (cmax g.val h.val) = valV g.val + valV h.val
  rw [valV_rhoY, valV_of_inY (cmax_inY g.prop h.prop), valV_of_inY g.prop, valV_of_inY h.prop]
  rw [max3_cmin_eq_min_max3 g.prop h.prop]
  have hmax_cmax : max3 (cmax g.val h.val) = max (max3 g.val) (max3 h.val) := by
    unfold max3 cmax
    refine le_antisymm ?_ ?_
    · refine max_le (max_le_max (le_max_left _ _) (le_max_left _ _))
        (max_le (max_le_max (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_trans (le_max_left _ _) (le_max_right _ _)))
        (max_le_max (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_trans (le_max_right _ _) (le_max_right _ _))))
    · refine max_le ?_ ?_
      · exact max_le (le_trans (le_max_left _ _) (le_max_left _ _))
          (max_le (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
            (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
      · exact max_le (le_trans (le_max_right _ _) (le_max_left _ _))
          (max_le (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  rw [hmax_cmax]
  have h0 : min (g.val 0) (h.val 0) + max (g.val 0) (h.val 0) = g.val 0 + h.val 0 :=
    min_add_max _ _
  have h1 : min (g.val 1) (h.val 1) + max (g.val 1) (h.val 1) = g.val 1 + h.val 1 :=
    min_add_max _ _
  have h2 : min (g.val 2) (h.val 2) + max (g.val 2) (h.val 2) = g.val 2 + h.val 2 :=
    min_add_max _ _
  have hm : min (max3 g.val) (max3 h.val) + max (max3 g.val) (max3 h.val) =
      max3 g.val + max3 h.val := min_add_max _ _
  dsimp [cmin, cmax]
  linarith

/-- Strict antimonotonicity of `valV` on `(YSpec, ≤_q)`:
`g ≤ h` and `valV g.val = valV h.val` implies `g = h`. -/
lemma eq_of_le_of_valV_eq {g h : YSpec} (hle : g ≤ h) (hv : valV g.val = valV h.val) :
    g = h := by
  rw [YSpec.le_iff_coord] at hle
  have hmax_le : max3 h.val ≤ max3 g.val := by
    unfold max3
    exact max_le_max (hle 0) (max_le_max (hle 1) (hle 2))
  have hmin_le : min3 h.val ≤ min3 g.val := by
    unfold min3
    exact min_le_min (hle 0) (min_le_min (hle 1) (hle 2))
  have hmax_eq : max3 h.val = max3 g.val := by unfold valV at hv; linarith
  have hmin_eq : min3 h.val = min3 g.val := by unfold valV at hv; linarith
  have hsum_eq : h.val 0 + h.val 1 + h.val 2 = g.val 0 + g.val 1 + g.val 2 := by
    have hg := valV_of_inY g.prop
    have hh := valV_of_inY h.prop
    linarith
  apply YSpec.ext
  funext k
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have he0 : g.val 0 = h.val 0 := by linarith
  have he1 : g.val 1 = h.val 1 := by linarith
  have he2 : g.val 2 = h.val 2 := by linarith
  match k with
  | ⟨0, _⟩ => exact he0
  | ⟨1, _⟩ => exact he1
  | ⟨2, _⟩ => exact he2

/-- **Theorem A (Part 1):** The specialization order `(Y, ≤_q)` of the Isbell-hull
of the equilateral three-point space is a modular lattice. -/
instance Y_isModularLattice : IsModularLattice YSpec where
  sup_inf_le_assoc_of_le {a} b {c} hac := by
    have hle : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ c := by
      refine le_inf (sup_le le_sup_left (le_trans inf_le_left le_sup_right))
        (sup_le hac inf_le_right)
    have h1 : a ⊓ (b ⊓ c) = a ⊓ b := by
      rw [← inf_assoc, inf_comm a b, inf_assoc, inf_eq_left.mpr hac, inf_comm]
    have h2 : (a ⊔ b) ⊔ c = b ⊔ c := by
      calc (a ⊔ b) ⊔ c = b ⊔ (a ⊔ c) := by rw [sup_comm a b, sup_assoc]
        _ = b ⊔ c := by rw [sup_eq_right.mpr hac]
    have hv_l : valV (a ⊔ (b ⊓ c)).val =
        valV a.val + valV b.val + valV c.val - valV (b ⊔ c).val - valV (a ⊓ b).val := by
      have hv1 := valV_valuation a (b ⊓ c)
      have hv2 := valV_valuation b c
      rw [h1] at hv1
      linarith
    have hv_r : valV ((a ⊔ b) ⊓ c).val =
        valV a.val + valV b.val + valV c.val - valV (b ⊔ c).val - valV (a ⊓ b).val := by
      have hv1 := valV_valuation (a ⊔ b) c
      have hv2 := valV_valuation a b
      rw [h2] at hv1
      linarith
    have heq : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ c := eq_of_le_of_valV_eq hle (hv_l.trans hv_r.symm)
    exact le_of_eq heq.symm

/-- Predicate asserting that a lattice `L` contains a five-element `N₅` sublattice. -/
def HasN5Sublattice (L : Type*) [Lattice L] : Prop :=
  ∃ (t c a b o : L),
    c < a ∧
    ¬ (c ≤ b) ∧ ¬ (b ≤ c) ∧
    ¬ (a ≤ b) ∧ ¬ (b ≤ a) ∧
    c ⊓ b = t ∧ a ⊓ b = t ∧
    c ⊔ b = o ∧ a ⊔ b = o

/-- **Theorem A (Corollary):** `N₅` does not occur as a sublattice of `(Y, ≤_q)`. -/
theorem Y_no_N5_sublattice : ¬ HasN5Sublattice YSpec := by
  rintro ⟨t, c, a, b, o, hca, _, _, _, _, hcb, hab, hcbo, habo⟩
  have hmod : (c ⊔ b) ⊓ a = c ⊔ (b ⊓ a) := sup_inf_assoc_of_le b (le_of_lt hca)
  have htc : t ≤ c := by rw [← hcb]; exact inf_le_left
  have hao : a ≤ o := by rw [← habo]; exact le_sup_left
  have hlhs : c ⊔ (b ⊓ a) = c := by
    rw [inf_comm, hab, sup_eq_left.mpr htc]
  have hrhs : (c ⊔ b) ⊓ a = a := by
    rw [hcbo, inf_eq_right.mpr hao]
  rw [hrhs, hlhs] at hmod
  exact ne_of_lt hca hmod.symm

/-- Helper constructor for explicit points in `R3` with definitional projections. -/
private def vec3 (x y z : ℝ) : R3
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y
  | ⟨2, _⟩ => z

/-- **Theorem A (Part 2):** `(Y, ≤_q)` is not distributive (explicit `M₃` sublattice). -/
theorem Y_not_distributive :
    ∃ a b c : YSpec, a ⊓ (b ⊔ c) ≠ (a ⊓ b) ⊔ (a ⊓ c) := by
  let e1 : YSpec := ⟨vec3 0 1 1, ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3], Or.inr (Or.inr ⟨rfl, by norm_num [vec3]⟩)⟩⟩
  let e2 : YSpec := ⟨vec3 1 0 1, ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3], Or.inr (Or.inl ⟨rfl, by norm_num [vec3]⟩)⟩⟩
  let e3 : YSpec := ⟨vec3 1 1 0, ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3], Or.inl ⟨rfl, by norm_num [vec3]⟩⟩⟩
  refine ⟨e1, e2, e3, ?_⟩
  intro heq
  have h0 := congr_fun (congr_arg YSpec.val heq) 0
  change max (e1.val 0) (rhoY (cmin e2.val e3.val) 0) =
    rhoY (cmin (cmax e1.val e2.val) (cmax e1.val e3.val)) 0 at h0
  norm_num [e1, e2, e3, rhoY_0, cmin, cmax, vec3] at h0

/-! ### 5. Theorem B: `q`-hyperconvexity of `Y` and `S`, and explicit `N₅` in `(S, ≤_q)` -/

/-- Helper: given a compatible nonempty double-ball family in `[0, 1]³`, the box
`[L k, U k]` is nonempty and contained in `[0, 1]`. -/
private lemma double_ball_box {ι : Type} [Nonempty ι]
    (y : ι → R3) (r s : ι → ℝ)
    (hcube : ∀ i, InCube (y i))
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i)
    (hcompat : ∀ i j, qdist (y i) (y j) ≤ r i + s j) :
    let L : R3 := fun k => max 0 (⨆ i, (y i k - s i))
    let U : R3 := fun k => min 1 (⨅ i, (y i k + r i))
    InCube U ∧ (∀ k, L k ≤ U k) ∧
    (∀ k i, y i k - s i ≤ L k ∧ U k ≤ y i k + r i) := by
  intro L U
  have hbddA : ∀ k, BddAbove (Set.range fun i => y i k - s i) := fun k =>
    ⟨1, by rintro _ ⟨i, rfl⟩; linarith [(hcube i k).2, hs i]⟩
  have hbddB : ∀ k, BddBelow (Set.range fun i => y i k + r i) := fun k =>
    ⟨0, by rintro _ ⟨i, rfl⟩; linarith [(hcube i k).1, hr i]⟩
  have hLU_bounds : ∀ k i, y i k - s i ≤ L k ∧ U k ≤ y i k + r i := fun k i =>
    ⟨le_trans (le_ciSup (hbddA k) i) (le_max_right _ _),
     le_trans (min_le_right _ _) (ciInf_le (hbddB k) i)⟩
  have h0U : ∀ k, 0 ≤ U k := fun k =>
    le_min zero_le_one (le_ciInf fun i => by linarith [(hcube i k).1, hr i])
  have hU1 : ∀ k, U k ≤ 1 := fun k => min_le_left _ _
  have hLU : ∀ k, L k ≤ U k := by
    intro k
    refine max_le (h0U k) (le_min ?_ ?_)
    · exact ciSup_le fun i => by linarith [(hcube i k).2, hs i]
    · refine le_ciInf fun j => ciSup_le fun i => ?_
      have hq := (qdist_le_iff (add_nonneg (hr j) (hs i))).mp (hcompat j i) k
      linarith
  exact ⟨fun k => ⟨h0U k, hU1 k⟩, hLU, hLU_bounds⟩

/-- **Theorem B (Part 1):** `(S, q)` is a bounded `q`-hyperconvex `T₀`-quasi-metric space. -/
theorem S_isQHyperconvex : IsQHyperconvex {g : R3 | InS g} := by
  intro ι y r s hy hr hs hcompat
  by_cases hne : Nonempty ι
  · have hbox := double_ball_box y r s (fun i => (hy i).1) hr hs hcompat
    dsimp only at hbox
    set L : R3 := fun k => max 0 (⨆ i, (y i k - s i))
    set U : R3 := fun k => min 1 (⨅ i, (y i k + r i))
    rcases hbox with ⟨hUcube, hLU, hbounds⟩
    have hbddA : ∀ k, BddAbove (Set.range fun i => y i k - s i) := fun k =>
      ⟨1, by rintro _ ⟨i, rfl⟩; linarith [((hy i).1 k).2, hs i]⟩
    refine ⟨rhoS U, rhoS_inS hUcube, ?_⟩
    have hz_ge : ∀ k, L k ≤ rhoS U k := by
      intro k
      fin_cases k
      · exact hLU 0
      · exact hLU 1
      · refine le_min (hLU 2) ?_
        refine max_le (le_trans (hUcube 0).1 (le_max_left _ _)) ?_
        refine ciSup_le fun i => ?_
        have hS : y i 2 ≤ max (y i 0) (y i 1) := (hy i).2
        rcases le_total (y i 0) (y i 1) with h01 | h10
        · rw [max_eq_right h01] at hS
          calc
            y i 2 - s i ≤ y i 1 - s i := by linarith
            _ ≤ L 1 := (hbounds 1 i).1
            _ ≤ U 1 := hLU 1
            _ ≤ max (U 0) (U 1) := le_max_right _ _
        · rw [max_eq_left h10] at hS
          calc
            y i 2 - s i ≤ y i 0 - s i := by linarith
            _ ≤ L 0 := (hbounds 0 i).1
            _ ≤ U 0 := hLU 0
            _ ≤ max (U 0) (U 1) := le_max_left _ _
    intro i
    constructor
    · rw [qdist_le_iff (hr i)]
      intro k
      have h1 : rhoS U k ≤ U k := rhoS_le U k
      have h2 : U k ≤ y i k + r i := (hbounds k i).2
      linarith
    · rw [qdist_le_iff (hs i)]
      intro k
      have h1 : y i k - s i ≤ L k := (hbounds k i).1
      have h2 : L k ≤ rhoS U k := hz_ge k
      linarith
  · refine ⟨fun _ => 0, ⟨fun _ => ⟨le_rfl, zero_le_one⟩, by simp⟩, ?_⟩
    intro i
    exact (hne ⟨i⟩).elim

/-- For completeness, `(Y, q)` is also `q`-hyperconvex (reproving Lemma `lem:Y` inline). -/
theorem Y_isQHyperconvex : IsQHyperconvex {g : R3 | InY g} := by
  intro ι y r s hy hr hs hcompat
  by_cases hne : Nonempty ι
  · have hbox := double_ball_box y r s (fun i => (hy i).1) hr hs hcompat
    dsimp only at hbox
    set L : R3 := fun k => max 0 (⨆ i, (y i k - s i))
    set U : R3 := fun k => min 1 (⨅ i, (y i k + r i))
    rcases hbox with ⟨hUcube, hLU, hbounds⟩
    refine ⟨rhoY U, rhoY_inY hUcube, ?_⟩
    have hz_ge : ∀ k, L k ≤ rhoY U k := by
      intro k
      have hmono : ∀ j, y j k - s j ≤ rhoY U k := by
        intro j
        have hle : ∀ m, y j m - s j ≤ U m := fun m => le_trans (hbounds m j).1 (hLU m)
        -- Since `y j ∈ Y`, for every `k` we have `y j k ≤ max_{m ≠ k} y j m`.
        have hy_self : ∀ m, y j m = rhoY (y j) m := fun m => (congr_fun (rhoY_fix (hy j)) m).symm
        match k with
        | ⟨0, _⟩ =>
          have h0 : y j 0 ≤ max (y j 1) (y j 2) := by rw [hy_self 0]; exact min_le_right _ _
          refine le_min (hle 0) ?_
          rcases le_total (y j 1) (y j 2) with h12 | h21
          · rw [max_eq_right h12] at h0
            exact le_trans (by linarith : y j 0 - s j ≤ y j 2 - s j) (le_trans (hle 2) (le_max_right _ _))
          · rw [max_eq_left h21] at h0
            exact le_trans (by linarith : y j 0 - s j ≤ y j 1 - s j) (le_trans (hle 1) (le_max_left _ _))
        | ⟨1, _⟩ =>
          have h1 : y j 1 ≤ max (y j 0) (y j 2) := by rw [hy_self 1]; exact min_le_right _ _
          refine le_min (hle 1) ?_
          rcases le_total (y j 0) (y j 2) with h02 | h20
          · rw [max_eq_right h02] at h1
            exact le_trans (by linarith : y j 1 - s j ≤ y j 2 - s j) (le_trans (hle 2) (le_max_right _ _))
          · rw [max_eq_left h20] at h1
            exact le_trans (by linarith : y j 1 - s j ≤ y j 0 - s j) (le_trans (hle 0) (le_max_left _ _))
        | ⟨2, _⟩ =>
          have h2 : y j 2 ≤ max (y j 0) (y j 1) := by rw [hy_self 2]; exact min_le_right _ _
          refine le_min (hle 2) ?_
          rcases le_total (y j 0) (y j 1) with h01 | h10
          · rw [max_eq_right h01] at h2
            exact le_trans (by linarith : y j 2 - s j ≤ y j 1 - s j) (le_trans (hle 1) (le_max_right _ _))
          · rw [max_eq_left h10] at h2
            exact le_trans (by linarith : y j 2 - s j ≤ y j 0 - s j) (le_trans (hle 0) (le_max_left _ _))
      exact max_le ((rhoY_inY hUcube).1 k).1 (ciSup_le hmono)
    intro i
    constructor
    · rw [qdist_le_iff (hr i)]
      intro k
      linarith [rhoY_le U k, (hbounds k i).2]
    · rw [qdist_le_iff (hs i)]
      intro k
      linarith [(hbounds k i).1, hz_ge k]
  · refine ⟨fun _ => 0, ⟨fun _ => ⟨le_rfl, zero_le_one⟩, Or.inl ⟨rfl, le_rfl⟩⟩, ?_⟩
    intro i
    exact (hne ⟨i⟩).elim

/-- **Theorem B (Part 2):** The specialization order `(S, ≤_q)` contains an explicit
`N₅` sublattice `{t, c, a, b, o}` (and is therefore not modular). -/
theorem S_has_N5_sublattice : HasN5Sublattice SSpec := by
  let t : SSpec := ⟨vec3 (1 / 4) (1 / 4) (1 / 4),
    ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3],
     by norm_num [vec3]⟩⟩
  let c : SSpec := ⟨vec3 0 (1 / 4) (1 / 4),
    ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3],
     by norm_num [vec3]⟩⟩
  let a : SSpec := ⟨vec3 0 (1 / 4) 0,
    ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3],
     by norm_num [vec3]⟩⟩
  let b : SSpec := ⟨vec3 (1 / 4) 0 (1 / 4),
    ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3],
     by norm_num [vec3]⟩⟩
  let o : SSpec := ⟨vec3 0 0 0,
    ⟨fun k => by match k with | ⟨0, _⟩ => norm_num [vec3] | ⟨1, _⟩ => norm_num [vec3] | ⟨2, _⟩ => norm_num [vec3],
     by norm_num [vec3]⟩⟩
  refine ⟨t, c, a, b, o, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- c < a
    rw [lt_iff_le_and_ne]
    refine ⟨(SSpec.le_iff_coord c a).mpr (fun k => by
      match k with | ⟨0, _⟩ => norm_num [c, a, vec3] | ⟨1, _⟩ => norm_num [c, a, vec3] | ⟨2, _⟩ => norm_num [c, a, vec3]), ?_⟩
    intro h
    have h2 := congr_fun (congr_arg SSpec.val h) 2
    norm_num [c, a, vec3] at h2
  · -- ¬ (c ≤ b)
    rw [SSpec.le_iff_coord]; intro h; have h0 := h 0; norm_num [c, b, vec3] at h0
  · -- ¬ (b ≤ c)
    rw [SSpec.le_iff_coord]; intro h; have h1 := h 1; norm_num [c, b, vec3] at h1
  · -- ¬ (a ≤ b)
    rw [SSpec.le_iff_coord]; intro h; have h0 := h 0; norm_num [a, b, vec3] at h0
  · -- ¬ (b ≤ a)
    rw [SSpec.le_iff_coord]; intro h; have h1 := h 1; norm_num [a, b, vec3] at h1
  · -- c ⊓ b = t
    apply SSpec.ext; funext k; change cmax c.val b.val k = t.val k
    match k with
    | ⟨0, _⟩ => norm_num [cmax, c, b, t, vec3]
    | ⟨1, _⟩ => norm_num [cmax, c, b, t, vec3]
    | ⟨2, _⟩ => norm_num [cmax, c, b, t, vec3]
  · -- a ⊓ b = t
    apply SSpec.ext; funext k; change cmax a.val b.val k = t.val k
    match k with
    | ⟨0, _⟩ => norm_num [cmax, a, b, t, vec3]
    | ⟨1, _⟩ => norm_num [cmax, a, b, t, vec3]
    | ⟨2, _⟩ => norm_num [cmax, a, b, t, vec3]
  · -- c ⊔ b = o
    apply SSpec.ext; funext k; change rhoS (cmin c.val b.val) k = o.val k
    match k with
    | ⟨0, _⟩ => norm_num [rhoS, cmin, c, b, o, vec3]
    | ⟨1, _⟩ => norm_num [rhoS, cmin, c, b, o, vec3]
    | ⟨2, _⟩ => norm_num [rhoS, cmin, c, b, o, vec3]
  · -- a ⊔ b = o
    apply SSpec.ext; funext k; change rhoS (cmin a.val b.val) k = o.val k
    match k with
    | ⟨0, _⟩ => norm_num [rhoS, cmin, a, b, o, vec3]
    | ⟨1, _⟩ => norm_num [rhoS, cmin, a, b, o, vec3]
    | ⟨2, _⟩ => norm_num [rhoS, cmin, a, b, o, vec3]

/-- **Master Theorem (Complete Resolution of Agyingi–Gaba Question `q:modular`, `arXiv:2611.32417v1`):**
1. `(Y, ≤_q)` is a modular, non-distributive lattice containing no `N₅` sublattice.
2. `(S, q)` is a bounded, `T₀`, `q`-hyperconvex quasi-metric space whose specialization order
   `(S, ≤_q)` contains an `N₅` sublattice (and hence is non-modular). -/
theorem agyingi_gaba_question_modular_resolution :
    (IsModularLattice YSpec) ∧
    (∃ a b c : YSpec, a ⊓ (b ⊔ c) ≠ (a ⊓ b) ⊔ (a ⊓ c)) ∧
    (¬ HasN5Sublattice YSpec) ∧
    (∀ g h : R3, InS g → InS h → qdist g h ≤ 1) ∧
    IsQHyperconvex {g : R3 | InS g} ∧
    HasN5Sublattice SSpec :=
  ⟨Y_isModularLattice,
   Y_not_distributive,
   Y_no_N5_sublattice,
   fun _ _ hg hh => qdist_le_one hg.1 hh.1,
   S_isQHyperconvex,
   S_has_N5_sublattice⟩

end AgyingiGabaQHyperconvexModular
