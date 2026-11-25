import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Kalmanovich–Nivasch, *All-even sets in ℝ² and ℝ³* (arXiv:2610.38864), Conjecture 9.1

Conjecture 9.1: every planar all-even set has a monotonically contagious triangle.
We refute it with a 36-point subset of the vertices of the regular 210-gon, working with
genuine points of `ℝ × ℝ`.

* `m_S(u) = |{⟨p, u⟩ : p ∈ S}|`; `S` is all-even if `m_S(u)` is even for every `u ≠ 0` (§1).
* Monotone contagion from a seed `T ⊆ S` (§5): repeatedly add `y ∈ S` when there are `x, p, q`
  already reached with `p ≠ q`, `x ≠ y` and the secant `xy` parallel to `pq`.
  `T` is monotonically contagious if this process reaches all of `S`.
-/

namespace KalmanovichNivaschAllEven

open Real

/-! ## Euclidean definitions -/

abbrev Pt := ℝ × ℝ

def dot (p u : Pt) : ℝ := p.1 * u.1 + p.2 * u.2

def det2 (a b : Pt) : ℝ := a.1 * b.2 - a.2 * b.1

/-- The secants `pq` and `rs` are nondegenerate and parallel. -/
def Parallel (p q r s : Pt) : Prop := p ≠ q ∧ r ≠ s ∧ det2 (q - p) (s - r) = 0

/-- Planar all-even set (§1): every direction meets an even number of occupied lines. -/
def IsAllEven (S : Finset Pt) : Prop :=
  S.Nonempty ∧ ∀ u : Pt, u ≠ (0, 0) → Even (S.image (fun p => dot p u)).card

/-- Points reached by monotone contagion in `S` from the seed `T`. -/
inductive InMonoClosure (S T : Finset Pt) : Pt → Prop
  | seed {y : Pt} : y ∈ T → InMonoClosure S T y
  | step {x p q y : Pt} : InMonoClosure S T x → InMonoClosure S T p → InMonoClosure S T q →
      y ∈ S → p ≠ q → x ≠ y → det2 (y - x) (q - p) = 0 → InMonoClosure S T y

/-- `U ⊆ S` admits no further monotone contagion move. -/
def IsMonoClosed (S U : Finset Pt) : Prop :=
  U ⊆ S ∧ ∀ x ∈ U, ∀ p ∈ U, ∀ q ∈ U, ∀ y ∈ S, p ≠ q → x ≠ y → det2 (y - x) (q - p) = 0 → y ∈ U

/-- `T` is a monotonically contagious triangle of `S`. -/
def IsMonoContagious (S T : Finset Pt) : Prop :=
  T ⊆ S ∧ T.card = 3 ∧ ∀ y ∈ S, InMonoClosure S T y

lemma InMonoClosure.mem {S T U : Finset Pt} (hTU : T ⊆ U) (hU : IsMonoClosed S U) {y : Pt}
    (h : InMonoClosure S T y) : y ∈ U := by
  induction h with
  | seed hy => exact hTU hy
  | step _ _ _ hy hpq hxy hdet ihx ihp ihq => exact hU.2 _ ihx _ ihp _ ihq _ hy hpq hxy hdet

/-- A proper monotonically closed superset of `T` rules out contagion from `T`. -/
lemma not_isMonoContagious {S T U : Finset Pt} (hTU : T ⊆ U) (hUS : U ⊂ S)
    (hU : IsMonoClosed S U) : ¬ IsMonoContagious S T := by
  rintro ⟨-, -, h⟩
  obtain ⟨y, hyS, hyU⟩ := Finset.exists_of_ssubset hUS
  exact hyU ((h y hyS).mem hTU hU)

lemma det2_eq_zero_iff_exists_smul {v w : Pt} (hw : w ≠ 0) :
    det2 v w = 0 ↔ ∃ c : ℝ, v = c • w := by
  constructor
  · intro h
    simp only [det2] at h
    by_cases h1 : w.1 = 0
    · have h2 : w.2 ≠ 0 := fun h2 => hw (Prod.ext h1 h2)
      refine ⟨v.2 / w.2, Prod.ext ?_ ?_⟩
      · simp only [Prod.smul_fst, smul_eq_mul, h1, mul_zero]
        have : v.1 * w.2 = 0 := by rw [h1] at h; linarith
        exact (mul_eq_zero.mp this).resolve_right h2
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp
    · refine ⟨v.1 / w.1, Prod.ext ?_ ?_⟩
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp; linarith
  · rintro ⟨c, rfl⟩
    simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma parallel_iff (p q r s : Pt) :
    Parallel p q r s ↔ p ≠ q ∧ r ≠ s ∧ ∃ c : ℝ, q - p = c • (s - r) := by
  unfold Parallel
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (det2_eq_zero_iff_exists_smul (sub_ne_zero.mpr h2.symm)).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (det2_eq_zero_iff_exists_smul (sub_ne_zero.mpr h2.symm)).mpr h3⟩

/-! ## The configuration -/

noncomputable def pt210 (k : ZMod 210) : Pt :=
  (Real.cos (2 * Real.pi * k.val / 210), Real.sin (2 * Real.pi * k.val / 210))

def A_idx : Finset (ZMod 210) :=
  ({4, 5, 7, 8, 9, 10, 12, 13} : Finset ℕ).image (fun i => ((15 * i : ℕ) : ZMod 210))

def B_idx : Finset (ZMod 210) :=
  ((Finset.range 35).filter (fun j => j % 5 ≠ 0)).image (fun j => ((1 + 6 * j : ℕ) : ZMod 210))

def S_idx : Finset (ZMod 210) := A_idx ∪ B_idx

noncomputable def S36 : Finset Pt := S_idx.image pt210

lemma S_idx_card : S_idx.card = 36 := by decide +kernel

/-! ## Unit-circle geometry -/

lemma sin_pi_mul_div_eq_zero_iff (m : ℤ) :
    Real.sin (π * m / 210) = 0 ↔ (210 : ℤ) ∣ m := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have h : ((n * 210 : ℤ) : ℝ) = m := by
      push_cast
      have := Real.pi_pos
      field_simp at hn
      linarith
    exact ⟨n, by exact_mod_cast (Int.cast_injective h).symm.trans (mul_comm _ _)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

lemma zmod_dvd_iff (m : ℤ) : (210 : ℤ) ∣ m ↔ (m : ZMod 210) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd m 210).symm

/-- Sine of half the angle between two vertices. -/
lemma sin_half_diff (a b : ZMod 210) :
    Real.sin ((2 * π * b.val / 210 - 2 * π * a.val / 210) / 2) = 0 ↔ a = b := by
  have : (2 * π * b.val / 210 - 2 * π * a.val / 210) / 2
      = π * (((b.val : ℤ) - a.val : ℤ) : ℝ) / 210 := by push_cast; ring
  rw [this, sin_pi_mul_div_eq_zero_iff, zmod_dvd_iff]
  push_cast
  simp [sub_eq_zero, eq_comm]

private lemma chord_det_formula (a b c d : ℝ) :
    (Real.cos b - Real.cos a) * (Real.sin d - Real.sin c)
      - (Real.sin b - Real.sin a) * (Real.cos d - Real.cos c)
      = 4 * Real.sin ((b - a) / 2) * Real.sin ((d - c) / 2)
          * Real.sin ((d + c) / 2 - (b + a) / 2) := by
  simp only [Real.cos_sub_cos, Real.sin_sub_sin, Real.sin_sub]
  ring

lemma pt210_injective : Function.Injective pt210 := by
  intro i j h
  simp only [pt210, Prod.mk.injEq] at h
  obtain ⟨hc, hs⟩ := h
  have hc' := sub_eq_zero.mpr hc.symm
  have hs' := sub_eq_zero.mpr hs.symm
  rw [Real.cos_sub_cos] at hc'
  rw [Real.sin_sub_sin] at hs'
  by_contra hij
  have hne := mt (sin_half_diff i j).mp hij
  set P := (2 * π * j.val / 210 + 2 * π * i.val / 210) / 2
  have h1 : Real.sin P = 0 := by
    rcases mul_eq_zero.mp hc' with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact h
    · exact absurd h hne
  have h2 : Real.cos P = 0 := by
    rcases mul_eq_zero.mp hs' with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact absurd h hne
    · exact h
  have := Real.sin_sq_add_cos_sq P
  rw [h1, h2] at this
  norm_num at this

lemma S36_card : S36.card = 36 := by
  rw [S36, Finset.card_image_of_injective _ pt210_injective, S_idx_card]

/-- Two chords of the 210-gon are parallel iff their endpoint-index sums agree. -/
lemma det2_chord_eq_zero_iff {i j k l : ZMod 210} (hij : i ≠ j) (hkl : k ≠ l) :
    det2 (pt210 j - pt210 i) (pt210 l - pt210 k) = 0 ↔ i + j = k + l := by
  simp only [det2, pt210, Prod.fst_sub, Prod.snd_sub]
  rw [chord_det_formula]
  have h1 := mt (sin_half_diff i j).mp hij
  have h2 := mt (sin_half_diff k l).mp hkl
  have : (2 * π * l.val / 210 + 2 * π * k.val / 210) / 2
      - (2 * π * j.val / 210 + 2 * π * i.val / 210) / 2
      = π * (((k.val + l.val : ℤ) - i.val - j.val : ℤ) : ℝ) / 210 := by push_cast; ring
  rw [this]
  simp only [mul_eq_zero, h1, h2, or_false, false_or, OfNat.ofNat_ne_zero]
  rw [sin_pi_mul_div_eq_zero_iff, zmod_dvd_iff]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

lemma dot_sub (p q u : Pt) : dot (p - q) u = dot p u - dot q u := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

lemma ne_zero_cases {w : Pt} (hw : w ≠ 0) : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
  by_contra h
  push Not at h
  exact hw (Prod.ext h.1 h.2)

/-- If `w ≠ 0` is orthogonal to `u` and `v ∥ w`, then `v` is orthogonal to `u`. -/
lemma dot_eq_zero_of_det2 {u v w : Pt} (hw : w ≠ 0) (hwu : dot w u = 0) (h : det2 v w = 0) :
    dot v u = 0 := by
  simp only [dot, det2] at *
  rcases ne_zero_cases hw with ha | hb
  · have : w.1 * (v.1 * u.1 + v.2 * u.2) = 0 := by linear_combination v.1 * hwu - u.2 * h
    exact (mul_eq_zero.mp this).resolve_left ha
  · have : w.2 * (v.1 * u.1 + v.2 * u.2) = 0 := by linear_combination v.2 * hwu + u.1 * h
    exact (mul_eq_zero.mp this).resolve_left hb

/-- Two vectors orthogonal to the same `u ≠ 0` are parallel. -/
lemma det2_eq_zero_of_dot {u v w : Pt} (hu : u ≠ 0) (hv : dot v u = 0) (hw : dot w u = 0) :
    det2 v w = 0 := by
  simp only [dot, det2] at *
  rcases ne_zero_cases hu with ha | hb
  · have : u.1 * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination w.2 * hv - v.2 * hw
    exact (mul_eq_zero.mp this).resolve_left ha
  · have : u.2 * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination -w.1 * hv + v.1 * hw
    exact (mul_eq_zero.mp this).resolve_left hb

/-- If the distinct vertices `i, j` share the projection onto `u`, then two vertices share
that projection iff they coincide or their index sum is `i + j`. In particular a line meets
the circle in at most two vertices. -/
lemma dot_eq_iff_sum_eq {u : Pt} (hu : u ≠ (0, 0)) {i j : ZMod 210} (hij : i ≠ j)
    (h : dot (pt210 i) u = dot (pt210 j) u) (k l : ZMod 210) :
    dot (pt210 k) u = dot (pt210 l) u ↔ k = l ∨ k + l = i + j := by
  have hu0 : u ≠ 0 := hu
  have hji : dot (pt210 j - pt210 i) u = 0 := by rw [dot_sub, h, sub_self]
  by_cases hkl : k = l
  · simp [hkl]
  simp only [hkl, false_or]
  rw [show dot (pt210 k) u = dot (pt210 l) u ↔ dot (pt210 l - pt210 k) u = 0 by
    rw [dot_sub, sub_eq_zero, eq_comm]]
  constructor
  · intro hlk
    exact (det2_chord_eq_zero_iff hkl hij).mp (det2_eq_zero_of_dot hu0 hlk hji)
  · intro hs
    exact dot_eq_zero_of_det2 (sub_ne_zero.mpr (pt210_injective.ne hij).symm) hji
      ((det2_chord_eq_zero_iff hkl hij).mpr hs)

/-! ## All-evenness -/

/-- For each `s`, the classes `{i, s - i}` of `S_idx` (labelled by their smaller index)
are even in number. -/
lemma pair_classes_even :
    ∀ s : ZMod 210, Even (S_idx.image (fun i => min i.val (s - i).val)).card := by
  decide +kernel

lemma min_val_eq_iff (s a b : ZMod 210) :
    min a.val (s - a).val = min b.val (s - b).val ↔ a = b ∨ a + b = s := by
  constructor
  · intro h
    rcases min_choice a.val (s - a).val with ha | ha <;>
      rcases min_choice b.val (s - b).val with hb | hb <;>
      rw [ha, hb] at h <;> have h' := ZMod.val_injective _ h
    · exact Or.inl h'
    · exact Or.inr (by rw [h']; ring)
    · exact Or.inr (by rw [← h']; ring)
    · exact Or.inl (sub_right_injective h')
  · rintro (rfl | h)
    · rfl
    · rw [show s - a = b by rw [← h]; ring, show s - b = a by rw [← h]; ring, min_comm]

lemma card_image_congr {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (S : Finset α)
    (f : α → β) (g : α → γ) (h : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ g a = g b) :
    (S.image f).card = (S.image g).card := by
  have e1 : (S.image fun a => (f a, g a)).image Prod.fst = S.image f := by
    rw [Finset.image_image]; rfl
  have e2 : (S.image fun a => (f a, g a)).image Prod.snd = S.image g := by
    rw [Finset.image_image]; rfl
  have h1 : Set.InjOn Prod.fst (S.image fun a => (f a, g a) : Set (β × γ)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact Prod.ext hxy ((h a ha b hb).mp hxy)
  have h2 : Set.InjOn Prod.snd (S.image fun a => (f a, g a) : Set (β × γ)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact Prod.ext ((h a ha b hb).mpr hxy) hxy
  rw [← e1, ← e2, Finset.card_image_of_injOn h1, Finset.card_image_of_injOn h2]

theorem S36_isAllEven : IsAllEven S36 := by
  refine ⟨Finset.card_pos.mp (by rw [S36_card]; norm_num), fun u hu => ?_⟩
  rw [S36, Finset.image_image]
  by_cases hcol : ∃ i ∈ S_idx, ∃ j ∈ S_idx, i ≠ j ∧ dot (pt210 i) u = dot (pt210 j) u
  · obtain ⟨i, -, j, -, hij, h⟩ := hcol
    rw [card_image_congr S_idx _ (fun k => min k.val ((i + j) - k).val)]
    · exact pair_classes_even (i + j)
    intro k _ l _
    rw [Function.comp_apply, Function.comp_apply, dot_eq_iff_sum_eq hu hij h, min_val_eq_iff]
  · push Not at hcol
    rw [Finset.card_image_of_injOn, S_idx_card]
    · decide
    · intro a ha b hb hab
      by_contra hne
      exact hcol a ha b hb hne hab

/-! ## No monotonically contagious triangle

Reduce indices modulo 30. Since `x + y = p + q` for every move, each index set
`{z ∈ S_idx : z.val % 30 ∈ R}` with `R ∈ Rs` is closed (the residues of `S_idx` mod 30 are
`0, 15` for `A_idx` and `7, 13, 19, 25` for `B_idx`). These are the sets `A ∪ (B ∩ (c + 15G))`
and `B ∪ (A ∩ (c + 6G))`; every triangle lies in one of them, and none is all of `S_idx`. -/

/-- Residues mod 30 occurring in `S_idx`. -/
def PS : List ℕ := [0, 15, 7, 13, 19, 25]

def Rs : List (List ℕ) :=
  [[0, 15, 7], [0, 15, 13], [0, 15, 19], [0, 15, 25], [7, 13, 19, 25, 0], [7, 13, 19, 25, 15]]

lemma mod30_mem : ∀ y ∈ S_idx, y.val % 30 ∈ PS := by decide +kernel

lemma Rs_closed : ∀ R ∈ Rs, ∀ X ∈ R, ∀ P ∈ R, ∀ Q ∈ R, ∀ Y ∈ PS,
    (X + Y) % 30 = (P + Q) % 30 → Y ∈ R := by
  decide +kernel

lemma Rs_cover : ∀ X ∈ PS, ∀ Y ∈ PS, ∀ Z ∈ PS, ∃ R ∈ Rs, X ∈ R ∧ Y ∈ R ∧ Z ∈ R := by
  decide +kernel

lemma Rs_proper : ∀ R ∈ Rs, ∃ z ∈ S_idx, z.val % 30 ∉ R := by decide +kernel

lemma mod30_add {x y p q : ZMod 210} (h : x + y = p + q) :
    (x.val % 30 + y.val % 30) % 30 = (p.val % 30 + q.val % 30) % 30 := by
  have h' := congrArg (fun z : ZMod 210 => z.val % 30) h
  simp only [ZMod.val_add, Nat.mod_mod_of_dvd _ (by norm_num : 30 ∣ 210)] at h'
  rwa [← Nat.add_mod, ← Nat.add_mod]

lemma idx_closed {R : List ℕ} (hR : R ∈ Rs) {x p q y : ZMod 210}
    (hx : x ∈ S_idx.filter (·.val % 30 ∈ R)) (hp : p ∈ S_idx.filter (·.val % 30 ∈ R))
    (hq : q ∈ S_idx.filter (·.val % 30 ∈ R)) (hy : y ∈ S_idx) (h : x + y = p + q) :
    y ∈ S_idx.filter (·.val % 30 ∈ R) := by
  rw [Finset.mem_filter] at *
  exact ⟨hy, Rs_closed R hR _ hx.2 _ hp.2 _ hq.2 _ (mod30_mem y hy) (mod30_add h)⟩

theorem S36_no_mono_contagious_triangle :
    ∀ T ⊆ S36, T.card = 3 → ∃ U, T ⊆ U ∧ U ⊂ S36 ∧ IsMonoClosed S36 U := by
  intro T hT hcard
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_image_iff.mp hT
  rw [Finset.card_image_of_injective _ pt210_injective, Finset.card_eq_three] at hcard
  obtain ⟨a, b, c, -, -, -, rfl⟩ := hcard
  have ha := hT'S (by simp : a ∈ ({a, b, c} : Finset _))
  have hb := hT'S (by simp : b ∈ ({a, b, c} : Finset _))
  have hc := hT'S (by simp : c ∈ ({a, b, c} : Finset _))
  obtain ⟨R, hR, haR, hbR, hcR⟩ := Rs_cover _ (mod30_mem a ha) _ (mod30_mem b hb) _ (mod30_mem c hc)
  refine ⟨(S_idx.filter (·.val % 30 ∈ R)).image pt210, ?_, ?_, ?_, ?_⟩
  · apply Finset.image_subset_image
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [*]
  · rw [S36]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.image_subset_image (Finset.filter_subset _ _), ?_⟩
    intro heq
    obtain ⟨z, hz, hzR⟩ := Rs_proper R hR
    have : pt210 z ∈ (S_idx.filter (·.val % 30 ∈ R)).image pt210 :=
      heq ▸ Finset.mem_image_of_mem _ hz
    rw [pt210_injective.mem_finset_image, Finset.mem_filter] at this
    exact hzR this.2
  · rw [S36]; exact Finset.image_subset_image (Finset.filter_subset _ _)
  · intro X hX P hP Q hQ Y hY hPQ hXY hdet
    simp only [S36, Finset.mem_image] at hX hP hQ hY
    obtain ⟨x, hx, rfl⟩ := hX
    obtain ⟨p, hp, rfl⟩ := hP
    obtain ⟨q, hq, rfl⟩ := hQ
    obtain ⟨y, hy, rfl⟩ := hY
    have hsum := (det2_chord_eq_zero_iff 
      (fun e => hXY (by rw [e])) (fun e => hPQ (by rw [e]))).mp hdet
    exact Finset.mem_image_of_mem _ (idx_closed hR hx hp hq hy hsum)

theorem not_conjecture_9_1 :
    ¬ (∀ S : Finset Pt, IsAllEven S → ∃ T ⊆ S, T.card = 3 ∧ IsMonoContagious S T) := by
  intro h
  obtain ⟨T, hT, hcard, hcont⟩ := h S36 S36_isAllEven
  obtain ⟨U, hTU, hUS, hU⟩ := S36_no_mono_contagious_triangle T hT hcard
  exact not_isMonoContagious hTU hUS hU hcont

end KalmanovichNivaschAllEven

#print axioms KalmanovichNivaschAllEven.S36_isAllEven
#print axioms KalmanovichNivaschAllEven.S36_no_mono_contagious_triangle
#print axioms KalmanovichNivaschAllEven.not_conjecture_9_1
