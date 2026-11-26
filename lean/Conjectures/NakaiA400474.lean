import Mathlib

/-!
# Proof of Takuto Nakai's OEIS A400474 Conjecture

This module proves Takuto Nakai's formula conjecture for OEIS A400474 (25 Oct 2026):
for every integer `n ≥ 3`, the maximum over all nondegenerate Euclidean triangles
`△ABC` (interior angles `A, B, C > 0`, `A + B + C = π`) of the number of admissible
pairwise-distinct integer-multiple angle triples `(Xπ/n, Yπ/n, Zπ/n)` with
`X + Y + Z = 2n`, `A < Xπ/n < π`, `B < Yπ/n < π`, `C < Zπ/n < π` equals
`(n^2 - 4n + c(n mod 6)) / 3`, where `c(0..5) = (6, -3, 4, 3, 0, -5)`.

## Main Theorems

* `angleTriples_card_eq_admissibleCount`: for any real triangle angles `A, B, C > 0`
  with `A + B + C = π`, the integer-multiple angle count equals
  `admissibleCount n ⌊nA/π⌋ ⌊nB/π⌋ ⌊nC/π⌋` with `⌊nA/π⌋ + ⌊nB/π⌋ + ⌊nC/π⌋ ≥ n - 2`.
* `exists_real_angles_of_floors`: every `(p, q, r) : ℕ × ℕ × ℕ` with `p + q + r = n - 2`
  is realized as `(⌊nA/π⌋, ⌊nB/π⌋, ⌊nC/π⌋)` for valid triangle angles `A, B, C > 0`,
  `A + B + C = π`.
* `admissibleCount_eq_sub_excl`: exact disjoint exclusion decomposition
  `admissibleCount n p q r = totalTriples n - excl n p - excl n q - excl n r`.
* `nakai_A400474_upper` and `nakai_A400474_attained`: for every `n ≥ 3`, every triangle's
  count is `≤ conjecturedFormula n`, and equality is attained by an explicit real triangle.
-/

namespace NakaiA400474

open Finset

/-! ### Core definitions -/

/-- The unrestricted set `U_n` of ordered triples `(u, v, w)` of pairwise distinct
positive integers with `u + v + w = n`. -/
def unrestrictedSet (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 n) ×ˢ ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n))).filter fun t =>
    t.1 + t.2.1 + t.2.2 = n ∧ t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2

/-- Admissible triples `S_n(p, q, r)` for floor triple `(p, q, r)`. -/
def admissibleSet (n p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (unrestrictedSet n).filter fun t =>
    t.1 < n - p ∧ t.2.1 < n - q ∧ t.2.2 < n - r

/-- Cardinality `|S_n(p, q, r)|`. -/
def admissibleCount (n p q r : ℕ) : ℕ :=
  (admissibleSet n p q r).card

/-- Closed-form unrestricted count `T(n) = (n-1)(n-2)/2 + 2*[3 ∣ n] - 3*⌊(n-1)/2⌋`. -/
def totalTriples (n : ℕ) : ℕ :=
  (n - 1) * (n - 2) / 2 + (if n % 3 = 0 then 2 else 0) - 3 * ((n - 1) / 2)

/-- Step exclusion count `D_n(s)` for `s = n - u = v + w`. -/
def dStep (n s : ℕ) : ℕ :=
  s - 1 - (if s % 2 = 0 then 1 else 0) - (if 2 * s > n ∧ 3 * s ≠ 2 * n then 2 else 0)

/-- Cumulative exclusion count `E_n(p) = ∑_{s=1}^p D_n(s)`. -/
def excl (n p : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 p, dStep n s

/-- Conjectured mod-6 offset `c(n mod 6) ∈ {6, -3, 4, 3, 0, -5}`. -/
def modOffset (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 6
  | 1 => -3
  | 2 => 4
  | 3 => 3
  | 4 => 0
  | _ => -5

/-- Takuto Nakai's conjectured formula `(n^2 - 4n + c(n mod 6)) / 3` (in `ℕ`). -/
def conjecturedFormula (n : ℕ) : ℕ :=
  (((n : ℤ) ^ 2 - 4 * (n : ℤ) + modOffset n) / 3).toNat

open Classical in
/-- Real-angle admissible integer-multiple triples `(X, Y, Z)` for triangle angles `A, B, C`. -/
noncomputable def angleTripleSet (n : ℕ) (A B C : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 n) ×ˢ ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n))).filter fun t =>
    t.1 + t.2.1 + t.2.2 = 2 * n ∧
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 ∧
    A < (t.1 : ℝ) * Real.pi / (n : ℝ) ∧ (t.1 : ℝ) * Real.pi / (n : ℝ) < Real.pi ∧
    B < (t.2.1 : ℝ) * Real.pi / (n : ℝ) ∧ (t.2.1 : ℝ) * Real.pi / (n : ℝ) < Real.pi ∧
    C < (t.2.2 : ℝ) * Real.pi / (n : ℝ) ∧ (t.2.2 : ℝ) * Real.pi / (n : ℝ) < Real.pi

/-! ### Section 1: Real-angle floor reduction -/

private lemma nat_lt_real_angle_iff {n : ℕ} (hn : 0 < n) {A : ℝ} (hA0 : 0 < A) (X : ℕ) :
    (A < (X : ℝ) * Real.pi / (n : ℝ) ∧ (X : ℝ) * Real.pi / (n : ℝ) < Real.pi) ↔
      (Nat.floor ((n : ℝ) * A / Real.pi) < X ∧ X < n) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv_nonneg : 0 ≤ (n : ℝ) * A / Real.pi := by positivity
  have h1 : A < (X : ℝ) * Real.pi / (n : ℝ) ↔ Nat.floor ((n : ℝ) * A / Real.pi) < X := by
    rw [lt_div_iff₀ hnR, mul_comm A (n : ℝ), ← div_lt_iff₀ hpi, Nat.floor_lt hdiv_nonneg]
  have h2 : (X : ℝ) * Real.pi / (n : ℝ) < Real.pi ↔ X < n := by
    rw [div_lt_iff₀ hnR]
    constructor
    · intro h
      have : (X : ℝ) < (n : ℝ) := by nlinarith
      exact Nat.cast_lt.mp this
    · intro h
      have : (X : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h
      nlinarith
  exact and_congr h1 h2

/-- Real-angle floor reduction: for any positive angles `A + B + C = π`,
`|angleTripleSet n A B C| = admissibleCount n ⌊nA/π⌋ ⌊nB/π⌋ ⌊nC/π⌋` and
`⌊nA/π⌋ + ⌊nB/π⌋ + ⌊nC/π⌋ ≥ n - 2`. -/
theorem angleTriples_card_eq_admissibleCount {n : ℕ} (hn : 3 ≤ n) {A B C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hsum : A + B + C = Real.pi) :
    (angleTripleSet n A B C).card =
      admissibleCount n (Nat.floor ((n : ℝ) * A / Real.pi))
        (Nat.floor ((n : ℝ) * B / Real.pi)) (Nat.floor ((n : ℝ) * C / Real.pi)) ∧
      n - 2 ≤ Nat.floor ((n : ℝ) * A / Real.pi) +
        Nat.floor ((n : ℝ) * B / Real.pi) + Nat.floor ((n : ℝ) * C / Real.pi) := by
  classical
  set p := Nat.floor ((n : ℝ) * A / Real.pi)
  set q := Nat.floor ((n : ℝ) * B / Real.pi)
  set r := Nat.floor ((n : ℝ) * C / Real.pi)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn0 : 0 < n := by omega
  have hsum_fl : n - 2 ≤ p + q + r := by
    have hp : (n : ℝ) * A / Real.pi < (p : ℝ) + 1 := Nat.lt_floor_add_one _
    have hq : (n : ℝ) * B / Real.pi < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hr : (n : ℝ) * C / Real.pi < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    have htot : (n : ℝ) * A / Real.pi + (n : ℝ) * B / Real.pi + (n : ℝ) * C / Real.pi = (n : ℝ) := by
      have hne : Real.pi ≠ 0 := ne_of_gt hpi
      field_simp [hne]
      nlinarith
    have hlt : (n : ℝ) < ((p + q + r + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hltN : n < p + q + r + 3 := Nat.cast_lt.mp hlt
    omega
  refine ⟨?_, hsum_fl⟩
  unfold admissibleCount
  apply Finset.card_nbij (fun t : ℕ × ℕ × ℕ => (n - t.1, n - t.2.1, n - t.2.2))
  · intro t ht
    simp only [Finset.mem_coe, angleTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
    obtain ⟨_, hadd, h12, h23, h13, hA1, hA2, hB1, hB2, hC1, hC2⟩ := ht
    have hXA := (nat_lt_real_angle_iff hn0 hA t.1).mp ⟨hA1, hA2⟩
    have hYB := (nat_lt_real_angle_iff hn0 hB t.2.1).mp ⟨hB1, hB2⟩
    have hZC := (nat_lt_real_angle_iff hn0 hC t.2.2).mp ⟨hC1, hC2⟩
    simp only [Finset.mem_coe, admissibleSet, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_coe, angleTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht₁ ht₂
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  · intro s hs
    rcases s with ⟨u, v, w⟩
    simp only [Finset.mem_coe, admissibleSet, unrestrictedSet, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc] at hs
    obtain ⟨⟨⟨⟨hu1, hun⟩, ⟨hv1, hvn⟩, ⟨hw1, hwn⟩⟩, hadd, h12, h23, h13⟩, hup, hvq, hwr⟩ := hs
    refine ⟨(n - u, n - v, n - w), ?_, ?_⟩
    · simp only [Finset.mem_coe, angleTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      have hA' := (nat_lt_real_angle_iff hn0 hA (n - u)).mpr ⟨by omega, by omega⟩
      have hB' := (nat_lt_real_angle_iff hn0 hB (n - v)).mpr ⟨by omega, by omega⟩
      have hC' := (nat_lt_real_angle_iff hn0 hC (n - w)).mpr ⟨by omega, by omega⟩
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
        by omega, by omega, by omega, by omega, hA'.1, hA'.2, hB'.1, hB'.2, hC'.1, hC'.2⟩
    · simp only [Prod.mk.injEq]
      exact ⟨by omega, by omega, by omega⟩

/-- Every `(p, q, r) : ℕ × ℕ × ℕ` with `p + q + r = n - 2` is realized by positive real
triangle angles `A + B + C = π`. -/
theorem exists_real_angles_of_floors {n p q r : ℕ} (hn : 3 ≤ n) (hsum : p + q + r = n - 2) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ A + B + C = Real.pi ∧
      Nat.floor ((n : ℝ) * A / Real.pi) = p ∧
      Nat.floor ((n : ℝ) * B / Real.pi) = q ∧
      Nat.floor ((n : ℝ) * C / Real.pi) = r := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  refine ⟨((p : ℝ) + 2 / 3) * Real.pi / (n : ℝ),
          ((q : ℝ) + 2 / 3) * Real.pi / (n : ℝ),
          ((r : ℝ) + 2 / 3) * Real.pi / (n : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · have hsumR : (p : ℝ) + (q : ℝ) + (r : ℝ) = (n : ℝ) - 2 := by
      have : ((p + q + r : ℕ) : ℝ) = ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hsum
      push_cast at this
      have hsub : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num
      linarith
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    field_simp [hne]
    linarith
  · have heq : (n : ℝ) * (((p : ℝ) + 2 / 3) * Real.pi / (n : ℝ)) / Real.pi = (p : ℝ) + 2 / 3 := by
      field_simp [ne_of_gt hpi, ne_of_gt hnR]
    rw [heq, Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  · have heq : (n : ℝ) * (((q : ℝ) + 2 / 3) * Real.pi / (n : ℝ)) / Real.pi = (q : ℝ) + 2 / 3 := by
      field_simp [ne_of_gt hpi, ne_of_gt hnR]
    rw [heq, Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  · have heq : (n : ℝ) * (((r : ℝ) + 2 / 3) * Real.pi / (n : ℝ)) / Real.pi = (r : ℝ) + 2 / 3 := by
      field_simp [ne_of_gt hpi, ne_of_gt hnR]
    rw [heq, Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith

lemma admissibleCount_anti {n p₁ q₁ r₁ p₂ q₂ r₂ : ℕ}
    (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) (hr : r₁ ≤ r₂) :
    admissibleCount n p₂ q₂ r₂ ≤ admissibleCount n p₁ q₁ r₁ := by
  apply Finset.card_le_card
  intro t ht
  simp only [admissibleSet, Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, by omega, by omega, by omega⟩

/-! ### Section 2: Unrestricted count `T(n)` and disjoint exclusions `E_n(p)` -/

/-- Exact slice cardinality: for `1 ≤ s ≤ n - 2`, the number of triples `(u, v, w) ∈ U_n`
with `u = n - s` (equivalently `v + w = s`) equals `dStep n s`. -/
lemma slice_card_eq_dStep {n s : ℕ} (hs1 : 1 ≤ s) (hsn : s + 2 ≤ n) :
    ((unrestrictedSet n).filter (fun t => t.1 = n - s)).card = dStep n s := by
  -- Map `(u, v, w) ↦ v ∈ Icc 1 (s - 1)` avoiding `2v = s`, `v = n - s`, and `s - v = n - s`
  let bad : Finset ℕ := (Finset.Icc 1 (s - 1)).filter fun v =>
    2 * v = s ∨ v = n - s ∨ v + (n - s) = s
  let good : Finset ℕ := (Finset.Icc 1 (s - 1)).filter fun v =>
    ¬ (2 * v = s ∨ v = n - s ∨ v + (n - s) = s)
  have hbij : ((unrestrictedSet n).filter (fun t => t.1 = n - s)).card = good.card := by
    apply Finset.card_nbij (fun t => t.2.1)
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, unrestrictedSet, Finset.mem_product, Finset.mem_Icc] at ht
      simp only [Finset.mem_coe, good, Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro t₁ ht₁ t₂ ht₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, unrestrictedSet, Finset.mem_product,
        Finset.mem_Icc] at ht₁ ht₂
      dsimp only at heq
      exact Prod.ext (by omega) (Prod.ext heq (by omega))
    · intro v hv
      simp only [Finset.mem_coe, good, Finset.mem_filter, Finset.mem_Icc, not_or] at hv
      obtain ⟨⟨hv1, hvs⟩, h1, h2, h3⟩ := hv
      refine ⟨(n - s, v, s - v), ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, unrestrictedSet, Finset.mem_product,
        Finset.mem_Icc]
      refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
        by omega, by omega, by omega, by omega⟩, trivial⟩
  rw [hbij]
  have hpart : good.card + bad.card = (Finset.Icc 1 (s - 1)).card := by
    have hgb_disj : Disjoint good bad := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [good, bad, Finset.mem_filter] at h1 h2; exact h1.2 h2.2
    have hgb_un : good ∪ bad = Finset.Icc 1 (s - 1) := by
      ext v; simp only [good, bad, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← Finset.card_union_of_disjoint hgb_disj, hgb_un]
  have hicc : (Finset.Icc 1 (s - 1)).card = s - 1 := by
    rw [Nat.card_Icc]; omega
  -- Compute `bad.card` by decomposing into `E = {s/2 | 2∣s}` and `F = {n-s, 2s-n | 2s>n ∧ 3s≠2n}`
  let E : Finset ℕ := if s % 2 = 0 then {s / 2} else ∅
  let F : Finset ℕ := if 2 * s > n ∧ 3 * s ≠ 2 * n then {n - s, 2 * s - n} else ∅
  have hbad_eq : bad = E ∪ F := by
    ext v
    simp only [bad, E, F, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨⟨hv1, hvs⟩, h | h | h⟩
      · left; rw [if_pos (by omega), Finset.mem_singleton]; omega
      · by_cases h3 : 3 * s = 2 * n
        · left; rw [if_pos (by omega), Finset.mem_singleton]; omega
        · right; rw [if_pos ⟨by omega, h3⟩, Finset.mem_insert, Finset.mem_singleton]; left; omega
      · by_cases h3 : 3 * s = 2 * n
        · left; rw [if_pos (by omega), Finset.mem_singleton]; omega
        · right; rw [if_pos ⟨by omega, h3⟩, Finset.mem_insert, Finset.mem_singleton]; right; omega
    · rintro (hE | hF)
      · split_ifs at hE with h
        · rw [Finset.mem_singleton] at hE; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
        · exact (Finset.notMem_empty v hE).elim
      · split_ifs at hF with h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hF
          rcases hF with rfl | rfl
          · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inl rfl)⟩
          · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inr (by omega))⟩
        · exact (Finset.notMem_empty v hF).elim
  have hdisj : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro v hvE hvF
    simp only [E, F] at hvE hvF
    split_ifs at hvE hvF with h1 h2 h2
    · simp only [Finset.mem_singleton, Finset.mem_insert] at hvE hvF; omega
    · simp at hvF
    · simp at hvE
    · simp at hvE
  have hEcard : E.card = if s % 2 = 0 then 1 else 0 := by
    dsimp [E]; split_ifs <;> simp
  have hFcard : F.card = if 2 * s > n ∧ 3 * s ≠ 2 * n then 2 else 0 := by
    dsimp [F]
    split_ifs with h
    · rw [Finset.card_pair (by omega)]
    · simp
  have hbad_card : bad.card =
      (if s % 2 = 0 then 1 else 0) + (if 2 * s > n ∧ 3 * s ≠ 2 * n then 2 else 0) := by
    rw [hbad_eq, Finset.card_union_of_disjoint hdisj, hEcard, hFcard]
  unfold dStep
  omega

/-- Exact exclusion count: for `p + 2 ≤ n`, `|{t ∈ U_n | t.1 ≥ n - p}| = excl n p`. -/
lemma excl_card_eq {n p : ℕ} (hp : p + 2 ≤ n) :
    ((unrestrictedSet n).filter (fun t => n - p ≤ t.1)).card = excl n p := by
  have hbi : (unrestrictedSet n).filter (fun t => n - p ≤ t.1) =
      (Finset.Icc 1 p).biUnion (fun s => (unrestrictedSet n).filter (fun t => t.1 = n - s)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨ht, hge⟩
      have htu : t.1 + t.2.1 + t.2.2 = n ∧ 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 := by
        simp only [unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
        omega
      exact ⟨n - t.1, ⟨by omega, by omega⟩, ht, by omega⟩
    · rintro ⟨s, ⟨hs1, hsp⟩, ht, heq⟩
      exact ⟨ht, by omega⟩
  rw [hbi, Finset.card_biUnion]
  · unfold excl
    apply Finset.sum_congr rfl
    intro s hs
    have hs' := Finset.mem_Icc.mp hs
    exact slice_card_eq_dStep hs'.1 (by omega)
  · intro s₁ hs₁ s₂ hs₂ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    simp only [Finset.mem_filter] at ht₁ ht₂
    have h1 := Finset.mem_Icc.mp hs₁
    have h2 := Finset.mem_Icc.mp hs₂
    omega

/-- Unrestricted count identity `|U_n| = totalTriples n` for every `n ≥ 3`. -/
theorem card_unrestrictedSet {n : ℕ} (hn : 3 ≤ n) :
    (unrestrictedSet n).card = totalTriples n := by
  -- Every `(u, v, w) ∈ U_n` has `u = n - s` with `1 ≤ s ≤ n - 1`, and the slice formula
  -- `dStep n s` also holds at the boundary `s = n - 1` (`u = 1`).
  have hslice_all : ∀ s ∈ Finset.Icc 1 (n - 1),
      ((unrestrictedSet n).filter (fun t => t.1 = n - s)).card = dStep n s := by
    intro s hs
    have hs' := Finset.mem_Icc.mp hs
    by_cases hsn : s + 2 ≤ n
    · exact slice_card_eq_dStep hs'.1 hsn
    · have hs_eq : s = n - 1 := by omega
      subst hs_eq
      -- Direct bijection `t ↦ t.2.1` onto `{v ∈ Icc 2 (n - 3) | 2 * v ≠ n - 1}`
      let bad : Finset ℕ := (Finset.Icc 1 (n - 2)).filter fun v =>
        2 * v = n - 1 ∨ v = 1 ∨ v + 1 = n - 1
      let good : Finset ℕ := (Finset.Icc 1 (n - 2)).filter fun v =>
        ¬ (2 * v = n - 1 ∨ v = 1 ∨ v + 1 = n - 1)
      have hbij : ((unrestrictedSet n).filter (fun t => t.1 = n - (n - 1))).card = good.card := by
        apply Finset.card_nbij (fun t => t.2.1)
        · intro t ht
          simp only [Finset.mem_coe, Finset.mem_filter, unrestrictedSet, Finset.mem_product, Finset.mem_Icc] at ht
          simp only [Finset.mem_coe, good, Finset.mem_filter, Finset.mem_Icc]; omega
        · intro t₁ ht₁ t₂ ht₂ heq
          simp only [Finset.mem_coe, Finset.mem_filter, unrestrictedSet, Finset.mem_product,
            Finset.mem_Icc] at ht₁ ht₂
          dsimp only at heq
          exact Prod.ext (by omega) (Prod.ext heq (by omega))
        · intro v hv
          simp only [Finset.mem_coe, good, Finset.mem_filter, Finset.mem_Icc] at hv
          refine ⟨(1, v, n - 1 - v), ?_, rfl⟩
          simp only [Finset.mem_coe, Finset.mem_filter, unrestrictedSet, Finset.mem_product,
            Finset.mem_Icc]
          omega
      rw [hbij]
      have hpart : good.card + bad.card = (Finset.Icc 1 (n - 2)).card := by
        have hgb_disj : Disjoint good bad := by
          rw [Finset.disjoint_left]; intro v h1 h2
          simp only [good, bad, Finset.mem_filter] at h1 h2; exact h1.2 h2.2
        have hgb_un : good ∪ bad = Finset.Icc 1 (n - 2) := by
          ext v; simp only [good, bad, Finset.mem_union, Finset.mem_filter]; tauto
        rw [← Finset.card_union_of_disjoint hgb_disj, hgb_un]
      have hicc : (Finset.Icc 1 (n - 2)).card = n - 2 := by rw [Nat.card_Icc]; omega
      let E : Finset ℕ := if (n - 1) % 2 = 0 then {(n - 1) / 2} else ∅
      let F : Finset ℕ := if 2 * (n - 1) > n ∧ 3 * (n - 1) ≠ 2 * n then {1, n - 2} else ∅
      have hbad_eq : bad = E ∪ F := by
        ext v
        simp only [bad, E, F, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
        constructor
        · rintro ⟨⟨hv1, hvn⟩, h | h | h⟩
          · left; rw [if_pos (by omega), Finset.mem_singleton]; omega
          · by_cases h3 : 3 * (n - 1) = 2 * n
            · left; rw [if_pos (by omega), Finset.mem_singleton]; omega
            · right; rw [if_pos ⟨by omega, h3⟩, Finset.mem_insert, Finset.mem_singleton]; left; omega
          · by_cases h3 : 3 * (n - 1) = 2 * n
            · left; rw [if_pos (by omega), Finset.mem_singleton]; omega
            · right; rw [if_pos ⟨by omega, h3⟩, Finset.mem_insert, Finset.mem_singleton]; right; omega
        · rintro (hE | hF)
          · split_ifs at hE with h
            · rw [Finset.mem_singleton] at hE; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
            · exact (Finset.notMem_empty v hE).elim
          · split_ifs at hF with h
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hF
              rcases hF with rfl | rfl
              · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inl rfl)⟩
              · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inr (by omega))⟩
            · exact (Finset.notMem_empty v hF).elim
      have hdisj : Disjoint E F := by
        rw [Finset.disjoint_left]; intro v hvE hvF
        simp only [E, F] at hvE hvF
        split_ifs at hvE hvF with h1 h2 h2
        · simp only [Finset.mem_singleton, Finset.mem_insert] at hvE hvF; omega
        · simp at hvF
        · simp at hvE
        · simp at hvE
      have hEcard : E.card = if (n - 1) % 2 = 0 then 1 else 0 := by dsimp [E]; split_ifs <;> simp
      have hFcard : F.card = if 2 * (n - 1) > n ∧ 3 * (n - 1) ≠ 2 * n then 2 else 0 := by
        dsimp [F]; split_ifs with h
        · rw [Finset.card_pair (by omega)]
        · simp
      rw [hbad_eq, Finset.card_union_of_disjoint hdisj, hEcard, hFcard] at hpart
      unfold dStep
      omega
  have hbi : unrestrictedSet n =
      (Finset.Icc 1 (n - 1)).biUnion (fun s => (unrestrictedSet n).filter (fun t => t.1 = n - s)) := by
    ext t
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ht
      have htu : 1 ≤ t.1 ∧ t.1 + 2 ≤ n := by
        simp only [unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
        omega
      exact ⟨n - t.1, ⟨by omega, by omega⟩, ht, by omega⟩
    · rintro ⟨_, _, ht, _⟩; exact ht
  have hcard_sum : (unrestrictedSet n).card = ∑ s ∈ Finset.Icc 1 (n - 1), dStep n s := by
    rw [hbi, Finset.card_biUnion]
    · exact Finset.sum_congr rfl hslice_all
    · intro s₁ hs₁ s₂ hs₂ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]; intro t ht₁ ht₂
      simp only [Finset.mem_filter] at ht₁ ht₂
      have := Finset.mem_Icc.mp hs₁; have := Finset.mem_Icc.mp hs₂; omega
  rw [hcard_sum]
  -- Evaluate `∑_{s=1}^{n-1} dStep n s` in `ℤ` directly!
  suffices hZ : (∑ s ∈ Finset.Icc 1 (n - 1), (dStep n s : ℤ)) = (totalTriples n : ℤ) by
    exact_mod_cast hZ
  have hterm : ∀ s ∈ Finset.Icc 1 (n - 1),
      (dStep n s : ℤ) = (s : ℤ) - 1 - (if s % 2 = 0 then 1 else 0) -
        (if 2 * s > n ∧ 3 * s ≠ 2 * n then 2 else 0) := by
    intro s hs
    have hs' := Finset.mem_Icc.mp hs
    unfold dStep
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- Sum 1: `∑_{s=1}^{n-1} (s - 1) = (n - 1) * (n - 2) / 2`
  have hS1 : ∑ s ∈ Finset.Icc 1 (n - 1), ((s : ℤ) - 1) = (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) := by
    have h2 : 2 * ∑ s ∈ Finset.Icc 1 (n - 1), ((s : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) * ((n - 2 : ℕ) : ℤ) := by
      clear hslice_all hbi hcard_sum hterm
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hsub1 : m + 2 - 1 = m + 1 := by omega
      have hsub2 : m + 2 - 2 = m := by omega
      rw [hsub1, hsub2]
      clear hn hsub1 hsub2
      induction m with
      | zero => simp
      | succ k ih =>
        rw [show k + 1 + 1 = (k + 1) + 1 from rfl,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ (k + 1) + 1), mul_add, ih]
        push_cast; ring
    have hev : 2 ∣ (n - 1) * (n - 2) := by
      rcases Nat.even_or_odd (n - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (n - 2), by rw [hk]; ring⟩
      · have h2k : n - 2 = 2 * k := by omega
        exact ⟨(n - 1) * k, by rw [h2k]; ring⟩
    have hmul : 2 * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) * ((n - 2 : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hev
    linarith
  -- Sum 2: `∑_{s=1}^{n-1} [2 ∣ s] = (n - 1) / 2`
  have hS2 : ∑ s ∈ Finset.Icc 1 (n - 1), (if s % 2 = 0 then (1 : ℤ) else 0) =
      (((n - 1) / 2 : ℕ) : ℤ) := by
    rw [Finset.sum_boole]
    congr 1
    have hbij : ((Finset.Icc 1 (n - 1)).filter (fun s => s % 2 = 0)).card =
        (Finset.Icc 1 ((n - 1) / 2)).card := by
      apply Finset.card_nbij (fun s => s / 2)
      · intro s hs; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hs ⊢; omega
      · intro s₁ hs₁ s₂ hs₂ h; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hs₁ hs₂; dsimp only at h; omega
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_Icc] at hk
        refine ⟨2 * k, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩), ?_⟩
        dsimp only; omega
    rw [hbij, Nat.card_Icc]; omega
  -- Sum 3: `∑_{s=1}^{n-1} 2 * [2s > n ∧ 3s ≠ 2n] = 2 * ((n - 1) / 2) - 2 * [3 ∣ n]`
  have hS3 : ∑ s ∈ Finset.Icc 1 (n - 1), (if 2 * s > n ∧ 3 * s ≠ 2 * n then (2 : ℤ) else 0) =
      2 * (((n - 1) / 2 : ℕ) : ℤ) - (if n % 3 = 0 then 2 else 0) := by
    have hpull : ∑ s ∈ Finset.Icc 1 (n - 1), (if 2 * s > n ∧ 3 * s ≠ 2 * n then (2 : ℤ) else 0) =
        2 * ∑ s ∈ Finset.Icc 1 (n - 1), (if 2 * s > n ∧ 3 * s ≠ 2 * n then (1 : ℤ) else 0) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; split_ifs <;> ring
    rw [hpull, Finset.sum_boole]
    set A := (Finset.Icc 1 (n - 1)).filter (fun s => 2 * s > n)
    have hA_eq : A = Finset.Icc (n / 2 + 1) (n - 1) := by
      ext s; simp only [A, Finset.mem_filter, Finset.mem_Icc]; omega
    have hA_card : A.card = (n - 1) / 2 := by
      rw [hA_eq, Nat.card_Icc]; omega
    by_cases h3 : n % 3 = 0
    · have hmem : 2 * (n / 3) ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_Icc]; omega
      have hfilt : (Finset.Icc 1 (n - 1)).filter (fun s => 2 * s > n ∧ 3 * s ≠ 2 * n) =
          A.erase (2 * (n / 3)) := by
        ext s; simp only [A, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
      rw [hfilt, Finset.card_erase_of_mem hmem, hA_card]
      have hpos : 1 ≤ (n - 1) / 2 := by omega
      simp only [h3, ↓reduceIte]
      omega
    · have hfilt : (Finset.Icc 1 (n - 1)).filter (fun s => 2 * s > n ∧ 3 * s ≠ 2 * n) = A := by
        ext s; simp only [A, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hfilt, hA_card]
      simp only [h3, ↓reduceIte]
      omega
  rw [hS1, hS2, hS3]
  unfold totalTriples
  have hge : 3 * ((n - 1) / 2) ≤ (n - 1) * (n - 2) / 2 + (if n % 3 = 0 then 2 else 0) := by
    by_cases h6 : 6 ≤ n
    · have h3le : 3 * (n - 1) ≤ (n - 1) * (n - 2) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left (n - 1) (by omega)
      omega
    · interval_cases n <;> norm_num
  rw [Nat.cast_sub hge]
  push_cast
  split_ifs <;> omega

/-- Exact disjoint exclusion decomposition for `p + q + r = n - 2`. -/
theorem admissibleCount_eq_sub_excl {n p q r : ℕ} (hn : 3 ≤ n) (hsum : p + q + r = n - 2) :
    admissibleCount n p q r + excl n p + excl n q + excl n r = totalTriples n := by
  let U := unrestrictedSet n
  let F1 := U.filter (fun t => n - p ≤ t.1)
  let F2 := U.filter (fun t => n - q ≤ t.2.1)
  let F3 := U.filter (fun t => n - r ≤ t.2.2)
  have hd12 : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [F1, F2, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h1 h2
    omega
  have hd13 : Disjoint F1 F3 := by
    rw [Finset.disjoint_left]; intro t h1 h3
    simp only [F1, F3, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h1 h3
    omega
  have hd23 : Disjoint F2 F3 := by
    rw [Finset.disjoint_left]; intro t h2 h3
    simp only [F2, F3, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h2 h3
    omega
  have hpart : U = admissibleSet n p q r ∪ (F1 ∪ (F2 ∪ F3)) := by
    ext t
    simp only [U, admissibleSet, F1, F2, F3, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ht
      by_cases h1 : t.1 < n - p
      · by_cases h2 : t.2.1 < n - q
        · by_cases h3 : t.2.2 < n - r
          · exact Or.inl ⟨ht, h1, h2, h3⟩
          · exact Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))
      · exact Or.inr (Or.inl ⟨ht, by omega⟩)
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  have hd_main : Disjoint (admissibleSet n p q r) (F1 ∪ (F2 ∪ F3)) := by
    rw [Finset.disjoint_left]; intro t hA hF
    simp only [admissibleSet, F1, F2, F3, Finset.mem_union, Finset.mem_filter] at hA hF
    rcases hF with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hF1 : F1.card = excl n p := excl_card_eq (by omega)
  have hF2 : F2.card = excl n q := by
    have hsymm : F2.card = (U.filter (fun t => n - q ≤ t.1)).card := by
      apply Finset.card_nbij (fun t => (t.2.1, t.1, t.2.2))
      · intro t ht; simp only [Finset.mem_coe, F2, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢; omega
      · intro t₁ _ t₂ _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
      · intro s hs
        simp only [Finset.mem_coe, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hs
        refine ⟨(s.2.1, s.1, s.2.2), ?_, rfl⟩
        simp only [Finset.mem_coe, F2, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
    rw [hsymm, excl_card_eq (by omega)]
  have hF3 : F3.card = excl n r := by
    have hsymm : F3.card = (U.filter (fun t => n - r ≤ t.1)).card := by
      apply Finset.card_nbij (fun t => (t.2.2, t.2.1, t.1))
      · intro t ht; simp only [Finset.mem_coe, F3, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢; omega
      · intro t₁ _ t₂ _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.2 (Prod.ext h.2.1 h.1)
      · intro s hs
        simp only [Finset.mem_coe, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hs
        refine ⟨(s.2.2, s.2.1, s.1), ?_, rfl⟩
        simp only [Finset.mem_coe, F3, U, unrestrictedSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
    rw [hsymm, excl_card_eq (by omega)]
  have htot : U.card = totalTriples n := card_unrestrictedSet hn
  have hcard := congrArg Finset.card hpart
  rw [htot, Finset.card_union_of_disjoint hd_main,
    Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hd12, hd13⟩),
    Finset.card_union_of_disjoint hd23, hF1, hF2, hF3] at hcard
  unfold admissibleCount
  omega

/-! ### Section 3: Balancing optimality (`n ≥ 16`) and closed-form mod-6 evaluation -/

private lemma excl_succ (n p : ℕ) : excl n (p + 1) = excl n p + dStep n (p + 1) := by
  unfold excl
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ p + 1)]

private lemma dStep_le_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : 2 * b ≤ n) :
    dStep n a ≤ dStep n b := by
  unfold dStep
  have h1 : ¬ (2 * a > n ∧ 3 * a ≠ 2 * n) := by omega
  have h2 : ¬ (2 * b > n ∧ 3 * b ≠ 2 * n) := by omega
  simp only [h1, h2, ↓reduceIte]
  split_ifs <;> omega

private lemma excl_closed_of_le_half {n p : ℕ} (hp : 2 * p ≤ n) :
    excl n p = if p = 0 then 0 else (p - 1) ^ 2 / 2 := by
  induction p with
  | zero => simp [excl]
  | succ k ih =>
    rw [excl_succ, ih (by omega)]
    unfold dStep
    have hno : ¬ (2 * (k + 1) > n ∧ 3 * (k + 1) ≠ 2 * n) := by omega
    simp only [hno, ↓reduceIte]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · have hmod : (t + t + 1 + 1) % 2 = 0 := by omega
        rw [hmod]; simp only [↓reduceIte]
        have h1 : (t + t + 1) ^ 2 / 2 = 2 * t ^ 2 + 2 * t := by
          have : (t + t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by ring
          omega
        have h2 : (t + t) ^ 2 / 2 = 2 * t ^ 2 := by
          have : (t + t) ^ 2 = 2 * (2 * t ^ 2) := by ring
          omega
        omega
      · have hmod : (2 * t + 1 + 1 + 1) % 2 ≠ 0 := by omega
        simp only [hmod, ↓reduceIte]
        have h1 : (2 * t + 1 + 1) ^ 2 / 2 = 2 * t ^ 2 + 4 * t + 2 := by
          have : (2 * t + 1 + 1) ^ 2 = 2 * (2 * t ^ 2 + 4 * t + 2) := by ring
          omega
        have h2 : (2 * t + 1) ^ 2 / 2 = 2 * t ^ 2 + 2 * t := by
          have : (2 * t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by ring
          omega
        omega

/-- Balanced triple `(b0, b1, b2)` summing to `n - 2`. -/
def bal0 (n : ℕ) : ℕ := (n - 2) / 3 + if 0 < (n - 2) % 3 then 1 else 0
def bal1 (n : ℕ) : ℕ := (n - 2) / 3 + if 1 < (n - 2) % 3 then 1 else 0
def bal2 (n : ℕ) : ℕ := (n - 2) / 3

lemma bal_sum {n : ℕ} (_hn : 3 ≤ n) : bal0 n + bal1 n + bal2 n = n - 2 := by
  unfold bal0 bal1 bal2; split_ifs <;> omega

/-- Lemma 4.2: For every `n ≥ 16`, every `(p, q, r)` with `p + q + r = n - 2` has
`excl n (bal0 n) + excl n (bal1 n) + excl n (bal2 n) ≤ excl n p + excl n q + excl n r`. -/
theorem excl_bal_le {n : ℕ} (hn : 16 ≤ n) (p q r : ℕ) (hsum : p + q + r = n - 2) :
    excl n (bal0 n) + excl n (bal1 n) + excl n (bal2 n) ≤
      excl n p + excl n q + excl n r := by
  -- Strong induction on `p^2 + q^2 + r^2`!
  suffices h : ∀ S p q r, p + q + r = n - 2 → p ^ 2 + q ^ 2 + r ^ 2 = S →
      excl n (bal0 n) + excl n (bal1 n) + excl n (bal2 n) ≤
        excl n p + excl n q + excl n r by
    exact h (p ^ 2 + q ^ 2 + r ^ 2) p q r hsum rfl
  intro S
  induction S using Nat.strongRecOn with
  | ind S ih =>
    intro p q r hsum hS
    -- Helper for one transfer `(x, y) ↦ (x - 1, y + 1)` when `x ≥ y + 2` and `dStep n (y + 1) ≤ dStep n x`
    have hstep : ∀ a b c : ℕ, a + b + c = n - 2 → a ^ 2 + b ^ 2 + c ^ 2 = S →
        b + 2 ≤ a → dStep n (b + 1) ≤ dStep n a →
        excl n (bal0 n) + excl n (bal1 n) + excl n (bal2 n) ≤
          excl n a + excl n b + excl n c := by
      intro a b c habc hsq hab hd
      have hsq_lt : (a - 1) ^ 2 + (b + 1) ^ 2 + c ^ 2 < S := by
        have h1 : (a - 1) ^ 2 + (b + 1) ^ 2 + 2 * (a - b - 1) = a ^ 2 + b ^ 2 := by
          zify [show 1 ≤ a by omega, show b ≤ a by omega, show 1 ≤ a - b by omega]; ring
        omega
      have hex_le : excl n (a - 1) + excl n (b + 1) ≤ excl n a + excl n b := by
        have ha : excl n a = excl n (a - 1) + dStep n a := by
          have := excl_succ n (a - 1)
          rw [show a - 1 + 1 = a by omega] at this
          exact this
        have hb : excl n (b + 1) = excl n b + dStep n (b + 1) := excl_succ n b
        omega
      have hrec := ih ((a - 1) ^ 2 + (b + 1) ^ 2 + c ^ 2) hsq_lt (a - 1) (b + 1) c
        (by omega) rfl
      omega
    -- Sort `(p, q, r)` into `M ≥ m₂ ≥ m₁` without changing sum, sum of squares, or excl sum
    have hperm : ∀ a b c : ℕ, a + b + c = n - 2 → a ^ 2 + b ^ 2 + c ^ 2 = S →
        c ≤ b → b ≤ a →
        excl n (bal0 n) + excl n (bal1 n) + excl n (bal2 n) ≤
          excl n a + excl n b + excl n c := by
      intro a b c habc hsq hcb hba
      by_cases hgt : n < 2 * a
      · -- `2a ≥ n + 1`, `4c ≤ n - 5` => `a - c ≥ 6` => `dStep n (c + 1) ≤ dStep n a`!
        have hac : c + 6 ≤ a := by omega
        have hd : dStep n (c + 1) ≤ dStep n a := by
          unfold dStep
          split_ifs <;> omega
        have := hstep a c b (by omega) (by linarith) (by omega) hd
        omega
      · by_cases hgap : c + 2 ≤ a
        · have hd : dStep n (c + 1) ≤ dStep n a := dStep_le_of_le_half (by omega) (by omega)
          have := hstep a c b (by omega) (by linarith) hgap hd
          omega
        · -- Balanced (`a - c ≤ 1`) and sorted `c ≤ b ≤ a` => `(a, b, c) = (bal0 n, bal1 n, bal2 n)`!
          have ha : a = bal0 n := by unfold bal0; split_ifs <;> omega
          have hb : b = bal1 n := by unfold bal1; split_ifs <;> omega
          have hc : c = bal2 n := by unfold bal2; omega
          rw [ha, hb, hc]
    -- Apply `hperm` to the sorted permutation of `(p, q, r)`
    rcases le_total p q with hpq | hqp
    · rcases le_total q r with hqr | hrq
      · have := hperm r q p (by omega) (by linarith) hpq hqr; omega
      · rcases le_total p r with hpr | hrp
        · have := hperm q r p (by omega) (by linarith) hpr hrq; omega
        · have := hperm q p r (by omega) (by linarith) hrp hpq; omega
    · rcases le_total p r with hpr | hrp
      · have := hperm r p q (by omega) (by linarith) hqp hpr; omega
      · rcases le_total q r with hqr | hrq
        · have := hperm p r q (by omega) (by linarith) hqr hrp; omega
        · have := hperm p q r (by omega) (by linarith) hrq hqp; omega

private lemma balanced_eq_mod0 {k : ℕ} (hk : 2 ≤ k) :
    totalTriples (6 * k) =
      conjecturedFormula (6 * k) +
        (bal0 (6 * k) - 1) ^ 2 / 2 + (bal1 (6 * k) - 1) ^ 2 / 2 + (bal2 (6 * k) - 1) ^ 2 / 2 := by
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold totalTriples conjecturedFormula modOffset bal0 bal1 bal2
  have hm6 : (6 * k) % 6 = 0 := by omega
  rw [hm6]
  have h1 : (6 * k - 1) * (6 * k - 2) / 2 = 18 * k ^ 2 - 9 * k + 1 := by
    have hle : 9 * k ≤ 18 * k ^ 2 := by nlinarith only [hk]
    have : (6 * k - 1) * (6 * k - 2) = 2 * (18 * k ^ 2 - 9 * k + 1) := by
      zify [show 1 ≤ 6 * k by omega, show 2 ≤ 6 * k by omega, hle]; ring
    omega
  have h2 : (6 * k - 1) / 2 = 3 * k - 1 := by omega
  have h3 : (6 * k) % 3 = 0 := by omega
  have h4 : (6 * k - 2) / 3 = 2 * k - 1 := by omega
  have h5 : (6 * k - 2) % 3 = 1 := by omega
  have h6 : (2 * k - 1) ^ 2 / 2 = 2 * k ^ 2 - 2 * k := by
    have hle : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 1) ^ 2 = 2 * (2 * k ^ 2 - 2 * k) + 1 := by
      zify [show 1 ≤ 2 * k by omega, hle]; ring
    omega
  have h7 : (2 * k - 2) ^ 2 / 2 = 2 * k ^ 2 - 4 * k + 2 := by
    have hle : 4 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 2) ^ 2 = 2 * (2 * k ^ 2 - 4 * k + 2) := by
      zify [show 2 ≤ 2 * k by omega, hle]; ring
    omega
  have h8 : (((6 * (k : ℤ)) ^ 2 - 4 * (6 * (k : ℤ)) + 6) / 3).toNat = 12 * k ^ 2 - 8 * k + 2 := by
    have : (6 * (k : ℤ)) ^ 2 - 4 * (6 * (k : ℤ)) + 6 = 3 * (12 * (k : ℤ) ^ 2 - 8 * (k : ℤ) + 2) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hnn : (0 : ℤ) ≤ 12 * (k : ℤ) ^ 2 - 8 * (k : ℤ) + 2 := by nlinarith only [hkZ]
    have hle : 8 * k ≤ 12 * k ^ 2 := by nlinarith only [hk]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn, Nat.cast_add, Nat.cast_sub hle]; push_cast; ring
  simp only [h1, h2, h3, h4, h5, show (0 : ℕ) < 1 by omega, show ¬((1 : ℕ) < 1) by omega,
    ↓reduceIte, Nat.add_zero]
  have hs1 : 2 * k - 1 + 1 - 1 = 2 * k - 1 := by omega
  have hs2 : 2 * k - 1 - 1 = 2 * k - 2 := by omega
  rw [hs1, hs2, h6, h7]
  have hcast : ((6 * k : ℕ) : ℤ) = 6 * (k : ℤ) := by push_cast; ring
  rw [hcast, h8]
  have hle1 : 9 * k ≤ 18 * k ^ 2 := by nlinarith only [hk]
  have hle0 : 3 * (3 * k - 1) ≤ 18 * k ^ 2 - 9 * k + 1 + 2 := by
    have : 18 * k ≤ 18 * k ^ 2 := by nlinarith only [hk]
    omega
  have hle2 : 8 * k ≤ 12 * k ^ 2 := by nlinarith only [hk]
  have hle3 : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  have hle4 : 4 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hle0, Nat.cast_add, Nat.cast_add, Nat.cast_sub hle1]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub (show 1 ≤ 3 * k by omega), Nat.cast_sub hle2, Nat.cast_sub hle3, Nat.cast_sub hle4]
  ring

private lemma balanced_eq_mod1 {k : ℕ} (hk : 2 ≤ k) :
    totalTriples (6 * k + 1) =
      conjecturedFormula (6 * k + 1) +
        (bal0 (6 * k + 1) - 1) ^ 2 / 2 + (bal1 (6 * k + 1) - 1) ^ 2 / 2 + (bal2 (6 * k + 1) - 1) ^ 2 / 2 := by
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold totalTriples conjecturedFormula modOffset bal0 bal1 bal2
  have hm6 : (6 * k + 1) % 6 = 1 := by omega
  rw [hm6]
  have h1 : (6 * k + 1 - 1) * (6 * k + 1 - 2) / 2 = 18 * k ^ 2 - 3 * k := by
    have hle : 3 * k ≤ 18 * k ^ 2 := by nlinarith only [hk]
    have : (6 * k + 1 - 1) * (6 * k + 1 - 2) = 2 * (18 * k ^ 2 - 3 * k) := by
      zify [show 1 ≤ 6 * k + 1 by omega, show 2 ≤ 6 * k + 1 by omega, hle]; ring
    omega
  have h2 : (6 * k + 1 - 1) / 2 = 3 * k := by omega
  have h3 : (6 * k + 1) % 3 ≠ 0 := by omega
  have h4 : (6 * k + 1 - 2) / 3 = 2 * k - 1 := by omega
  have h5 : (6 * k + 1 - 2) % 3 = 2 := by omega
  have h6 : (2 * k - 1) ^ 2 / 2 = 2 * k ^ 2 - 2 * k := by
    have hle : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 1) ^ 2 = 2 * (2 * k ^ 2 - 2 * k) + 1 := by
      zify [show 1 ≤ 2 * k by omega, hle]; ring
    omega
  have h7 : (2 * k - 2) ^ 2 / 2 = 2 * k ^ 2 - 4 * k + 2 := by
    have hle : 4 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 2) ^ 2 = 2 * (2 * k ^ 2 - 4 * k + 2) := by
      zify [show 2 ≤ 2 * k by omega, hle]; ring
    omega
  have h8 : (((6 * (k : ℤ) + 1) ^ 2 - 4 * (6 * (k : ℤ) + 1) + -3) / 3).toNat = 12 * k ^ 2 - 4 * k - 2 := by
    have : (6 * (k : ℤ) + 1) ^ 2 - 4 * (6 * (k : ℤ) + 1) + -3 = 3 * (12 * (k : ℤ) ^ 2 - 4 * (k : ℤ) - 2) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hnn : (0 : ℤ) ≤ 12 * (k : ℤ) ^ 2 - 4 * (k : ℤ) - 2 := by nlinarith only [hkZ]
    have hle1 : 4 * k + 2 ≤ 12 * k ^ 2 := by nlinarith only [hk]
    have hle2 : 2 ≤ 12 * k ^ 2 - 4 * k := by omega
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn, Nat.cast_sub hle2, Nat.cast_sub (by omega : 4 * k ≤ 12 * k ^ 2)]; push_cast; ring
  simp only [h1, h2, h3, h4, h5, show (0 : ℕ) < 2 by omega, show (1 : ℕ) < 2 by omega,
    ↓reduceIte, Nat.add_zero]
  have hs1 : 2 * k - 1 + 1 - 1 = 2 * k - 1 := by omega
  have hs2 : 2 * k - 1 - 1 = 2 * k - 2 := by omega
  rw [hs1, hs2, h6, h7]
  have hcast : ((6 * k + 1 : ℕ) : ℤ) = 6 * (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, h8]
  have hle1 : 3 * k ≤ 18 * k ^ 2 := by nlinarith only [hk]
  have hle0 : 3 * (3 * k) ≤ 18 * k ^ 2 - 3 * k := by
    have : 12 * k ≤ 18 * k ^ 2 := by nlinarith only [hk]
    omega
  have hle2a : 4 * k + 2 ≤ 12 * k ^ 2 := by nlinarith only [hk]
  have hle2b : 2 ≤ 12 * k ^ 2 - 4 * k := by omega
  have hle2c : 4 * k ≤ 12 * k ^ 2 := by omega
  have hle3 : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  have hle4 : 4 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hle0, Nat.cast_sub hle1]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub hle2b, Nat.cast_sub hle2c, Nat.cast_sub hle3, Nat.cast_sub hle4]
  ring

private lemma balanced_eq_mod2 {k : ℕ} (hk : 2 ≤ k) :
    totalTriples (6 * k + 2) =
      conjecturedFormula (6 * k + 2) +
        (bal0 (6 * k + 2) - 1) ^ 2 / 2 + (bal1 (6 * k + 2) - 1) ^ 2 / 2 + (bal2 (6 * k + 2) - 1) ^ 2 / 2 := by
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold totalTriples conjecturedFormula modOffset bal0 bal1 bal2
  have hm6 : (6 * k + 2) % 6 = 2 := by omega
  rw [hm6]
  have h1 : (6 * k + 2 - 1) * (6 * k + 2 - 2) / 2 = 18 * k ^ 2 + 3 * k := by
    have : (6 * k + 2 - 1) * (6 * k + 2 - 2) = 2 * (18 * k ^ 2 + 3 * k) := by
      zify [show 1 ≤ 6 * k + 2 by omega, show 2 ≤ 6 * k + 2 by omega]; ring
    omega
  have h2 : (6 * k + 2 - 1) / 2 = 3 * k := by omega
  have h3 : (6 * k + 2) % 3 ≠ 0 := by omega
  have h4 : (6 * k + 2 - 2) / 3 = 2 * k := by omega
  have h5 : (6 * k + 2 - 2) % 3 = 0 := by omega
  have h6 : (2 * k - 1) ^ 2 / 2 = 2 * k ^ 2 - 2 * k := by
    have hle : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 1) ^ 2 = 2 * (2 * k ^ 2 - 2 * k) + 1 := by
      zify [show 1 ≤ 2 * k by omega, hle]; ring
    omega
  have h8 : (((6 * (k : ℤ) + 2) ^ 2 - 4 * (6 * (k : ℤ) + 2) + 4) / 3).toNat = 12 * k ^ 2 := by
    have : (6 * (k : ℤ) + 2) ^ 2 - 4 * (6 * (k : ℤ) + 2) + 4 = 3 * (12 * (k : ℤ) ^ 2) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hnn : (0 : ℤ) ≤ 12 * (k : ℤ) ^ 2 := by nlinarith only [hkZ]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn]; push_cast; ring
  simp only [h1, h2, h3, h4, h5, show ¬((0 : ℕ) < 0) by omega, show ¬((1 : ℕ) < 0) by omega,
    ↓reduceIte, Nat.add_zero]
  rw [h6]
  have hcast : ((6 * k + 2 : ℕ) : ℤ) = 6 * (k : ℤ) + 2 := by push_cast; ring
  rw [hcast, h8]
  have hle0 : 3 * (3 * k) ≤ 18 * k ^ 2 + 3 * k := by nlinarith only [hk]
  have hle3 : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hle0]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hle3]
  ring

private lemma balanced_eq_mod3 {k : ℕ} (hk : 2 ≤ k) :
    totalTriples (6 * k + 3) =
      conjecturedFormula (6 * k + 3) +
        (bal0 (6 * k + 3) - 1) ^ 2 / 2 + (bal1 (6 * k + 3) - 1) ^ 2 / 2 + (bal2 (6 * k + 3) - 1) ^ 2 / 2 := by
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold totalTriples conjecturedFormula modOffset bal0 bal1 bal2
  have hm6 : (6 * k + 3) % 6 = 3 := by omega
  rw [hm6]
  have h1 : (6 * k + 3 - 1) * (6 * k + 3 - 2) / 2 = 18 * k ^ 2 + 9 * k + 1 := by
    have : (6 * k + 3 - 1) * (6 * k + 3 - 2) = 2 * (18 * k ^ 2 + 9 * k + 1) := by
      zify [show 1 ≤ 6 * k + 3 by omega, show 2 ≤ 6 * k + 3 by omega]; ring
    omega
  have h2 : (6 * k + 3 - 1) / 2 = 3 * k + 1 := by omega
  have h3 : (6 * k + 3) % 3 = 0 := by omega
  have h4 : (6 * k + 3 - 2) / 3 = 2 * k := by omega
  have h5 : (6 * k + 3 - 2) % 3 = 1 := by omega
  have h6 : (2 * k) ^ 2 / 2 = 2 * k ^ 2 := by
    have : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  have h7 : (2 * k - 1) ^ 2 / 2 = 2 * k ^ 2 - 2 * k := by
    have hle : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 1) ^ 2 = 2 * (2 * k ^ 2 - 2 * k) + 1 := by
      zify [show 1 ≤ 2 * k by omega, hle]; ring
    omega
  have h8 : (((6 * (k : ℤ) + 3) ^ 2 - 4 * (6 * (k : ℤ) + 3) + 3) / 3).toNat = 12 * k ^ 2 + 4 * k := by
    have : (6 * (k : ℤ) + 3) ^ 2 - 4 * (6 * (k : ℤ) + 3) + 3 = 3 * (12 * (k : ℤ) ^ 2 + 4 * (k : ℤ)) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hnn : (0 : ℤ) ≤ 12 * (k : ℤ) ^ 2 + 4 * (k : ℤ) := by nlinarith only [hkZ]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn]; push_cast; ring
  simp only [h1, h2, h3, h4, h5, show (0 : ℕ) < 1 by omega, show ¬((1 : ℕ) < 1) by omega,
    ↓reduceIte, Nat.add_zero, Nat.add_sub_cancel]
  rw [h6, h7]
  have hcast : ((6 * k + 3 : ℕ) : ℤ) = 6 * (k : ℤ) + 3 := by push_cast; ring
  rw [hcast, h8]
  have hle0 : 3 * (3 * k + 1) ≤ 18 * k ^ 2 + 9 * k + 1 + 2 := by nlinarith only [hk]
  have hle3 : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hle0]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hle3]
  ring

private lemma balanced_eq_mod4 {k : ℕ} (hk : 2 ≤ k) :
    totalTriples (6 * k + 4) =
      conjecturedFormula (6 * k + 4) +
        (bal0 (6 * k + 4) - 1) ^ 2 / 2 + (bal1 (6 * k + 4) - 1) ^ 2 / 2 + (bal2 (6 * k + 4) - 1) ^ 2 / 2 := by
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold totalTriples conjecturedFormula modOffset bal0 bal1 bal2
  have hm6 : (6 * k + 4) % 6 = 4 := by omega
  rw [hm6]
  have h1 : (6 * k + 4 - 1) * (6 * k + 4 - 2) / 2 = 18 * k ^ 2 + 15 * k + 3 := by
    have : (6 * k + 4 - 1) * (6 * k + 4 - 2) = 2 * (18 * k ^ 2 + 15 * k + 3) := by
      zify [show 1 ≤ 6 * k + 4 by omega, show 2 ≤ 6 * k + 4 by omega]; ring
    omega
  have h2 : (6 * k + 4 - 1) / 2 = 3 * k + 1 := by omega
  have h3 : (6 * k + 4) % 3 ≠ 0 := by omega
  have h4 : (6 * k + 4 - 2) / 3 = 2 * k := by omega
  have h5 : (6 * k + 4 - 2) % 3 = 2 := by omega
  have h6 : (2 * k) ^ 2 / 2 = 2 * k ^ 2 := by
    have : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  have h7 : (2 * k - 1) ^ 2 / 2 = 2 * k ^ 2 - 2 * k := by
    have hle : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
    have : (2 * k - 1) ^ 2 = 2 * (2 * k ^ 2 - 2 * k) + 1 := by
      zify [show 1 ≤ 2 * k by omega, hle]; ring
    omega
  have h8 : (((6 * (k : ℤ) + 4) ^ 2 - 4 * (6 * (k : ℤ) + 4) + 0) / 3).toNat = 12 * k ^ 2 + 8 * k := by
    have : (6 * (k : ℤ) + 4) ^ 2 - 4 * (6 * (k : ℤ) + 4) + 0 = 3 * (12 * (k : ℤ) ^ 2 + 8 * (k : ℤ)) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hnn : (0 : ℤ) ≤ 12 * (k : ℤ) ^ 2 + 8 * (k : ℤ) := by nlinarith only [hkZ]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn]; push_cast; ring
  simp only [h1, h2, h3, h4, h5, show (0 : ℕ) < 2 by omega, show (1 : ℕ) < 2 by omega,
    ↓reduceIte, Nat.add_zero, Nat.add_sub_cancel]
  rw [h6, h7]
  have hcast : ((6 * k + 4 : ℕ) : ℤ) = 6 * (k : ℤ) + 4 := by push_cast; ring
  rw [hcast, h8]
  have hle0 : 3 * (3 * k + 1) ≤ 18 * k ^ 2 + 15 * k + 3 := by nlinarith only [hk]
  have hle3 : 2 * k ≤ 2 * k ^ 2 := by nlinarith only [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hle0]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hle3]
  ring

private lemma balanced_eq_mod5 {k : ℕ} (hk : 2 ≤ k) :
    totalTriples (6 * k + 5) =
      conjecturedFormula (6 * k + 5) +
        (bal0 (6 * k + 5) - 1) ^ 2 / 2 + (bal1 (6 * k + 5) - 1) ^ 2 / 2 + (bal2 (6 * k + 5) - 1) ^ 2 / 2 := by
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold totalTriples conjecturedFormula modOffset bal0 bal1 bal2
  have hm6 : (6 * k + 5) % 6 = 5 := by omega
  rw [hm6]
  have h1 : (6 * k + 5 - 1) * (6 * k + 5 - 2) / 2 = 18 * k ^ 2 + 21 * k + 6 := by
    have : (6 * k + 5 - 1) * (6 * k + 5 - 2) = 2 * (18 * k ^ 2 + 21 * k + 6) := by
      zify [show 1 ≤ 6 * k + 5 by omega, show 2 ≤ 6 * k + 5 by omega]; ring
    omega
  have h2 : (6 * k + 5 - 1) / 2 = 3 * k + 2 := by omega
  have h3 : (6 * k + 5) % 3 ≠ 0 := by omega
  have h4 : (6 * k + 5 - 2) / 3 = 2 * k + 1 := by omega
  have h5 : (6 * k + 5 - 2) % 3 = 0 := by omega
  have h6 : (2 * k) ^ 2 / 2 = 2 * k ^ 2 := by
    have : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  have h8 : (((6 * (k : ℤ) + 5) ^ 2 - 4 * (6 * (k : ℤ) + 5) + -5) / 3).toNat = 12 * k ^ 2 + 12 * k := by
    have : (6 * (k : ℤ) + 5) ^ 2 - 4 * (6 * (k : ℤ) + 5) + -5 = 3 * (12 * (k : ℤ) ^ 2 + 12 * (k : ℤ)) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hnn : (0 : ℤ) ≤ 12 * (k : ℤ) ^ 2 + 12 * (k : ℤ) := by nlinarith only [hkZ]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn]; push_cast; ring
  simp only [h1, h2, h3, h4, h5, show ¬((0 : ℕ) < 0) by omega, show ¬((1 : ℕ) < 0) by omega,
    ↓reduceIte, Nat.add_zero, Nat.add_sub_cancel]
  rw [h6]
  have hcast : ((6 * k + 5 : ℕ) : ℤ) = 6 * (k : ℤ) + 5 := by push_cast; ring
  rw [hcast, h8]
  have hle0 : 3 * (3 * k + 2) ≤ 18 * k ^ 2 + 21 * k + 6 := by nlinarith only [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hle0]; push_cast; ring

/-- Closed-form identity for `n ≥ 16`: `totalTriples n - excl_bal(n) = conjecturedFormula n`. -/
theorem balanced_eq_conjectured {n : ℕ} (hn : 16 ≤ n) :
    totalTriples n =
      conjecturedFormula n + excl n (bal0 n) + excl n (bal1 n) + excl n (bal2 n) := by
  have hb0 : 2 * bal0 n ≤ n := by unfold bal0; split_ifs <;> omega
  have hb1 : 2 * bal1 n ≤ n := by unfold bal1; split_ifs <;> omega
  have hb2 : 2 * bal2 n ≤ n := by unfold bal2; omega
  rw [excl_closed_of_le_half hb0, excl_closed_of_le_half hb1, excl_closed_of_le_half hb2]
  have hpos0 : bal0 n ≠ 0 := by unfold bal0; omega
  have hpos1 : bal1 n ≠ 0 := by unfold bal1; omega
  have hpos2 : bal2 n ≠ 0 := by unfold bal2; omega
  simp only [hpos0, hpos1, hpos2, ↓reduceIte]
  set k := n / 6
  have hk : 2 ≤ k := by omega
  have hrem : n % 6 < 6 := Nat.mod_lt n (by omega)
  have hdiv : n = 6 * k + n % 6 := by omega
  generalize hj : n % 6 = j at hrem hdiv
  interval_cases j
  · rw [hdiv, Nat.add_zero]; exact balanced_eq_mod0 hk
  · rw [hdiv]; exact balanced_eq_mod1 hk
  · rw [hdiv]; exact balanced_eq_mod2 hk
  · rw [hdiv]; exact balanced_eq_mod3 hk
  · rw [hdiv]; exact balanced_eq_mod4 hk
  · rw [hdiv]; exact balanced_eq_mod5 hk

/-! ### Section 4: Finite cases `3 ≤ n ≤ 15` and main theorem for all `n ≥ 3` -/

/-- Fast recursive evaluator `exclRec n p = excl n p` for `decide` on `3 ≤ n ≤ 15`. -/
private def exclRec (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => exclRec n p + dStep n (p + 1)

private lemma exclRec_eq (n p : ℕ) : exclRec n p = excl n p := by
  induction p with
  | zero => simp [exclRec, excl]
  | succ k ih => rw [exclRec, ih, excl_succ]

private def checkUpperOne (n : ℕ) : Bool :=
  (List.range (n - 1)).all fun p =>
    (List.range (n - 1 - p)).all fun q =>
      decide (totalTriples n ≤ conjecturedFormula n +
        exclRec n p + exclRec n q + exclRec n (n - 2 - p - q))

private def checkAttainOne (n : ℕ) : Bool :=
  (List.range (n - 1)).any fun p =>
    (List.range (n - 1 - p)).any fun q =>
      decide (totalTriples n = conjecturedFormula n +
        exclRec n p + exclRec n q + exclRec n (n - 2 - p - q))

private lemma checkSmall_3_15 :
    (List.range 13).all (fun i => checkUpperOne (i + 3) && checkAttainOne (i + 3)) = true := by
  decide

/-- Complete combinatorial theorem for all `n ≥ 3`:
1. Every `(p, q, r)` with `p + q + r = n - 2` satisfies `admissibleCount n p q r ≤ conjecturedFormula n`.
2. There exists `(p, q, r)` with `p + q + r = n - 2` achieving `admissibleCount n p q r = conjecturedFormula n`. -/
theorem nakai_A400474_combinatorial {n : ℕ} (hn : 3 ≤ n) :
    (∀ p q r : ℕ, p + q + r = n - 2 → admissibleCount n p q r ≤ conjecturedFormula n) ∧
    (∃ p q r : ℕ, p + q + r = n - 2 ∧ admissibleCount n p q r = conjecturedFormula n) := by
  by_cases h16 : 16 ≤ n
  · constructor
    · intro p q r hsum
      have h1 := admissibleCount_eq_sub_excl hn hsum
      have h2 := excl_bal_le h16 p q r hsum
      have h3 := balanced_eq_conjectured h16
      omega
    · refine ⟨bal0 n, bal1 n, bal2 n, bal_sum hn, ?_⟩
      have h1 := admissibleCount_eq_sub_excl hn (bal_sum hn)
      have h3 := balanced_eq_conjectured h16
      omega
  · have hchk := List.all_eq_true.mp checkSmall_3_15 (n - 3) (List.mem_range.mpr (by omega))
    have hsub : n - 3 + 3 = n := by omega
    rw [hsub, Bool.and_eq_true] at hchk
    constructor
    · intro p q r hsum
      have hu := List.all_eq_true.mp hchk.1 p (List.mem_range.mpr (by omega))
      have hq := List.all_eq_true.mp hu q (List.mem_range.mpr (by omega))
      have hle := of_decide_eq_true hq
      rw [exclRec_eq, exclRec_eq, exclRec_eq, show n - 2 - p - q = r by omega] at hle
      have h1 := admissibleCount_eq_sub_excl hn hsum
      omega
    · obtain ⟨p, hp_mem, hp_any⟩ := List.any_eq_true.mp hchk.2
      obtain ⟨q, hq_mem, hq_eq⟩ := List.any_eq_true.mp hp_any
      have hp_lt := List.mem_range.mp hp_mem
      have hq_lt := List.mem_range.mp hq_mem
      have heq := of_decide_eq_true hq_eq
      rw [exclRec_eq, exclRec_eq, exclRec_eq] at heq
      refine ⟨p, q, n - 2 - p - q, by omega, ?_⟩
      have h1 := admissibleCount_eq_sub_excl hn (by omega : p + q + (n - 2 - p - q) = n - 2)
      omega

/-- **Main Theorem (Upper Bound — OEIS A400474):**
For every `n ≥ 3` and every nondegenerate triangle with positive angles `A + B + C = π`,
the number of pairwise distinct integer-multiple angle triples `(Xπ/n, Yπ/n, Zπ/n)` in
`Ω(A, B, C)` is at most `conjecturedFormula n`. -/
theorem nakai_A400474_upper {n : ℕ} (hn : 3 ≤ n) {A B C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hsum : A + B + C = Real.pi) :
    (angleTripleSet n A B C).card ≤ conjecturedFormula n := by
  obtain ⟨heq, hfl⟩ := angleTriples_card_eq_admissibleCount hn hA hB hC hsum
  rw [heq]
  set p := Nat.floor ((n : ℝ) * A / Real.pi)
  set q := Nat.floor ((n : ℝ) * B / Real.pi)
  set r := Nat.floor ((n : ℝ) * C / Real.pi)
  -- Shrink `(p, q, r)` to `(p', q', r')` summing to `n - 2`
  have hex : ∃ p' q' r' : ℕ, p' ≤ p ∧ q' ≤ q ∧ r' ≤ r ∧ p' + q' + r' = n - 2 := by
    let p' := min p (n - 2)
    let q' := min q (n - 2 - p')
    let r' := n - 2 - p' - q'
    exact ⟨p', q', r', min_le_left _ _, min_le_left _ _, by omega, by omega⟩
  obtain ⟨p', q', r', hp', hq', hr', hsum'⟩ := hex
  exact le_trans (admissibleCount_anti hp' hq' hr')
    ((nakai_A400474_combinatorial hn).1 p' q' r' hsum')

/-- **Main Theorem (Attainment — OEIS A400474):**
For every `n ≥ 3`, there exist positive triangle angles `A + B + C = π` whose admissible
integer-multiple angle count equals `conjecturedFormula n`. -/
theorem nakai_A400474_attained {n : ℕ} (hn : 3 ≤ n) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ A + B + C = Real.pi ∧
      (angleTripleSet n A B C).card = conjecturedFormula n := by
  obtain ⟨p, q, r, hsum, hcnt⟩ := (nakai_A400474_combinatorial hn).2
  obtain ⟨A, B, C, hA, hB, hC, hpi, hp, hq, hr⟩ := exists_real_angles_of_floors hn hsum
  refine ⟨A, B, C, hA, hB, hC, hpi, ?_⟩
  rw [(angleTriples_card_eq_admissibleCount hn hA hB hC hpi).1, hp, hq, hr, hcnt]

end NakaiA400474
