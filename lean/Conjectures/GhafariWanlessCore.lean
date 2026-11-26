import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Conjectures.GhafariWanlessData

/-!
# Proof of Conjecture 3 (Wormald's Question) of Ghafari & Wanless (`arXiv:2607.17547v1`)

In *Latin Squares whose transversals intersect in unusual ways* (`arXiv:2607.17547v1`, July 2026),
Afsane Ghafari and Ian M. Wanless study Latin squares of even order whose transversals have no
disjoint pair yet share no pinned entry, and pose:

**Conjecture 3 (`arXiv:2607.17547v1`).** *Let $n \ge 28$ be an even integer. There is a latin
square of order $n$ that has no two disjoint transversals, but also has no pinned entry.*

Ghafari and Wanless verified this computationally for $n = 28$ and $32 \le n \le 10\,000$, leaving
$n = 30$ and all even $n > 10\,000$ open.

We prove Conjecture 3 for **every** even integer $n \ge 22$ with $n \ne 24$ (in particular, every
even $n \ge 28$, including $n = 30$ and all $n > 10\,000$). All proofs use only standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) with zero `sorry` and zero `native_decide`.
-/

namespace GhafariWanless

open Finset BigOperators

/-! ## Section 1: Latin Squares, Transversals, and the Δ-Lemma -/

/-- A Latin square of order `n` on `Fin n`. -/
structure LatinSquare (n : ℕ) where
  entry : Fin n → Fin n → Fin n
  row_bijective : ∀ r : Fin n, Function.Bijective (entry r)
  col_bijective : ∀ c : Fin n, Function.Bijective (fun r => entry r c)

/-- A transversal of `L` is a bijection `T : Fin n → Fin n` (row `r` chooses column `T r`)
such that the selected symbols `r ↦ L.entry r (T r)` are also a bijection. -/
def IsTransversal {n : ℕ} (L : LatinSquare n) (T : Fin n → Fin n) : Prop :=
  Function.Bijective T ∧ Function.Bijective (fun r => L.entry r (T r))

/-- Two transversals are disjoint if they pick different columns in every row. -/
def DisjointTransversals {n : ℕ} (T₁ T₂ : Fin n → Fin n) : Prop :=
  ∀ r : Fin n, T₁ r ≠ T₂ r

/-- Entry `(r, c)` is pinned in `L` if every transversal of `L` contains `(r, c)`. -/
def IsPinnedEntry {n : ℕ} (L : LatinSquare n) (r c : Fin n) : Prop :=
  ∀ T : Fin n → Fin n, IsTransversal L T → T r = c

/-- `L` has no pinned entry. -/
def HasNoPinnedEntry {n : ℕ} (L : LatinSquare n) : Prop :=
  ∀ r c : Fin n, ¬ IsPinnedEntry L r c

/-- Three transversals with empty triple intersection guarantee no pinned entry. -/
theorem no_pinned_of_three_transversals {n : ℕ} {L : LatinSquare n}
    {T₀ T₁ T₂ : Fin n → Fin n}
    (h₀ : IsTransversal L T₀) (h₁ : IsTransversal L T₁) (h₂ : IsTransversal L T₂)
    (hempty : ∀ r : Fin n, ¬ (T₀ r = T₁ r ∧ T₁ r = T₂ r)) :
    HasNoPinnedEntry L := by
  intro r c hpin
  have e0 := hpin T₀ h₀
  have e1 := hpin T₁ h₁
  have e2 := hpin T₂ h₂
  exact hempty r ⟨e0.trans e1.symm, e1.trans e2.symm⟩

private lemma sum_fin_val_int (n : ℕ) :
    2 * (∑ i : Fin n, (i.val : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    linarith

private lemma sum_fin_val_even (m : ℕ) :
    (∑ i : Fin (2 * m), (i.val : ℤ)) = (m : ℤ) * (2 * (m : ℤ) - 1) := by
  have h := sum_fin_val_int (2 * m)
  push_cast at h
  linarith

private lemma sum_bijective_fin_val {n : ℕ} {f : Fin n → Fin n} (hf : Function.Bijective f) :
    (∑ r : Fin n, ((f r).val : ℤ)) = ∑ r : Fin n, (r.val : ℤ) :=
  Fintype.sum_bijective f hf _ _ (fun _ => rfl)

private lemma modEq_sum_fin {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (d : ℤ)
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD d]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD d] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Int.ModEq.refl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **The Δ-Lemma (Ghafari–Wanless Lemma 5).** -/
theorem delta_sum_modEq {m : ℕ} (L : LatinSquare (2 * m))
    (Δ : Fin (2 * m) → Fin (2 * m) → ℤ)
    (hL : ∀ r c, ((L.entry r c).val : ℤ) ≡ (r.val : ℤ) + (c.val : ℤ) + Δ r c [ZMOD (2 * m : ℤ)])
    (T : Fin (2 * m) → Fin (2 * m)) (hT : IsTransversal L T) :
    (∑ r : Fin (2 * m), Δ r (T r)) ≡ (m : ℤ) [ZMOD (2 * m : ℤ)] := by
  have hsum_mod :
      (∑ r : Fin (2 * m), ((L.entry r (T r)).val : ℤ)) ≡
      (∑ r : Fin (2 * m), ((r.val : ℤ) + ((T r).val : ℤ) + Δ r (T r))) [ZMOD (2 * m : ℤ)] :=
    modEq_sum_fin Finset.univ _ _ _ (fun r _ => hL r (T r))
  have hS_L : (∑ r : Fin (2 * m), ((L.entry r (T r)).val : ℤ)) =
      ∑ r : Fin (2 * m), (r.val : ℤ) := sum_bijective_fin_val hT.2
  have hS_T : (∑ r : Fin (2 * m), ((T r).val : ℤ)) =
      ∑ r : Fin (2 * m), (r.val : ℤ) := sum_bijective_fin_val hT.1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hS_L, hS_T] at hsum_mod
  have hS_val : (∑ r : Fin (2 * m), (r.val : ℤ)) = (m : ℤ) * (2 * (m : ℤ) - 1) :=
    sum_fin_val_even m
  rw [Int.modEq_iff_dvd] at hsum_mod ⊢
  rcases hsum_mod with ⟨k, hk⟩
  rw [hS_val] at hk
  refine ⟨(m : ℤ) - k, ?_⟩
  linarith

/-- If `∑ max Δ = m + 1`, `∑ min Δ > -m`, and three distinct rows each have a unique maximum
column `c_k`, then `L` has no two disjoint transversals. -/
theorem no_disjoint_of_three_unique_max {m : ℕ} (hm : 0 < m)
    (L : LatinSquare (2 * m))
    (Δ : Fin (2 * m) → Fin (2 * m) → ℤ)
    (hL : ∀ r c, ((L.entry r c).val : ℤ) ≡ (r.val : ℤ) + (c.val : ℤ) + Δ r c [ZMOD (2 * m : ℤ)])
    (mn mx : Fin (2 * m) → ℤ)
    (hmn : ∀ r c, mn r ≤ Δ r c)
    (hmx : ∀ r c, Δ r c ≤ mx r)
    (hsum_mx : (∑ r : Fin (2 * m), mx r) = (m : ℤ) + 1)
    (hsum_mn : -((m : ℤ)) < ∑ r : Fin (2 * m), mn r)
    (r₁ r₂ r₃ c₁ c₂ c₃ : Fin (2 * m))
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (hu₁ : ∀ c, c ≠ c₁ → Δ r₁ c ≤ mx r₁ - 1)
    (hu₂ : ∀ c, c ≠ c₂ → Δ r₂ c ≤ mx r₂ - 1)
    (hu₃ : ∀ c, c ≠ c₃ → Δ r₃ c ≤ mx r₃ - 1) :
    ∀ T₁ T₂, IsTransversal L T₁ → IsTransversal L T₂ → ¬ DisjointTransversals T₁ T₂ := by
  have hits_two : ∀ T, IsTransversal L T →
      (T r₁ = c₁ ∧ T r₂ = c₂) ∨ (T r₁ = c₁ ∧ T r₃ = c₃) ∨ (T r₂ = c₂ ∧ T r₃ = c₃) := by
    intro T hT
    have hmod := delta_sum_modEq L Δ hL T hT
    have hlo : -((m : ℤ)) < ∑ r : Fin (2 * m), Δ r (T r) :=
      lt_of_lt_of_le hsum_mn (Finset.sum_le_sum (fun r _ => hmn r (T r)))
    have hhi : (∑ r : Fin (2 * m), Δ r (T r)) ≤ (m : ℤ) + 1 := by
      calc (∑ r : Fin (2 * m), Δ r (T r)) ≤ ∑ r : Fin (2 * m), mx r :=
            Finset.sum_le_sum (fun r _ => hmx r (T r))
        _ = (m : ℤ) + 1 := hsum_mx
    have hsum_eq : (∑ r : Fin (2 * m), Δ r (T r)) = (m : ℤ) := by
      rw [Int.modEq_iff_dvd] at hmod
      rcases hmod with ⟨k, hk⟩
      have hk0 : k = 0 := by nlinarith
      subst hk0
      linarith
    have hdef : (∑ r : Fin (2 * m), (mx r - Δ r (T r))) = 1 := by
      rw [Finset.sum_sub_distrib, hsum_mx, hsum_eq]; ring
    have hnonneg : ∀ r : Fin (2 * m), 0 ≤ mx r - Δ r (T r) :=
      fun r => sub_nonneg.mpr (hmx r (T r))
    have pair_contra : ∀ (a b : Fin (2 * m)), a ≠ b →
        1 ≤ mx a - Δ a (T a) → 1 ≤ mx b - Δ b (T b) → False := by
      intro a b hab ha hb
      have hsub : ({a, b} : Finset (Fin (2 * m))) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hnonneg r)
      rw [Finset.sum_pair hab, hdef] at hle
      linarith
    by_cases e1 : T r₁ = c₁
    · by_cases e2 : T r₂ = c₂
      · exact Or.inl ⟨e1, e2⟩
      · by_cases e3 : T r₃ = c₃
        · exact Or.inr (Or.inl ⟨e1, e3⟩)
        · exfalso
          exact pair_contra r₂ r₃ h23 (by linarith [hu₂ (T r₂) e2]) (by linarith [hu₃ (T r₃) e3])
    · by_cases e2 : T r₂ = c₂
      · by_cases e3 : T r₃ = c₃
        · exact Or.inr (Or.inr ⟨e2, e3⟩)
        · exfalso
          exact pair_contra r₁ r₃ h13 (by linarith [hu₁ (T r₁) e1]) (by linarith [hu₃ (T r₃) e3])
      · exfalso
        exact pair_contra r₁ r₂ h12 (by linarith [hu₁ (T r₁) e1]) (by linarith [hu₂ (T r₂) e2])
  intro T₁ T₂ hT₁ hT₂ hdisj
  rcases hits_two T₁ hT₁ with ⟨a1, a2⟩ | ⟨a1, a3⟩ | ⟨a2, a3⟩ <;>
    rcases hits_two T₂ hT₂ with ⟨b1, b2⟩ | ⟨b1, b3⟩ | ⟨b2, b3⟩
  · exact hdisj r₁ (a1.trans b1.symm)
  · exact hdisj r₁ (a1.trans b1.symm)
  · exact hdisj r₂ (a2.trans b2.symm)
  · exact hdisj r₁ (a1.trans b1.symm)
  · exact hdisj r₁ (a1.trans b1.symm)
  · exact hdisj r₃ (a3.trans b3.symm)
  · exact hdisj r₂ (a2.trans b2.symm)
  · exact hdisj r₃ (a3.trans b3.symm)
  · exact hdisj r₂ (a2.trans b2.symm)

/-! ## Section 2: Modular Row-Block Construction of `L_{n, n0}` -/

private lemma emod_add_one {n : ℕ} (hn : 2 ≤ n) : ((n : ℤ) + 1) % (n : ℤ) = 1 := by
  rw [Int.add_emod, Int.emod_self, zero_add, Int.emod_emod, Int.emod_eq_of_lt (by omega) (by omega)]

private lemma emod_neg_one {n : ℕ} (hn : 2 ≤ n) : (-(1 : ℤ)) % (n : ℤ) = (n : ℤ) - 1 := by
  have h : -(1 : ℤ) = (n : ℤ) * (-1) + ((n : ℤ) - 1) := by ring
  rw [h, Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

/-- Even horizontal column shift `sh` for base order `n0`, placing gadget columns near `n0 / 2`. -/
def baseShift (n0 : ℕ) : ℕ := 2 * ((n0 / 2 - 4) / 2)

/-- Small lookup table for the 11 special columns `j ∈ {0, ..., 10}` of 4-row gadget `A`. -/
def dATab (row j : ℕ) : ℤ :=
  match row, j with
  | 0, 1 => 3 | 0, 4 => 1 | 0, 5 => 3 | 0, 8 => 3 | 0, _ => 0
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 2 | 1, 6 => 1 | 1, 7 => 2 | 1, 9 => 2 | 1, _ => 0
  | 2, 1 => -2 | 2, 2 => -1 | 2, 3 => 1 | 2, 4 => -2 | 2, 5 => -2 | 2, 6 => -1 | 2, 8 => -2 | 2, 9 => -1 | 2, _ => 0
  | _, 1 => -2 | _, 3 => -2 | _, 4 => -1 | _, 5 => -1 | _, 7 => -2 | _, 8 => -1 | _, 9 => -1 | _, _ => 0

/-- 4-row gadget `A` shifted horizontally by even `s` (`4 ≤ s`, `s + 14 < n`). -/
def dA (row s c : ℕ) : ℤ :=
  if s ≤ c ∧ c ≤ s + 10 then dATab row (c - s)
  else if c % 2 = 1 then (if row < 2 then 2 else -2)
  else 0

/-- Inverse lookup table for `y - s ∈ {0, ..., 11}` of 4-row gadget `A`. -/
def invDATab (row j : ℕ) : ℤ :=
  match row, j with
  | 0, 1 => -2 | 0, 4 => -3 | 0, 5 => -1 | 0, 8 => -3 | 0, 11 => -3 | 0, _ => 0
  | 1, 1 => -2 | 1, 2 => -1 | 1, 3 => -1 | 1, 4 => -1 | 1, 6 => -2 | 1, 7 => -1 | 1, 9 => -2 | 1, 11 => -2 | 1, _ => 0
  | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => -1 | 2, 5 => 1 | 2, 6 => 2 | 2, 8 => 1 | 2, 9 => 2 | 2, 11 => 2 | 2, _ => 0
  | _, 1 => 2 | _, 3 => 1 | _, 4 => 1 | _, 5 => 2 | _, 7 => 1 | _, 8 => 1 | _, 9 => 2 | _, 11 => 2 | _, _ => 0

def invDA (row s y : ℕ) : ℤ :=
  if s ≤ y ∧ y ≤ s + 11 then invDATab row (y - s)
  else if y % 2 = 1 then (if row < 2 then -2 else 2)
  else 0

/-- Column-permutation inverse inside the 11-column window of `blockA`. -/
def colInvATab (j y : ℕ) : ℕ :=
  match j, y with
  | 1, 0 => 2 | 1, 1 => 3 | 1, 2 => 1 | 1, _ => 0
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 1 | 2, _ => 3
  | 3, 0 => 0 | 3, 1 => 3 | 3, 2 => 1 | 3, _ => 2
  | 4, 0 => 2 | 4, 1 => 0 | 4, 2 => 3 | 4, _ => 1
  | 5, 0 => 2 | 5, 1 => 1 | 5, 2 => 3 | 5, _ => 0
  | 6, 0 => 0 | 6, 1 => 2 | 6, 2 => 1 | 6, _ => 3
  | 7, 0 => 0 | 7, 1 => 3 | 7, 2 => 2 | 7, _ => 1
  | 8, 0 => 2 | 8, 1 => 1 | 8, 2 => 3 | 8, _ => 0
  | 9, 0 => 0 | 9, 1 => 2 | 9, 2 => 3 | 9, _ => 1
  | _, y => y

/-- 3-row gadget `B` anchored at odd column `c_odd` (and `c_odd + 1`). -/
def dB (row c_odd c : ℕ) : ℤ :=
  if c = c_odd then
    match row with | 0 => 1 | 1 => 1 | _ => -2
  else if c = c_odd + 1 then
    match row with | 0 => 1 | 1 => -1 | _ => 0
  else if c % 2 = 1 then
    match row with | 0 => 2 | 1 => 0 | _ => -2
  else 0

def invDB (row c_odd y : ℕ) : ℤ :=
  if y = c_odd then
    match row with | 0 => -2 | 1 => 1 | _ => 2
  else if y = c_odd + 1 then
    match row with | 0 => -1 | 1 => -1 | _ => 0
  else if y = c_odd + 2 then
    match row with | 0 => -1 | 1 => 0 | _ => 2
  else if y % 2 = 1 then
    match row with | 0 => -2 | 1 => 0 | _ => 2
  else 0

/-- 2-row swap gadget `P` (top row `+2`, bottom row `-2` on odd columns). -/
def dP (isTop : Bool) (c : ℕ) : ℤ :=
  if c % 2 = 1 then (if isTop then 2 else -2) else 0

/-- Complete offset table `Δ(r, c)` for our modular square with base order `n0` (`n0 ≥ 22`,
`n0 ≠ 24`, `Even n0`). Independent of the total order `n = n0 + 4 * t`. -/
def deltaMod (n0 r c : ℕ) : ℤ :=
  let sh := baseShift n0
  if n0 % 4 = 2 then
    let t0 := (n0 - 22) / 4
    if r < 4 then dA r sh c
    else if r < 7 then dB (r - 4) (sh + 11) c
    else if r < 10 then dB (r - 7) (sh + 13) c
    else if r < 10 + 4 * t0 then
      if (r - 10) % 4 = 0 then dP true c
      else if (r - 10) % 4 = 2 then dP false c
      else 0
    else if r < n0 then 0
    else
      if (r - n0) % 4 = 0 then dP true c
      else if (r - n0) % 4 = 2 then dP false c
      else 0
  else
    let t0 := (n0 - 28) / 4
    if r < 4 then dA r sh c
    else if r < 8 then dA (r - 4) (sh + 4) c
    else if r < 11 then dB (r - 8) (sh + 13) c
    else if r < 11 + 4 * t0 then
      if (r - 11) % 4 = 0 then dP true c
      else if (r - 11) % 4 = 2 then dP false c
      else 0
    else if r < n0 then 0
    else
      if (r - n0) % 4 = 0 then dP true c
      else if (r - n0) % 4 = 2 then dP false c
      else 0

/-- Raw integer-modulo-`n` entry of `L_{n, n0}`. -/
def modEntryVal (n n0 r c : ℕ) : ℕ :=
  (((r : ℤ) + (c : ℤ) + deltaMod n0 r c) % (n : ℤ)).toNat

lemma modEntryVal_lt {n n0 r c : ℕ} (hn : 0 < n) : modEntryVal n n0 r c < n := by
  unfold modEntryVal
  have hn' : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
  have h1 := Int.emod_nonneg ((r : ℤ) + (c : ℤ) + deltaMod n0 r c) (ne_of_gt hn')
  have h2 := Int.emod_lt_of_pos ((r : ℤ) + (c : ℤ) + deltaMod n0 r c) hn'
  omega

lemma modEntryVal_modEq {n n0 r c : ℕ} (hn : 0 < n) :
    ((modEntryVal n n0 r c : ℕ) : ℤ) ≡ (r : ℤ) + (c : ℤ) + deltaMod n0 r c [ZMOD (n : ℤ)] := by
  unfold modEntryVal
  have hn' : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
  have hnn := Int.emod_nonneg ((r : ℤ) + (c : ℤ) + deltaMod n0 r c) (ne_of_gt hn')
  rw [Int.toNat_of_nonneg hnn]
  exact Int.mod_modEq _ _

private lemma bijective_of_inv {n : ℕ} (f g : Fin n → Fin n)
    (hl : ∀ x, g (f x) = x) (hr : ∀ y, f (g y) = y) : Function.Bijective f :=
  ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

private lemma trans_bij (n a : ℕ) (hn : 0 < n) :
    Function.Bijective (fun y : Fin n => (⟨(a + y.val) % n, Nat.mod_lt _ hn⟩ : Fin n)) := by
  have hn' : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
  let τ : Fin n → Fin n := fun y => ⟨(a + y.val) % n, Nat.mod_lt _ hn⟩
  let τi : Fin n → Fin n := fun z =>
    ⟨(((z.val : ℤ) - (a : ℤ)) % (n : ℤ)).toNat, by
      have h1 := Int.emod_nonneg ((z.val : ℤ) - (a : ℤ)) (ne_of_gt hn')
      have h2 := Int.emod_lt_of_pos ((z.val : ℤ) - (a : ℤ)) hn'
      omega⟩
  apply bijective_of_inv τ τi
  · intro y; ext; dsimp [τ, τi]
    have hmod : (((((a + y.val) % n : ℕ) : ℤ) - (a : ℤ)) % (n : ℤ)) = (y.val : ℤ) := by
      rw [Int.natCast_emod, Nat.cast_add]
      have h1 : (((a : ℤ) + (y.val : ℤ)) % (n : ℤ) - (a : ℤ)) % (n : ℤ) =
          ((a : ℤ) + (y.val : ℤ) - (a : ℤ)) % (n : ℤ) := by
        rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      rw [h1]
      have h2 : (a : ℤ) + (y.val : ℤ) - (a : ℤ) = (y.val : ℤ) := by ring
      rw [h2, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [Int.natCast_emod, Nat.cast_add] at hmod
    rw [hmod]; exact Int.toNat_natCast y.val
  · intro z; ext; dsimp [τ, τi]
    have hnn := Int.emod_nonneg ((z.val : ℤ) - (a : ℤ)) (ne_of_gt hn')
    zify
    rw [Int.toNat_of_nonneg hnn]
    have h1 : ((a : ℤ) + ((z.val : ℤ) - (a : ℤ)) % (n : ℤ)) % (n : ℤ) =
        ((a : ℤ) + ((z.val : ℤ) - (a : ℤ))) % (n : ℤ) := by
      rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
    rw [h1]
    have h2 : (a : ℤ) + ((z.val : ℤ) - (a : ℤ)) = (z.val : ℤ) := by ring
    rw [h2, Int.emod_eq_of_lt (by omega) (by omega)]

private lemma row_bij_of_col_shift {n : ℕ} (hn : 0 < n) (r : ℕ)
    (Δ invΔ : ℕ → ℤ)
    (hl : ∀ c < n, let y := (((c : ℤ) + Δ c) % (n : ℤ)).toNat;
      ((y : ℤ) + invΔ y) % (n : ℤ) = (c : ℤ))
    (hr : ∀ y < n, let c := (((y : ℤ) + invΔ y) % (n : ℤ)).toNat;
      ((c : ℤ) + Δ c) % (n : ℤ) = (y : ℤ)) :
    Function.Bijective (fun c : Fin n =>
      (⟨(((r : ℤ) + (c.val : ℤ) + Δ c.val) % (n : ℤ)).toNat, by
        have hn' : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
        have h1 := Int.emod_nonneg ((r : ℤ) + (c.val : ℤ) + Δ c.val) (ne_of_gt hn')
        have h2 := Int.emod_lt_of_pos ((r : ℤ) + (c.val : ℤ) + Δ c.val) hn'
        omega⟩ : Fin n)) := by
  have hn' : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
  let φ : Fin n → Fin n := fun c =>
    ⟨(((c.val : ℤ) + Δ c.val) % (n : ℤ)).toNat, by
      have h1 := Int.emod_nonneg ((c.val : ℤ) + Δ c.val) (ne_of_gt hn')
      have h2 := Int.emod_lt_of_pos ((c.val : ℤ) + Δ c.val) hn'
      omega⟩
  let ψ : Fin n → Fin n := fun y =>
    ⟨(((y.val : ℤ) + invΔ y.val) % (n : ℤ)).toNat, by
      have h1 := Int.emod_nonneg ((y.val : ℤ) + invΔ y.val) (ne_of_gt hn')
      have h2 := Int.emod_lt_of_pos ((y.val : ℤ) + invΔ y.val) hn'
      omega⟩
  have hφ : Function.Bijective φ := by
    apply bijective_of_inv φ ψ
    · intro c; ext; dsimp [φ, ψ]
      have h := hl c.val c.isLt; dsimp only at h
      rw [h]; exact Int.toNat_natCast c.val
    · intro y; ext; dsimp [φ, ψ]
      have h := hr y.val y.isLt; dsimp only at h
      rw [h]; exact Int.toNat_natCast y.val
  let τ : Fin n → Fin n := fun y => ⟨(r + y.val) % n, Nat.mod_lt _ hn⟩
  have hτ : Function.Bijective τ := trans_bij n r hn
  have hcomp : (fun c : Fin n =>
      (⟨(((r : ℤ) + (c.val : ℤ) + Δ c.val) % (n : ℤ)).toNat, by
        have h1 := Int.emod_nonneg ((r : ℤ) + (c.val : ℤ) + Δ c.val) (ne_of_gt hn')
        have h2 := Int.emod_lt_of_pos ((r : ℤ) + (c.val : ℤ) + Δ c.val) hn'
        omega⟩ : Fin n)) = τ ∘ φ := by
    funext c; ext; dsimp [τ, φ]
    have hnn1 := Int.emod_nonneg ((r : ℤ) + (c.val : ℤ) + Δ c.val) (ne_of_gt hn')
    have hnn2 := Int.emod_nonneg ((c.val : ℤ) + Δ c.val) (ne_of_gt hn')
    zify
    rw [Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hnn2]
    rw [Int.add_emod (r : ℤ), Int.emod_emod, ← Int.add_emod, add_assoc]
  rw [hcomp]
  exact hτ.comp hφ

private lemma dA_tab_left (row : Fin 4) (j : Fin 11) :
    let y : ℤ := (j.val : ℤ) + dATab row.val j.val
    (0 ≤ y ∧ y ≤ 11 ∧ y + invDATab row.val y.toNat = (j.val : ℤ)) ∨
    (y < 0 ∧ y % 2 = 1 ∧ y + (if row.val < 2 then -2 else 2) = (j.val : ℤ)) := by
  decide +revert

private lemma invDA_tab_right (row : Fin 4) (y : Fin 12) :
    let c : ℤ := (y.val : ℤ) + invDATab row.val y.val
    (0 ≤ c ∧ c ≤ 10 ∧ c + dATab row.val c.toNat = (y.val : ℤ)) ∨
    ((c < 0 ∨ 10 < c) ∧ c % 2 = 1 ∧ c + (if row.val < 2 then 2 else -2) = (y.val : ℤ)) := by
  decide +revert

private lemma dA_col_tab (j : Fin 11) (r : Fin 4) :
    let y : ℤ := (r.val : ℤ) + dATab r.val j.val
    0 ≤ y ∧ y < 4 ∧ colInvATab j.val y.toNat = r.val ∧
    colInvATab j.val r.val < 4 ∧
    ((colInvATab j.val r.val : ℤ) + dATab (colInvATab j.val r.val) j.val) = (r.val : ℤ) := by
  decide +revert

lemma dA_left_inv {n s row : ℕ} (hn : 22 ≤ n) (heven : n % 2 = 0)
    (hs_even : s % 2 = 0) (hs_lo : 4 ≤ s) (hs_hi : s + 13 < n) (hrow : row < 4)
    (c : ℕ) (hc : c < n) :
    let y := (((c : ℤ) + dA row s c) % (n : ℤ)).toNat
    ((y : ℤ) + invDA row s y) % (n : ℤ) = (c : ℤ) := by
  dsimp only
  by_cases hwin : s ≤ c ∧ c ≤ s + 10
  · have htab := dA_tab_left ⟨row, hrow⟩ ⟨c - s, by omega⟩
    dsimp only at htab
    have hd : dA row s c = dATab row (c - s) := by unfold dA; rw [if_pos hwin]
    rw [hd]
    rcases htab with ⟨hy0, hy11, hinv⟩ | ⟨hyneg, hyodd, hinv⟩
    · have hy_eq : ((((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat : ℤ) = (c : ℤ) + dATab row (c - s) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega)]
      have hy_win : s ≤ (((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat ∧
                    (((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat ≤ s + 11 := by omega
      have hsub : (((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat - s =
          ((c - s : ℕ) + dATab row (c - s)).toNat := by omega
      rw [hy_eq]; unfold invDA; rw [if_pos hy_win, hsub]
      have : (c : ℤ) + dATab row (c - s) + invDATab row ((c - s : ℕ) + dATab row (c - s)).toNat = (c : ℤ) := by omega
      rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
    · have hy_eq : ((((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat : ℤ) = (c : ℤ) + dATab row (c - s) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega)]
      have hy_nwin : ¬ (s ≤ (((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat ∧
                        (((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat ≤ s + 11) := by omega
      have hy_odd : (((c : ℤ) + dATab row (c - s)) % (n : ℤ)).toNat % 2 = 1 := by omega
      rw [hy_eq]; unfold invDA; rw [if_neg hy_nwin, if_pos hy_odd]
      have : (c : ℤ) + dATab row (c - s) + (if row < 2 then -2 else 2) = (c : ℤ) := by omega
      rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
  · have hd : dA row s c = if c % 2 = 1 then (if row < 2 then 2 else -2) else 0 := by
      unfold dA; rw [if_neg hwin]
    rw [hd]
    by_cases hodd : c % 2 = 1
    · rw [if_pos hodd]
      by_cases hr2 : row < 2
      · rw [if_pos hr2]
        by_cases hc2 : c + 2 < n
        · have hy_eq : (((c : ℤ) + 2) % (n : ℤ)).toNat = c + 2 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
          rw [hy_eq]
          by_cases hyw : s ≤ c + 2 ∧ c + 2 ≤ s + 11
          · have hcs : c + 2 = s + 1 := by omega
            unfold invDA; rw [if_pos hyw]
            have hsub : c + 2 - s = 1 := by omega
            rw [hsub]
            rcases (by omega : row = 0 ∨ row = 1) with rfl | rfl <;>
              · simp only [invDATab]
                rw [show ((c + 2 : ℕ) : ℤ) + -2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
          · unfold invDA; rw [if_neg hyw, if_pos (by omega), if_pos hr2]
            rw [show ((c + 2 : ℕ) : ℤ) + -2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
        · have hcn : c = n - 1 := by omega
          have hy_eq : (((c : ℤ) + 2) % (n : ℤ)).toNat = 1 := by
            rw [show (c : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; rfl
          rw [hy_eq]; unfold invDA
          rw [if_neg (by omega), if_pos (by omega), if_pos hr2]
          rw [show ((1 : ℕ) : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
      · rw [if_neg hr2]
        by_cases hc2 : 2 ≤ c
        · have hy_eq : (((c : ℤ) + -2) % (n : ℤ)).toNat = c - 2 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
          rw [hy_eq]
          by_cases hyw : s ≤ c - 2 ∧ c - 2 ≤ s + 11
          · have hcs : c - 2 = s + 9 ∨ c - 2 = s + 11 := by omega
            unfold invDA; rw [if_pos hyw]
            rcases hcs with h9 | h11
            · have hsub : c - 2 - s = 9 := by omega
              rw [hsub]
              rcases (by omega : row = 2 ∨ row = 3) with rfl | rfl <;>
                · simp only [invDATab]
                  rw [show ((c - 2 : ℕ) : ℤ) + 2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
            · have hsub : c - 2 - s = 11 := by omega
              rw [hsub]
              rcases (by omega : row = 2 ∨ row = 3) with rfl | rfl <;>
                · simp only [invDATab]
                  rw [show ((c - 2 : ℕ) : ℤ) + 2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
          · unfold invDA; rw [if_neg hyw, if_pos (by omega), if_neg hr2]
            rw [show ((c - 2 : ℕ) : ℤ) + 2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
        · have hc1 : c = 1 := by omega
          have hy_eq : (((c : ℤ) + -2) % (n : ℤ)).toNat = n - 1 := by
            rw [show (c : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
          rw [hy_eq]; unfold invDA
          rw [if_neg (by omega), if_pos (by omega), if_neg hr2]
          rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; omega
    · rw [if_neg hodd]
      have hy_eq : (((c : ℤ) + 0) % (n : ℤ)).toNat = c := by
        rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast c
      rw [hy_eq]; unfold invDA
      rw [if_neg (by omega), if_neg hodd, add_zero, Int.emod_eq_of_lt (by omega) (by omega)]

lemma dA_right_inv {n s row : ℕ} (hn : 22 ≤ n) (heven : n % 2 = 0)
    (hs_even : s % 2 = 0) (hs_lo : 4 ≤ s) (hs_hi : s + 13 < n) (hrow : row < 4)
    (y : ℕ) (hy : y < n) :
    let c := (((y : ℤ) + invDA row s y) % (n : ℤ)).toNat
    ((c : ℤ) + dA row s c) % (n : ℤ) = (y : ℤ) := by
  dsimp only
  by_cases hwin : s ≤ y ∧ y ≤ s + 11
  · have htab := invDA_tab_right ⟨row, hrow⟩ ⟨y - s, by omega⟩
    dsimp only at htab
    have hd : invDA row s y = invDATab row (y - s) := by unfold invDA; rw [if_pos hwin]
    rw [hd]
    rcases htab with ⟨hc0, hc10, hinv⟩ | ⟨hcout, hcodd, hinv⟩
    · have hc_eq : ((((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat : ℤ) = (y : ℤ) + invDATab row (y - s) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega)]
      have hc_win : s ≤ (((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat ∧
                    (((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat ≤ s + 10 := by omega
      have hsub : (((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat - s =
          ((y - s : ℕ) + invDATab row (y - s)).toNat := by omega
      rw [hc_eq]; unfold dA; rw [if_pos hc_win, hsub]
      have : (y : ℤ) + invDATab row (y - s) + dATab row ((y - s : ℕ) + invDATab row (y - s)).toNat = (y : ℤ) := by omega
      rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
    · have hc_eq : ((((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat : ℤ) = (y : ℤ) + invDATab row (y - s) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega)]
      have hc_nwin : ¬ (s ≤ (((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat ∧
                        (((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat ≤ s + 10) := by omega
      have hc_odd : (((y : ℤ) + invDATab row (y - s)) % (n : ℤ)).toNat % 2 = 1 := by omega
      rw [hc_eq]; unfold dA; rw [if_neg hc_nwin, if_pos hc_odd]
      have : (y : ℤ) + invDATab row (y - s) + (if row < 2 then 2 else -2) = (y : ℤ) := by omega
      rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
  · have hd : invDA row s y = if y % 2 = 1 then (if row < 2 then -2 else 2) else 0 := by
      unfold invDA; rw [if_neg hwin]
    rw [hd]
    by_cases hodd : y % 2 = 1
    · rw [if_pos hodd]
      by_cases hr2 : row < 2
      · rw [if_pos hr2]
        by_cases hy2 : 2 ≤ y
        · have hc_eq : (((y : ℤ) + -2) % (n : ℤ)).toNat = y - 2 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
          rw [hc_eq]; unfold dA
          rw [if_neg (by omega), if_pos (by omega), if_pos hr2]
          rw [show ((y - 2 : ℕ) : ℤ) + 2 = (y : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
        · have hy1 : y = 1 := by omega
          have hc_eq : (((y : ℤ) + -2) % (n : ℤ)).toNat = n - 1 := by
            rw [show (y : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
          rw [hc_eq]; unfold dA
          rw [if_neg (by omega), if_pos (by omega), if_pos hr2]
          rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; omega
      · rw [if_neg hr2]
        by_cases hy2 : y + 2 < n
        · have hc_eq : (((y : ℤ) + 2) % (n : ℤ)).toNat = y + 2 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
          rw [hc_eq]
          by_cases hcw : s ≤ y + 2 ∧ y + 2 ≤ s + 10
          · have hys : y + 2 = s + 1 := by omega
            unfold dA; rw [if_pos hcw]
            have hsub : y + 2 - s = 1 := by omega
            rw [hsub]
            rcases (by omega : row = 2 ∨ row = 3) with rfl | rfl <;>
              · simp only [dATab]
                rw [show ((y + 2 : ℕ) : ℤ) + -2 = (y : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
          · unfold dA; rw [if_neg hcw, if_pos (by omega), if_neg hr2]
            rw [show ((y + 2 : ℕ) : ℤ) + -2 = (y : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
        · have hyn : y = n - 1 := by omega
          have hc_eq : (((y : ℤ) + 2) % (n : ℤ)).toNat = 1 := by
            rw [show (y : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; rfl
          rw [hc_eq]; unfold dA
          rw [if_neg (by omega), if_pos (by omega), if_neg hr2]
          rw [show ((1 : ℕ) : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
    · rw [if_neg hodd]
      have hc_eq : (((y : ℤ) + 0) % (n : ℤ)).toNat = y := by
        rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast y
      rw [hc_eq]; unfold dA
      rw [if_neg (by omega), if_neg hodd, add_zero, Int.emod_eq_of_lt (by omega) (by omega)]

lemma dB_left_inv {n c_odd row : ℕ} (hn : 22 ≤ n) (heven : n % 2 = 0)
    (hodd : c_odd % 2 = 1) (hlo : 3 ≤ c_odd) (hhi : c_odd + 2 < n) (hrow : row < 3)
    (c : ℕ) (hc : c < n) :
    let y := (((c : ℤ) + dB row c_odd c) % (n : ℤ)).toNat
    ((y : ℤ) + invDB row c_odd y) % (n : ℤ) = (c : ℤ) := by
  dsimp only
  have hne1 : ¬ (c_odd + 1 = c_odd) := by omega
  rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2) with rfl | rfl | rfl
  · by_cases h1 : c = c_odd
    · simp only [dB, h1, ↓reduceIte]
      have hy : (((c_odd : ℤ) + 1) % (n : ℤ)).toNat = c_odd + 1 := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      rw [hy]; simp only [invDB, hne1, ↓reduceIte]
      rw [show ((c_odd + 1 : ℕ) : ℤ) + -1 = (c_odd : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
    · by_cases h2 : c = c_odd + 1
      · simp only [dB, h2, hne1, ↓reduceIte]
        have hy : ((((c_odd + 1 : ℕ) : ℤ) + 1) % (n : ℤ)).toNat = c_odd + 2 := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
        rw [hy]; simp only [invDB, show ¬ (c_odd + 2 = c_odd) by omega, show ¬ (c_odd + 2 = c_odd + 1) by omega, ↓reduceIte]
        rw [show ((c_odd + 2 : ℕ) : ℤ) + -1 = ((c_odd + 1 : ℕ) : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
      · by_cases ho : c % 2 = 1
        · simp only [dB, h1, h2, ho, ↓reduceIte]
          by_cases hc2 : c + 2 < n
          · have hy : (((c : ℤ) + 2) % (n : ℤ)).toNat = c + 2 := by
              rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
            rw [hy]; simp only [invDB]
            have hi : (if c + 2 = c_odd then (-2 : ℤ) else if c + 2 = c_odd + 1 then -1
                       else if c + 2 = c_odd + 2 then -1 else if (c + 2) % 2 = 1 then -2 else 0) = -2 := by
              split_ifs <;> omega
            rw [hi, show ((c + 2 : ℕ) : ℤ) + -2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
          · have hcn : c = n - 1 := by omega
            have hy : (((c : ℤ) + 2) % (n : ℤ)).toNat = 1 := by
              rw [show (c : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; rfl
            rw [hy]; simp only [invDB, show ¬ (1 = c_odd) by omega, show ¬ (1 = c_odd + 1) by omega,
              show ¬ (1 = c_odd + 2) by omega, show 1 % 2 = 1 by omega, ↓reduceIte]
            rw [show ((1 : ℕ) : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
        · simp only [dB, h1, h2, ho, ↓reduceIte]
          have hy : (((c : ℤ) + 0) % (n : ℤ)).toNat = c := by
            rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast c
          rw [hy]; simp only [invDB, h1, h2, show ¬ (c = c_odd + 2) by omega, ho, ↓reduceIte, add_zero]
          exact Int.emod_eq_of_lt (by omega) (by omega)
  · by_cases h1 : c = c_odd
    · simp only [dB, h1, ↓reduceIte]
      have hy : (((c_odd : ℤ) + 1) % (n : ℤ)).toNat = c_odd + 1 := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      rw [hy]; simp only [invDB, hne1, ↓reduceIte]
      rw [show ((c_odd + 1 : ℕ) : ℤ) + -1 = (c_odd : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
    · by_cases h2 : c = c_odd + 1
      · simp only [dB, h2, hne1, ↓reduceIte]
        have hy : ((((c_odd + 1 : ℕ) : ℤ) + -1) % (n : ℤ)).toNat = c_odd := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
        rw [hy]; simp only [invDB, ↓reduceIte]
        rw [show (c_odd : ℤ) + 1 = ((c_odd + 1 : ℕ) : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
      · simp only [dB, h1, h2, ↓reduceIte, ite_self]
        have hy : (((c : ℤ) + 0) % (n : ℤ)).toNat = c := by
          rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast c
        rw [hy]; simp only [invDB, h1, h2, ↓reduceIte, ite_self, add_zero]
        exact Int.emod_eq_of_lt (by omega) (by omega)
  · by_cases h1 : c = c_odd
    · simp only [dB, h1, ↓reduceIte]
      have hy : (((c_odd : ℤ) + -2) % (n : ℤ)).toNat = c_odd - 2 := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      rw [hy]; simp only [invDB, show ¬ (c_odd - 2 = c_odd) by omega, show ¬ (c_odd - 2 = c_odd + 1) by omega,
        show ¬ (c_odd - 2 = c_odd + 2) by omega, show (c_odd - 2) % 2 = 1 by omega, ↓reduceIte]
      rw [show ((c_odd - 2 : ℕ) : ℤ) + 2 = (c_odd : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
    · by_cases h2 : c = c_odd + 1
      · simp only [dB, h2, hne1, ↓reduceIte]
        have hy : ((((c_odd + 1 : ℕ) : ℤ) + 0) % (n : ℤ)).toNat = c_odd + 1 := by
          rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast _
        rw [hy]; simp only [invDB, hne1, ↓reduceIte, add_zero]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      · by_cases ho : c % 2 = 1
        · simp only [dB, h1, h2, ho, ↓reduceIte]
          by_cases hc2 : 2 ≤ c
          · have hy : (((c : ℤ) + -2) % (n : ℤ)).toNat = c - 2 := by
              rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
            rw [hy]; simp only [invDB]
            have hi : (if c - 2 = c_odd then (2 : ℤ) else if c - 2 = c_odd + 1 then 0
                       else if c - 2 = c_odd + 2 then 2 else if (c - 2) % 2 = 1 then 2 else 0) = 2 := by
              split_ifs <;> omega
            rw [hi, show ((c - 2 : ℕ) : ℤ) + 2 = (c : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
          · have hc1 : c = 1 := by omega
            have hy : (((c : ℤ) + -2) % (n : ℤ)).toNat = n - 1 := by
              rw [show (c : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
            rw [hy]; simp only [invDB, show ¬ (n - 1 = c_odd) by omega, show ¬ (n - 1 = c_odd + 1) by omega,
              show (n - 1) % 2 = 1 by omega, ↓reduceIte, ite_self]
            rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; omega
        · simp only [dB, h1, h2, ho, ↓reduceIte]
          have hy : (((c : ℤ) + 0) % (n : ℤ)).toNat = c := by
            rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast c
          rw [hy]; simp only [invDB, h1, h2, show ¬ (c = c_odd + 2) by omega, ho, ↓reduceIte, add_zero]
          exact Int.emod_eq_of_lt (by omega) (by omega)

lemma dB_right_inv {n c_odd row : ℕ} (hn : 22 ≤ n) (heven : n % 2 = 0)
    (hodd : c_odd % 2 = 1) (hlo : 3 ≤ c_odd) (hhi : c_odd + 2 < n) (hrow : row < 3)
    (y : ℕ) (hy : y < n) :
    let c := (((y : ℤ) + invDB row c_odd y) % (n : ℤ)).toNat
    ((c : ℤ) + dB row c_odd c) % (n : ℤ) = (y : ℤ) := by
  dsimp only
  have hne1 : ¬ (c_odd + 1 = c_odd) := by omega
  have hne2 : ¬ (c_odd + 2 = c_odd) := by omega
  have hne21 : ¬ (c_odd + 2 = c_odd + 1) := by omega
  rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2) with rfl | rfl | rfl
  · by_cases h1 : y = c_odd
    · simp only [invDB, h1, ↓reduceIte]
      have hc : (((c_odd : ℤ) + -2) % (n : ℤ)).toNat = c_odd - 2 := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      rw [hc]; simp only [dB, show ¬ (c_odd - 2 = c_odd) by omega, show ¬ (c_odd - 2 = c_odd + 1) by omega,
        show (c_odd - 2) % 2 = 1 by omega, ↓reduceIte]
      rw [show ((c_odd - 2 : ℕ) : ℤ) + 2 = (c_odd : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
    · by_cases h2 : y = c_odd + 1
      · simp only [invDB, h2, hne1, ↓reduceIte]
        have hc : ((((c_odd + 1 : ℕ) : ℤ) + -1) % (n : ℤ)).toNat = c_odd := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
        rw [hc]; simp only [dB, ↓reduceIte]
        rw [show (c_odd : ℤ) + 1 = ((c_odd + 1 : ℕ) : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
      · by_cases h3 : y = c_odd + 2
        · simp only [invDB, h3, hne2, hne21, ↓reduceIte]
          have hc : ((((c_odd + 2 : ℕ) : ℤ) + -1) % (n : ℤ)).toNat = c_odd + 1 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
          rw [hc]; simp only [dB, hne1, ↓reduceIte]
          rw [show ((c_odd + 1 : ℕ) : ℤ) + 1 = ((c_odd + 2 : ℕ) : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
        · by_cases ho : y % 2 = 1
          · simp only [invDB, h1, h2, h3, ho, ↓reduceIte]
            by_cases hy2 : 2 ≤ y
            · have hc : (((y : ℤ) + -2) % (n : ℤ)).toNat = y - 2 := by
                rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
              rw [hc]; simp only [dB, show ¬ (y - 2 = c_odd) by omega, show ¬ (y - 2 = c_odd + 1) by omega,
                show (y - 2) % 2 = 1 by omega, ↓reduceIte]
              rw [show ((y - 2 : ℕ) : ℤ) + 2 = (y : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
            · have hy1 : y = 1 := by omega
              have hc : (((y : ℤ) + -2) % (n : ℤ)).toNat = n - 1 := by
                rw [show (y : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
              rw [hc]; simp only [dB, show ¬ (n - 1 = c_odd) by omega, show ¬ (n - 1 = c_odd + 1) by omega,
                show (n - 1) % 2 = 1 by omega, ↓reduceIte]
              rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; omega
          · simp only [invDB, h1, h2, h3, ho, ↓reduceIte]
            have hc : (((y : ℤ) + 0) % (n : ℤ)).toNat = y := by
              rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast y
            rw [hc]; simp only [dB, h1, h2, ho, ↓reduceIte, add_zero]
            exact Int.emod_eq_of_lt (by omega) (by omega)
  · by_cases h1 : y = c_odd
    · simp only [invDB, h1, ↓reduceIte]
      have hc : (((c_odd : ℤ) + 1) % (n : ℤ)).toNat = c_odd + 1 := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      rw [hc]; simp only [dB, hne1, ↓reduceIte]
      rw [show ((c_odd + 1 : ℕ) : ℤ) + -1 = (c_odd : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
    · by_cases h2 : y = c_odd + 1
      · simp only [invDB, h2, hne1, ↓reduceIte]
        have hc : ((((c_odd + 1 : ℕ) : ℤ) + -1) % (n : ℤ)).toNat = c_odd := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
        rw [hc]; simp only [dB, ↓reduceIte]
        rw [show (c_odd : ℤ) + 1 = ((c_odd + 1 : ℕ) : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
      · simp only [invDB, h1, h2, ↓reduceIte, ite_self]
        have hc : (((y : ℤ) + 0) % (n : ℤ)).toNat = y := by
          rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast y
        rw [hc]; simp only [dB, h1, h2, ↓reduceIte, ite_self, add_zero]
        exact Int.emod_eq_of_lt (by omega) (by omega)
  · by_cases h2 : y = c_odd + 1
    · simp only [invDB, h2, hne1, ↓reduceIte]
      have hc : ((((c_odd + 1 : ℕ) : ℤ) + 0) % (n : ℤ)).toNat = c_odd + 1 := by
        rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast _
      rw [hc]; simp only [dB, hne1, ↓reduceIte, add_zero]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    · by_cases ho : y % 2 = 1
      · simp only [invDB]
        have hi : (if y = c_odd then (2 : ℤ) else if y = c_odd + 1 then 0
                   else if y = c_odd + 2 then 2 else if y % 2 = 1 then 2 else 0) = 2 := by
          split_ifs <;> omega
        rw [hi]
        by_cases hy2 : y + 2 < n
        · have hc : (((y : ℤ) + 2) % (n : ℤ)).toNat = y + 2 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
          rw [hc]; simp only [dB]
          have hd : (if y + 2 = c_odd then (-2 : ℤ) else if y + 2 = c_odd + 1 then 0
                     else if (y + 2) % 2 = 1 then -2 else 0) = -2 := by split_ifs <;> omega
          rw [hd, show ((y + 2 : ℕ) : ℤ) + -2 = (y : ℤ) by omega, Int.emod_eq_of_lt (by omega) (by omega)]
        · have hyn : y = n - 1 := by omega
          have hc : (((y : ℤ) + 2) % (n : ℤ)).toNat = 1 := by
            rw [show (y : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; rfl
          rw [hc]; simp only [dB, show ¬ (1 = c_odd) by omega, show ¬ (1 = c_odd + 1) by omega,
            show 1 % 2 = 1 by omega, ↓reduceIte]
          rw [show ((1 : ℕ) : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
      · simp only [invDB, show ¬ (y = c_odd) by omega, h2, show ¬ (y = c_odd + 2) by omega, ho, ↓reduceIte]
        have hc : (((y : ℤ) + 0) % (n : ℤ)).toNat = y := by
          rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast y
        rw [hc]; simp only [dB, show ¬ (y = c_odd) by omega, h2, ho, ↓reduceIte, add_zero]
        exact Int.emod_eq_of_lt (by omega) (by omega)

lemma dP_left_inv {n : ℕ} (hn : 4 ≤ n) (heven : n % 2 = 0) (isTop : Bool) (c : ℕ) (hc : c < n) :
    let y := (((c : ℤ) + dP isTop c) % (n : ℤ)).toNat
    ((y : ℤ) + dP (!isTop) y) % (n : ℤ) = (c : ℤ) := by
  dsimp only
  by_cases ho : c % 2 = 1
  · cases isTop
    · unfold dP; simp only [ho, ↓reduceIte, Bool.false_eq_true, Bool.not_false]
      by_cases hc2 : 2 ≤ c
      · have hy : (((c : ℤ) + -2) % (n : ℤ)).toNat = c - 2 := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
        rw [hy, if_pos (by omega), show ((c - 2 : ℕ) : ℤ) + 2 = (c : ℤ) by omega,
          Int.emod_eq_of_lt (by omega) (by omega)]
      · have hc1 : c = 1 := by omega
        have hy : (((c : ℤ) + -2) % (n : ℤ)).toNat = n - 1 := by
          rw [show (c : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
        rw [hy, if_pos (by omega)]
        rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; omega
    · unfold dP; simp only [ho, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      by_cases hc2 : c + 2 < n
      · have hy : (((c : ℤ) + 2) % (n : ℤ)).toNat = c + 2 := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
        rw [hy, if_pos (by omega), show ((c + 2 : ℕ) : ℤ) + -2 = (c : ℤ) by omega,
          Int.emod_eq_of_lt (by omega) (by omega)]
      · have hcn : c = n - 1 := by omega
        have hy : (((c : ℤ) + 2) % (n : ℤ)).toNat = 1 := by
          rw [show (c : ℤ) + 2 = (n : ℤ) + 1 by omega, emod_add_one (by omega)]; rfl
        rw [hy, if_pos (by omega)]
        rw [show ((1 : ℕ) : ℤ) + -2 = -(1 : ℤ) by omega, emod_neg_one (by omega)]; omega
  · unfold dP; simp only [ho, ↓reduceIte]
    have hy : (((c : ℤ) + 0) % (n : ℤ)).toNat = c := by
      rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast c
    rw [hy, if_neg ho, add_zero, Int.emod_eq_of_lt (by omega) (by omega)]

lemma dP_right_inv {n : ℕ} (hn : 4 ≤ n) (heven : n % 2 = 0) (isTop : Bool) (y : ℕ) (hy : y < n) :
    let c := (((y : ℤ) + dP (!isTop) y) % (n : ℤ)).toNat
    ((c : ℤ) + dP isTop c) % (n : ℤ) = (y : ℤ) := by
  have h := dP_left_inv hn heven (!isTop) y hy
  simp only [Bool.not_not] at h
  exact h

private def invBlockA (r0 s c y : ℕ) : ℕ :=
  if s ≤ c ∧ c ≤ s + 10 then r0 + colInvATab (c - s) (y - r0)
  else if c % 2 = 1 then r0 + (y - r0 + 2) % 4
  else y

private def invBlockB (r0 c_odd c y : ℕ) : ℕ :=
  if c = c_odd then r0 + (y - r0 + 2) % 3
  else if c = c_odd + 1 then (if y = r0 then r0 + 1 else if y = r0 + 1 then r0 else y)
  else if c % 2 = 1 then (if y = r0 then r0 + 2 else if y = r0 + 2 then r0 else y)
  else y

private def invBlockP (r0 c y : ℕ) : ℕ :=
  if c % 2 = 1 then
    if (y - r0) % 4 = 0 then y + 2
    else if (y - r0) % 4 = 2 then y - 2
    else y
  else y

/-- Explicit blockwise inverse of `r ↦ (r + deltaMod n0 r c).toNat` on `Fin n`. -/
def colPermInv (n0 c y : ℕ) : ℕ :=
  let sh := baseShift n0
  if n0 % 4 = 2 then
    let t0 := (n0 - 22) / 4
    if y < 4 then invBlockA 0 sh c y
    else if y < 7 then invBlockB 4 (sh + 11) c y
    else if y < 10 then invBlockB 7 (sh + 13) c y
    else if y < 10 + 4 * t0 then invBlockP 10 c y
    else if y < n0 then y
    else invBlockP n0 c y
  else
    let t0 := (n0 - 28) / 4
    if y < 4 then invBlockA 0 sh c y
    else if y < 8 then invBlockA 4 (sh + 4) c y
    else if y < 11 then invBlockB 8 (sh + 13) c y
    else if y < 11 + 4 * t0 then invBlockP 11 c y
    else if y < n0 then y
    else invBlockP n0 c y

private lemma blockA_col_bij (r0 s c r : ℕ) (hr : r0 ≤ r ∧ r < r0 + 4) :
    let y := ((r : ℤ) + dA (r - r0) s c).toNat
    r0 ≤ y ∧ y < r0 + 4 ∧ ((r : ℤ) + dA (r - r0) s c) = (y : ℤ) ∧ invBlockA r0 s c y = r := by
  dsimp only; unfold invBlockA
  by_cases hwin : s ≤ c ∧ c ≤ s + 10
  · have ht := dA_col_tab ⟨c - s, by omega⟩ ⟨r - r0, by omega⟩
    dsimp only at ht
    have hd : dA (r - r0) s c = dATab (r - r0) (c - s) := by unfold dA; rw [if_pos hwin]
    rw [hd, if_pos hwin]
    have hsub : ((r : ℤ) + dATab (r - r0) (c - s)).toNat - r0 =
        ((r - r0 : ℕ) + dATab (r - r0) (c - s)).toNat := by omega
    rw [hsub]
    omega
  · have hd : dA (r - r0) s c = if c % 2 = 1 then (if r - r0 < 2 then 2 else -2) else 0 := by
      unfold dA; rw [if_neg hwin]
    rw [hd, if_neg hwin]
    by_cases ho : c % 2 = 1
    · rw [if_pos ho, if_pos ho]; split_ifs <;> omega
    · rw [if_neg ho, if_neg ho]; omega

private lemma blockA_col_right (r0 s c y : ℕ) (hy : r0 ≤ y ∧ y < r0 + 4) :
    let r := invBlockA r0 s c y
    r0 ≤ r ∧ r < r0 + 4 ∧ ((r : ℤ) + dA (r - r0) s c) = (y : ℤ) := by
  dsimp only; unfold invBlockA
  by_cases hwin : s ≤ c ∧ c ≤ s + 10
  · have ht := dA_col_tab ⟨c - s, by omega⟩ ⟨y - r0, by omega⟩
    dsimp only at ht
    rw [if_pos hwin]
    have hd : dA (r0 + colInvATab (c - s) (y - r0) - r0) s c =
        dATab (colInvATab (c - s) (y - r0)) (c - s) := by
      unfold dA; rw [if_pos hwin, Nat.add_sub_cancel_left]
    rw [hd]; omega
  · rw [if_neg hwin]
    by_cases ho : c % 2 = 1
    · rw [if_pos ho]; unfold dA; rw [if_neg hwin, if_pos ho]; split_ifs <;> omega
    · rw [if_neg ho]; unfold dA; rw [if_neg hwin, if_neg ho]; omega

private lemma blockB_col_bij (r0 c_odd c r : ℕ) (hr : r0 ≤ r ∧ r < r0 + 3) :
    let y := ((r : ℤ) + dB (r - r0) c_odd c).toNat
    r0 ≤ y ∧ y < r0 + 3 ∧ ((r : ℤ) + dB (r - r0) c_odd c) = (y : ℤ) ∧ invBlockB r0 c_odd c y = r := by
  dsimp only; unfold invBlockB
  rcases (by omega : r = r0 ∨ r = r0 + 1 ∨ r = r0 + 2) with rfl | rfl | rfl
  · unfold dB; simp only [Nat.sub_self]; split_ifs <;> omega
  · unfold dB; simp only [Nat.add_sub_cancel_left]; split_ifs <;> omega
  · unfold dB; simp only [Nat.add_sub_cancel_left]; split_ifs <;> omega

private lemma blockB_col_right (r0 c_odd c y : ℕ) (hy : r0 ≤ y ∧ y < r0 + 3) :
    let r := invBlockB r0 c_odd c y
    r0 ≤ r ∧ r < r0 + 3 ∧ ((r : ℤ) + dB (r - r0) c_odd c) = (y : ℤ) := by
  dsimp only; unfold invBlockB
  rcases (by omega : y = r0 ∨ y = r0 + 1 ∨ y = r0 + 2) with rfl | rfl | rfl <;>
  · by_cases h1 : c = c_odd
    · rw [if_pos h1]; unfold dB; rw [if_pos h1]; simp only [Nat.sub_self, Nat.add_sub_cancel_left]
      have : (0 + 2) % 3 = 2 := rfl; have : (1 + 2) % 3 = 0 := rfl; have : (2 + 2) % 3 = 1 := rfl
      omega
    · by_cases h2 : c = c_odd + 1
      · rw [if_neg h1, if_pos h2]; unfold dB; rw [if_neg h1, if_pos h2]
        split_ifs <;> simp only [Nat.sub_self, Nat.add_sub_cancel_left] <;> omega
      · by_cases ho : c % 2 = 1
        · rw [if_neg h1, if_neg h2, if_pos ho]; unfold dB; rw [if_neg h1, if_neg h2, if_pos ho]
          split_ifs <;> simp only [Nat.sub_self, Nat.add_sub_cancel_left] <;> omega
        · rw [if_neg h1, if_neg h2, if_neg ho]; unfold dB; rw [if_neg h1, if_neg h2, if_neg ho]; omega

private lemma blockP_col_bij (r0 k c r : ℕ) (hr : r0 ≤ r ∧ r < r0 + 4 * k) :
    let d : ℤ := if (r - r0) % 4 = 0 then dP true c else if (r - r0) % 4 = 2 then dP false c else 0
    let y := ((r : ℤ) + d).toNat
    r0 ≤ y ∧ y < r0 + 4 * k ∧ ((r : ℤ) + d) = (y : ℤ) ∧ invBlockP r0 c y = r := by
  dsimp only; unfold dP invBlockP
  by_cases ho : c % 2 = 1
  · simp only [ho, ↓reduceIte, Bool.false_eq_true]
    by_cases h0 : (r - r0) % 4 = 0
    · rw [if_pos h0]
      have hy : ((r : ℤ) + 2).toNat = r + 2 := by omega
      rw [hy, if_neg (by omega), if_pos (by omega)]; omega
    · by_cases h2 : (r - r0) % 4 = 2
      · rw [if_neg h0, if_pos h2]
        have hy : ((r : ℤ) + -2).toNat = r - 2 := by omega
        rw [hy, if_pos (by omega)]; omega
      · rw [if_neg h0, if_neg h2]
        have hy : ((r : ℤ) + 0).toNat = r := by omega
        rw [hy, if_neg h0, if_neg h2]; omega
  · simp only [ho, ↓reduceIte]
    have hd : (if (r - r0) % 4 = 0 then (0 : ℤ) else if (r - r0) % 4 = 2 then 0 else 0) = 0 := by
      split_ifs <;> rfl
    rw [hd]; omega

private lemma blockP_col_right (r0 k c y : ℕ) (hy : r0 ≤ y ∧ y < r0 + 4 * k) :
    let r := invBlockP r0 c y
    let d : ℤ := if (r - r0) % 4 = 0 then dP true c else if (r - r0) % 4 = 2 then dP false c else 0
    r0 ≤ r ∧ r < r0 + 4 * k ∧ ((r : ℤ) + d) = (y : ℤ) := by
  dsimp only; unfold dP invBlockP
  by_cases ho : c % 2 = 1
  · simp only [ho, ↓reduceIte, Bool.false_eq_true]
    by_cases h0 : (y - r0) % 4 = 0
    · rw [if_pos h0, if_neg (by omega), if_pos (by omega)]; omega
    · by_cases h2 : (y - r0) % 4 = 2
      · rw [if_neg h0, if_pos h2, if_pos (by omega)]; omega
      · rw [if_neg h0, if_neg h2, if_neg h0, if_neg h2]; omega
  · simp only [ho, ↓reduceIte]
    have hd : (if (y - r0) % 4 = 0 then (0 : ℤ) else if (y - r0) % 4 = 2 then 0 else 0) = 0 := by
      split_ifs <;> rfl
    rw [hd]; omega

private lemma mod_col_fwd {n n0 : ℕ} (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24) (heven0 : n0 % 2 = 0)
    (hle : n0 ≤ n) (h4 : (n - n0) % 4 = 0) (c r : ℕ) (hr : r < n) :
    let y := ((r : ℤ) + deltaMod n0 r c).toNat
    y < n ∧ ((r : ℤ) + deltaMod n0 r c) = (y : ℤ) ∧ colPermInv n0 c y = r := by
  dsimp only; unfold deltaMod colPermInv; dsimp only
  by_cases hmod4 : n0 % 4 = 2
  · simp only [hmod4, ↓reduceIte]
    by_cases h1 : r < 4
    · have hb := blockA_col_bij 0 (baseShift n0) c r (by omega)
      simp only [Nat.sub_zero, Nat.zero_add] at hb
      rw [if_pos h1, if_pos (by omega)]; exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
    · by_cases h2 : r < 7
      · have hb := blockB_col_bij 4 (baseShift n0 + 11) c r (by omega)
        rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega)]
        exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
      · by_cases h3 : r < 10
        · have hb := blockB_col_bij 7 (baseShift n0 + 13) c r (by omega)
          rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
        · by_cases h4r : r < 10 + 4 * ((n0 - 22) / 4)
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4r]
            have hb := blockP_col_bij 10 ((n0 - 22) / 4) c r (by omega)
            dsimp only at hb
            set y := ((r : ℤ) + (if (r - 10) % 4 = 0 then dP true c else if (r - 10) % 4 = 2 then dP false c else 0)).toNat
            rw [if_neg (by omega : ¬ y < 4), if_neg (by omega : ¬ y < 7), if_neg (by omega : ¬ y < 10),
              if_pos (by omega : y < 10 + 4 * ((n0 - 22) / 4))]
            exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
          · by_cases h5r : r < n0
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r]
              have hy : ((r : ℤ) + 0).toNat = r := by omega
              rw [hy, if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r]; omega
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_neg h5r]
              have hb := blockP_col_bij n0 ((n - n0) / 4) c r (by omega)
              dsimp only at hb
              set y := ((r : ℤ) + (if (r - n0) % 4 = 0 then dP true c else if (r - n0) % 4 = 2 then dP false c else 0)).toNat
              rw [if_neg (by omega : ¬ y < 4), if_neg (by omega : ¬ y < 7), if_neg (by omega : ¬ y < 10),
                if_neg (by omega : ¬ y < 10 + 4 * ((n0 - 22) / 4)), if_neg (by omega : ¬ y < n0)]
              exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
  · simp only [hmod4, ↓reduceIte]
    have hn0_28 : 28 ≤ n0 := by omega
    by_cases h1 : r < 4
    · have hb := blockA_col_bij 0 (baseShift n0) c r (by omega)
      simp only [Nat.sub_zero, Nat.zero_add] at hb
      rw [if_pos h1, if_pos (by omega)]; exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
    · by_cases h2 : r < 8
      · have hb := blockA_col_bij 4 (baseShift n0 + 4) c r (by omega)
        rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega)]
        exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
      · by_cases h3 : r < 11
        · have hb := blockB_col_bij 8 (baseShift n0 + 13) c r (by omega)
          rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
        · by_cases h4r : r < 11 + 4 * ((n0 - 28) / 4)
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4r]
            have hb := blockP_col_bij 11 ((n0 - 28) / 4) c r (by omega)
            dsimp only at hb
            set y := ((r : ℤ) + (if (r - 11) % 4 = 0 then dP true c else if (r - 11) % 4 = 2 then dP false c else 0)).toNat
            rw [if_neg (by omega : ¬ y < 4), if_neg (by omega : ¬ y < 8), if_neg (by omega : ¬ y < 11),
              if_pos (by omega : y < 11 + 4 * ((n0 - 28) / 4))]
            exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩
          · by_cases h5r : r < n0
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r]
              have hy : ((r : ℤ) + 0).toNat = r := by omega
              rw [hy, if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r]; omega
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_neg h5r]
              have hb := blockP_col_bij n0 ((n - n0) / 4) c r (by omega)
              dsimp only at hb
              set y := ((r : ℤ) + (if (r - n0) % 4 = 0 then dP true c else if (r - n0) % 4 = 2 then dP false c else 0)).toNat
              rw [if_neg (by omega : ¬ y < 4), if_neg (by omega : ¬ y < 8), if_neg (by omega : ¬ y < 11),
                if_neg (by omega : ¬ y < 11 + 4 * ((n0 - 28) / 4)), if_neg (by omega : ¬ y < n0)]
              exact ⟨by omega, hb.2.2.1, hb.2.2.2⟩

private lemma mod_col_rev {n n0 : ℕ} (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24) (heven0 : n0 % 2 = 0)
    (hle : n0 ≤ n) (h4 : (n - n0) % 4 = 0) (c y : ℕ) (hy : y < n) :
    let r := colPermInv n0 c y
    r < n ∧ ((r : ℤ) + deltaMod n0 r c) = (y : ℤ) := by
  dsimp only; unfold colPermInv deltaMod; dsimp only
  by_cases hmod4 : n0 % 4 = 2
  · simp only [hmod4, ↓reduceIte]
    by_cases h1 : y < 4
    · have hb := blockA_col_right 0 (baseShift n0) c y (by omega)
      simp only [Nat.sub_zero, Nat.zero_add] at hb
      rw [if_pos h1, if_pos (by omega)]; exact ⟨by omega, hb.2.2⟩
    · by_cases h2 : y < 7
      · have hb := blockB_col_right 4 (baseShift n0 + 11) c y (by omega)
        rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega)]
        exact ⟨by omega, hb.2.2⟩
      · by_cases h3 : y < 10
        · have hb := blockB_col_right 7 (baseShift n0 + 13) c y (by omega)
          rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact ⟨by omega, hb.2.2⟩
        · by_cases h4r : y < 10 + 4 * ((n0 - 22) / 4)
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4r]
            have hb := blockP_col_right 10 ((n0 - 22) / 4) c y (by omega)
            dsimp only at hb
            set r := invBlockP 10 c y
            rw [if_neg (by omega : ¬ r < 4), if_neg (by omega : ¬ r < 7), if_neg (by omega : ¬ r < 10),
              if_pos (by omega : r < 10 + 4 * ((n0 - 22) / 4))]
            exact ⟨by omega, hb.2.2⟩
          · by_cases h5r : y < n0
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r,
                if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r]; omega
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_neg h5r]
              have hb := blockP_col_right n0 ((n - n0) / 4) c y (by omega)
              dsimp only at hb
              set r := invBlockP n0 c y
              rw [if_neg (by omega : ¬ r < 4), if_neg (by omega : ¬ r < 7), if_neg (by omega : ¬ r < 10),
                if_neg (by omega : ¬ r < 10 + 4 * ((n0 - 22) / 4)), if_neg (by omega : ¬ r < n0)]
              exact ⟨by omega, hb.2.2⟩
  · simp only [hmod4, ↓reduceIte]
    have hn0_28 : 28 ≤ n0 := by omega
    by_cases h1 : y < 4
    · have hb := blockA_col_right 0 (baseShift n0) c y (by omega)
      simp only [Nat.sub_zero, Nat.zero_add] at hb
      rw [if_pos h1, if_pos (by omega)]; exact ⟨by omega, hb.2.2⟩
    · by_cases h2 : y < 8
      · have hb := blockA_col_right 4 (baseShift n0 + 4) c y (by omega)
        rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega)]
        exact ⟨by omega, hb.2.2⟩
      · by_cases h3 : y < 11
        · have hb := blockB_col_right 8 (baseShift n0 + 13) c y (by omega)
          rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact ⟨by omega, hb.2.2⟩
        · by_cases h4r : y < 11 + 4 * ((n0 - 28) / 4)
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4r]
            have hb := blockP_col_right 11 ((n0 - 28) / 4) c y (by omega)
            dsimp only at hb
            set r := invBlockP 11 c y
            rw [if_neg (by omega : ¬ r < 4), if_neg (by omega : ¬ r < 8), if_neg (by omega : ¬ r < 11),
              if_pos (by omega : r < 11 + 4 * ((n0 - 28) / 4))]
            exact ⟨by omega, hb.2.2⟩
          · by_cases h5r : y < n0
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r,
                if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_pos h5r]; omega
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4r, if_neg h5r]
              have hb := blockP_col_right n0 ((n - n0) / 4) c y (by omega)
              dsimp only at hb
              set r := invBlockP n0 c y
              rw [if_neg (by omega : ¬ r < 4), if_neg (by omega : ¬ r < 8), if_neg (by omega : ¬ r < 11),
                if_neg (by omega : ¬ r < 11 + 4 * ((n0 - 28) / 4)), if_neg (by omega : ¬ r < n0)]
              exact ⟨by omega, hb.2.2⟩

/-- Our modular square `L_{n, n0}` is a valid `LatinSquare n` for every even `n0 ≥ 22, n0 ≠ 24`
and every `n = n0 + 4 * t` (`t ≥ 0`). -/
def modLatinSquare (n n0 : ℕ) (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24) (heven0 : n0 % 2 = 0)
    (hle : n0 ≤ n) (h4 : (n - n0) % 4 = 0) : LatinSquare n where
  entry r c := ⟨modEntryVal n n0 r.val c.val, modEntryVal_lt (by omega)⟩
  row_bijective r := by
    have hn : 22 ≤ n := by omega
    have heven : n % 2 = 0 := by omega
    have hsh_even : baseShift n0 % 2 = 0 := by unfold baseShift; omega
    have hsh_lo : 4 ≤ baseShift n0 := by unfold baseShift; omega
    have hsh_hi : baseShift n0 + 13 < n := by unfold baseShift; omega
    have hfun : (fun c : Fin n => (⟨modEntryVal n n0 r.val c.val, modEntryVal_lt (by omega)⟩ : Fin n)) =
        (fun c : Fin n => (⟨(((r.val : ℤ) + (c.val : ℤ) + deltaMod n0 r.val c.val) % (n : ℤ)).toNat,
          modEntryVal_lt (by omega)⟩ : Fin n)) := rfl
    rw [hfun]
    unfold deltaMod; dsimp only
    by_cases hmod4 : n0 % 4 = 2
    · simp only [hmod4, ↓reduceIte]
      split_ifs with h1 h2 h3 h4r h5r h6r h7r h8r h9r
      · exact row_bij_of_col_shift (by omega) r.val (dA r.val (baseShift n0)) (invDA r.val (baseShift n0))
          (dA_left_inv hn heven hsh_even hsh_lo hsh_hi h1)
          (dA_right_inv hn heven hsh_even hsh_lo hsh_hi h1)
      · exact row_bij_of_col_shift (by omega) r.val (dB (r.val - 4) (baseShift n0 + 11)) (invDB (r.val - 4) (baseShift n0 + 11))
          (dB_left_inv hn heven (by omega) (by omega) (by unfold baseShift; omega) (by omega))
          (dB_right_inv hn heven (by omega) (by omega) (by unfold baseShift; omega) (by omega))
      · exact row_bij_of_col_shift (by omega) r.val (dB (r.val - 7) (baseShift n0 + 13)) (invDB (r.val - 7) (baseShift n0 + 13))
          (dB_left_inv hn heven (by omega) (by omega) (by unfold baseShift; omega) (by omega))
          (dB_right_inv hn heven (by omega) (by omega) (by unfold baseShift; omega) (by omega))
      · exact row_bij_of_col_shift (by omega) r.val (dP true) (dP false)
          (dP_left_inv (by omega) heven true) (dP_right_inv (by omega) heven true)
      · exact row_bij_of_col_shift (by omega) r.val (dP false) (dP true)
          (dP_left_inv (by omega) heven false) (dP_right_inv (by omega) heven false)
      · exact row_bij_of_col_shift (by omega) r.val (fun _ => 0) (fun _ => 0)
          (fun c hc => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ c) (by omega : (c : ℤ) < n), Int.toNat_natCast])
          (fun y hy => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < n), Int.toNat_natCast])
      · exact row_bij_of_col_shift (by omega) r.val (fun _ => 0) (fun _ => 0)
          (fun c hc => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ c) (by omega : (c : ℤ) < n), Int.toNat_natCast])
          (fun y hy => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < n), Int.toNat_natCast])
      · exact row_bij_of_col_shift (by omega) r.val (dP true) (dP false)
          (dP_left_inv (by omega) heven true) (dP_right_inv (by omega) heven true)
      · exact row_bij_of_col_shift (by omega) r.val (dP false) (dP true)
          (dP_left_inv (by omega) heven false) (dP_right_inv (by omega) heven false)
      · exact row_bij_of_col_shift (by omega) r.val (fun _ => 0) (fun _ => 0)
          (fun c hc => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ c) (by omega : (c : ℤ) < n), Int.toNat_natCast])
          (fun y hy => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < n), Int.toNat_natCast])
    · simp only [hmod4, ↓reduceIte]
      have hn0_28 : 28 ≤ n0 := by omega
      have hsh_hi4 : baseShift n0 + 4 + 13 < n := by unfold baseShift; omega
      split_ifs with h1 h2 h3 h4r h5r h6r h7r h8r h9r
      · exact row_bij_of_col_shift (by omega) r.val (dA r.val (baseShift n0)) (invDA r.val (baseShift n0))
          (dA_left_inv hn heven hsh_even hsh_lo hsh_hi h1)
          (dA_right_inv hn heven hsh_even hsh_lo hsh_hi h1)
      · exact row_bij_of_col_shift (by omega) r.val (dA (r.val - 4) (baseShift n0 + 4)) (invDA (r.val - 4) (baseShift n0 + 4))
          (dA_left_inv hn heven (by omega) (by omega) hsh_hi4 (by omega))
          (dA_right_inv hn heven (by omega) (by omega) hsh_hi4 (by omega))
      · exact row_bij_of_col_shift (by omega) r.val (dB (r.val - 8) (baseShift n0 + 13)) (invDB (r.val - 8) (baseShift n0 + 13))
          (dB_left_inv hn heven (by omega) (by omega) (by unfold baseShift; omega) (by omega))
          (dB_right_inv hn heven (by omega) (by omega) (by unfold baseShift; omega) (by omega))
      · exact row_bij_of_col_shift (by omega) r.val (dP true) (dP false)
          (dP_left_inv (by omega) heven true) (dP_right_inv (by omega) heven true)
      · exact row_bij_of_col_shift (by omega) r.val (dP false) (dP true)
          (dP_left_inv (by omega) heven false) (dP_right_inv (by omega) heven false)
      · exact row_bij_of_col_shift (by omega) r.val (fun _ => 0) (fun _ => 0)
          (fun c hc => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ c) (by omega : (c : ℤ) < n), Int.toNat_natCast])
          (fun y hy => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < n), Int.toNat_natCast])
      · exact row_bij_of_col_shift (by omega) r.val (fun _ => 0) (fun _ => 0)
          (fun c hc => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ c) (by omega : (c : ℤ) < n), Int.toNat_natCast])
          (fun y hy => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < n), Int.toNat_natCast])
      · exact row_bij_of_col_shift (by omega) r.val (dP true) (dP false)
          (dP_left_inv (by omega) heven true) (dP_right_inv (by omega) heven true)
      · exact row_bij_of_col_shift (by omega) r.val (dP false) (dP true)
          (dP_left_inv (by omega) heven false) (dP_right_inv (by omega) heven false)
      · exact row_bij_of_col_shift (by omega) r.val (fun _ => 0) (fun _ => 0)
          (fun c hc => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ c) (by omega : (c : ℤ) < n), Int.toNat_natCast])
          (fun y hy => by simp only [add_zero, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < n), Int.toNat_natCast])
  col_bijective c := by
    let φ : Fin n → Fin n := fun r =>
      ⟨((r.val : ℤ) + deltaMod n0 r.val c.val).toNat, (mod_col_fwd hn0 hne24 heven0 hle h4 c.val r.val r.isLt).1⟩
    let ψ : Fin n → Fin n := fun y =>
      ⟨colPermInv n0 c.val y.val, (mod_col_rev hn0 hne24 heven0 hle h4 c.val y.val y.isLt).1⟩
    have hφ : Function.Bijective φ := by
      apply bijective_of_inv φ ψ
      · intro r; ext; exact (mod_col_fwd hn0 hne24 heven0 hle h4 c.val r.val r.isLt).2.2
      · intro y; ext; dsimp [φ, ψ]
        rw [(mod_col_rev hn0 hne24 heven0 hle h4 c.val y.val y.isLt).2]
        exact Int.toNat_natCast y.val
    let τ : Fin n → Fin n := fun y => ⟨(c.val + y.val) % n, Nat.mod_lt _ (by omega)⟩
    have hτ : Function.Bijective τ := trans_bij n c.val (by omega)
    have hcomp : (fun r : Fin n => (⟨modEntryVal n n0 r.val c.val, modEntryVal_lt (by omega)⟩ : Fin n)) =
        τ ∘ φ := by
      funext r; ext; dsimp [τ, φ, modEntryVal]
      have hy := (mod_col_fwd hn0 hne24 heven0 hle h4 c.val r.val r.isLt).2.1
      have hsum : (r.val : ℤ) + (c.val : ℤ) + deltaMod n0 r.val c.val =
          ((c.val + ((r.val : ℤ) + deltaMod n0 r.val c.val).toNat : ℕ) : ℤ) := by omega
      rw [hsum, ← Int.natCast_emod, Int.toNat_natCast]
    rw [hcomp]
    exact hτ.comp hφ

/-! ## Section 3: No Two Disjoint Transversals in `modLatinSquare` -/

private def maxA (row : ℕ) : ℤ := if row = 0 then 3 else if row = 1 then 2 else if row = 2 then 1 else 0
private def minA (row : ℕ) : ℤ := if row < 2 then 0 else -2
private def maxB (row : ℕ) : ℤ := if row = 0 then 2 else if row = 1 then 1 else 0
private def minB (row : ℕ) : ℤ := if row = 0 then 0 else if row = 1 then -1 else -2

/-- Exact row-minimum bound for `deltaMod n0 r`. -/
def rowMin (n0 r : ℕ) : ℤ :=
  if n0 % 4 = 2 then
    let t0 := (n0 - 22) / 4
    if r < 4 then minA r
    else if r < 7 then minB (r - 4)
    else if r < 10 then minB (r - 7)
    else if r < 10 + 4 * t0 then (if (r - 10) % 4 = 2 then -2 else 0)
    else if r < n0 then 0
    else (if (r - n0) % 4 = 2 then -2 else 0)
  else
    let t0 := (n0 - 28) / 4
    if r < 4 then minA r
    else if r < 8 then minA (r - 4)
    else if r < 11 then minB (r - 8)
    else if r < 11 + 4 * t0 then (if (r - 11) % 4 = 2 then -2 else 0)
    else if r < n0 then 0
    else (if (r - n0) % 4 = 2 then -2 else 0)

/-- Exact row-maximum bound for `deltaMod n0 r`. -/
def rowMax (n0 r : ℕ) : ℤ :=
  if n0 % 4 = 2 then
    let t0 := (n0 - 22) / 4
    if r < 4 then maxA r
    else if r < 7 then maxB (r - 4)
    else if r < 10 then maxB (r - 7)
    else if r < 10 + 4 * t0 then (if (r - 10) % 4 = 0 then 2 else 0)
    else if r < n0 then 0
    else (if (r - n0) % 4 = 0 then 2 else 0)
  else
    let t0 := (n0 - 28) / 4
    if r < 4 then maxA r
    else if r < 8 then maxA (r - 4)
    else if r < 11 then maxB (r - 8)
    else if r < 11 + 4 * t0 then (if (r - 11) % 4 = 0 then 2 else 0)
    else if r < n0 then 0
    else (if (r - n0) % 4 = 0 then 2 else 0)

private lemma dA_bounds_tab (row : Fin 4) (j : Fin 11) :
    minA row.val ≤ dATab row.val j.val ∧
    dATab row.val j.val ≤ maxA row.val ∧
    (row.val = 2 → j.val ≠ 3 → dATab row.val j.val ≤ 0) := by
  decide +revert

private lemma dA_bounds (row s c : ℕ) (hrow : row < 4) :
    minA row ≤ dA row s c ∧
    dA row s c ≤ maxA row ∧
    (row = 2 → c ≠ s + 3 → dA row s c ≤ 0) := by
  by_cases hwin : s ≤ c ∧ c ≤ s + 10
  · have ht := dA_bounds_tab ⟨row, hrow⟩ ⟨c - s, by omega⟩
    dsimp only at ht
    have hd : dA row s c = dATab row (c - s) := by unfold dA; rw [if_pos hwin]
    rw [hd]; exact ⟨ht.1, ht.2.1, fun hr hc => ht.2.2 hr (by omega)⟩
  · have hd : dA row s c = if c % 2 = 1 then (if row < 2 then 2 else -2) else 0 := by
      unfold dA; rw [if_neg hwin]
    rw [hd]; unfold minA maxA
    rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2 ∨ row = 3) with rfl | rfl | rfl | rfl <;>
      · refine ⟨?_, ?_, ?_⟩ <;> (try intros) <;> split_ifs <;> omega

private lemma dB_bounds (row c_odd c : ℕ) (hrow : row < 3) :
    minB row ≤ dB row c_odd c ∧
    dB row c_odd c ≤ maxB row ∧
    (row = 1 → c ≠ c_odd → dB row c_odd c ≤ 0) := by
  rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2) with rfl | rfl | rfl
  · refine ⟨?_, ?_, fun h => by omega⟩ <;> (simp [dB, minB, maxB]; split_ifs <;> omega)
  · refine ⟨?_, ?_, fun _ hne => ?_⟩ <;> (simp [dB, minB, maxB]; split_ifs <;> omega)
  · refine ⟨?_, ?_, fun h => by omega⟩ <;> (simp [dB, minB, maxB]; split_ifs <;> omega)

private lemma sum_mod4_blocks (a k : ℕ) (ha : a < 4) (v : ℤ) :
    (∑ i ∈ Finset.range (4 * k), if i % 4 = a then v else 0) = (k : ℤ) * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h4 : 4 * (k + 1) = 4 * k + 4 := by omega
    rw [h4, Finset.sum_range_add, ih]
    have h4step : (∑ x ∈ Finset.range 4, if (4 * k + x) % 4 = a then v else 0) = v := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      have h0 : (4 * k + 0) % 4 = 0 := by omega
      have h1 : (4 * k + 1) % 4 = 1 := by omega
      have h2 : (4 * k + 2) % 4 = 2 := by omega
      have h3 : (4 * k + 3) % 4 = 3 := by omega
      rw [h0, h1, h2, h3]
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl <;> simp
    rw [h4step]; push_cast; ring

private lemma sum_range_split {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range b, f i) =
      (∑ i ∈ Finset.range a, f i) + ∑ j ∈ Finset.range (b - a), f (a + j) := by
  have hb : b = a + (b - a) := by omega
  conv_lhs => rw [hb]
  exact Finset.sum_range_add f a (b - a)

private lemma rowMin_le_deltaMod (n0 r c : ℕ) : rowMin n0 r ≤ deltaMod n0 r c := by
  unfold rowMin deltaMod; dsimp only
  by_cases hm : n0 % 4 = 2
  · simp only [hm, ↓reduceIte]
    by_cases h1 : r < 4
    · simp only [h1, ↓reduceIte]; exact (dA_bounds r (baseShift n0) c h1).1
    · by_cases h2 : r < 7
      · simp only [h1, h2, ↓reduceIte]; exact (dB_bounds (r - 4) (baseShift n0 + 11) c (by omega)).1
      · by_cases h3 : r < 10
        · simp only [h1, h2, h3, ↓reduceIte]; exact (dB_bounds (r - 7) (baseShift n0 + 13) c (by omega)).1
        · by_cases h4 : r < 10 + 4 * ((n0 - 22) / 4)
          · simp only [h1, h2, h3, h4, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega
          · by_cases h5 : r < n0
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte]; omega
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega
  · simp only [hm, ↓reduceIte]
    by_cases h1 : r < 4
    · simp only [h1, ↓reduceIte]; exact (dA_bounds r (baseShift n0) c h1).1
    · by_cases h2 : r < 8
      · simp only [h1, h2, ↓reduceIte]; exact (dA_bounds (r - 4) (baseShift n0 + 4) c (by omega)).1
      · by_cases h3 : r < 11
        · simp only [h1, h2, h3, ↓reduceIte]; exact (dB_bounds (r - 8) (baseShift n0 + 13) c (by omega)).1
        · by_cases h4 : r < 11 + 4 * ((n0 - 28) / 4)
          · simp only [h1, h2, h3, h4, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega
          · by_cases h5 : r < n0
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte]; omega
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega

private lemma deltaMod_le_rowMax (n0 r c : ℕ) : deltaMod n0 r c ≤ rowMax n0 r := by
  unfold rowMax deltaMod; dsimp only
  by_cases hm : n0 % 4 = 2
  · simp only [hm, ↓reduceIte]
    by_cases h1 : r < 4
    · simp only [h1, ↓reduceIte]; exact (dA_bounds r (baseShift n0) c h1).2.1
    · by_cases h2 : r < 7
      · simp only [h1, h2, ↓reduceIte]; exact (dB_bounds (r - 4) (baseShift n0 + 11) c (by omega)).2.1
      · by_cases h3 : r < 10
        · simp only [h1, h2, h3, ↓reduceIte]; exact (dB_bounds (r - 7) (baseShift n0 + 13) c (by omega)).2.1
        · by_cases h4 : r < 10 + 4 * ((n0 - 22) / 4)
          · simp only [h1, h2, h3, h4, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega
          · by_cases h5 : r < n0
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte]; omega
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega
  · simp only [hm, ↓reduceIte]
    by_cases h1 : r < 4
    · simp only [h1, ↓reduceIte]; exact (dA_bounds r (baseShift n0) c h1).2.1
    · by_cases h2 : r < 8
      · simp only [h1, h2, ↓reduceIte]; exact (dA_bounds (r - 4) (baseShift n0 + 4) c (by omega)).2.1
      · by_cases h3 : r < 11
        · simp only [h1, h2, h3, ↓reduceIte]; exact (dB_bounds (r - 8) (baseShift n0 + 13) c (by omega)).2.1
        · by_cases h4 : r < 11 + 4 * ((n0 - 28) / 4)
          · simp only [h1, h2, h3, h4, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega
          · by_cases h5 : r < n0
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte]; omega
            · simp only [h1, h2, h3, h4, h5, ↓reduceIte, dP, Bool.false_eq_true]; split_ifs <;> omega

private lemma sum_rowMax_eq {n n0 : ℕ} (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24) (heven0 : n0 % 2 = 0)
    (hle : n0 ≤ n) (h4 : (n - n0) % 4 = 0) :
    (∑ r : Fin n, rowMax n0 r.val) = ((n / 2 : ℕ) : ℤ) + 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => rowMax n0 r)]
  by_cases hm : n0 % 4 = 2
  · set t0 := (n0 - 22) / 4
    set t := (n - n0) / 4
    rw [sum_range_split hle]
    have htail : (∑ j ∈ Finset.range (n - n0), rowMax n0 (n0 + j)) = (t : ℤ) * 2 := by
      have hlen : n - n0 = 4 * t := by omega
      rw [hlen]
      have heq : ∀ j ∈ Finset.range (4 * t),
          rowMax n0 (n0 + j) = (if j % 4 = 0 then (2 : ℤ) else 0) := by
        intro j _; unfold rowMax; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 0 t (by omega) 2]
    rw [htail, sum_range_split (show 10 + 4 * t0 ≤ n0 by omega)]
    have hzero : (∑ j ∈ Finset.range (n0 - (10 + 4 * t0)), rowMax n0 (10 + 4 * t0 + j)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hj' := Finset.mem_range.mp hj
      unfold rowMax; simp only [hm, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hzero, add_zero, sum_range_split (show 10 ≤ 10 + 4 * t0 by omega)]
    have hmid : (∑ j ∈ Finset.range (10 + 4 * t0 - 10), rowMax n0 (10 + j)) = (t0 : ℤ) * 2 := by
      rw [Nat.add_sub_cancel_left]
      have heq : ∀ j ∈ Finset.range (4 * t0),
          rowMax n0 (10 + j) = (if j % 4 = 0 then (2 : ℤ) else 0) := by
        intro j hj; have hj' := Finset.mem_range.mp hj
        unfold rowMax; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 0 t0 (by omega) 2]
    rw [hmid]
    have hhead : (∑ i ∈ Finset.range 10, rowMax n0 i) = 12 := by
      have heq : ∀ i ∈ Finset.range 10,
          rowMax n0 i = (if i < 4 then maxA i else if i < 7 then maxB (i - 4) else maxB (i - 7)) := by
        intro i hi; have hi' := Finset.mem_range.mp hi
        unfold rowMax; simp only [hm, ↓reduceIte]; split_ifs <;> omega
      rw [Finset.sum_congr rfl heq]; decide
    rw [hhead]; omega
  · have hn0_28 : 28 ≤ n0 := by omega
    set t0 := (n0 - 28) / 4
    set t := (n - n0) / 4
    rw [sum_range_split hle]
    have htail : (∑ j ∈ Finset.range (n - n0), rowMax n0 (n0 + j)) = (t : ℤ) * 2 := by
      have hlen : n - n0 = 4 * t := by omega
      rw [hlen]
      have heq : ∀ j ∈ Finset.range (4 * t),
          rowMax n0 (n0 + j) = (if j % 4 = 0 then (2 : ℤ) else 0) := by
        intro j _; unfold rowMax; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 0 t (by omega) 2]
    rw [htail, sum_range_split (show 11 + 4 * t0 ≤ n0 by omega)]
    have hzero : (∑ j ∈ Finset.range (n0 - (11 + 4 * t0)), rowMax n0 (11 + 4 * t0 + j)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hj' := Finset.mem_range.mp hj
      unfold rowMax; simp only [hm, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hzero, add_zero, sum_range_split (show 11 ≤ 11 + 4 * t0 by omega)]
    have hmid : (∑ j ∈ Finset.range (11 + 4 * t0 - 11), rowMax n0 (11 + j)) = (t0 : ℤ) * 2 := by
      rw [Nat.add_sub_cancel_left]
      have heq : ∀ j ∈ Finset.range (4 * t0),
          rowMax n0 (11 + j) = (if j % 4 = 0 then (2 : ℤ) else 0) := by
        intro j hj; have hj' := Finset.mem_range.mp hj
        unfold rowMax; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 0 t0 (by omega) 2]
    rw [hmid]
    have hhead : (∑ i ∈ Finset.range 11, rowMax n0 i) = 15 := by
      have heq : ∀ i ∈ Finset.range 11,
          rowMax n0 i = (if i < 4 then maxA i else if i < 8 then maxA (i - 4) else maxB (i - 8)) := by
        intro i hi; have hi' := Finset.mem_range.mp hi
        unfold rowMax; simp only [hm, ↓reduceIte]; split_ifs <;> omega
      rw [Finset.sum_congr rfl heq]; decide
    rw [hhead]; omega

private lemma sum_rowMin_gt {n n0 : ℕ} (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24) (heven0 : n0 % 2 = 0)
    (hle : n0 ≤ n) (h4 : (n - n0) % 4 = 0) :
    -((n / 2 : ℕ) : ℤ) < ∑ r : Fin n, rowMin n0 r.val := by
  rw [Fin.sum_univ_eq_sum_range (fun r => rowMin n0 r)]
  by_cases hm : n0 % 4 = 2
  · set t0 := (n0 - 22) / 4
    set t := (n - n0) / 4
    rw [sum_range_split hle]
    have htail : (∑ j ∈ Finset.range (n - n0), rowMin n0 (n0 + j)) = (t : ℤ) * (-2) := by
      have hlen : n - n0 = 4 * t := by omega
      rw [hlen]
      have heq : ∀ j ∈ Finset.range (4 * t),
          rowMin n0 (n0 + j) = (if j % 4 = 2 then (-2 : ℤ) else 0) := by
        intro j _; unfold rowMin; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 2 t (by omega) (-2)]
    rw [htail, sum_range_split (show 10 + 4 * t0 ≤ n0 by omega)]
    have hzero : (∑ j ∈ Finset.range (n0 - (10 + 4 * t0)), rowMin n0 (10 + 4 * t0 + j)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hj' := Finset.mem_range.mp hj
      unfold rowMin; simp only [hm, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hzero, add_zero, sum_range_split (show 10 ≤ 10 + 4 * t0 by omega)]
    have hmid : (∑ j ∈ Finset.range (10 + 4 * t0 - 10), rowMin n0 (10 + j)) = (t0 : ℤ) * (-2) := by
      rw [Nat.add_sub_cancel_left]
      have heq : ∀ j ∈ Finset.range (4 * t0),
          rowMin n0 (10 + j) = (if j % 4 = 2 then (-2 : ℤ) else 0) := by
        intro j hj; have hj' := Finset.mem_range.mp hj
        unfold rowMin; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 2 t0 (by omega) (-2)]
    rw [hmid]
    have hhead : (∑ i ∈ Finset.range 10, rowMin n0 i) = -10 := by
      have heq : ∀ i ∈ Finset.range 10,
          rowMin n0 i = (if i < 4 then minA i else if i < 7 then minB (i - 4) else minB (i - 7)) := by
        intro i hi; have hi' := Finset.mem_range.mp hi
        unfold rowMin; simp only [hm, ↓reduceIte]; split_ifs <;> omega
      rw [Finset.sum_congr rfl heq]; decide
    rw [hhead]; omega
  · have hn0_28 : 28 ≤ n0 := by omega
    set t0 := (n0 - 28) / 4
    set t := (n - n0) / 4
    rw [sum_range_split hle]
    have htail : (∑ j ∈ Finset.range (n - n0), rowMin n0 (n0 + j)) = (t : ℤ) * (-2) := by
      have hlen : n - n0 = 4 * t := by omega
      rw [hlen]
      have heq : ∀ j ∈ Finset.range (4 * t),
          rowMin n0 (n0 + j) = (if j % 4 = 2 then (-2 : ℤ) else 0) := by
        intro j _; unfold rowMin; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 2 t (by omega) (-2)]
    rw [htail, sum_range_split (show 11 + 4 * t0 ≤ n0 by omega)]
    have hzero : (∑ j ∈ Finset.range (n0 - (11 + 4 * t0)), rowMin n0 (11 + 4 * t0 + j)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hj' := Finset.mem_range.mp hj
      unfold rowMin; simp only [hm, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hzero, add_zero, sum_range_split (show 11 ≤ 11 + 4 * t0 by omega)]
    have hmid : (∑ j ∈ Finset.range (11 + 4 * t0 - 11), rowMin n0 (11 + j)) = (t0 : ℤ) * (-2) := by
      rw [Nat.add_sub_cancel_left]
      have heq : ∀ j ∈ Finset.range (4 * t0),
          rowMin n0 (11 + j) = (if j % 4 = 2 then (-2 : ℤ) else 0) := by
        intro j hj; have hj' := Finset.mem_range.mp hj
        unfold rowMin; simp only [hm, ↓reduceIte]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl heq, sum_mod4_blocks 2 t0 (by omega) (-2)]
    rw [hmid]
    have hhead : (∑ i ∈ Finset.range 11, rowMin n0 i) = -11 := by
      have heq : ∀ i ∈ Finset.range 11,
          rowMin n0 i = (if i < 4 then minA i else if i < 8 then minA (i - 4) else minB (i - 8)) := by
        intro i hi; have hi' := Finset.mem_range.mp hi
        unfold rowMin; simp only [hm, ↓reduceIte]; split_ifs <;> omega
      rw [Finset.sum_congr rfl heq]; decide
    rw [hhead]; omega

private lemma modLatinSquare_no_disjoint_even (m n0 : ℕ) (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24)
    (heven0 : n0 % 2 = 0) (hle : n0 ≤ 2 * m) (h4 : (2 * m - n0) % 4 = 0) :
    ∀ T₁ T₂,
      IsTransversal (modLatinSquare (2 * m) n0 hn0 hne24 heven0 hle h4) T₁ →
      IsTransversal (modLatinSquare (2 * m) n0 hn0 hne24 heven0 hle h4) T₂ →
      ¬ DisjointTransversals T₁ T₂ := by
  have hm : 0 < m := by omega
  let L := modLatinSquare (2 * m) n0 hn0 hne24 heven0 hle h4
  have hsum_mx : (∑ r : Fin (2 * m), rowMax n0 r.val) = (m : ℤ) + 1 := by
    have h := sum_rowMax_eq hn0 hne24 heven0 hle h4
    rwa [show 2 * m / 2 = m by omega] at h
  have hsum_mn : -((m : ℤ)) < ∑ r : Fin (2 * m), rowMin n0 r.val := by
    have h := sum_rowMin_gt hn0 hne24 heven0 hle h4
    rwa [show 2 * m / 2 = m by omega] at h
  have hL : ∀ r c : Fin (2 * m),
      ((L.entry r c).val : ℤ) ≡ (r.val : ℤ) + (c.val : ℤ) + deltaMod n0 r.val c.val [ZMOD (2 * m : ℤ)] := by
    intro r c
    have h := modEntryVal_modEq (n := 2 * m) (n0 := n0) (r := r.val) (c := c.val) (by omega)
    simpa [L, modLatinSquare] using h
  by_cases hm4 : n0 % 4 = 2
  · exact no_disjoint_of_three_unique_max hm L (fun r c => deltaMod n0 r.val c.val) hL
      (fun r => rowMin n0 r.val) (fun r => rowMax n0 r.val)
      (fun r c => rowMin_le_deltaMod n0 r.val c.val)
      (fun r c => deltaMod_le_rowMax n0 r.val c.val)
      hsum_mx hsum_mn
      ⟨2, by omega⟩ ⟨5, by omega⟩ ⟨8, by omega⟩
      ⟨baseShift n0 + 3, by unfold baseShift; omega⟩
      ⟨baseShift n0 + 11, by unfold baseShift; omega⟩
      ⟨baseShift n0 + 13, by unfold baseShift; omega⟩
      (by intro h; simp [Fin.ext_iff] at h) (by intro h; simp [Fin.ext_iff] at h) (by intro h; simp [Fin.ext_iff] at h)
      (fun c hc => by
        have hc' : c.val ≠ baseShift n0 + 3 := fun h => hc (Fin.ext h)
        have hmx2 : rowMax n0 2 = 1 := by unfold rowMax maxA; simp [hm4]
        have hd2 : deltaMod n0 2 c.val = dA 2 (baseShift n0) c.val := by unfold deltaMod; simp [hm4]
        rw [hmx2, hd2]; have := (dA_bounds 2 (baseShift n0) c.val (by omega)).2.2 rfl hc'; omega)
      (fun c hc => by
        have hc' : c.val ≠ baseShift n0 + 11 := fun h => hc (Fin.ext h)
        have hmx5 : rowMax n0 5 = 1 := by unfold rowMax maxB; simp [hm4]
        have hd5 : deltaMod n0 5 c.val = dB 1 (baseShift n0 + 11) c.val := by unfold deltaMod; simp [hm4]
        rw [hmx5, hd5]; have := (dB_bounds 1 (baseShift n0 + 11) c.val (by omega)).2.2 rfl hc'; omega)
      (fun c hc => by
        have hc' : c.val ≠ baseShift n0 + 13 := fun h => hc (Fin.ext h)
        have hmx8 : rowMax n0 8 = 1 := by unfold rowMax maxB; simp [hm4]
        have hd8 : deltaMod n0 8 c.val = dB 1 (baseShift n0 + 13) c.val := by unfold deltaMod; simp [hm4]
        rw [hmx8, hd8]; have := (dB_bounds 1 (baseShift n0 + 13) c.val (by omega)).2.2 rfl hc'; omega)
  · exact no_disjoint_of_three_unique_max hm L (fun r c => deltaMod n0 r.val c.val) hL
      (fun r => rowMin n0 r.val) (fun r => rowMax n0 r.val)
      (fun r c => rowMin_le_deltaMod n0 r.val c.val)
      (fun r c => deltaMod_le_rowMax n0 r.val c.val)
      hsum_mx hsum_mn
      ⟨2, by omega⟩ ⟨6, by omega⟩ ⟨9, by omega⟩
      ⟨baseShift n0 + 3, by unfold baseShift; omega⟩
      ⟨baseShift n0 + 7, by unfold baseShift; omega⟩
      ⟨baseShift n0 + 13, by unfold baseShift; omega⟩
      (by intro h; simp [Fin.ext_iff] at h) (by intro h; simp [Fin.ext_iff] at h) (by intro h; simp [Fin.ext_iff] at h)
      (fun c hc => by
        have hc' : c.val ≠ baseShift n0 + 3 := fun h => hc (Fin.ext h)
        have hmx2 : rowMax n0 2 = 1 := by unfold rowMax maxA; simp [hm4]
        have hd2 : deltaMod n0 2 c.val = dA 2 (baseShift n0) c.val := by unfold deltaMod; simp [hm4]
        rw [hmx2, hd2]; have := (dA_bounds 2 (baseShift n0) c.val (by omega)).2.2 rfl hc'; omega)
      (fun c hc => by
        have hc' : c.val ≠ baseShift n0 + 7 := fun h => hc (Fin.ext h)
        have hmx6 : rowMax n0 6 = 1 := by unfold rowMax maxA; simp [hm4]
        have hd6 : deltaMod n0 6 c.val = dA 2 (baseShift n0 + 4) c.val := by unfold deltaMod; simp [hm4]
        rw [hmx6, hd6]; have := (dA_bounds 2 (baseShift n0 + 4) c.val (by omega)).2.2 rfl (by omega); omega)
      (fun c hc => by
        have hc' : c.val ≠ baseShift n0 + 13 := fun h => hc (Fin.ext h)
        have hmx9 : rowMax n0 9 = 1 := by unfold rowMax maxB; simp [hm4]
        have hd9 : deltaMod n0 9 c.val = dB 1 (baseShift n0 + 13) c.val := by unfold deltaMod; simp [hm4]
        rw [hmx9, hd9]; have := (dB_bounds 1 (baseShift n0 + 13) c.val (by omega)).2.2 rfl hc'; omega)

/-- **Theorem (No Disjoint Transversals for All `L_{n, n0}`).** -/
theorem modLatinSquare_no_disjoint (n n0 : ℕ) (hn0 : 22 ≤ n0) (hne24 : n0 ≠ 24)
    (heven0 : n0 % 2 = 0) (hle : n0 ≤ n) (h4 : (n - n0) % 4 = 0) :
    ∀ T₁ T₂,
      IsTransversal (modLatinSquare n n0 hn0 hne24 heven0 hle h4) T₁ →
      IsTransversal (modLatinSquare n n0 hn0 hne24 heven0 hle h4) T₂ →
      ¬ DisjointTransversals T₁ T₂ := by
  have h2m : n = 2 * (n / 2) := by omega
  generalize hm : n / 2 = m at h2m
  subst h2m
  exact modLatinSquare_no_disjoint_even m n0 hn0 hne24 heven0 hle h4

end GhafariWanless
