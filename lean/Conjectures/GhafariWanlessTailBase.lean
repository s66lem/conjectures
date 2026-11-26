import Mathlib.Tactic
import Conjectures.GhafariWanlessData
import Conjectures.GhafariWanlessCore

/-!
# Shared Tail Primitives for Ghafari–Wanless Conjecture 3

Common definitions and lemmas shared by the even-`h` and odd-`h` parametric tail constructions
and the gluing theorem in `Conjectures.GhafariWanlessLatinTransversals`.
-/

namespace GhafariWanless

/-- Check a boolean predicate on all `i < k`. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, P => P k && allLt k P

lemma allLt_true {k : ℕ} {P : ℕ → Bool} (h : allLt k P = true) : ∀ i < k, P i = true := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [allLt, Bool.and_eq_true] at h
    intro i hi
    by_cases heq : i = k
    · subst heq; exact h.1
    · exact ih h.2 i (by omega)

/-- Pairwise distinctness check on `f 0, ..., f (k - 1)`. -/
def allPairsDistinct {α : Type} [BEq α] (k : ℕ) (f : ℕ → α) : Bool :=
  allLt k fun i => allLt i fun j => !(f i == f j)

lemma allPairsDistinct_inj {α : Type} [BEq α] [LawfulBEq α] {k : ℕ} {f : ℕ → α}
    (h : allPairsDistinct k f = true) {i j : ℕ} (hi : i < k) (hj : j < k)
    (heq : f i = f j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h' := allLt_true (allLt_true h j hj) i hlt
    simp [heq] at h'
  · have h' := allLt_true (allLt_true h i hi) j hgt
    simp [heq] at h'

/-- Offset on tail row `i` and tail column `c` (`i < 4 * t`, `c < 4 * t`). -/
def tailDelta (i c : ℕ) : ℤ :=
  if i % 4 = 0 then dP true c else if i % 4 = 2 then dP false c else 0

lemma deltaMod_tail_eq (h i c : ℕ) (hh : 11 ≤ h) :
    deltaMod (2 * h) (2 * h + i) (2 * h + c) = tailDelta i c := by
  unfold deltaMod tailDelta dP; dsimp only
  have hpar : (2 * h + c) % 2 = c % 2 := by omega
  by_cases hm : (2 * h) % 4 = 2
  · simp only [hm, ↓reduceIte, Nat.add_sub_cancel_left, hpar]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp only [hm, ↓reduceIte, Nat.add_sub_cancel_left, hpar]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma tailDelta_mod0_odd (j u : ℕ) :
    ((4 * j : ℕ) : ℤ) + ((2 * u + 1 : ℕ) : ℤ) + tailDelta (4 * j) (2 * u + 1) =
    ((2 * (2 * j + u + 1) + 1 : ℕ) : ℤ) := by
  simp only [tailDelta, dP, ↓reduceIte, Bool.false_eq_true]; split_ifs <;> omega

lemma tailDelta_mod1_odd (j u : ℕ) :
    ((4 * j + 1 : ℕ) : ℤ) + ((2 * u + 1 : ℕ) : ℤ) + tailDelta (4 * j + 1) (2 * u + 1) =
    ((2 * (2 * j + u + 1) : ℕ) : ℤ) := by
  simp only [tailDelta, dP, ↓reduceIte, Bool.false_eq_true]; split_ifs <;> omega

lemma tailDelta_mod1_even (j u : ℕ) :
    ((4 * j + 1 : ℕ) : ℤ) + ((2 * u : ℕ) : ℤ) + tailDelta (4 * j + 1) (2 * u) =
    ((2 * (2 * j + u) + 1 : ℕ) : ℤ) := by
  simp only [tailDelta, dP, ↓reduceIte, Bool.false_eq_true]; split_ifs <;> omega

lemma tailDelta_mod2_even (j u : ℕ) :
    ((4 * j + 2 : ℕ) : ℤ) + ((2 * u : ℕ) : ℤ) + tailDelta (4 * j + 2) (2 * u) =
    ((2 * (2 * j + u + 1) : ℕ) : ℤ) := by
  simp only [tailDelta, dP, ↓reduceIte, Bool.false_eq_true]; split_ifs <;> omega

lemma tailDelta_mod3_even (j u : ℕ) :
    ((4 * j + 3 : ℕ) : ℤ) + ((2 * u : ℕ) : ℤ) + tailDelta (4 * j + 3) (2 * u) =
    ((2 * (2 * j + u + 1) + 1 : ℕ) : ℤ) := by
  simp only [tailDelta, dP, ↓reduceIte, Bool.false_eq_true]; split_ifs <;> omega

lemma tailDelta_mod3_odd (j u : ℕ) :
    ((4 * j + 3 : ℕ) : ℤ) + ((2 * u + 1 : ℕ) : ℤ) + tailDelta (4 * j + 3) (2 * u + 1) =
    ((2 * (2 * j + u + 2) : ℕ) : ℤ) := by
  simp only [tailDelta, dP, ↓reduceIte, Bool.false_eq_true]; split_ifs <;> omega

/-- A valid tail transversal map on `[0, 4 * t)` hitting `[2t - h, 4t - h) ∪ [4t + h, 6t + h)`. -/
structure ValidTail (h t : ℕ) where
  col : ℕ → ℕ
  col_lt : ∀ i < 4 * t, col i < 4 * t
  col_inj : ∀ i₁ < 4 * t, ∀ i₂ < 4 * t, col i₁ = col i₂ → i₁ = i₂
  sym_band : ∀ i < 4 * t,
    let s : ℤ := (i : ℤ) + (col i : ℤ) + tailDelta i (col i)
    (((2 * t : ℤ) - (h : ℤ) ≤ s ∧ s < (4 * t : ℤ) - (h : ℤ)) ∨
     ((4 * t : ℤ) + (h : ℤ) ≤ s ∧ s < (6 * t : ℤ) + (h : ℤ)))
  sym_inj : ∀ i₁ < 4 * t, ∀ i₂ < 4 * t,
    (i₁ : ℤ) + (col i₁ : ℤ) + tailDelta i₁ (col i₁) =
    (i₂ : ℤ) + (col i₂ : ℤ) + tailDelta i₂ (col i₂) → i₁ = i₂

/-- Slope of leftover row-quadruple index `ji` in the 3 gaps between the 4 parametric blocks. -/
def rjSlope (j3_0 j1_0 ji : ℕ) : ℕ :=
  if ji < j3_0 then 1 else if ji < j1_0 then 2 else 3

def evalRJ (j3_0 j1_0 p ji : ℕ) : ℕ :=
  ji + rjSlope j3_0 j1_0 ji * p

/-- Slope of leftover column-pair index `ui` in the 5 gaps between the 4 parametric blocks. -/
def ruSlope (U1_0 U2_0 U0_0 U3_0 ui : ℕ) : ℕ :=
  if ui < U1_0 then 0
  else if ui < U2_0 then 2
  else if ui < U0_0 then 4
  else if ui < U3_0 then 6
  else 8

def evalRU (U1_0 U2_0 U0_0 U3_0 p ui : ℕ) : ℕ :=
  ui + ruSlope U1_0 U2_0 U0_0 U3_0 ui * p

lemma evalRU_lt {U1_0 U2_0 U0_0 U3_0 R p ui : ℕ}
    (_h12 : U1_0 ≤ U2_0) (_h20 : U2_0 ≤ U0_0) (_h03 : U0_0 ≤ U3_0) (_h3R : U3_0 ≤ 2 * R)
    (hui : ui < 2 * R) :
    evalRU U1_0 U2_0 U0_0 U3_0 p ui < 2 * (4 * p + R) := by
  unfold evalRU ruSlope; split_ifs <;> omega

lemma evalRU_inj {U1_0 U2_0 U0_0 U3_0 p u1 u2 : ℕ}
    (_h12 : U1_0 ≤ U2_0) (_h20 : U2_0 ≤ U0_0) (_h03 : U0_0 ≤ U3_0)
    (heq : evalRU U1_0 U2_0 U0_0 U3_0 p u1 = evalRU U1_0 U2_0 U0_0 U3_0 p u2) :
    u1 = u2 := by
  unfold evalRU ruSlope at heq; split_ifs at heq <;> omega

lemma evalRU_not_in_blocks {U1_0 U2_0 U0_0 U3_0 R p ui : ℕ}
    (h12 : U1_0 ≤ U2_0) (h20 : U2_0 ≤ U0_0) (h03 : U0_0 ≤ U3_0) (_h3R : U3_0 ≤ 2 * R)
    (_hui : ui < 2 * R) :
    let u := evalRU U1_0 U2_0 U0_0 U3_0 p ui
    ¬ (U1_0 ≤ u ∧ u < U1_0 + 2 * p) ∧
    ¬ (U2_0 + 2 * p ≤ u ∧ u < U2_0 + 4 * p) ∧
    ¬ (U0_0 + 4 * p ≤ u ∧ u < U0_0 + 6 * p) ∧
    ¬ (U3_0 + 6 * p ≤ u ∧ u < U3_0 + 8 * p) := by
  dsimp only; unfold evalRU ruSlope; split_ifs <;> omega

/-- Check that a linear half-symbol `s0 + cs * q` lies in one of the 4 parametric gap intervals
`[a1+4q, lo1+4q) ∪ [hi1+8q, c1+8q) ∪ [a2+8q, lo2+8q) ∪ [hi2+12q, c2+12q)`. -/
def inSGaps (a1 lo1 hi1 c1 a2 lo2 hi2 c2 s0 cs : ℕ) : Bool :=
  (cs == 4 && a1 ≤ s0 && s0 < lo1) ||
  (cs == 8 && ((hi1 ≤ s0 && s0 < c1) || (a2 ≤ s0 && s0 < lo2))) ||
  (cs == 12 && hi2 ≤ s0 && s0 < c2)

lemma inSGaps_spec {a1 lo1 hi1 c1 a2 lo2 hi2 c2 s0 cs q : ℕ}
    (hord : a1 ≤ lo1 ∧ lo1 + 4 * q ≤ hi1 + 8 * q ∧ hi1 ≤ c1 ∧ c1 ≤ a2 ∧
            a2 ≤ lo2 ∧ lo2 + 8 * q ≤ hi2 + 12 * q ∧ hi2 ≤ c2)
    (hin : inSGaps a1 lo1 hi1 c1 a2 lo2 hi2 c2 s0 cs = true) :
    let s := s0 + cs * q
    ((a1 + 4 * q ≤ s ∧ s < c1 + 8 * q) ∨ (a2 + 8 * q ≤ s ∧ s < c2 + 12 * q)) ∧
    ¬ (lo1 + 4 * q ≤ s ∧ s < hi1 + 8 * q) ∧
    ¬ (lo2 + 8 * q ≤ s ∧ s < hi2 + 12 * q) := by
  rcases hord with ⟨_, _, _, _, _, _, _⟩
  unfold inSGaps at hin
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hin
  rcases hin with (⟨⟨rfl, hlo⟩, hhi⟩ | ⟨rfl, ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩⟩) | ⟨⟨rfl, hlo⟩, hhi⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

lemma inSGaps_inj {a1 lo1 hi1 c1 a2 lo2 hi2 c2 sA cA sB cB q : ℕ}
    (hord : a1 ≤ lo1 ∧ lo1 + 4 * q ≤ hi1 + 8 * q ∧ hi1 ≤ c1 ∧ c1 ≤ a2 ∧
            a2 ≤ lo2 ∧ lo2 + 8 * q ≤ hi2 + 12 * q ∧ hi2 ≤ c2)
    (hA : inSGaps a1 lo1 hi1 c1 a2 lo2 hi2 c2 sA cA = true)
    (hB : inSGaps a1 lo1 hi1 c1 a2 lo2 hi2 c2 sB cB = true)
    (heq : sA + cA * q = sB + cB * q) :
    sA = sB ∧ cA = cB := by
  rcases hord with ⟨_, _, _, _, _, _, _⟩
  unfold inSGaps at hA hB
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hA hB
  rcases hA with (⟨⟨rfl, _⟩, _⟩ | ⟨rfl, ⟨_, _⟩ | ⟨_, _⟩⟩) | ⟨⟨rfl, _⟩, _⟩ <;>
    rcases hB with (⟨⟨rfl, _⟩, _⟩ | ⟨rfl, ⟨_, _⟩ | ⟨_, _⟩⟩) | ⟨⟨rfl, _⟩, _⟩ <;> omega

end GhafariWanless
