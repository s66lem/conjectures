import Conjectures.StableKneserK3.Weights
import Mathlib.Data.Nat.Bitwise

namespace StableKneserK3.PackedWeights

variable {α : Type*}

/-- A sample contributes one digit, equal to its weight when the predicate holds. -/
def pack (width : ℕ) (p : α → Bool) : List (α × ℕ) → ℕ
  | [] => 0
  | (a,w) :: tail => 2^width * pack width p tail + (if p a then w else 0)

def mass (p : α → Bool) : List (α × ℕ) → ℕ
  | [] => 0
  | (a,w) :: tail => (if p a then w else 0) + mass p tail

private theorem mono (p : α → Bool) (l : List (α × ℕ)) :
    mass p l ≤ mass (fun _ => true) l := by
  induction l with
  | nil => rfl
  | cons e l ih => cases e with | mk a w => cases h : p a <;> simp [mass, h] <;> omega

private theorem mod_pack (width : ℕ) (p : α → Bool) (l : List (α × ℕ)) :
    ∃ k, pack width p l = mass p l + k * (2^width-1) := by
  induction l with
  | nil => exact ⟨0, by simp [pack, mass]⟩
  | cons e l ih =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨a,w⟩ := e
    refine ⟨k + pack width p l, ?_⟩
    have h : 2^width = (2^width-1) + 1 := by have := Nat.two_pow_pos width; omega
    simp only [pack, mass, Nat.add_mul]
    conv_lhs => lhs; lhs; rw [h]
    simp only [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm (2^width-1)]
    omega

theorem eval (width : ℕ) (p : α → Bool) (l : List (α × ℕ))
    (h : mass (fun _ => true) l < 2^width-1) :
    pack width p l % (2^width-1) = mass p l := by
  obtain ⟨k,hk⟩ := mod_pack width p l
  rw [hk, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ((mono p l).trans_lt h)]

private theorem digit_lt {width w : ℕ} (hw : w < 2^width) (b : Bool) :
    (if b then w else 0) < 2^width := by cases b <;> simp [hw]

theorem pack_and (width : ℕ) (p q : α → Bool) (l : List (α × ℕ))
    (h : ∀ e ∈ l, e.2 < 2^width) :
    pack width (fun a => p a && q a) l = pack width p l &&& pack width q l := by
  induction l with
  | nil => simp [pack]
  | cons e l ih =>
    obtain ⟨a,w⟩ := e
    have hw := h (a,w) List.mem_cons_self
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [pack, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (digit_lt hw _)]
    by_cases hj : j < width
    · simp only [if_pos hj]; cases p a <;> cases q a <;> simp
    · simp [hj, ht, Nat.testBit_and]

theorem pack_or (width : ℕ) (p q : α → Bool) (l : List (α × ℕ))
    (h : ∀ e ∈ l, e.2 < 2^width) :
    pack width (fun a => p a || q a) l = pack width p l ||| pack width q l := by
  induction l with
  | nil => simp [pack]
  | cons e l ih =>
    obtain ⟨a,w⟩ := e
    have hw := h (a,w) List.mem_cons_self
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [pack, Nat.testBit_or, Nat.testBit_two_pow_mul_add _ (digit_lt hw _)]
    by_cases hj : j < width
    · simp only [if_pos hj]; cases p a <;> cases q a <;> simp
    · simp [hj, ht, Nat.testBit_or]

open Finset

def assign [DecidableEq α] (l : List (α × ℕ)) (t : α) := mass (fun s => s == t) l

theorem sum_assign [DecidableEq α] (l : List (α × ℕ)) (T : Finset α) :
    ∑ t ∈ T, assign l t = mass (fun t => decide (t ∈ T)) l := by
  induction l with
  | nil => simp [assign, mass]
  | cons e l ih =>
    obtain ⟨a,w⟩ := e
    simp only [assign, mass, sum_add_distrib, beq_iff_eq]
    change (∑ t ∈ T, if a = t then w else 0) + (∑ t ∈ T, assign l t) = _
    rw [ih]
    simp

private theorem mass_congr {p q : α → Bool} (l : List (α × ℕ)) (h : ∀ e ∈ l, p e.1 = q e.1) :
    mass p l = mass q l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a,w⟩ := e
    simp only [mass, h _ List.mem_cons_self, ih (fun e he => h e (List.mem_cons_of_mem _ he))]

/-- A mask represents a predicate on the support of the weight certificate. -/
def Represents (width : ℕ) (l : List (α × ℕ)) (p : α → Prop) (v : ℕ) : Prop :=
  ∃ f : α → Bool, pack width f l = v ∧ ∀ e ∈ l, f e.1 = true ↔ p e.1

namespace Represents

variable {width : ℕ} {l : List (α × ℕ)} {p q : α → Prop} {a b : ℕ}

theorem and (hp : Represents width l p a) (hq : Represents width l q b)
    (hd : ∀ e ∈ l, e.2 < 2^width) : Represents width l (fun x => p x ∧ q x) (a &&& b) := by
  obtain ⟨f,rfl,hf⟩ := hp
  obtain ⟨g,rfl,hg⟩ := hq
  exact ⟨_, pack_and width f g l hd, fun e he => by simp [hf e he, hg e he]⟩

theorem or (hp : Represents width l p a) (hq : Represents width l q b)
    (hd : ∀ e ∈ l, e.2 < 2^width) : Represents width l (fun x => p x ∨ q x) (a ||| b) := by
  obtain ⟨f,rfl,hf⟩ := hp
  obtain ⟨g,rfl,hg⟩ := hq
  exact ⟨_, pack_or width f g l hd, fun e he => by simp [hf e he, hg e he]⟩

theorem congr (hp : Represents width l p a) (h : ∀ e ∈ l, p e.1 ↔ q e.1) :
    Represents width l q a := by
  obtain ⟨f,he,hf⟩ := hp
  exact ⟨f,he,fun e he => (hf e he).trans (h e he)⟩

theorem weight_filter [DecidableEq α] (T : Finset α) [DecidablePred p]
    (hT : ∀ e ∈ l, e.1 ∈ T) (h : Represents width l p a)
    (ht : mass (fun _ => true) l < 2^width-1) :
    (∑ t ∈ T.filter p, assign l t) = a % (2^width-1) := by
  obtain ⟨f,rfl,hf⟩ := h
  rw [sum_assign, eval _ _ _ ht]
  apply mass_congr
  intro e he
  apply Bool.eq_iff_iff.mpr
  simp [hT e he, hf e he]

end Represents

end StableKneserK3.PackedWeights
