import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith

namespace StableKneserK3.DigitSum

open Finset

def digit (base j u : ℕ) := u / base^j % base

private theorem remainder_lt {B j u M : ℕ} (hB : 0 < B) (hu : digit B j u ≤ M) :
    u % B^(j+1) < (M+1)*B^j := by
  have hp : 0 < B^j := Nat.pow_pos hB
  rw [Nat.pow_succ, Nat.mod_mul]
  have hr := Nat.mod_lt u hp
  have hb := Nat.mul_le_mul_right (B^j) hu
  change u / B^j % B * B^j ≤ M * B^j at hb
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (B^j) (u / B^j % B)]
  omega

/-- Digit extraction commutes with summation when even a full column cannot carry. -/
theorem digit_sum {α : Type*} (s : Finset α) (f : α → ℕ) {B M D : ℕ}
    (hB : 0 < B) (hd : ∀ i ∈ s, ∀ j < D, digit B j (f i) ≤ M)
    (hs : s.card*(M+1) ≤ B) {j : ℕ} (hj : j < D) :
    digit B j (∑ i ∈ s, f i) = ∑ i ∈ s, digit B j (f i) := by
  have hp : 0 < B^j := Nat.pow_pos hB
  have hrem : ∑ i ∈ s, f i % B^j < B^j := by
    cases j with
    | zero => simp [Nat.mod_one]
    | succ t =>
      by_cases he : s.Nonempty
      · calc
          _ < ∑ _i ∈ s, (M+1)*B^t := Finset.sum_lt_sum_of_nonempty he
            (fun i hi => remainder_lt hB (hd i hi t (by omega)))
          _ = (s.card*(M+1))*B^t := by simp [Nat.mul_assoc]
          _ ≤ B^(t+1) := by simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (B^t) hs
      · simp [Finset.not_nonempty_iff_eq_empty.mp he, Nat.pow_pos hB]
  have htot : (∑ i ∈ s, f i) = (∑ i ∈ s, f i % B^j) + B^j*(∑ i ∈ s, f i / B^j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact sum_congr rfl (fun i _ => (Nat.mod_add_div _ _).symm)
  have hdiv : (∑ i ∈ s, f i) / B^j = ∑ i ∈ s, f i / B^j := by
    rw [htot, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hrem, Nat.zero_add]
  have hdigit : (∑ i ∈ s, digit B j (f i)) < B := by
    have h₁ : (∑ i ∈ s, digit B j (f i)) ≤ s.card*M := by
      simpa using Finset.sum_le_sum (fun i hi => hd i hi j hj)
    by_cases he : s.Nonempty
    · have := card_pos.mpr he
      rw [Nat.mul_add, Nat.mul_one] at hs
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp he, hB]
  unfold digit at *
  rw [hdiv, Finset.sum_nat_mod] 
  exact Nat.mod_eq_of_lt hdigit

theorem digit_le_of_mask {bits j x mask : ℕ} (h : x &&& mask = x) :
    digit (2^bits) j x ≤ digit (2^bits) j mask := by
  have eq := congrArg (digit (2^bits) j) h
  simp only [digit, ← Nat.pow_mul, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib,
    Nat.and_mod_two_pow] at eq ⊢
  exact eq ▸ Nat.and_le_right

end StableKneserK3.DigitSum
