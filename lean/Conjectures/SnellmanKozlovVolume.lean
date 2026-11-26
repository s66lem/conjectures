import Mathlib

/-!
# Proof of Snellman's Normalized-Volume Monotonicity Conjecture for Rank-Two Kozlov Polytopes

This module proves the sole conjecture (`conj-nv-monotone`) in Jan Snellman,
*Hilbert functions over the exterior algebra and f-vectors in higher rank III:
Lattice points of the Kozlov polytope*, arXiv:2611.26110v1 (19 Nov 2026).

## Statement

Let `NV(Koz(n; 0, d))` be the normalized volume of the rank-two Kozlov polytope.
By Snellman's Corollary `cor-rank2-volume` (for `0 ≤ d ≤ n - 1`) and Proposition
`prop-product-regime` (constancy for `d ≥ n - 1`),
`NV(Koz(n; 0, d)) = nvKoz n * rank2Sum n (min d (n - 1))`, where
`nvKoz n = ∏ k ∈ Icc 2 n, C(n, k)` and
`rank2Sum n d = ∑ j ∈ Icc 1 (n - d), C(n - 1 + d, d + j - 1) * ∏ k ∈ Icc (j + 1) (j + d), C(n, k)`.

## Main Theorems

* `rank2Sum_step_lower_bound`: for `2 ≤ n` and `d + 2 ≤ n`,
  `rank2Sum n d + (Nat.choose n d - 1) * cellFactor n d (n - d) ≤ rank2Sum n (d + 1)`.
* `snellman_conjecture_monotone`: for every `n ≥ 1`, `Monotone (nvRank2 n)`.
* `snellman_strict_increase`: for `2 ≤ n`, `d + 2 ≤ n`, and `(n, d) ≠ (2, 0)`,
  `nvRank2 n d < nvRank2 n (d + 1)`.
* `snellman_equality_n2_d0`: `nvRank2 2 0 = 2 ∧ nvRank2 2 1 = 2`.
* `rank2Sum_zero` and `nvRank2_product_regime`: exact boundary identities at `d = 0`
  and `d ≥ n - 1`.
-/

namespace SnellmanKozlovVolume

open Finset

/-- Normalized volume `NV(Koz(n)) = ∏_{k=2}^n C(n, k)` of the rank-one Kozlov polytope. -/
def nvKoz (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 n, Nat.choose n k

/-- Cell factor `t_d(j) = C(n - 1 + d, d + j - 1) * ∏_{k=j+1}^{j+d} C(n, k)` in
Snellman's Corollary `cor-rank2-volume`. -/
def cellFactor (n d j : ℕ) : ℕ :=
  Nat.choose (n - 1 + d) (d + j - 1) * ∏ k ∈ Finset.Icc (j + 1) (j + d), Nat.choose n k

/-- Sum of cell factors `T(n, d) = ∑_{j=1}^{n-d} t_d(j)` for `0 ≤ d ≤ n - 1`. -/
def rank2Sum (n d : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (n - d), cellFactor n d j

/-- Normalized volume `NV(Koz(n; 0, d))` from Corollary `cor-rank2-volume` (`0 ≤ d ≤ n - 1`)
and Proposition `prop-product-regime` (constant for `d ≥ n - 1`). -/
def nvRank2 (n d : ℕ) : ℕ :=
  nvKoz n * rank2Sum n (min d (n - 1))

lemma nvKoz_pos (n : ℕ) : 0 < nvKoz n := by
  unfold nvKoz
  apply Finset.prod_pos
  intro k hk
  exact Nat.choose_pos (Finset.mem_Icc.mp hk).2

lemma cellFactor_pos {n d j : ℕ} (hj1 : 1 ≤ j) (hjd : j + d ≤ n) :
    0 < cellFactor n d j := by
  unfold cellFactor
  apply Nat.mul_pos
  · exact Nat.choose_pos (by omega)
  · apply Finset.prod_pos
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).2
    exact Nat.choose_pos (by omega)

/-- Step 1 (cleared-denominator ratio identity): for `1 ≤ j` and `j + d + 1 ≤ n`,
`(d + j) * t_{d+1}(j) = (n + d) * C(n, j + d + 1) * t_d(j)`. -/
lemma cellFactor_step_mul {n d j : ℕ} (hj1 : 1 ≤ j) (hjd : j + d + 1 ≤ n) :
    (d + j) * cellFactor n (d + 1) j =
      (n + d) * Nat.choose n (j + d + 1) * cellFactor n d j := by
  unfold cellFactor
  have hbinom : (d + j) * Nat.choose (n - 1 + (d + 1)) (d + 1 + j - 1) =
      (n + d) * Nat.choose (n - 1 + d) (d + j - 1) := by
    set m := n - 1 + d
    set k := d + j - 1
    have h1 : n - 1 + (d + 1) = m + 1 := by omega
    have h2 : d + 1 + j - 1 = k + 1 := by omega
    have h3 : k + 1 = d + j := by omega
    have h4 : m + 1 = n + d := by omega
    rw [h1, h2, ← h3, ← h4]
    have hf1 := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ m)
    have hf2 := Nat.choose_mul_factorial_mul_factorial (by omega : k + 1 ≤ m + 1)
    have hsub : m + 1 - (k + 1) = m - k := by omega
    rw [hsub, Nat.factorial_succ m, Nat.factorial_succ k] at hf2
    have hpos : 0 < k.factorial * (m - k).factorial :=
      Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (m - k))
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (k + 1) * (m + 1).choose (k + 1) * (k.factorial * (m - k).factorial)
        = (m + 1).choose (k + 1) * ((k + 1) * k.factorial) * (m - k).factorial := by ring
      _ = (m + 1) * m.factorial := hf2
      _ = (m + 1) * (m.choose k * k.factorial * (m - k).factorial) := by rw [hf1]
      _ = (m + 1) * m.choose k * (k.factorial * (m - k).factorial) := by ring
  have hprod : ∏ k ∈ Finset.Icc (j + 1) (j + (d + 1)), Nat.choose n k =
      Nat.choose n (j + d + 1) * ∏ k ∈ Finset.Icc (j + 1) (j + d), Nat.choose n k := by
    rw [show j + (d + 1) = (j + d) + 1 by omega,
      Finset.prod_Icc_succ_top (by omega : j + 1 ≤ j + d + 1), mul_comm]
  rw [hprod]
  calc (d + j) * (Nat.choose (n - 1 + (d + 1)) (d + 1 + j - 1) *
          (Nat.choose n (j + d + 1) * ∏ k ∈ Finset.Icc (j + 1) (j + d), Nat.choose n k))
      = ((d + j) * Nat.choose (n - 1 + (d + 1)) (d + 1 + j - 1)) *
          (Nat.choose n (j + d + 1) * ∏ k ∈ Finset.Icc (j + 1) (j + d), Nat.choose n k) := by ring
    _ = ((n + d) * Nat.choose (n - 1 + d) (d + j - 1)) *
          (Nat.choose n (j + d + 1) * ∏ k ∈ Finset.Icc (j + 1) (j + d), Nat.choose n k) := by
        rw [hbinom]
    _ = (n + d) * Nat.choose n (j + d + 1) *
          (Nat.choose (n - 1 + d) (d + j - 1) * ∏ k ∈ Finset.Icc (j + 1) (j + d), Nat.choose n k) := by
        ring

/-- Every surviving cell `1 ≤ j ≤ n - d - 1` satisfies `t_d(j) ≤ t_{d+1}(j)`. -/
lemma cellFactor_le_succ {n d j : ℕ} (hj1 : 1 ≤ j) (hjd : j + d + 1 ≤ n) :
    cellFactor n d j ≤ cellFactor n (d + 1) j := by
  have hmul := cellFactor_step_mul hj1 hjd
  have hch : 1 ≤ Nat.choose n (j + d + 1) := Nat.choose_pos hjd
  have hcoef : d + j ≤ (n + d) * Nat.choose n (j + d + 1) := by nlinarith
  have hle : (d + j) * cellFactor n d j ≤ (d + j) * cellFactor n (d + 1) j := by
    rw [hmul]
    exact Nat.mul_le_mul_right _ hcoef
  exact Nat.le_of_mul_le_mul_left hle (by omega)

/-- Strict termwise increase when `j < n - d` and `d = 0`, or more generally when `j + d + 1 < n`. -/
lemma cellFactor_lt_succ_of_lt {n d j : ℕ} (hj1 : 1 ≤ j) (hjd : j + d + 1 < n) :
    cellFactor n d j < cellFactor n (d + 1) j := by
  have hmul := cellFactor_step_mul (n := n) (d := d) (j := j) hj1 (by omega)
  have hch : 1 ≤ Nat.choose n (j + d + 1) := Nat.choose_pos (by omega)
  have hcoef : d + j < (n + d) * Nat.choose n (j + d + 1) := by nlinarith
  have hpos : 0 < cellFactor n d j := cellFactor_pos hj1 (by omega)
  have hlt : (d + j) * cellFactor n d j < (d + j) * cellFactor n (d + 1) j := by
    rw [hmul]
    exact Nat.mul_lt_mul_of_pos_right hcoef hpos
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- Step 3 (exact last-cell gain identity): for `2 ≤ n` and `d + 2 ≤ n`, the gain of the
last surviving cell `j = n - d - 1` equals `C(n, d)` times the dropped cell `j = n - d`. -/
lemma lastCell_gain_identity {n d : ℕ} (hn : 2 ≤ n) (hd : d + 2 ≤ n) :
    cellFactor n (d + 1) (n - d - 1) =
      cellFactor n d (n - d - 1) + Nat.choose n d * cellFactor n d (n - d) := by
  have hstep := cellFactor_step_mul (n := n) (d := d) (j := n - d - 1) (by omega) (by omega)
  have hdj : d + (n - d - 1) = n - 1 := by omega
  have hjdn : n - d - 1 + d + 1 = n := by omega
  rw [hdj, hjdn, Nat.choose_self, mul_one] at hstep
  -- Compare `t_d(n - d - 1)` and `t_d(n - d)`
  have hrel : (d + 1) * cellFactor n d (n - d - 1) =
      (n - 1) * Nat.choose n d * cellFactor n d (n - d) := by
    unfold cellFactor
    have hbi : (d + 1) * Nat.choose (n - 1 + d) (d + (n - d - 1) - 1) =
        (n - 1) * Nat.choose (n - 1 + d) (d + (n - d) - 1) := by
      have ha : d + (n - d - 1) - 1 = n - 2 := by omega
      have hb : d + (n - d) - 1 = n - 1 := by omega
      rw [ha, hb]
      have h := Nat.choose_succ_right_eq (n - 1 + d) (n - 2)
      have h1 : n - 2 + 1 = n - 1 := by omega
      have h2 : n - 1 + d - (n - 2) = d + 1 := by omega
      rw [h1, h2] at h
      linarith
    have hpr : ∏ k ∈ Finset.Icc (n - d - 1 + 1) (n - d - 1 + d), Nat.choose n k =
        Nat.choose n d * ∏ k ∈ Finset.Icc (n - d + 1) (n - d + d), Nat.choose n k := by
      have ha : n - d - 1 + 1 = n - d := by omega
      have hb : n - d - 1 + d = n - 1 := by omega
      have hc : n - d + d = n := by omega
      rw [ha, hb, hc]
      by_cases hd0 : d = 0
      · subst hd0
        have hI1 : Finset.Icc (n - 0) (n - 1) = ∅ := Finset.Icc_eq_empty (by omega)
        have hI2 : Finset.Icc (n - 0 + 1) n = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hI1, hI2]
        simp
      · have hle1 : n - d ≤ n - 1 := by omega
        have hle2 : n - d + 1 ≤ n := by omega
        have hsplit1 : Finset.Icc (n - d) (n - 1) =
            insert (n - d) (Finset.Icc (n - d + 1) (n - 1)) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot1 : n - d ∉ Finset.Icc (n - d + 1) (n - 1) := by simp
        have hsplit2 : Finset.Icc (n - d + 1) n =
            insert n (Finset.Icc (n - d + 1) (n - 1)) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot2 : n ∉ Finset.Icc (n - d + 1) (n - 1) := by
          simp only [Finset.mem_Icc]; omega
        rw [hsplit1, Finset.prod_insert hnot1, hsplit2, Finset.prod_insert hnot2,
          Nat.choose_self, one_mul, Nat.choose_symm (by omega : d ≤ n)]
    calc (d + 1) * (Nat.choose (n - 1 + d) (d + (n - d - 1) - 1) *
            ∏ k ∈ Finset.Icc (n - d - 1 + 1) (n - d - 1 + d), Nat.choose n k)
        = ((d + 1) * Nat.choose (n - 1 + d) (d + (n - d - 1) - 1)) *
            ∏ k ∈ Finset.Icc (n - d - 1 + 1) (n - d - 1 + d), Nat.choose n k := by ring
      _ = ((n - 1) * Nat.choose (n - 1 + d) (d + (n - d) - 1)) *
            (Nat.choose n d * ∏ k ∈ Finset.Icc (n - d + 1) (n - d + d), Nat.choose n k) := by
          rw [hbi, hpr]
      _ = (n - 1) * Nat.choose n d *
            (Nat.choose (n - 1 + d) (d + (n - d) - 1) *
              ∏ k ∈ Finset.Icc (n - d + 1) (n - d + d), Nat.choose n k) := by ring
  have hcomb : (n - 1) * cellFactor n (d + 1) (n - d - 1) =
      (n - 1) * (cellFactor n d (n - d - 1) + Nat.choose n d * cellFactor n d (n - d)) := by
    have hnd : n + d = (n - 1) + (d + 1) := by omega
    calc (n - 1) * cellFactor n (d + 1) (n - d - 1)
        = (n + d) * cellFactor n d (n - d - 1) := hstep
      _ = (n - 1) * cellFactor n d (n - d - 1) + (d + 1) * cellFactor n d (n - d - 1) := by
          rw [hnd, add_mul]
      _ = (n - 1) * cellFactor n d (n - d - 1) +
            (n - 1) * Nat.choose n d * cellFactor n d (n - d) := by rw [hrel]
      _ = (n - 1) * (cellFactor n d (n - d - 1) + Nat.choose n d * cellFactor n d (n - d)) := by
          ring
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < n - 1) hcomb

/-- Exact decomposition of `rank2Sum n (d + 1)` vs `rank2Sum n d` with explicit quantitative surplus. -/
theorem rank2Sum_step_lower_bound {n d : ℕ} (hn : 2 ≤ n) (hd : d + 2 ≤ n) :
    rank2Sum n d + (Nat.choose n d - 1) * cellFactor n d (n - d) ≤ rank2Sum n (d + 1) := by
  unfold rank2Sum
  have hsplit_d : Finset.Icc 1 (n - d) =
      insert (n - d) (insert (n - d - 1) (Finset.Icc 1 (n - d - 2))) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hsplit_d1 : Finset.Icc 1 (n - (d + 1)) =
      insert (n - d - 1) (Finset.Icc 1 (n - d - 2)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot_nd : n - d ∉ insert (n - d - 1) (Finset.Icc 1 (n - d - 2)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hnot_nd1 : n - d - 1 ∉ Finset.Icc 1 (n - d - 2) := by
    simp only [Finset.mem_Icc]; omega
  rw [hsplit_d, Finset.sum_insert hnot_nd, Finset.sum_insert hnot_nd1,
    hsplit_d1, Finset.sum_insert hnot_nd1, lastCell_gain_identity hn hd]
  have hsum_le : ∑ j ∈ Finset.Icc 1 (n - d - 2), cellFactor n d j ≤
      ∑ j ∈ Finset.Icc 1 (n - d - 2), cellFactor n (d + 1) j := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact cellFactor_le_succ hj'.1 (by omega)
  have hch_pos : 1 ≤ Nat.choose n d := Nat.choose_pos (by omega)
  have hmul_eq : cellFactor n d (n - d) + (Nat.choose n d - 1) * cellFactor n d (n - d) =
      Nat.choose n d * cellFactor n d (n - d) := by
    calc cellFactor n d (n - d) + (Nat.choose n d - 1) * cellFactor n d (n - d)
        = (1 + (Nat.choose n d - 1)) * cellFactor n d (n - d) := by ring
      _ = Nat.choose n d * cellFactor n d (n - d) := by rw [show 1 + (Nat.choose n d - 1) = Nat.choose n d by omega]
  linarith

/-- Strict monotonicity of `rank2Sum n` on `0 ≤ d ≤ n - 2` except at `(n, d) = (2, 0)`. -/
theorem rank2Sum_strict_step {n d : ℕ} (hn : 2 ≤ n) (hd : d + 2 ≤ n)
    (hne : ¬ (n = 2 ∧ d = 0)) :
    rank2Sum n d < rank2Sum n (d + 1) := by
  by_cases hd0 : d = 0
  · subst hd0
    have hn3 : 3 ≤ n := by omega
    unfold rank2Sum
    have hsplit_0 : Finset.Icc 1 (n - 0) =
        insert n (insert (n - 1) (Finset.Icc 1 (n - 2))) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsplit_1 : Finset.Icc 1 (n - 1) =
        insert (n - 1) (Finset.Icc 1 (n - 2)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_n : n ∉ insert (n - 1) (Finset.Icc 1 (n - 2)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot_n1 : n - 1 ∉ Finset.Icc 1 (n - 2) := by
      simp only [Finset.mem_Icc]; omega
    have hlast := lastCell_gain_identity (n := n) (d := 0) hn (by omega)
    simp only [Nat.sub_zero, Nat.choose_zero_right, one_mul] at hlast
    rw [hsplit_0, Finset.sum_insert hnot_n, Finset.sum_insert hnot_n1,
      hsplit_1, Finset.sum_insert hnot_n1, hlast]
    have hsum_lt : ∑ j ∈ Finset.Icc 1 (n - 2), cellFactor n 0 j <
        ∑ j ∈ Finset.Icc 1 (n - 2), cellFactor n 1 j := by
      apply Finset.sum_lt_sum
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        exact cellFactor_le_succ hj'.1 (by omega)
      · refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, ?_⟩
        exact cellFactor_lt_succ_of_lt (le_refl 1) (by omega)
    linarith
  · have hlb := rank2Sum_step_lower_bound hn hd
    have hd1 : 1 ≤ d := by omega
    have hch_ge2 : 2 ≤ Nat.choose n d := by
      have hpascal : Nat.choose n d = Nat.choose (n - 1) (d - 1) + Nat.choose (n - 1) d := by
        have h := Nat.choose_succ_succ (n - 1) (d - 1)
        simp only [Nat.succ_eq_add_one] at h
        rw [show n - 1 + 1 = n by omega, show d - 1 + 1 = d by omega] at h
        exact h
      have ha : 1 ≤ Nat.choose (n - 1) (d - 1) := Nat.choose_pos (by omega)
      have hb : 1 ≤ Nat.choose (n - 1) d := Nat.choose_pos (by omega)
      omega
    have hpos : 0 < cellFactor n d (n - d) := cellFactor_pos (by omega) (by omega)
    have hsurp : 0 < (Nat.choose n d - 1) * cellFactor n d (n - d) :=
      Nat.mul_pos (by omega) hpos
    omega

/-- Complete proof of Snellman's Conjecture (`conj-nv-monotone`, arXiv:2611.26110v1):
for every `n ≥ 1`, `NV(Koz(n; 0, d))` is weakly increasing in `d ≥ 0`. -/
theorem snellman_conjecture_monotone (n : ℕ) (hn : 1 ≤ n) :
    Monotone (nvRank2 n) := by
  apply monotone_nat_of_le_succ
  intro d
  unfold nvRank2
  apply Nat.mul_le_mul_left
  by_cases hd : d + 2 ≤ n
  · have hmin1 : min d (n - 1) = d := by omega
    have hmin2 : min (d + 1) (n - 1) = d + 1 := by omega
    rw [hmin1, hmin2]
    have hlb := rank2Sum_step_lower_bound (n := n) (d := d) (by omega) hd
    omega
  · have hmin : min d (n - 1) = min (d + 1) (n - 1) := by omega
    rw [hmin]

/-- Sharper strictness theorem: `NV(Koz(n; 0, d)) < NV(Koz(n; 0, d + 1))` for every
`n ≥ 2` and `0 ≤ d ≤ n - 2`, except the unique equality `(n, d) = (2, 0)`. -/
theorem snellman_strict_increase (n d : ℕ) (hn : 2 ≤ n) (hd : d + 2 ≤ n)
    (hne : ¬ (n = 2 ∧ d = 0)) :
    nvRank2 n d < nvRank2 n (d + 1) := by
  unfold nvRank2
  have hmin1 : min d (n - 1) = d := by omega
  have hmin2 : min (d + 1) (n - 1) = d + 1 := by omega
  rw [hmin1, hmin2]
  exact Nat.mul_lt_mul_of_pos_left (rank2Sum_strict_step hn hd hne) (nvKoz_pos n)

/-- Unique equality case inside `0 ≤ d ≤ n - 2`: `NV(Koz(2; 0, 0)) = NV(Koz(2; 0, 1)) = 2`. -/
theorem snellman_equality_n2_d0 :
    nvRank2 2 0 = 2 ∧ nvRank2 2 1 = 2 := by
  decide

/-- Boundary identity at `d = 0`: `T(n, 0) = 2^(n - 1)` for every `n ≥ 1`. -/
theorem rank2Sum_zero (n : ℕ) (hn : 1 ≤ n) :
    rank2Sum n 0 = 2 ^ (n - 1) := by
  unfold rank2Sum
  have hsimp : ∑ j ∈ Finset.Icc 1 (n - 0), cellFactor n 0 j =
      ∑ j ∈ Finset.Icc 1 n, Nat.choose (n - 1) (j - 1) := by
    rw [Nat.sub_zero]
    apply Finset.sum_congr rfl
    intro j _
    unfold cellFactor
    rw [Nat.add_zero, zero_add, Nat.add_zero, Finset.Icc_eq_empty (by omega),
      Finset.prod_empty, mul_one]
  rw [hsimp, ← Nat.sum_range_choose (n - 1)]
  apply Finset.sum_nbij (fun j => j - 1)
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    rw [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
    dsimp only at h
    omega
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    exact ⟨k + 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by simp⟩
  · intro _ _; rfl

/-- Boundary identity in the product regime `d ≥ n - 1`:
`NV(Koz(n; 0, d)) = C(2n - 2, n - 1) * NV(Koz(n))^2`. -/
theorem nvRank2_product_regime (n d : ℕ) (hn : 1 ≤ n) (hd : n - 1 ≤ d) :
    nvRank2 n d = Nat.choose (2 * n - 2) (n - 1) * (nvKoz n) ^ 2 := by
  unfold nvRank2
  rw [min_eq_right hd]
  unfold rank2Sum cellFactor
  have hsub : n - (n - 1) = 1 := by omega
  rw [hsub, Finset.Icc_self, Finset.sum_singleton]
  have h2 : n - 1 + (n - 1) = 2 * n - 2 := by omega
  have h1 : n - 1 + 1 - 1 = n - 1 := by omega
  have h3 : 1 + (n - 1) = n := by omega
  rw [h2, h1, h3]
  change nvKoz n * (Nat.choose (2 * n - 2) (n - 1) * nvKoz n) = _
  ring

end SnellmanKozlovVolume
