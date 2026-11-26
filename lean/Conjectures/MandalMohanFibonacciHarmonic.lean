import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Mandal–Mohan Conjecture 1.19 (Harmonic-Type Means of Powers of Fibonacci Numbers)

Proves Conjecture 1.19 (and reproves Theorem 1.18) of
Sagar Mandal and Mohan, *Integral Means of Fibonacci Numbers: Divisibility, Density,
and Arithmetic Structure* (`arXiv:2611.32519v1`, 24 Nov 2026).

For positive integers `n, k ≥ 1`, let
  `H(n, k) = n^k / ∑_{i=1}^n F_i^{-k}`.
We prove that `H(n, k) ∈ ℕ` if and only if `n = 1`, `n = 2`, or `(n, k) = (3, 2)`.
In particular, for every `k ≥ 3`, `H(n, k) ∈ ℕ ↔ n = 1 ∨ n = 2`.

The proof is completely elementary and self-contained, using Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`) and the strong divisibility property
`Nat.fib_gcd` rather than Carmichael's primitive divisor theorem.
-/

namespace MandalMohanFibonacciHarmonic

/-- The reciprocal `k`-th power sum `∑_{i=1}^n F_i^{-k}` in `ℚ`. -/
def fibRecipSum (n k : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, ((Nat.fib i : ℚ) ^ k)⁻¹

/-- The Mandal–Mohan harmonic-type quotient `n^k / ∑_{i=1}^n F_i^{-k}` in `ℚ`. -/
def fibHarmonic (n k : ℕ) : ℚ :=
  (n : ℚ) ^ k / fibRecipSum n k

private lemma fibRecipSum_pos {n k : ℕ} (hn : 1 ≤ n) : 0 < fibRecipSum n k := by
  unfold fibRecipSum
  apply Finset.sum_pos
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hpos : (0 : ℚ) < (Nat.fib i : ℚ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    exact inv_pos.mpr (pow_pos hpos k)
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩

private lemma fib_ge_two_mul_sub_one : ∀ m : ℕ, 7 ≤ m → 2 * m - 1 ≤ Nat.fib m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    rcases (by omega : m = 7 ∨ m = 8 ∨ 9 ≤ m) with rfl | rfl | h9
    · decide
    · decide
    · obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
      have h1 := ih r (by omega) (by omega)
      have h2 := ih (r + 1) (by omega) (by omega)
      rw [Nat.fib_add_two]
      omega

private lemma coprime_fib_of_prime_gt_half {n q i : ℕ}
    (hq : q.Prime) (hgt : n < 2 * q) (hi1 : 1 ≤ i) (hin : i ≤ n) (hne : i ≠ q) :
    Nat.Coprime (Nat.fib q) (Nat.fib i) := by
  unfold Nat.Coprime
  rw [← Nat.fib_gcd]
  have hdvd : Nat.gcd q i ∣ q := Nat.gcd_dvd_left q i
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hqeq
  · rw [h1]; rfl
  · exfalso
    have hqi : q ∣ i := hqeq ▸ Nat.gcd_dvd_right q i
    rcases hqi with ⟨c, rfl⟩
    rcases (by omega : c = 0 ∨ c = 1 ∨ 2 ≤ c) with rfl | rfl | hc2
    · omega
    · exact hne (by ring)
    · have : 2 * q ≤ q * c := by nlinarith
      omega

private lemma no_int_of_isolated_fib {n k q : ℕ}
    (_hk : 1 ≤ k) (hq3 : 3 ≤ q) (hqn : q ≤ n)
    (hcop : ∀ i ∈ Finset.Icc 1 n, i ≠ q → Nat.Coprime (Nat.fib q) (Nat.fib i))
    (hge : n ≤ Nat.fib q) :
    ¬ ∃ m : ℕ, (m : ℚ) = fibHarmonic n k := by
  rintro ⟨m, hm⟩
  have hSpos : 0 < fibRecipSum n k := fibRecipSum_pos (by omega)
  have hSne : fibRecipSum n k ≠ 0 := ne_of_gt hSpos
  have hmulQ : (m : ℚ) * fibRecipSum n k = (n : ℚ) ^ k := by
    rw [hm, fibHarmonic, div_mul_cancel₀ _ hSne]
  let s := (Finset.Icc 1 n).erase q
  let P : ℕ := ∏ i ∈ s, Nat.fib i ^ k
  let Q : ℕ := ∑ i ∈ s, P / Nat.fib i ^ k
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    exact pow_pos (Nat.fib_pos.mpr (by omega)) k
  have hFqpos : 0 < Nat.fib q ^ k := pow_pos (Nat.fib_pos.mpr (by omega)) k
  have hS_clear : fibRecipSum n k * ((Nat.fib q ^ k * P : ℕ) : ℚ) =
      ((P + Nat.fib q ^ k * Q : ℕ) : ℚ) := by
    have hqmem : q ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, hqn⟩
    have hsplit : fibRecipSum n k =
        ((Nat.fib q : ℚ) ^ k)⁻¹ + ∑ i ∈ s, ((Nat.fib i : ℚ) ^ k)⁻¹ := by
      unfold fibRecipSum
      rw [← Finset.add_sum_erase _ _ hqmem]
    rw [hsplit, add_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    have h1 : ((Nat.fib q : ℚ) ^ k)⁻¹ * ((Nat.fib q : ℚ) ^ k * (P : ℚ)) = (P : ℚ) := by
      have hne : (Nat.fib q : ℚ) ^ k ≠ 0 := by exact_mod_cast ne_of_gt hFqpos
      field_simp [hne]
    have h2 : (∑ i ∈ s, ((Nat.fib i : ℚ) ^ k)⁻¹) * ((Nat.fib q : ℚ) ^ k * (P : ℚ)) =
        (Nat.fib q : ℚ) ^ k * (Q : ℚ) := by
      rw [show (∑ i ∈ s, ((Nat.fib i : ℚ) ^ k)⁻¹) * ((Nat.fib q : ℚ) ^ k * (P : ℚ)) =
          (Nat.fib q : ℚ) ^ k * ((∑ i ∈ s, ((Nat.fib i : ℚ) ^ k)⁻¹) * (P : ℚ)) by ring]
      congr 1
      rw [Finset.sum_mul]
      simp only [Q, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hdvd : Nat.fib i ^ k ∣ P := Finset.dvd_prod_of_mem (fun j => Nat.fib j ^ k) hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
      have hne : (Nat.fib i : ℚ) ^ k ≠ 0 := by
        exact_mod_cast ne_of_gt (pow_pos (Nat.fib_pos.mpr (by omega)) k)
      rw [Nat.cast_div hdvd (by exact_mod_cast hne), Nat.cast_pow]
      field_simp [hne]
    rw [h1, h2]
  have hnatQ : ((m * (P + Nat.fib q ^ k * Q) : ℕ) : ℚ) =
      ((n ^ k * (Nat.fib q ^ k * P) : ℕ) : ℚ) := by
    calc ((m * (P + Nat.fib q ^ k * Q) : ℕ) : ℚ)
        = (m : ℚ) * ((P + Nat.fib q ^ k * Q : ℕ) : ℚ) := by push_cast; ring
      _ = (m : ℚ) * (fibRecipSum n k * ((Nat.fib q ^ k * P : ℕ) : ℚ)) := by rw [hS_clear]
      _ = ((m : ℚ) * fibRecipSum n k) * ((Nat.fib q ^ k * P : ℕ) : ℚ) := by ring
      _ = (n : ℚ) ^ k * ((Nat.fib q ^ k * P : ℕ) : ℚ) := by rw [hmulQ]
      _ = ((n ^ k * (Nat.fib q ^ k * P) : ℕ) : ℚ) := by push_cast; ring
  have hnat : m * (P + Nat.fib q ^ k * Q) = n ^ k * (Nat.fib q ^ k * P) :=
    Nat.cast_injective hnatQ
  have hcopP : Nat.Coprime (Nat.fib q ^ k) P := by
    apply Nat.Coprime.prod_right
    intro i hi
    have hmem : i ∈ Finset.Icc 1 n := Finset.mem_of_mem_erase hi
    have hne : i ≠ q := Finset.ne_of_mem_erase hi
    exact (hcop i hmem hne).pow k k
  have hcopT : Nat.Coprime (P + Nat.fib q ^ k * Q) (Nat.fib q ^ k) := by
    have : Nat.Coprime (Nat.fib q ^ k) (P + Nat.fib q ^ k * Q) := by
      simpa [Nat.mul_comm] using (Nat.coprime_add_mul_right_right (Nat.fib q ^ k) P Q).mpr hcopP
    exact this.symm
  have hdvd1 : P + Nat.fib q ^ k * Q ∣ Nat.fib q ^ k * (n ^ k * P) :=
    ⟨m, by linarith⟩
  have hdvd2 : P + Nat.fib q ^ k * Q ∣ n ^ k * P :=
    hcopT.dvd_of_dvd_mul_left hdvd1
  have hnkP_pos : 0 < n ^ k * P := mul_pos (pow_pos (by omega) k) hPpos
  have hle : P + Nat.fib q ^ k * Q ≤ n ^ k * P := Nat.le_of_dvd hnkP_pos hdvd2
  have h1s : 1 ∈ s := Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have h2s : 2 ∈ s := Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hQge : 2 * P ≤ Q := by
    have hsub : ({1, 2} : Finset ℕ) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx2
      · exact h1s
      · rw [Finset.mem_singleton.mp hx2]; exact h2s
    have hsum_le : ∑ i ∈ ({1, 2} : Finset ℕ), P / Nat.fib i ^ k ≤ Q :=
      Finset.sum_le_sum_of_subset hsub
    have h12 : ∑ i ∈ ({1, 2} : Finset ℕ), P / Nat.fib i ^ k = 2 * P := by
      rw [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
      simp only [Nat.fib_one, Nat.fib_two, one_pow, Nat.div_one]
      omega
    omega
  have hpow : n ^ k ≤ Nat.fib q ^ k := Nat.pow_le_pow_left hge k
  nlinarith

private lemma case_n4 {k : ℕ} (hk : 1 ≤ k) :
    ¬ ∃ m : ℕ, (m : ℚ) = fibHarmonic 4 k := by
  rintro ⟨m, hm⟩
  have hSpos : 0 < fibRecipSum 4 k := fibRecipSum_pos (by omega)
  have hmulQ : (m : ℚ) * fibRecipSum 4 k = (4 : ℚ) ^ k := by
    rw [hm, fibHarmonic, div_mul_cancel₀ _ (ne_of_gt hSpos)]; norm_cast
  have hS : fibRecipSum 4 k =
      ((2 * 6 ^ k + 3 ^ k + 2 ^ k : ℕ) : ℚ) / ((6 ^ k : ℕ) : ℚ) := by
    unfold fibRecipSum
    have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
    rw [hIcc]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true,
      Finset.sum_singleton]
    have hf1 : Nat.fib 1 = 1 := rfl
    have hf2 : Nat.fib 2 = 1 := rfl
    have hf3 : Nat.fib 3 = 2 := rfl
    have hf4 : Nat.fib 4 = 3 := rfl
    rw [hf1, hf2, hf3, hf4]
    push_cast
    have h2 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
    have h3 : ((3 : ℚ) ^ k) ≠ 0 := by positivity
    have h6 : ((6 : ℚ) ^ k) ≠ 0 := by positivity
    have h6eq : (6 : ℚ) ^ k = (2 : ℚ) ^ k * (3 : ℚ) ^ k := by rw [← mul_pow]; norm_num
    field_simp [h2, h3, h6]
    rw [h6eq]; ring
  rw [hS] at hmulQ
  have h6ne : ((6 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hnatQ : ((m * (2 * 6 ^ k + 3 ^ k + 2 ^ k) : ℕ) : ℚ) = ((4 ^ k * 6 ^ k : ℕ) : ℚ) := by
    have := congrArg (· * ((6 ^ k : ℕ) : ℚ)) hmulQ
    rw [mul_assoc, div_mul_cancel₀ _ h6ne] at this
    push_cast at this ⊢; exact this
  have hnat : m * (2 * 6 ^ k + 3 ^ k + 2 ^ k) = 4 ^ k * 6 ^ k := Nat.cast_injective hnatQ
  set U := 2 * 6 ^ k + 3 ^ k + 2 ^ k
  have hU_gt : 1 < U := by
    have h1 : 1 ≤ 6 ^ k := Nat.one_le_pow k 6 (by omega)
    have h2 : 2 * 6 ^ k ≤ U := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    omega
  have h2_ndvd : ¬ (2 ∣ U) := by
    intro h
    have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    have h6k : 2 ∣ 2 * 6 ^ k := dvd_mul_right 2 _
    have h3k : 2 ∣ 3 ^ k := by
      have : 2 ∣ 2 * 6 ^ k + 2 ^ k := dvd_add h6k h2k
      have hUeq : U = (2 * 6 ^ k + 2 ^ k) + 3 ^ k := by omega
      rw [hUeq] at h
      exact (Nat.dvd_add_right this).mp h
    have h23 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h3k
    omega
  have h3_ndvd : ¬ (3 ∣ U) := by
    intro h
    have h3k : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have h6k : 3 ∣ 2 * 6 ^ k := dvd_mul_of_dvd_right (dvd_pow (by decide : 3 ∣ 6) (by omega)) 2
    have h2k : 3 ∣ 2 ^ k := by
      have : 3 ∣ 2 * 6 ^ k + 3 ^ k := dvd_add h6k h3k
      exact (Nat.dvd_add_right this).mp h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2k
    omega
  have hcop2 : Nat.Coprime U 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2_ndvd).symm
  have hcop3 : Nat.Coprime U 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3_ndvd).symm
  have hcop4 : Nat.Coprime U (4 ^ k) := by
    rw [show (4 : ℕ) = 2 * 2 by rfl]
    exact (hcop2.mul_right hcop2).pow_right k
  have hcop6 : Nat.Coprime U (6 ^ k) := by
    rw [show (6 : ℕ) = 2 * 3 by rfl]
    exact (hcop2.mul_right hcop3).pow_right k
  have hcop_all : Nat.Coprime U (4 ^ k * 6 ^ k) := hcop4.mul_right hcop6
  have hdvd : U ∣ 4 ^ k * 6 ^ k := ⟨m, by linarith⟩
  have hU1 : U ∣ 1 := by
    have := hcop_all.dvd_of_dvd_mul_right (show U ∣ 1 * (4 ^ k * 6 ^ k) by simpa using hdvd)
    exact this
  have := Nat.le_of_dvd (by omega) hU1
  omega

private lemma case_n6 {k : ℕ} (hk : 1 ≤ k) :
    ¬ ∃ m : ℕ, (m : ℚ) = fibHarmonic 6 k := by
  rintro ⟨m, hm⟩
  have hSpos : 0 < fibRecipSum 6 k := fibRecipSum_pos (by omega)
  have hmulQ : (m : ℚ) * fibRecipSum 6 k = (6 : ℚ) ^ k := by
    rw [hm, fibHarmonic, div_mul_cancel₀ _ (ne_of_gt hSpos)]; norm_cast
  have hS : fibRecipSum 6 k =
      ((2 * 120 ^ k + 60 ^ k + 40 ^ k + 24 ^ k + 15 ^ k : ℕ) : ℚ) / ((120 ^ k : ℕ) : ℚ) := by
    unfold fibRecipSum
    have hIcc : Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by decide
    rw [hIcc]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true,
      Finset.sum_singleton]
    have hf1 : Nat.fib 1 = 1 := rfl
    have hf2 : Nat.fib 2 = 1 := rfl
    have hf3 : Nat.fib 3 = 2 := rfl
    have hf4 : Nat.fib 4 = 3 := rfl
    have hf5 : Nat.fib 5 = 5 := rfl
    have hf6 : Nat.fib 6 = 8 := rfl
    rw [hf1, hf2, hf3, hf4, hf5, hf6]
    push_cast
    simp only [one_pow, inv_one]
    have h2 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
    have h3 : ((3 : ℚ) ^ k) ≠ 0 := by positivity
    have h5 : ((5 : ℚ) ^ k) ≠ 0 := by positivity
    have h8 : ((8 : ℚ) ^ k) ≠ 0 := by positivity
    have h120 : ((120 : ℚ) ^ k) ≠ 0 := by positivity
    have h60 : (60 : ℚ) ^ k * (2 : ℚ) ^ k = (120 : ℚ) ^ k := by rw [← mul_pow]; norm_num
    have h40 : (40 : ℚ) ^ k * (3 : ℚ) ^ k = (120 : ℚ) ^ k := by rw [← mul_pow]; norm_num
    have h24 : (24 : ℚ) ^ k * (5 : ℚ) ^ k = (120 : ℚ) ^ k := by rw [← mul_pow]; norm_num
    have h15 : (15 : ℚ) ^ k * (8 : ℚ) ^ k = (120 : ℚ) ^ k := by rw [← mul_pow]; norm_num
    rw [eq_div_iff h120]
    have hassoc : (1 + (1 + (((2 : ℚ) ^ k)⁻¹ + (((3 : ℚ) ^ k)⁻¹ + (((5 : ℚ) ^ k)⁻¹ + ((8 : ℚ) ^ k)⁻¹))))) * (120 : ℚ) ^ k =
        2 * (120 : ℚ) ^ k + ((2 : ℚ) ^ k)⁻¹ * ((60 : ℚ) ^ k * (2 : ℚ) ^ k) +
        ((3 : ℚ) ^ k)⁻¹ * ((40 : ℚ) ^ k * (3 : ℚ) ^ k) +
        ((5 : ℚ) ^ k)⁻¹ * ((24 : ℚ) ^ k * (5 : ℚ) ^ k) +
        ((8 : ℚ) ^ k)⁻¹ * ((15 : ℚ) ^ k * (8 : ℚ) ^ k) := by
      rw [h60, h40, h24, h15]; ring
    rw [hassoc]
    field_simp [h2, h3, h5, h8]
  rw [hS] at hmulQ
  have h120ne : ((120 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hnatQ : ((m * (2 * 120 ^ k + 60 ^ k + 40 ^ k + 24 ^ k + 15 ^ k) : ℕ) : ℚ) =
      ((6 ^ k * 120 ^ k : ℕ) : ℚ) := by
    have := congrArg (· * ((120 ^ k : ℕ) : ℚ)) hmulQ
    rw [mul_assoc, div_mul_cancel₀ _ h120ne] at this
    push_cast at this ⊢; exact this
  have hnat : m * (2 * 120 ^ k + 60 ^ k + 40 ^ k + 24 ^ k + 15 ^ k) = 6 ^ k * 120 ^ k :=
    Nat.cast_injective hnatQ
  set U := 2 * 120 ^ k + 60 ^ k + 40 ^ k + 24 ^ k + 15 ^ k
  have hU_gt : 1 < U := by
    have h1 : 1 ≤ 120 ^ k := Nat.one_le_pow k 120 (by omega)
    have h2 : 2 * 120 ^ k ≤ U :=
      Nat.le_trans (Nat.le_add_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _)
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    omega
  have h2_ndvd : ¬ (2 ∣ U) := by
    intro h
    have hrest : 2 ∣ 2 * 120 ^ k + 60 ^ k + 40 ^ k + 24 ^ k :=
      dvd_add (dvd_add (dvd_add (dvd_mul_right 2 _) (dvd_pow (by decide : 2 ∣ 60) (by omega)))
        (dvd_pow (by decide : 2 ∣ 40) (by omega))) (dvd_pow (by decide : 2 ∣ 24) (by omega))
    have h15 : 2 ∣ 15 ^ k := (Nat.dvd_add_right hrest).mp h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h15
    omega
  have h3_ndvd : ¬ (3 ∣ U) := by
    intro h
    have hrest : 3 ∣ 2 * 120 ^ k + 60 ^ k + 24 ^ k + 15 ^ k :=
      dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (dvd_pow (by decide : 3 ∣ 120) (by omega)) 2)
        (dvd_pow (by decide : 3 ∣ 60) (by omega))) (dvd_pow (by decide : 3 ∣ 24) (by omega)))
        (dvd_pow (by decide : 3 ∣ 15) (by omega))
    have hUeq : U = (2 * 120 ^ k + 60 ^ k + 24 ^ k + 15 ^ k) + 40 ^ k := by omega
    rw [hUeq] at h
    have h40 : 3 ∣ 40 ^ k := (Nat.dvd_add_right hrest).mp h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h40
    omega
  have h5_ndvd : ¬ (5 ∣ U) := by
    intro h
    have hrest : 5 ∣ 2 * 120 ^ k + 60 ^ k + 40 ^ k + 15 ^ k :=
      dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (dvd_pow (by decide : 5 ∣ 120) (by omega)) 2)
        (dvd_pow (by decide : 5 ∣ 60) (by omega))) (dvd_pow (by decide : 5 ∣ 40) (by omega)))
        (dvd_pow (by decide : 5 ∣ 15) (by omega))
    have hUeq : U = (2 * 120 ^ k + 60 ^ k + 40 ^ k + 15 ^ k) + 24 ^ k := by omega
    rw [hUeq] at h
    have h24 : 5 ∣ 24 ^ k := (Nat.dvd_add_right hrest).mp h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h24
    omega
  have hcop2 : Nat.Coprime U 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2_ndvd).symm
  have hcop3 : Nat.Coprime U 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3_ndvd).symm
  have hcop5 : Nat.Coprime U 5 := (Nat.prime_five.coprime_iff_not_dvd.mpr h5_ndvd).symm
  have hcop6 : Nat.Coprime U (6 ^ k) := by
    rw [show (6 : ℕ) = 2 * 3 by rfl]
    exact (hcop2.mul_right hcop3).pow_right k
  have hcop120 : Nat.Coprime U (120 ^ k) := by
    rw [show (120 : ℕ) = 2 * 2 * 2 * 3 * 5 by rfl]
    exact ((((hcop2.mul_right hcop2).mul_right hcop2).mul_right hcop3).mul_right hcop5).pow_right k
  have hcop_all : Nat.Coprime U (6 ^ k * 120 ^ k) := hcop6.mul_right hcop120
  have hdvd : U ∣ 6 ^ k * 120 ^ k := ⟨m, by linarith⟩
  have hU1 : U ∣ 1 :=
    hcop_all.dvd_of_dvd_mul_right (show U ∣ 1 * (6 ^ k * 120 ^ k) by simpa using hdvd)
  have := Nat.le_of_dvd (by omega) hU1
  omega

private lemma pow_three_odd_mod_four : ∀ t : ℕ, 3 ^ (2 * t + 1) % 4 = 3 := by
  intro t
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by omega, pow_add]
    omega

private lemma case_n3_only_k2 {k : ℕ} (hk : 1 ≤ k)
    (h : ∃ m : ℕ, (m : ℚ) = fibHarmonic 3 k) : k = 2 := by
  rcases h with ⟨m, hm⟩
  have hSpos : 0 < fibRecipSum 3 k := fibRecipSum_pos (by omega)
  have hmulQ : (m : ℚ) * fibRecipSum 3 k = (3 : ℚ) ^ k := by
    rw [hm, fibHarmonic, div_mul_cancel₀ _ (ne_of_gt hSpos)]; norm_cast
  have hS : fibRecipSum 3 k = ((2 ^ (k + 1) + 1 : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
    unfold fibRecipSum
    have hIcc : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
    rw [hIcc]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true,
      Finset.sum_singleton]
    have hf1 : Nat.fib 1 = 1 := rfl
    have hf2 : Nat.fib 2 = 1 := rfl
    have hf3 : Nat.fib 3 = 2 := rfl
    rw [hf1, hf2, hf3]
    have h2ne : ((2 : ℚ) ^ k) ≠ 0 := by positivity
    push_cast
    rw [pow_succ]
    field_simp [h2ne]
    ring
  rw [hS] at hmulQ
  have h2ne : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hnatQ : ((m * (2 ^ (k + 1) + 1) : ℕ) : ℚ) = ((3 ^ k * 2 ^ k : ℕ) : ℚ) := by
    have := congrArg (· * ((2 ^ k : ℕ) : ℚ)) hmulQ
    rw [mul_assoc, div_mul_cancel₀ _ h2ne] at this
    push_cast at this ⊢; exact this
  have hnat : m * (2 ^ (k + 1) + 1) = 3 ^ k * 2 ^ k := Nat.cast_injective hnatQ
  have hcop2 : Nat.Coprime (2 ^ (k + 1) + 1) (2 ^ k) := by
    have h2ndvd : ¬ (2 ∣ 2 ^ (k + 1) + 1) := by
      have : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
      omega
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr h2ndvd).symm).pow_right k
  have hdvd3k : 2 ^ (k + 1) + 1 ∣ 3 ^ k :=
    hcop2.dvd_of_dvd_mul_right ⟨m, by linarith⟩
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3k
  rcases Nat.even_or_odd j with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · -- j = t + t: (3^t - 1)(3^t + 1) = 2^(k+1)
    have ht1 : 1 ≤ t := by
      by_contra h0
      have ht0 : t = 0 := by omega
      subst ht0
      have : 2 ^ (k + 1) ≥ 4 := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (show 2 ≤ k + 1 by omega)
        omega
      omega
    have h3t_ge : 3 ≤ 3 ^ t := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 3) ht1
      simpa using this
    have hfac : (3 ^ t - 1) * (3 ^ t + 1) = 2 ^ (k + 1) := by
      have hsq : 3 ^ (t + t) = 3 ^ t * 3 ^ t := by rw [pow_add]
      zify [show 1 ≤ 3 ^ t by omega]
      zify at hj hsq
      nlinarith
    have hdvd_lo : 3 ^ t - 1 ∣ 2 ^ (k + 1) := ⟨3 ^ t + 1, by linarith⟩
    have hdvd_hi : 3 ^ t + 1 ∣ 2 ^ (k + 1) := ⟨3 ^ t - 1, by linarith⟩
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_lo
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_hi
    have hdiff : 2 ^ b - 2 ^ a = 2 := by omega
    have ha1 : a = 1 := by
      by_contra hne
      rcases (by omega : a = 0 ∨ 2 ≤ a) with rfl | ha2
      · omega
      · have h4a : 4 ∣ 2 ^ a := by
          rw [show (4 : ℕ) = 2 ^ 2 by rfl]
          exact Nat.pow_dvd_pow 2 ha2
        have hab : a < b := by
          by_contra hle
          have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h4b : 4 ∣ 2 ^ b := by
          rw [show (4 : ℕ) = 2 ^ 2 by rfl]
          exact Nat.pow_dvd_pow 2 (by omega)
        have h4_2 : 4 ∣ 2 := by
          rw [← hdiff]
          exact Nat.dvd_sub h4b h4a
        omega
    subst ha1
    have h3t3 : 3 ^ t = 3 := by omega
    have ht_eq : t = 1 := by
      by_contra hne
      have ht2 : 2 ≤ t := by omega
      have : 9 ≤ 3 ^ t := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 3) ht2
        simpa using this
      omega
    subst ht_eq
    have h2k : 2 ^ (k + 1) = 8 := by omega
    have hk_eq : k + 1 = 3 := by
      by_contra hne
      rcases (by omega : k + 1 ≤ 2 ∨ 4 ≤ k + 1) with hle2 | hge4
      · have : 2 ^ (k + 1) ≤ 4 := by
          have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hle2
          simpa using this
        omega
      · have : 16 ≤ 2 ^ (k + 1) := by
          have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hge4
          simpa using this
        omega
    omega
  · -- j = 2*t + 1: 3^(2*t+1) ≡ 3 (mod 4), but 2^(k+1) + 1 ≡ 1 (mod 4)
    have hmod3 : 3 ^ (2 * t + 1) % 4 = 3 := pow_three_odd_mod_four t
    have h4dvd : 4 ∣ 2 ^ (k + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl]
      exact Nat.pow_dvd_pow 2 (by omega)
    rcases h4dvd with ⟨q, hq⟩
    rw [hq] at hj
    have hmod := congrArg (· % 4) hj
    rw [hmod3] at hmod
    omega

/-- Complete classification of integral harmonic-type Fibonacci means for all `n ≥ 1, k ≥ 1`
(reproving Theorem 1.18 and proving Conjecture 1.19 of Mandal–Mohan, `arXiv:2611.32519v1`). -/
theorem mandal_mohan_harmonic_iff {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∃ m : ℕ, (m : ℚ) = fibHarmonic n k) ↔ n = 1 ∨ n = 2 ∨ (n = 3 ∧ k = 2) := by
  constructor
  · intro hex
    by_cases h1 : n = 1
    · exact Or.inl h1
    by_cases h2 : n = 2
    · exact Or.inr (Or.inl h2)
    by_cases h3 : n = 3
    · subst h3
      exact Or.inr (Or.inr ⟨rfl, case_n3_only_k2 hk hex⟩)
    exfalso
    by_cases h4 : n = 4
    · subst h4; exact case_n4 hk hex
    by_cases h5 : n = 5
    · subst h5
      exact no_int_of_isolated_fib hk (q := 5) (by omega) (by omega)
        (fun i hi hne => coprime_fib_of_prime_gt_half (by decide) (by omega)
          (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2 hne)
        (by decide) hex
    by_cases h6 : n = 6
    · subst h6; exact case_n6 hk hex
    by_cases h11 : n ≤ 11
    · exact no_int_of_isolated_fib hk (q := 7) (by omega) (by omega)
        (fun i hi hne => coprime_fib_of_prime_gt_half (by decide) (by omega)
          (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2 hne)
        (by
          have : Nat.fib 7 = 13 := rfl
          omega) hex
    · -- n ≥ 12: Bertrand's postulate gives a prime q with n / 2 < q ≤ 2 * (n / 2) ≤ n
      obtain ⟨q, hq_prime, hq_gt, hq_le⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
      have hq7 : 7 ≤ q := by omega
      have hqn : q ≤ n := by omega
      have h2q : n < 2 * q := by omega
      have hge : n ≤ Nat.fib q := by
        have := fib_ge_two_mul_sub_one q hq7
        omega
      exact no_int_of_isolated_fib hk (by omega) hqn
        (fun i hi hne => coprime_fib_of_prime_gt_half hq_prime h2q
          (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2 hne)
        hge hex
  · rintro (rfl | rfl | ⟨rfl, rfl⟩)
    · refine ⟨1, ?_⟩
      unfold fibHarmonic fibRecipSum
      have hIcc : Finset.Icc 1 1 = ({1} : Finset ℕ) := by decide
      rw [hIcc, Finset.sum_singleton]
      simp [Nat.fib_one]
    · refine ⟨2 ^ (k - 1), ?_⟩
      unfold fibHarmonic fibRecipSum
      have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
      rw [hIcc, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
      simp only [Nat.fib_one, Nat.fib_two, Nat.cast_one, one_pow, inv_one]
      have hk1 : k = (k - 1) + 1 := by omega
      conv_rhs => rw [hk1, pow_succ]
      push_cast; ring
    · refine ⟨4, ?_⟩
      unfold fibHarmonic fibRecipSum
      have hIcc : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
      rw [hIcc]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
        OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true,
        Finset.sum_singleton]
      have hf1 : Nat.fib 1 = 1 := rfl
      have hf2 : Nat.fib 2 = 1 := rfl
      have hf3 : Nat.fib 3 = 2 := rfl
      rw [hf1, hf2, hf3]; norm_num

/-- Equivalent formulation in terms of `Rat.den = 1` (since `fibHarmonic n k > 0`). -/
theorem mandal_mohan_harmonic_den_iff {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (fibHarmonic n k).den = 1 ↔ n = 1 ∨ n = 2 ∨ (n = 3 ∧ k = 2) := by
  rw [← mandal_mohan_harmonic_iff hn hk]
  constructor
  · intro hden
    have hpos : 0 < fibHarmonic n k :=
      div_pos (pow_pos (by exact_mod_cast (by omega : 0 < n)) k) (fibRecipSum_pos hn)
    have hnum_nonneg : 0 ≤ (fibHarmonic n k).num := Rat.num_nonneg.mpr (le_of_lt hpos)
    refine ⟨(fibHarmonic n k).num.toNat, ?_⟩
    have hrat := (Rat.num_div_den (fibHarmonic n k)).symm
    rw [hden, Nat.cast_one, div_one] at hrat
    rw [hrat]
    exact_mod_cast Int.toNat_of_nonneg hnum_nonneg
  · rintro ⟨m, hm⟩
    rw [← hm]
    exact Rat.den_natCast m

/-- **Conjecture 1.19 of Mandal–Mohan (`arXiv:2611.32519v1`)**:
For every `k ≥ 3` and `n ≥ 1`, `n^k / ∑_{i=1}^n F_i^{-k} ∈ ℕ` if and only if `n = 1` or `n = 2`. -/
theorem mandal_mohan_conjecture_1_19 {n k : ℕ} (hn : 1 ≤ n) (hk : 3 ≤ k) :
    (∃ m : ℕ, (m : ℚ) = fibHarmonic n k) ↔ n = 1 ∨ n = 2 := by
  rw [mandal_mohan_harmonic_iff hn (by omega)]
  omega

/-- Denominator formulation of Conjecture 1.19 of Mandal–Mohan (`arXiv:2611.32519v1`). -/
theorem mandal_mohan_conjecture_1_19_den {n k : ℕ} (hn : 1 ≤ n) (hk : 3 ≤ k) :
    (fibHarmonic n k).den = 1 ↔ n = 1 ∨ n = 2 := by
  rw [mandal_mohan_harmonic_den_iff hn (by omega)]
  omega

end MandalMohanFibonacciHarmonic
