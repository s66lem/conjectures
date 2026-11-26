import Mathlib

/-!
# 2-Adic Valuation of Central Coefficients of `(1 + x + ... + x^(2^r - 1))^(2m)` and OEIS A402341

This module gives a complete, self-contained proof of the 2-adic valuation conjecture on
[OEIS A402341](https://oeis.org/A402341) (Sajid Khan Hussain, Nov 17 2026) and its
generalization to every power-of-two block length `2^r` (`r ≥ 1`).

## Conjecture (OEIS A402341)

Let `a(n)` be the central coefficient `[x^(⌊15n/2⌋)] (1 + x + x^2 + ... + x^15)^n`.
For every even `n ≥ 0`,
`v₂(a(n)) = s₂(15n / 2) = A000120(15n / 2)`,
where `s₂(t)` is the number of `1`s in the binary expansion of `t`.

## Main Theorems

* `centralPolyCoeff_congr_centralBinom`: for every `r ≥ 1` and `m ≥ 0`, with `N = (2^r - 1) * m`,
  `centralPolyCoeff r (2 * m) ≡ Nat.centralBinom N [MOD 2 ^ (popcount N + 1)]`.
* `padicValNat_centralPolyCoeff_even`: for every `r ≥ 1` and `m ≥ 0`,
  `padicValNat 2 (centralPolyCoeff r (2 * m)) = popcount ((2 ^ r - 1) * m)`.
* `oeis_A402341_conjecture`: for every `n : ℕ` with `Even n`,
  `padicValNat 2 (a402341 n) = (Nat.digits 2 (15 * n / 2)).sum`.
-/

namespace HussainA402341

open Polynomial Finset

/-! ### Section 1: Binary digit sum (`A000120`) and 2-adic valuation of central binomials -/

/-- Binary digit sum `s₂(n) = A000120(n)`, the number of `1`s in the base-2 expansion of `n`. -/
def popcount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma popcount_zero : popcount 0 = 0 := by
  simp [popcount]

lemma popcount_one : popcount 1 = 1 := by
  simp [popcount]

lemma popcount_two_mul (k : ℕ) : popcount (2 * k) = popcount k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [popcount]
  · unfold popcount
    rw [Nat.digits_def' (by omega) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_right k (by omega : 0 < 2)]

lemma popcount_two_mul_add_one (k : ℕ) : popcount (2 * k + 1) = popcount k + 1 := by
  unfold popcount
  rw [Nat.digits_def' (by omega) (by omega),
    show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  simp [add_comm]

lemma popcount_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < popcount n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h2 : n % 2 = 0
    · have hm : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      have heq : n = 2 * (n / 2) := by omega
      rw [heq, popcount_two_mul]
      exact ih (n / 2) hlt hm
    · have heq : n = 2 * (n / 2) + 1 := by omega
      rw [heq, popcount_two_mul_add_one]
      omega

lemma popcount_pow_two (k : ℕ) : popcount (2 ^ k) = 1 := by
  induction k with
  | zero => exact popcount_one
  | succ k ih =>
    rw [pow_succ', popcount_two_mul, ih]

lemma popcount_succ_le (n : ℕ) : popcount (n + 1) ≤ popcount n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h2 : n % 2 = 0
    · have heq : n = 2 * (n / 2) := by omega
      rw [heq, popcount_two_mul_add_one, popcount_two_mul]
    · set m := n / 2
      have hlt : m < n := by omega
      have hih := ih m hlt
      have heq : n = 2 * m + 1 := by omega
      have hsucc : n + 1 = 2 * (m + 1) := by omega
      rw [hsucc, popcount_two_mul, heq, popcount_two_mul_add_one]
      omega

lemma popcount_add_le (u v : ℕ) : popcount (u + v) ≤ popcount u + popcount v := by
  induction h : u + v using Nat.strongRecOn generalizing u v with
  | ind s ih =>
    rcases eq_or_ne s 0 with rfl | hs
    · have hu : u = 0 := by omega
      have hv : v = 0 := by omega
      subst hu; subst hv; simp [popcount_zero]
    · set a := u / 2
      set b := u % 2
      set c := v / 2
      set d := v % 2
      have hu : u = 2 * a + b := by omega
      have hv : v = 2 * c + d := by omega
      have hb : b = 0 ∨ b = 1 := by omega
      have hd : d = 0 ∨ d = 1 := by omega
      have hac_lt : a + c < s := by omega
      have hih := ih (a + c) hac_lt a c rfl
      rcases hb with hb | hb <;> rcases hd with hd | hd
      · have huv : s = 2 * (a + c) := by omega
        rw [huv, popcount_two_mul, hu, hv, hb, hd, add_zero, add_zero,
          popcount_two_mul, popcount_two_mul]
        exact hih
      · have huv : s = 2 * (a + c) + 1 := by omega
        rw [huv, popcount_two_mul_add_one, hu, hv, hb, hd, add_zero,
          popcount_two_mul, popcount_two_mul_add_one]
        omega
      · have huv : s = 2 * (a + c) + 1 := by omega
        rw [huv, popcount_two_mul_add_one, hu, hv, hb, hd, add_zero,
          popcount_two_mul_add_one, popcount_two_mul]
        omega
      · have huv : s = 2 * (a + c + 1) := by omega
        rw [huv, popcount_two_mul, hu, hv, hb, hd,
          popcount_two_mul_add_one, popcount_two_mul_add_one]
        have hstep := popcount_succ_le (a + c)
        omega

lemma padicValNat_two_factorial_two_mul (m : ℕ) :
    padicValNat 2 ((2 * m).factorial) = m + padicValNat 2 (m.factorial) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction m with
  | zero => simp
  | succ m ih =>
    have hfac : (2 * (m + 1)).factorial =
        2 * (m + 1) * (2 * m + 1) * (2 * m).factorial := by
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have hodd : padicValNat 2 (2 * m + 1) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      omega
    have hm1 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
    rw [hfac,
      padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
      padicValNat.mul (by positivity) (by omega),
      padicValNat.mul (by omega) (by omega),
      padicValNat.self (by omega), hodd, ih, hm1,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    omega

lemma padicValNat_two_factorial_add_popcount (n : ℕ) :
    padicValNat 2 (n.factorial) + popcount n = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp [popcount_zero]
    · by_cases h2 : n % 2 = 0
      · have heq : n = 2 * (n / 2) := by omega
        have hlt : n / 2 < n := by omega
        rw [heq, padicValNat_two_factorial_two_mul, popcount_two_mul]
        have := ih (n / 2) hlt
        omega
      · have heq : n = 2 * (n / 2) + 1 := by omega
        have hlt : n / 2 < n := by omega
        have hodd : padicValNat 2 (2 * (n / 2) + 1) = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          omega
        rw [heq, Nat.factorial_succ,
          padicValNat.mul (by omega) (Nat.factorial_ne_zero _),
          hodd, zero_add, padicValNat_two_factorial_two_mul, popcount_two_mul_add_one]
        have := ih (n / 2) hlt
        omega

lemma padicValNat_two_centralBinom (t : ℕ) :
    padicValNat 2 (Nat.centralBinom t) = popcount t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul : Nat.centralBinom t * (t.factorial * t.factorial) = (2 * t).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show t ≤ 2 * t by omega)
    rw [show 2 * t - t = t by omega] at h
    simpa [Nat.centralBinom_eq_two_mul_choose, mul_assoc] using h
  have hcb_ne : Nat.centralBinom t ≠ 0 := Nat.centralBinom_ne_zero t
  have hval := congrArg (padicValNat 2) hmul
  rw [padicValNat.mul hcb_ne (mul_ne_zero (Nat.factorial_ne_zero t) (Nat.factorial_ne_zero t)),
    padicValNat.mul (Nat.factorial_ne_zero t) (Nat.factorial_ne_zero t),
    padicValNat_two_factorial_two_mul] at hval
  have hleg := padicValNat_two_factorial_add_popcount t
  omega

lemma two_pow_popcount_dvd_centralBinom (t : ℕ) :
    2 ^ popcount t ∣ Nat.centralBinom t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← padicValNat_two_centralBinom t]
  exact pow_padicValNat_dvd

lemma not_two_pow_popcount_succ_dvd_centralBinom (t : ℕ) :
    ¬ (2 ^ (popcount t + 1) ∣ Nat.centralBinom t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  have hle := (padicValNat_dvd_iff_le (Nat.centralBinom_ne_zero t)).mp hdvd
  rw [padicValNat_two_centralBinom t] at hle
  omega

/-! ### Section 2: Polynomial homogenization `evalY` and the factors `R k`, `Q r` -/

/-- Homogeneous substitution `D`-lift of `F(y)` at `y = x / (1 + x)^2`:
`evalY D F = ∑ j ∈ F.support, F.coeff j * X^j * (1 + X)^(D - 2*j)`. -/
noncomputable def evalY (D : ℕ) (F : Polynomial ℤ) : Polynomial ℤ :=
  ∑ j ∈ F.support, C (F.coeff j) * X ^ j * (1 + X) ^ (D - 2 * j)

lemma evalY_eq_sum (D : ℕ) (F : Polynomial ℤ) (S : Finset ℕ) (hS : F.support ⊆ S) :
    evalY D F = ∑ j ∈ S, C (F.coeff j) * X ^ j * (1 + X) ^ (D - 2 * j) := by
  unfold evalY
  apply Finset.sum_subset hS
  intro j _ hj
  simp [Polynomial.notMem_support_iff.mp hj]

lemma evalY_zero (D : ℕ) : evalY D 0 = 0 := by
  simp [evalY]

lemma evalY_add (D : ℕ) (F G : Polynomial ℤ) :
    evalY D (F + G) = evalY D F + evalY D G := by
  let S := F.support ∪ G.support
  have hFG : (F + G).support ⊆ S := Polynomial.support_add
  rw [evalY_eq_sum D (F + G) S hFG,
    evalY_eq_sum D F S Finset.subset_union_left,
    evalY_eq_sum D G S Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.coeff_add, map_add]
  ring

lemma evalY_neg (D : ℕ) (F : Polynomial ℤ) :
    evalY D (-F) = -evalY D F := by
  have h := evalY_add D F (-F)
  rw [add_neg_cancel, evalY_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma evalY_sub (D : ℕ) (F G : Polynomial ℤ) :
    evalY D (F - G) = evalY D F - evalY D G := by
  rw [sub_eq_add_neg, evalY_add, evalY_neg, ← sub_eq_add_neg]

lemma evalY_sum {ι : Type*} (D : ℕ) (s : Finset ι) (f : ι → Polynomial ℤ) :
    evalY D (∑ i ∈ s, f i) = ∑ i ∈ s, evalY D (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [evalY_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, evalY_add, ih, Finset.sum_insert ha]

lemma evalY_monomial (D : ℕ) (a : ℤ) (j : ℕ) :
    evalY D (C a * X ^ j) = C a * X ^ j * (1 + X) ^ (D - 2 * j) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [evalY_zero]
  · have hsupp : (C a * X ^ j).support = {j} := by
      rw [Polynomial.C_mul_X_pow_eq_monomial]
      exact Polynomial.support_monomial j ha
    unfold evalY
    rw [hsupp, Finset.sum_singleton, Polynomial.coeff_C_mul_X_pow]
    simp

lemma evalY_one (D : ℕ) : evalY D 1 = (1 + X) ^ D := by
  have h := evalY_monomial D 1 0
  simpa using h

/-- Degree bound condition `2 * j ≤ D` on every monomial in `F.support`. -/
def FitsDeg (D : ℕ) (F : Polynomial ℤ) : Prop :=
  ∀ j ∈ F.support, 2 * j ≤ D

lemma fitsDeg_zero (D : ℕ) : FitsDeg D 0 := by
  intro j hj; simp at hj

lemma fitsDeg_one (D : ℕ) : FitsDeg D 1 := by
  intro j hj
  rw [Polynomial.mem_support_iff, Polynomial.coeff_one] at hj
  have hj0 : j = 0 := by
    by_contra h
    exact hj (if_neg h)
  omega

lemma fitsDeg_add {D : ℕ} {F G : Polynomial ℤ} (hF : FitsDeg D F) (hG : FitsDeg D G) :
    FitsDeg D (F + G) := by
  intro j hj
  rcases Finset.mem_union.mp (Polynomial.support_add hj) with hjF | hjG
  · exact hF j hjF
  · exact hG j hjG

lemma fitsDeg_neg {D : ℕ} {F : Polynomial ℤ} (hF : FitsDeg D F) : FitsDeg D (-F) := by
  intro j hj
  exact hF j (by simpa [Polynomial.support_neg] using hj)

lemma fitsDeg_sub {D : ℕ} {F G : Polynomial ℤ} (hF : FitsDeg D F) (hG : FitsDeg D G) :
    FitsDeg D (F - G) := by
  rw [sub_eq_add_neg]
  exact fitsDeg_add hF (fitsDeg_neg hG)

lemma fitsDeg_monomial {D j : ℕ} (a : ℤ) (h : 2 * j ≤ D) : FitsDeg D (C a * X ^ j) := by
  intro k hk
  rcases eq_or_ne a 0 with rfl | ha
  · simp at hk
  · rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.support_monomial j ha,
      Finset.mem_singleton] at hk
    omega

lemma fitsDeg_mul {D₁ D₂ : ℕ} {F G : Polynomial ℤ} (hF : FitsDeg D₁ F) (hG : FitsDeg D₂ G) :
    FitsDeg (D₁ + D₂) (F * G) := by
  intro n hn
  have hne : (F * G).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  rw [Polynomial.coeff_mul] at hne
  obtain ⟨⟨u, v⟩, huv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hu : u ∈ F.support := Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hterm)
  have hv : v ∈ G.support := Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hterm)
  have hsum : u + v = n := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have h1 := hF u hu
  have h2 := hG v hv
  omega

lemma fitsDeg_pow {D : ℕ} {F : Polynomial ℤ} (hF : FitsDeg D F) (n : ℕ) :
    FitsDeg (n * D) (F ^ n) := by
  induction n with
  | zero => simpa using fitsDeg_one 0
  | succ n ih =>
    rw [pow_succ, show (n + 1) * D = n * D + D by ring]
    exact fitsDeg_mul ih hF

lemma evalY_mul {D₁ D₂ : ℕ} {F G : Polynomial ℤ} (hF : FitsDeg D₁ F) (hG : FitsDeg D₂ G) :
    evalY (D₁ + D₂) (F * G) = evalY D₁ F * evalY D₂ G := by
  have hFsum : F = ∑ j ∈ F.support, C (F.coeff j) * X ^ j :=
    Polynomial.as_sum_support_C_mul_X_pow F
  have hGsum : G = ∑ k ∈ G.support, C (G.coeff k) * X ^ k :=
    Polynomial.as_sum_support_C_mul_X_pow G
  conv_lhs => rw [hFsum, hGsum, Finset.sum_mul]
  rw [evalY_sum]
  conv_rhs => unfold evalY
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, evalY_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h1 : 2 * j ≤ D₁ := hF j hj
  have h2 : 2 * k ≤ D₂ := hG k hk
  have hexp : D₁ + D₂ - 2 * (j + k) = (D₁ - 2 * j) + (D₂ - 2 * k) := by omega
  have hmon : (C (F.coeff j) * X ^ j) * (C (G.coeff k) * X ^ k) =
      C (F.coeff j * G.coeff k) * X ^ (j + k) := by
    rw [map_mul, pow_add]; ring
  rw [hmon, evalY_monomial, hexp, pow_add, pow_add, map_mul]
  ring

lemma evalY_pow {D : ℕ} {F : Polynomial ℤ} (hF : FitsDeg D F) (n : ℕ) :
    evalY (n * D) (F ^ n) = (evalY D F) ^ n := by
  induction n with
  | zero => simp [evalY_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, show (n + 1) * D = n * D + D by ring,
      evalY_mul (fitsDeg_pow hF n) hF, ih]

/-- Recursive polynomials `R k` satisfying `(1 + x)^(2^k) * R_k(x / (1 + x)^2) = 1 + x^(2^k)`. -/
noncomputable def R : ℕ → Polynomial ℤ
  | 0 => 1
  | k + 1 => (R k) ^ 2 - C 2 * X ^ (2 ^ k)

lemma fitsDeg_R (k : ℕ) : FitsDeg (2 ^ k) (R k) := by
  induction k with
  | zero => simpa [R] using fitsDeg_one 1
  | succ k ih =>
    rw [R]
    have hsq : FitsDeg (2 ^ (k + 1)) ((R k) ^ 2) := by
      have := fitsDeg_pow ih 2
      simpa [pow_succ'] using this
    have hmon : FitsDeg (2 ^ (k + 1)) (C 2 * X ^ (2 ^ k)) :=
      fitsDeg_monomial 2 (by rw [pow_succ'])
    exact fitsDeg_sub hsq hmon

lemma evalY_R (k : ℕ) : evalY (2 ^ k) (R k) = 1 + X ^ (2 ^ k) := by
  induction k with
  | zero => simp [R, evalY_one]
  | succ k ih =>
    rw [R, evalY_sub]
    have hsq : evalY (2 ^ (k + 1)) ((R k) ^ 2) = (evalY (2 ^ k) (R k)) ^ 2 := by
      have := evalY_pow (fitsDeg_R k) 2
      simpa [pow_succ'] using this
    have hmon : evalY (2 ^ (k + 1)) (C 2 * X ^ (2 ^ k)) = C 2 * X ^ (2 ^ k) := by
      rw [evalY_monomial]
      have h0 : 2 ^ (k + 1) - 2 * 2 ^ k = 0 := by rw [pow_succ']; omega
      rw [h0, pow_zero, mul_one]
    rw [hsq, ih, hmon]
    have hexp : (X ^ 2 ^ k : Polynomial ℤ) ^ 2 = X ^ 2 ^ (k + 1) := by
      rw [← pow_mul, pow_succ]
    calc (1 + (X : Polynomial ℤ) ^ 2 ^ k) ^ 2 - C (2 : ℤ) * X ^ 2 ^ k
        = 1 + ((X : Polynomial ℤ) ^ 2 ^ k) ^ 2 := by
          have hC2 : C (2 : ℤ) = (2 : Polynomial ℤ) := map_ofNat C 2
          rw [hC2]; ring
      _ = 1 + (X : Polynomial ℤ) ^ 2 ^ (k + 1) := by rw [hexp]

/-- The product polynomial `Q r = ∏_{k < r} R k`, satisfying
`evalY (2^r - 1) (Q r) = 1 + x + ... + x^(2^r - 1)`. -/
noncomputable def Q (r : ℕ) : Polynomial ℤ :=
  ∏ k ∈ Finset.range r, R k

lemma sum_pow_two_range (r : ℕ) : ∑ k ∈ Finset.range r, 2 ^ k = 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    rw [pow_succ']
    omega

lemma fitsDeg_Q (r : ℕ) : FitsDeg (2 ^ r - 1) (Q r) := by
  induction r with
  | zero => simpa [Q] using fitsDeg_one 0
  | succ r ih =>
    rw [Q, Finset.prod_range_succ, ← Q]
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    have hsum : 2 ^ (r + 1) - 1 = (2 ^ r - 1) + 2 ^ r := by
      rw [pow_succ']; omega
    rw [hsum]
    exact fitsDeg_mul ih (fitsDeg_R r)

lemma prod_one_add_X_pow_two (r : ℕ) :
    ∏ k ∈ Finset.range r, (1 + (X : Polynomial ℤ) ^ (2 ^ k)) =
      ∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℤ) ^ i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, Finset.sum_mul]
    have hshift :
        ∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℤ) ^ i * X ^ (2 ^ r) =
          ∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℤ) ^ (2 ^ r + i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_add, add_comm]
    rw [hshift, show 2 ^ (r + 1) = 2 ^ r + 2 ^ r by rw [pow_succ']; omega,
      Finset.sum_range_add]

lemma evalY_Q (r : ℕ) :
    evalY (2 ^ r - 1) (Q r) = ∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℤ) ^ i := by
  rw [← prod_one_add_X_pow_two r]
  induction r with
  | zero => simp [Q, evalY_one]
  | succ r ih =>
    rw [Q, Finset.prod_range_succ, ← Q, Finset.prod_range_succ]
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    have hsum : 2 ^ (r + 1) - 1 = (2 ^ r - 1) + 2 ^ r := by
      rw [pow_succ']; omega
    rw [hsum, evalY_mul (fitsDeg_Q r) (fitsDeg_R r), ih, evalY_R r]

/-! ### Section 3: Admissibility and strong admissibility of `Q r ^ (2 * m)` -/

/-- `F` is admissible if `2^(s₂(j)) ∣ F.coeff j` for every `j`. -/
def IsAdmissible (F : Polynomial ℤ) : Prop :=
  ∀ j : ℕ, ((2 : ℤ) ^ popcount j) ∣ F.coeff j

/-- `F` is strongly admissible if `F.coeff 0 = 1` and `2^(s₂(j) + 1) ∣ F.coeff j` for every `j > 0`. -/
def IsStrongAdmissible (F : Polynomial ℤ) : Prop :=
  F.coeff 0 = 1 ∧ ∀ j : ℕ, 0 < j → ((2 : ℤ) ^ (popcount j + 1)) ∣ F.coeff j

lemma isAdmissible_one : IsAdmissible 1 := by
  intro j
  rcases eq_or_ne j 0 with rfl | hj
  · simp [popcount_zero]
  · simp [Polynomial.coeff_one, hj]

lemma isAdmissible_sub {F G : Polynomial ℤ} (hF : IsAdmissible F) (hG : IsAdmissible G) :
    IsAdmissible (F - G) := by
  intro j
  rw [Polynomial.coeff_sub]
  exact dvd_sub (hF j) (hG j)

lemma isAdmissible_mul {F G : Polynomial ℤ} (hF : IsAdmissible F) (hG : IsAdmissible G) :
    IsAdmissible (F * G) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hle : popcount n ≤ popcount p.1 + popcount p.2 := by
    rw [← hsum]; exact popcount_add_le p.1 p.2
  have hdvd_pow : ((2 : ℤ) ^ popcount n) ∣ ((2 : ℤ) ^ (popcount p.1 + popcount p.2)) :=
    pow_dvd_pow 2 hle
  have hmul : ((2 : ℤ) ^ (popcount p.1 + popcount p.2)) ∣ F.coeff p.1 * G.coeff p.2 := by
    rw [pow_add]
    exact mul_dvd_mul (hF p.1) (hG p.2)
  exact dvd_trans hdvd_pow hmul

lemma isAdmissible_R (k : ℕ) : IsAdmissible (R k) ∧ (R k).coeff 0 = 1 := by
  induction k with
  | zero =>
    exact ⟨isAdmissible_one, by simp [R]⟩
  | succ k ih =>
    rcases ih with ⟨hadm, h0⟩
    refine ⟨?_, ?_⟩
    · rw [R]
      have hsq : IsAdmissible ((R k) ^ 2) := by
        rw [sq]; exact isAdmissible_mul hadm hadm
      have hmon : IsAdmissible (C 2 * X ^ (2 ^ k)) := by
        intro j
        rw [Polynomial.coeff_C_mul_X_pow]
        split_ifs with hj
        · subst hj
          rw [popcount_pow_two, pow_one]
        · exact dvd_zero _
      exact isAdmissible_sub hsq hmon
    · rw [R, Polynomial.coeff_sub, sq, Polynomial.mul_coeff_zero, h0, mul_one,
        Polynomial.coeff_C_mul_X_pow]
      have hne : (0 : ℕ) ≠ 2 ^ k := by positivity
      simp [hne]

lemma isAdmissible_Q (r : ℕ) : IsAdmissible (Q r) ∧ (Q r).coeff 0 = 1 := by
  induction r with
  | zero => exact ⟨isAdmissible_one, by simp [Q]⟩
  | succ r ih =>
    rcases ih with ⟨hQa, hQ0⟩
    rcases isAdmissible_R r with ⟨hRa, hR0⟩
    rw [Q, Finset.prod_range_succ, ← Q]
    exact ⟨isAdmissible_mul hQa hRa, by rw [Polynomial.mul_coeff_zero, hQ0, hR0, mul_one]⟩

lemma isStrongAdmissible_one : IsStrongAdmissible 1 := by
  refine ⟨by simp, fun j hj => ?_⟩
  simp [Polynomial.coeff_one, Nat.ne_of_gt hj]

lemma isStrongAdmissible_sq {F : Polynomial ℤ} (hF : IsAdmissible F) (h0 : F.coeff 0 = 1) :
    IsStrongAdmissible (F ^ 2) := by
  refine ⟨by rw [sq, Polynomial.mul_coeff_zero, h0, mul_one], fun n hn => ?_⟩
  rw [sq, Polynomial.coeff_mul]
  let S := Finset.HasAntidiagonal.antidiagonal n
  let Slt := S.filter (fun p : ℕ × ℕ => p.1 < p.2)
  let Sgt := S.filter (fun p : ℕ × ℕ => p.2 < p.1)
  let Seq := S.filter (fun p : ℕ × ℕ => p.1 = p.2)
  have hsplit : ∑ p ∈ S, F.coeff p.1 * F.coeff p.2 =
      (∑ p ∈ Slt, F.coeff p.1 * F.coeff p.2) +
      (∑ p ∈ Sgt, F.coeff p.1 * F.coeff p.2) +
      (∑ p ∈ Seq, F.coeff p.1 * F.coeff p.2) := by
    have hdisj1 : Disjoint Slt Sgt := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; omega
    have hdisj2 : Disjoint (Slt ∪ Sgt) Seq := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_union, Finset.mem_filter, Slt, Sgt, Seq] at hp1 hp2
      omega
    have hunion : Slt ∪ Sgt ∪ Seq = S := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Slt, Sgt, Seq]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro hp
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · exact Or.inl (Or.inl ⟨hp, h⟩)
        · exact Or.inr ⟨hp, h⟩
        · exact Or.inl (Or.inr ⟨hp, h⟩)
    rw [← hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
  have hsymm : ∑ p ∈ Sgt, F.coeff p.1 * F.coeff p.2 =
      ∑ p ∈ Slt, F.coeff p.1 * F.coeff p.2 := by
    apply Finset.sum_nbij (fun p => (p.2, p.1))
    · intro p hp
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Sgt, Slt, S] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hsum : q.1 + q.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq'.1
      refine ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), hq'.2⟩, rfl⟩
    · intro p _
      exact mul_comm _ _
  change ((2 : ℤ) ^ (popcount n + 1)) ∣ ∑ p ∈ S, F.coeff p.1 * F.coeff p.2
  rw [hsplit, hsymm, ← two_mul]
  apply dvd_add
  · rw [pow_succ']
    apply mul_dvd_mul_left 2
    apply Finset.dvd_sum
    intro p hp
    have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp hp).1
    have hle : popcount n ≤ popcount p.1 + popcount p.2 := by
      rw [← hsum]; exact popcount_add_le p.1 p.2
    exact dvd_trans (pow_dvd_pow 2 hle) (by rw [pow_add]; exact mul_dvd_mul (hF p.1) (hF p.2))
  · apply Finset.dvd_sum
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
    have heq : p.1 = p.2 := hmem.2
    have hn2 : n = 2 * p.1 := by omega
    have hu_pos : 0 < p.1 := by omega
    have hpop_pos : 0 < popcount p.1 := popcount_pos_of_pos hu_pos
    have hle : popcount n + 1 ≤ popcount p.1 + popcount p.2 := by
      rw [hn2, popcount_two_mul, ← heq]
      omega
    exact dvd_trans (pow_dvd_pow 2 hle) (by rw [pow_add]; exact mul_dvd_mul (hF p.1) (hF p.2))

lemma isStrongAdmissible_mul {F G : Polynomial ℤ}
    (hF : IsStrongAdmissible F) (hG : IsStrongAdmissible G) :
    IsStrongAdmissible (F * G) := by
  refine ⟨by rw [Polynomial.mul_coeff_zero, hF.1, hG.1, mul_one], fun n hn => ?_⟩
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hle : popcount n ≤ popcount p.1 + popcount p.2 := by
    rw [← hsum]; exact popcount_add_le p.1 p.2
  by_cases h1 : 0 < p.1
  · have hF1 := hF.2 p.1 h1
    have hG2 : ((2 : ℤ) ^ popcount p.2) ∣ G.coeff p.2 := by
      rcases eq_or_ne p.2 0 with h2 | h2
      · rw [h2, popcount_zero, pow_zero]; exact one_dvd _
      · exact dvd_trans (pow_dvd_pow 2 (Nat.le_succ _)) (hG.2 p.2 (Nat.pos_of_ne_zero h2))
    have hle' : popcount n + 1 ≤ (popcount p.1 + 1) + popcount p.2 := by omega
    exact dvd_trans (pow_dvd_pow 2 hle') (by rw [pow_add]; exact mul_dvd_mul hF1 hG2)
  · have hp1 : p.1 = 0 := by omega
    have hp2 : 0 < p.2 := by omega
    have hG2 := hG.2 p.2 hp2
    rw [hp1, hF.1, one_mul]
    have hpn : p.2 = n := by omega
    rw [hpn] at hG2 ⊢
    exact hG2

lemma isStrongAdmissible_Q_pow_two_mul (r m : ℕ) :
    IsStrongAdmissible (Q r ^ (2 * m)) := by
  rw [pow_mul]
  rcases isAdmissible_Q r with ⟨hQa, hQ0⟩
  have hsq := isStrongAdmissible_sq hQa hQ0
  induction m with
  | zero => simpa using isStrongAdmissible_one
  | succ m ih =>
    rw [pow_succ]
    exact isStrongAdmissible_mul ih hsq

/-! ### Section 4: Extracting the central coefficient and proving the main theorem -/

lemma coeff_X_pow_mul_one_add_X_pow (N j : ℕ) (hj : 2 * j ≤ 2 * N) :
    ((X : Polynomial ℤ) ^ j * (1 + X) ^ (2 * N - 2 * j)).coeff N =
      (Nat.centralBinom (N - j) : ℤ) := by
  have hjN : j ≤ N := by omega
  have h2 : 2 * N - 2 * j = 2 * (N - j) := by omega
  rw [h2, Polynomial.coeff_X_pow_mul', if_pos hjN]
  have hbin : ((1 + (X : Polynomial ℤ)) ^ (2 * (N - j))).coeff (N - j) =
      ((Nat.choose (2 * (N - j)) (N - j) : ℕ) : ℤ) := by
    rw [add_comm (1 : Polynomial ℤ) X, Polynomial.coeff_X_add_one_pow]
  rw [hbin, Nat.centralBinom_eq_two_mul_choose]

/-- The central coefficient `[x^(⌊(2^r - 1)n / 2⌋)] (1 + x + ... + x^(2^r - 1))^n` as a natural number. -/
noncomputable def centralPolyCoeff (r n : ℕ) : ℕ :=
  (((∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℕ) ^ i) ^ n)).coeff (((2 ^ r - 1) * n) / 2)

/-- OEIS A402341: central coefficient `[x^(⌊15n/2⌋)] (1 + x + ... + x^15)^n`. -/
noncomputable def a402341 (n : ℕ) : ℕ :=
  (((∑ i ∈ Finset.range 16, (X : Polynomial ℕ) ^ i) ^ n)).coeff ((15 * n) / 2)

lemma a402341_eq_centralPolyCoeff (n : ℕ) : a402341 n = centralPolyCoeff 4 n := by
  unfold a402341 centralPolyCoeff
  norm_num

lemma int_cast_centralPolyCoeff_even (r m : ℕ) :
    (centralPolyCoeff r (2 * m) : ℤ) =
      (((∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℤ) ^ i) ^ (2 * m))).coeff
        ((2 ^ r - 1) * m) := by
  unfold centralPolyCoeff
  have hidx : (2 ^ r - 1) * (2 * m) / 2 = (2 ^ r - 1) * m := by
    rw [show (2 ^ r - 1) * (2 * m) = 2 * ((2 ^ r - 1) * m) by ring,
      Nat.mul_div_right _ (by omega : 0 < 2)]
  rw [hidx]
  have hmap : Polynomial.map (Nat.castRingHom ℤ)
      ((∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℕ) ^ i) ^ (2 * m)) =
      (∑ i ∈ Finset.range (2 ^ r), (X : Polynomial ℤ) ^ i) ^ (2 * m) := by
    rw [Polynomial.map_pow, Polynomial.map_sum]
    simp
  rw [← hmap, Polynomial.coeff_map]
  rfl

/-- Central coefficient expansion in terms of `Q r ^ (2 * m)` and central binomial coefficients. -/
theorem centralPolyCoeff_even_eq_sum (r m : ℕ) :
    (centralPolyCoeff r (2 * m) : ℤ) =
      ∑ j ∈ (Q r ^ (2 * m)).support,
        (Q r ^ (2 * m)).coeff j * (Nat.centralBinom ((2 ^ r - 1) * m - j) : ℤ) := by
  set N := (2 ^ r - 1) * m
  rw [int_cast_centralPolyCoeff_even, ← evalY_Q r, ← evalY_pow (fitsDeg_Q r) (2 * m)]
  have hD : 2 * m * (2 ^ r - 1) = 2 * N := by ring
  rw [hD]
  unfold evalY
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  have hfits : 2 * j ≤ 2 * N := by
    have := fitsDeg_pow (fitsDeg_Q r) (2 * m) j hj
    omega
  rw [mul_assoc, Polynomial.coeff_C_mul, coeff_X_pow_mul_one_add_X_pow N j hfits]

/-- Strong congruence modulo `2^(s₂(N) + 1)`: the central coefficient of
`(1 + x + ... + x^(2^r - 1))^(2m)` is congruent to `binomial(2N, N)` modulo `2^(s₂(N) + 1)`. -/
theorem centralPolyCoeff_congr_centralBinom (r m : ℕ) :
    centralPolyCoeff r (2 * m) ≡ Nat.centralBinom ((2 ^ r - 1) * m)
      [MOD 2 ^ (popcount ((2 ^ r - 1) * m) + 1)] := by
  set N := (2 ^ r - 1) * m
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, centralPolyCoeff_even_eq_sum]
  have hSA := isStrongAdmissible_Q_pow_two_mul r m
  have h0mem : 0 ∈ (Q r ^ (2 * m)).support := by
    rw [Polynomial.mem_support_iff, hSA.1]; decide
  rw [← Finset.add_sum_erase _ _ h0mem, hSA.1, one_mul, Nat.sub_zero,
    show (Nat.centralBinom N : ℤ) -
      ((Nat.centralBinom N : ℤ) +
        ∑ j ∈ (Q r ^ (2 * m)).support.erase 0,
          (Q r ^ (2 * m)).coeff j * (Nat.centralBinom (N - j) : ℤ)) =
      -(∑ j ∈ (Q r ^ (2 * m)).support.erase 0,
        (Q r ^ (2 * m)).coeff j * (Nat.centralBinom (N - j) : ℤ)) by ring]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro j hj
  have hj_ne : j ≠ 0 := (Finset.mem_erase.mp hj).1
  have hj_supp : j ∈ (Q r ^ (2 * m)).support := (Finset.mem_erase.mp hj).2
  have hj_pos : 0 < j := Nat.pos_of_ne_zero hj_ne
  have hj_le : j ≤ N := by
    have hD : 2 * m * (2 ^ r - 1) = 2 * N := by ring
    have := fitsDeg_pow (fitsDeg_Q r) (2 * m) j hj_supp
    omega
  have hc : ((2 : ℤ) ^ (popcount j + 1)) ∣ (Q r ^ (2 * m)).coeff j := hSA.2 j hj_pos
  have hb : ((2 : ℤ) ^ popcount (N - j)) ∣ (Nat.centralBinom (N - j) : ℤ) := by
    exact_mod_cast two_pow_popcount_dvd_centralBinom (N - j)
  have hpop : popcount N + 1 ≤ (popcount j + 1) + popcount (N - j) := by
    have h1 := popcount_add_le j (N - j)
    rw [Nat.add_sub_of_le hj_le] at h1
    omega
  have hcast : ((2 ^ (popcount N + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (popcount N + 1) := by norm_cast
  rw [hcast]
  exact dvd_trans (pow_dvd_pow 2 hpop) (by rw [pow_add]; exact mul_dvd_mul hc hb)

/-- General theorem for every power-of-two block length `2^r` and every even exponent `2m`:
`v₂([x^((2^r - 1)m)] (1 + x + ... + x^(2^r - 1))^(2m)) = s₂((2^r - 1)m)`. -/
theorem padicValNat_centralPolyCoeff_even (r m : ℕ) :
    padicValNat 2 (centralPolyCoeff r (2 * m)) = popcount ((2 ^ r - 1) * m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (2 ^ r - 1) * m
  have hcong := centralPolyCoeff_congr_centralBinom r m
  have hmod_le : centralPolyCoeff r (2 * m) ≡ Nat.centralBinom N [MOD 2 ^ popcount N] :=
    hcong.of_dvd (pow_dvd_pow 2 (Nat.le_succ _))
  have hdvd : 2 ^ popcount N ∣ centralPolyCoeff r (2 * m) :=
    (Nat.ModEq.dvd_iff hmod_le dvd_rfl).mpr (two_pow_popcount_dvd_centralBinom N)
  have hndvd : ¬ (2 ^ (popcount N + 1) ∣ centralPolyCoeff r (2 * m)) := by
    intro h
    exact not_two_pow_popcount_succ_dvd_centralBinom N ((Nat.ModEq.dvd_iff hcong dvd_rfl).mp h)
  have hne : centralPolyCoeff r (2 * m) ≠ 0 := by
    intro hz
    rw [hz] at hndvd
    exact hndvd (dvd_zero _)
  have hge : popcount N ≤ padicValNat 2 (centralPolyCoeff r (2 * m)) :=
    (padicValNat_dvd_iff_le hne).mp hdvd
  have hlt : ¬ (popcount N + 1 ≤ padicValNat 2 (centralPolyCoeff r (2 * m))) := by
    intro h
    exact hndvd ((padicValNat_dvd_iff_le hne).mpr h)
  omega

/-- Complete proof of the OEIS A402341 conjecture (Sajid Khan Hussain, Nov 17 2026):
for every even `n ≥ 0`, the 2-adic valuation of the central coefficient of
`(1 + x + ... + x^15)^n` equals `A000120(15n/2)`. -/
theorem oeis_A402341_conjecture (n : ℕ) (hn : Even n) :
    padicValNat 2 (a402341 n) = (Nat.digits 2 (15 * n / 2)).sum := by
  rcases hn with ⟨m, rfl⟩
  rw [← two_mul, a402341_eq_centralPolyCoeff, padicValNat_centralPolyCoeff_even]
  have h15 : (2 ^ 4 - 1) * m = 15 * (2 * m) / 2 := by omega
  rw [h15]
  rfl

/-- Stronger congruence for OEIS A402341: for every even `n = 2m`,
`a402341(2m) ≡ binomial(30m, 15m) (mod 2^(A000120(15m) + 1))`. -/
theorem oeis_A402341_congr_centralBinom (m : ℕ) :
    a402341 (2 * m) ≡ Nat.centralBinom (15 * m)
      [MOD 2 ^ ((Nat.digits 2 (15 * m)).sum + 1)] := by
  rw [a402341_eq_centralPolyCoeff]
  simpa [popcount] using centralPolyCoeff_congr_centralBinom 4 m

end HussainA402341
