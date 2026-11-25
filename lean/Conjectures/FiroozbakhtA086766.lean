import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Disproof of Farideh Firoozbakht's OEIS A086766 Conjecture

For `n > 0`, let `d = (Nat.digits 10 n).length` and
`primeCandidate n r = (n * ∑ i ∈ Finset.range r, (10 ^ d) ^ i) * 10 + 1`.
In OEIS A086766 (and `google-deepmind/formal-conjectures`,
`FormalConjectures/OEIS/86766.lean`, `OeisA86766.conjecture2`),
Farideh Firoozbakht (Jan 7, 2015) conjectured that if `n > 0` is not of the
form `10 ^ m`, then `a n ≠ 0` (i.e., some `r > 0` makes `primeCandidate n r` prime).

We disprove this conjecture with:
1. An explicit infinite family `n_k = 10 * (10 ^ (2 * k) - 1) / 99` for all `k ≥ 2`,
   whose smallest member is `n = 1010` (`k = 2`).
2. A general algebraic difference-of-squares theorem yielding primitive (non-periodic)
   counterexamples, instantiated on the minimal primitive 6-digit witness `n = 104040`
   and the 78-digit primitive witness
   `n = 100558839880907801793259217884670002826017800775406752876641328923179557019040`.
-/

namespace FiroozbakhtA086766

/-- Verbatim definition from `FormalConjectures/OEIS/86766.lean`:
the candidate prime obtained by concatenating `n` with itself `r` times,
multiplying by 10, and adding 1. -/
def primeCandidate (n r : ℕ) : ℕ :=
  let ℓ : ℕ := (Nat.digits 10 n).length
  let M : ℕ := 10 ^ ℓ
  (n * ∑ i ∈ Finset.range r, M ^ i) * 10 + 1

/-- Verbatim definition of OEIS A086766 from `FormalConjectures/OEIS/86766.lean`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {r : ℕ | 0 < r ∧ (primeCandidate n r).Prime}

private theorem a_eq_zero_of_all_not_prime {n : ℕ}
    (h : ∀ r : ℕ, 0 < r → ¬ (primeCandidate n r).Prime) : a n = 0 := by
  unfold a
  split_ifs with hn
  · rfl
  · have hemp : {r : ℕ | 0 < r ∧ (primeCandidate n r).Prime} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact h r
    rw [hemp, Nat.sInf_empty]

private theorem digits_length_eq {n d : ℕ} (hd : 1 ≤ d)
    (hlo : 10 ^ (d - 1) ≤ n) (hhi : n < 10 ^ d) :
    (Nat.digits 10 n).length = d := by
  have hn0 : n ≠ 0 := by
    have : 0 < 10 ^ (d - 1) := by positivity
    omega
  rw [Nat.length_digits 10 n (by decide) hn0]
  have hlog : Nat.log 10 n = d - 1 := by
    apply Nat.log_eq_of_pow_le_of_lt_pow hlo
    rwa [Nat.sub_add_cancel hd]
  omega

private theorem geom_sum_mul_pred (M r : ℕ) (hM : 1 ≤ M) :
    (∑ i ∈ Finset.range r, M ^ i) * (M - 1) = M ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : 1 ≤ M ^ r := Nat.one_le_pow r M hM
    have h2 : M ^ r ≤ M ^ r * M := Nat.le_mul_of_pos_right _ hM
    zify [hM, h1, h2, Nat.one_le_pow (r + 1) M hM]
    ring

private theorem primeCandidate_mul_sub_one {n d : ℕ} (hdig : (Nat.digits 10 n).length = d)
    (r : ℕ) :
    primeCandidate n r * (10 ^ d - 1) = 10 * n * 10 ^ (d * r) + (10 ^ d - 1) - 10 * n := by
  unfold primeCandidate
  rw [hdig]
  have hM : 1 ≤ 10 ^ d := Nat.one_le_pow d 10 (by decide)
  have hgeom := geom_sum_mul_pred (10 ^ d) r hM
  have hpow : (10 ^ d) ^ r = 10 ^ (d * r) := (pow_mul 10 d r).symm
  have hcalc : (n * ∑ i ∈ Finset.range r, (10 ^ d) ^ i) * 10 * (10 ^ d - 1) =
      10 * n * (10 ^ (d * r) - 1) := by
    calc (n * ∑ i ∈ Finset.range r, (10 ^ d) ^ i) * 10 * (10 ^ d - 1)
        = 10 * n * ((∑ i ∈ Finset.range r, (10 ^ d) ^ i) * (10 ^ d - 1)) := by ring
      _ = 10 * n * ((10 ^ d) ^ r - 1) := by rw [hgeom]
      _ = 10 * n * (10 ^ (d * r) - 1) := by rw [hpow]
  rw [add_mul, one_mul, hcalc]
  have h1 : 1 ≤ 10 ^ (d * r) := Nat.one_le_pow (d * r) 10 (by decide)
  have hle : 10 * n ≤ 10 * n * 10 ^ (d * r) := Nat.le_mul_of_pos_right _ h1
  have hadd : 10 * n ≤ 10 * n * 10 ^ (d * r) + (10 ^ d - 1) := le_trans hle (Nat.le_add_right _ _)
  zify [hM, h1, hadd]
  ring

private theorem not_prime_of_mul_eq {N M' A B g1 g2 : ℕ}
    (hM' : M' = g1 * g2) (_hM'pos : 0 < M')
    (hprod : N * M' = A * B)
    (hd1 : g1 ∣ A) (hd2 : g2 ∣ B)
    (hA : g1 < A) (hB : g2 < B) : ¬ N.Prime := by
  obtain ⟨q1, hq1⟩ := hd1
  obtain ⟨q2, hq2⟩ := hd2
  have hg1pos : 0 < g1 := by
    rcases Nat.eq_zero_or_pos g1 with rfl | hp
    · simp at hM'; omega
    · exact hp
  have hg2pos : 0 < g2 := by
    rcases Nat.eq_zero_or_pos g2 with rfl | hp
    · simp at hM'; omega
    · exact hp
  have hq1_gt : 1 < q1 := by nlinarith
  have hq2_gt : 1 < q2 := by nlinarith
  have hN : N = q1 * q2 := by
    have hmul : N * (g1 * g2) = (q1 * q2) * (g1 * g2) := by
      calc N * (g1 * g2) = N * M' := by rw [← hM']
        _ = A * B := hprod
        _ = (g1 * q1) * (g2 * q2) := by rw [hq1, hq2]
        _ = (q1 * q2) * (g1 * g2) := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hg1pos hg2pos) hmul
  rw [hN]
  exact Nat.not_prime_mul (by omega) (by omega)

private theorem dvd_sub_of_modEq_of_dvd {a b e g : ℕ}
    (h : a ≡ b [MOD g]) (he1 : e ≤ a) (he2 : e ≤ b) (hd : g ∣ b - e) : g ∣ a - e := by
  have hZ : (a : ℤ) ≡ (b : ℤ) [ZMOD (g : ℤ)] := by
    change (a : ℤ) % (g : ℤ) = (b : ℤ) % (g : ℤ)
    exact_mod_cast h
  have hsub : (a : ℤ) - (e : ℤ) ≡ (b : ℤ) - (e : ℤ) [ZMOD (g : ℤ)] := hZ.sub_right (e : ℤ)
  have hdZ : (g : ℤ) ∣ ((b : ℤ) - (e : ℤ)) := by
    rw [← Nat.cast_sub he2]
    exact Int.natCast_dvd_natCast.mpr hd
  have h0 : (b : ℤ) - (e : ℤ) ≡ 0 [ZMOD (g : ℤ)] := Int.modEq_zero_iff_dvd.mpr hdZ
  have ha0 : (g : ℤ) ∣ ((a : ℤ) - (e : ℤ)) := Int.modEq_zero_iff_dvd.mp (hsub.trans h0)
  rw [← Nat.cast_sub he1] at ha0
  exact Int.natCast_dvd_natCast.mp ha0

private theorem dvd_add_of_modEq_of_dvd {a b e g : ℕ}
    (h : a ≡ b [MOD g]) (hd : g ∣ b + e) : g ∣ a + e :=
  Nat.modEq_zero_iff_dvd.mp ((h.add_right e).trans (Nat.modEq_zero_iff_dvd.mpr hd))

/-! ### Part 1: Infinite Family `n_k = 10 * (10^(2k) - 1) / 99` (`k ≥ 2`) -/

private theorem dvd_99_ten_pow_two_mul (k : ℕ) : 99 ∣ 10 ^ (2 * k) - 1 := by
  have h100 : (100 : ℕ) ^ k ≡ 1 ^ k [MOD 99] := Nat.ModEq.pow k (by decide : 100 ≡ 1 [MOD 99])
  rw [one_pow, show (100 : ℕ) ^ k = 10 ^ (2 * k) by rw [pow_mul]; norm_num] at h100
  have h1 : 1 ≤ 10 ^ (2 * k) := Nat.one_le_pow _ 10 (by decide)
  exact (Nat.modEq_iff_dvd' h1).mp h100.symm

private theorem dvd_9_ten_pow_sub_one (m : ℕ) : 9 ∣ 10 ^ m - 1 := by
  have h : (10 : ℕ) ^ m ≡ 1 ^ m [MOD 9] := Nat.ModEq.pow m (by decide : 10 ≡ 1 [MOD 9])
  rw [one_pow] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow m 10 (by decide))).mp h.symm

private theorem dvd_11_ten_pow_odd_add_one (j : ℕ) : 11 ∣ 10 ^ (2 * j + 1) + 1 := by
  have h100 : (100 : ℤ) ^ j ≡ 1 ^ j [ZMOD 11] := Int.ModEq.pow j (by decide : (100 : ℤ) ≡ 1 [ZMOD 11])
  have hmul : (100 : ℤ) ^ j * 10 ≡ 1 * 10 [ZMOD 11] := by
    simpa [one_pow] using h100.mul_right 10
  have hadd : (100 : ℤ) ^ j * 10 + 1 ≡ 10 + 1 [ZMOD 11] := hmul.add_right 1
  have hz : (11 : ℤ) ∣ ((10 : ℤ) ^ (2 * j + 1) + 1) := by
    have h11 : (10 + 1 : ℤ) ≡ 0 [ZMOD 11] := by decide
    have h0 := hadd.trans h11
    rw [Int.modEq_zero_iff_dvd] at h0
    have heq : (100 : ℤ) ^ j * 10 + 1 = (10 : ℤ) ^ (2 * j + 1) + 1 := by
      rw [pow_succ, pow_mul]; norm_num
    rwa [← heq]
  exact_mod_cast hz

/-- The explicit infinite counterexample family: `n_k = 10 * (10^(2k) - 1) / 99` (`1010`, `101010`, ...). -/
def rep10 (k : ℕ) : ℕ := 10 * ((10 ^ (2 * k) - 1) / 99)

theorem rep10_eq_1010 : rep10 2 = 1010 := by decide

theorem rep10_digits (k : ℕ) (hk : 2 ≤ k) : (Nat.digits 10 (rep10 k)).length = 2 * k := by
  have hdvd := dvd_99_ten_pow_two_mul k
  have hmul : 99 * ((10 ^ (2 * k) - 1) / 99) = 10 ^ (2 * k) - 1 := Nat.mul_div_cancel' hdvd
  have h1 : 100 ≤ 10 ^ (2 * k) := by
    calc 100 = 10 ^ 2 := by norm_num
      _ ≤ 10 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmul1 : 99 * ((10 ^ (2 * k) - 1) / 99) + 1 = 10 ^ (2 * k) := by omega
  have hten : 10 * 10 ^ (2 * k - 1) = 10 ^ (2 * k) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  apply digits_length_eq (by omega)
  · unfold rep10; omega
  · unfold rep10; omega

theorem rep10_ne_ten_pow (k : ℕ) (hk : 2 ≤ k) (m : ℕ) : rep10 k ≠ 10 ^ m := by
  intro heq
  have hlen := rep10_digits k hk
  rw [heq] at hlen
  have h10len : (Nat.digits 10 (10 ^ m)).length = m + 1 := by
    apply digits_length_eq (by omega)
    · simp
    · exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hm : m = 2 * k - 1 := by omega
  subst hm
  have hdvd := dvd_99_ten_pow_two_mul k
  have hmul : 99 * ((10 ^ (2 * k) - 1) / 99) = 10 ^ (2 * k) - 1 := Nat.mul_div_cancel' hdvd
  have h1 : 10000 ≤ 10 ^ (2 * k) := by
    calc 10000 = 10 ^ 4 := by norm_num
      _ ≤ 10 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmul1 : 99 * ((10 ^ (2 * k) - 1) / 99) + 1 = 10 ^ (2 * k) := by omega
  have hten : 10 * 10 ^ (2 * k - 1) = 10 ^ (2 * k) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  unfold rep10 at heq
  omega

theorem a_rep10_eq_zero (k : ℕ) (hk : 2 ≤ k) : a (rep10 k) = 0 := by
  apply a_eq_zero_of_all_not_prime
  intro r hr
  have hdig := rep10_digits k hk
  have hbase := primeCandidate_mul_sub_one hdig r
  have hdvd := dvd_99_ten_pow_two_mul k
  set q := (10 ^ (2 * k) - 1) / 99
  have hq : 99 * q = 10 ^ (2 * k) - 1 := Nat.mul_div_cancel' hdvd
  have hqpos : 0 < q := by
    have : 10000 ≤ 10 ^ (2 * k) := by
      calc 10000 = 10 ^ 4 := by norm_num
        _ ≤ 10 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h1 : 1 ≤ 10 ^ (2 * k * r) := Nat.one_le_pow _ 10 (by decide)
  have h99 : primeCandidate (rep10 k) r * 99 = 10 ^ (2 * (k * r + 1)) - 1 := by
    have hmul : primeCandidate (rep10 k) r * (99 * q) = (10 ^ (2 * (k * r + 1)) - 1) * q := by
      have h10 : 10 * rep10 k = 100 * q := by unfold rep10; ring
      have h2kr : 10 ^ (2 * (k * r + 1)) = 100 * 10 ^ (2 * k * r) := by
        rw [show 2 * (k * r + 1) = 2 * k * r + 2 by ring, pow_add]; ring
      have hsub1 : 10 * rep10 k ≤ 10 * rep10 k * 10 ^ (2 * k * r) :=
        Nat.le_mul_of_pos_right _ h1
      have hadd1 : 10 * rep10 k ≤ 10 * rep10 k * 10 ^ (2 * k * r) + (10 ^ (2 * k) - 1) :=
        le_trans hsub1 (Nat.le_add_right _ _)
      have hsub2 : 1 ≤ 10 ^ (2 * (k * r + 1)) := Nat.one_le_pow _ 10 (by decide)
      rw [hq, hbase]
      zify [hadd1, hsub2, Nat.one_le_pow (2 * k) 10 (by decide)]
      have h10Z : (10 * rep10 k : ℤ) = 100 * q := by exact_mod_cast h10
      have hqZ : ((10 ^ (2 * k) - 1 : ℕ) : ℤ) = 99 * q := by exact_mod_cast hq.symm
      rw [Nat.cast_sub (Nat.one_le_pow (2 * k) 10 (by decide))] at hqZ
      have h2krZ : (10 : ℤ) ^ (2 * (k * r + 1)) = 100 * (10 : ℤ) ^ (2 * k * r) := by
        exact_mod_cast h2kr
      have h10Z' : 10 * (rep10 k : ℤ) = 100 * (q : ℤ) := by simpa using h10Z
      have hqZ' : (10 : ℤ) ^ (2 * k) - 1 = 99 * (q : ℤ) := by simpa using hqZ
      rw [h10Z', hqZ', h2krZ]
      ring
    have hmul' : (primeCandidate (rep10 k) r * 99) * q = (10 ^ (2 * (k * r + 1)) - 1) * q := by
      linarith [hmul]
    exact Nat.eq_of_mul_eq_mul_right hqpos hmul'
  have hdiff : 10 ^ (2 * (k * r + 1)) - 1 = (10 ^ (k * r + 1) - 1) * (10 ^ (k * r + 1) + 1) := by
    have h1' : 1 ≤ 10 ^ (k * r + 1) := Nat.one_le_pow _ 10 (by decide)
    have h2' : 1 ≤ 10 ^ (2 * (k * r + 1)) := Nat.one_le_pow _ 10 (by decide)
    zify [h1', h2']
    rw [show 2 * (k * r + 1) = (k * r + 1) + (k * r + 1) by ring, pow_add]
    ring
  rw [hdiff] at h99
  have hkr3 : 3 ≤ k * r + 1 := by nlinarith
  have h10ge : 1000 ≤ 10 ^ (k * r + 1) := by
    calc 1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ (k * r + 1) := Nat.pow_le_pow_right (by decide) hkr3
  rcases Nat.even_or_odd (k * r) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hodd : k * r + 1 = 2 * j + 1 := by omega
    apply not_prime_of_mul_eq (M' := 99) (g1 := 9) (g2 := 11) (by decide) (by decide) h99
    · exact dvd_9_ten_pow_sub_one (k * r + 1)
    · rw [hodd]; exact dvd_11_ten_pow_odd_add_one j
    · omega
    · omega
  · have heven : k * r + 1 = 2 * (j + 1) := by omega
    apply not_prime_of_mul_eq (M' := 99) (g1 := 99) (g2 := 1) (by decide) (by decide) h99
    · rw [heven]; exact dvd_99_ten_pow_two_mul (j + 1)
    · exact one_dvd _
    · omega
    · omega

/-- Minimal 4-digit disproof of Firoozbakht's OEIS A086766 conjecture (`n = 1010`). -/
theorem disproof_minimal_1010 :
    0 < (1010 : ℕ) ∧ (∀ m : ℕ, (1010 : ℕ) ≠ 10 ^ m) ∧ a 1010 = 0 :=
  ⟨by decide, fun m => rep10_eq_1010 ▸ rep10_ne_ten_pow 2 le_rfl m,
    rep10_eq_1010 ▸ a_rep10_eq_zero 2 le_rfl⟩

/-- Infinite family of disproofs of Firoozbakht's OEIS A086766 conjecture. -/
theorem disproof_infinite_family (k : ℕ) (hk : 2 ≤ k) :
    0 < rep10 k ∧ (∀ m : ℕ, rep10 k ≠ 10 ^ m) ∧ a (rep10 k) = 0 := by
  refine ⟨?_, rep10_ne_ten_pow k hk, a_rep10_eq_zero k hk⟩
  have hdig := rep10_digits k hk
  by_contra h0
  have : rep10 k = 0 := by omega
  rw [this] at hdig
  simp at hdig
  omega

/-! ### Part 2: General Primitive Difference-of-Squares Family & Giant 78-Digit Witness -/

/-- General algebraic theorem producing primitive (non-periodic) counterexamples
to OEIS A086766 for any even digit length `d = 2k`. -/
theorem a_eq_zero_of_diff_squares {n k c e g1o g2o g1e g2e : ℕ}
    (hk : 1 ≤ k)
    (hlo : 10 ^ (2 * k - 1) ≤ n) (hhi : n < 10 ^ (2 * k))
    (hce : 10 * n = c ^ 2)
    (hM : c ^ 2 - e ^ 2 = 10 ^ (2 * k) - 1)
    (he_lt : e < c)
    (hgo : g1o * g2o = 10 ^ (2 * k) - 1)
    (hge : g1e * g2e = 10 ^ (2 * k) - 1)
    (ho1 : g1o ∣ c * 10 ^ k - e) (ho2 : g2o ∣ c * 10 ^ k + e)
    (he1 : g1e ∣ c - e) (he2 : g2e ∣ c + e)
    (hgt_o1 : g1o < c * 10 ^ k - e) (hgt_o2 : g2o < c * 10 ^ k + e)
    (hgt_e1 : g1e < c * 10 ^ (2 * k) - e) (hgt_e2 : g2e < c * 10 ^ (2 * k) + e) :
    a n = 0 := by
  apply a_eq_zero_of_all_not_prime
  intro r hr
  have hdig : (Nat.digits 10 n).length = 2 * k := digits_length_eq (by omega) hlo hhi
  have hbase := primeCandidate_mul_sub_one hdig r
  set M := 10 ^ (2 * k) - 1
  have hMpos : 0 < M := by
    have : 100 ≤ 10 ^ (2 * k) := by
      calc 100 = 10 ^ 2 := by norm_num
        _ ≤ 10 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h1kr : 1 ≤ 10 ^ (k * r) := Nat.one_le_pow _ 10 (by decide)
  have he_le_c10 : e ≤ c * 10 ^ (k * r) := le_trans he_lt.le (Nat.le_mul_of_pos_right c h1kr)
  have hprod : primeCandidate n r * M = (c * 10 ^ (k * r) - e) * (c * 10 ^ (k * r) + e) := by
    rw [hbase]
    have h10n_le : 10 * n ≤ 10 * n * 10 ^ (2 * k * r) :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ 10 (by decide))
    have hadd_le : 10 * n ≤ 10 * n * 10 ^ (2 * k * r) + M :=
      le_trans h10n_le (Nat.le_add_right _ _)
    have he2_le : e ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left he_lt.le 2
    have hpow : (10 : ℤ) ^ (2 * k * r) = ((10 : ℤ) ^ (k * r)) ^ 2 := by
      rw [← pow_mul, show k * r * 2 = 2 * k * r by ring]
    zify [hadd_le, he_le_c10]
    have hceZ : (10 : ℤ) * (n : ℤ) = (c : ℤ) ^ 2 := by exact_mod_cast hce
    have hMZ : (M : ℤ) = (c : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
      have hMZ' : ((c ^ 2 - e ^ 2 : ℕ) : ℤ) = (M : ℤ) := by exact_mod_cast hM
      rw [Nat.cast_sub he2_le] at hMZ'
      simpa using hMZ'.symm
    rw [hceZ, hMZ, hpow]
    ring
  have hmodM : ∀ j : ℕ, 10 ^ (2 * k * j) ≡ 1 [MOD M] := by
    intro j
    have h1 : 1 ≤ 10 ^ (2 * k) := Nat.one_le_pow _ 10 (by decide)
    have hstep : 10 ^ (2 * k) ≡ 1 [MOD M] := ((Nat.modEq_iff_dvd' h1).mpr dvd_rfl).symm
    have hpow := Nat.ModEq.pow j hstep
    rwa [← pow_mul, one_pow] at hpow
  rcases Nat.even_or_odd r with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj1 : 1 ≤ j := by omega
    have hkr : k * r = 2 * k * j := by rw [hj]; ring
    have hmod_g1 : 10 ^ (k * r) ≡ 1 [MOD g1e] := by
      rw [hkr]
      exact (hmodM j).of_dvd ⟨g2e, hge.symm⟩
    have hmod_g2 : 10 ^ (k * r) ≡ 1 [MOD g2e] := by
      rw [hkr]
      exact (hmodM j).of_dvd ⟨g1e, by rw [mul_comm]; exact hge.symm⟩
    have hd1 : g1e ∣ c * 10 ^ (k * r) - e :=
      dvd_sub_of_modEq_of_dvd (by simpa using hmod_g1.mul_left c) he_le_c10 he_lt.le he1
    have hd2 : g2e ∣ c * 10 ^ (k * r) + e :=
      dvd_add_of_modEq_of_dvd (by simpa using hmod_g2.mul_left c) he2
    have hpow_ge : 10 ^ (2 * k) ≤ 10 ^ (k * r) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    apply not_prime_of_mul_eq hge.symm hMpos hprod hd1 hd2
    · have : c * 10 ^ (2 * k) ≤ c * 10 ^ (k * r) := Nat.mul_le_mul_left c hpow_ge
      omega
    · have : c * 10 ^ (2 * k) ≤ c * 10 ^ (k * r) := Nat.mul_le_mul_left c hpow_ge
      omega
  · have hkr : k * r = 2 * k * j + k := by rw [hj]; ring
    have hmod_g1 : 10 ^ (k * r) ≡ 10 ^ k [MOD g1o] := by
      rw [hkr, pow_add]
      simpa using ((hmodM j).of_dvd ⟨g2o, hgo.symm⟩).mul_right (10 ^ k)
    have hmod_g2 : 10 ^ (k * r) ≡ 10 ^ k [MOD g2o] := by
      rw [hkr, pow_add]
      simpa using ((hmodM j).of_dvd ⟨g1o, by rw [mul_comm]; exact hgo.symm⟩).mul_right (10 ^ k)
    have h1k : e ≤ c * 10 ^ k :=
      le_trans he_lt.le (Nat.le_mul_of_pos_right c (Nat.one_le_pow k 10 (by decide)))
    have hd1 : g1o ∣ c * 10 ^ (k * r) - e :=
      dvd_sub_of_modEq_of_dvd (hmod_g1.mul_left c) he_le_c10 h1k ho1
    have hd2 : g2o ∣ c * 10 ^ (k * r) + e :=
      dvd_add_of_modEq_of_dvd (hmod_g2.mul_left c) ho2
    have hpow_ge : 10 ^ k ≤ 10 ^ (k * r) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    apply not_prime_of_mul_eq hgo.symm hMpos hprod hd1 hd2
    · have : c * 10 ^ k ≤ c * 10 ^ (k * r) := Nat.mul_le_mul_left c hpow_ge
      omega
    · have : c * 10 ^ k ≤ c * 10 ^ (k * r) := Nat.mul_le_mul_left c hpow_ge
      omega

private theorem ne_ten_pow_of_lt_of_gt {n d : ℕ} (hd : 1 ≤ d)
    (hlo : 10 ^ (d - 1) < n) (hhi : n < 10 ^ d) (m : ℕ) : n ≠ 10 ^ m := by
  intro h
  subst h
  have h1 : d - 1 < m := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp hlo
  have h2 : m < d := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp hhi
  omega

/-- Minimal primitive (non-periodic) 6-digit counterexample: `n = 104040`. -/
theorem disproof_primitive_104040 :
    0 < (104040 : ℕ) ∧ (∀ m : ℕ, (104040 : ℕ) ≠ 10 ^ m) ∧ a 104040 = 0 := by
  refine ⟨by norm_num, ne_ten_pow_of_lt_of_gt (d := 6) (by decide) (by norm_num) (by norm_num), ?_⟩
  exact a_eq_zero_of_diff_squares (k := 3) (c := 1020) (e := 201)
    (g1o := 99) (g2o := 10101) (g1e := 819) (g2e := 1221)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Giant 78-digit primitive counterexample to Firoozbakht's OEIS A086766 conjecture. -/
def giant78 : ℕ :=
  100558839880907801793259217884670002826017800775406752876641328923179557019040

theorem disproof_giant78 :
    0 < giant78 ∧ (∀ m : ℕ, giant78 ≠ 10 ^ m) ∧ a giant78 = 0 := by
  refine ⟨by norm_num [giant78],
    ne_ten_pow_of_lt_of_gt (d := 78) (by decide) (by norm_num [giant78]) (by norm_num [giant78]), ?_⟩
  exact a_eq_zero_of_diff_squares (k := 39)
    (c := 1002790306499358826910734486514389551480)
    (e := 74755593831351630382001287234042424799)
    (g1o := 82858281)
    (g2o := 12068799737711189060270270390958267647382160872972974179852946744091879)
    (g1e := 928034712668007196528733199280347126681)
    (g2e := 1077545900330710457292735773748431976279)
    (by norm_num) (by norm_num [giant78]) (by norm_num [giant78])
    (by norm_num [giant78]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms disproof_minimal_1010
#print axioms disproof_infinite_family
#print axioms disproof_primitive_104040
#print axioms disproof_giant78

end FiroozbakhtA086766
