import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Disproof of John M. Campbell's OEIS A189409 Squarefree Conjecture

In OEIS A189409 (and `google-deepmind/formal-conjectures`,
`FormalConjectures/OEIS/189409.lean`, `OeisA189409.conjecture_1`),
John M. Campbell (Apr 21, 2011) asked whether every term of
`a n = (p_n#)^2 + 1` (where `p_n# = ∏ k ∈ Finset.range n, Nat.nth Nat.Prime k`
is the `n`-th primorial, OEIS A002110) is squarefree.

We disprove `∀ n : ℕ, Squarefree (a n)` and establish exact minimality:
1. `a 9 = (23#)^2 + 1 = 223092870^2 + 1 = 49770428644836901 = 29^2 * 53 * 1116604864937`
   is divisible by `29^2`, hence `¬ Squarefree (a 9)`.
2. Every earlier term `a 0, a 1, ..., a 8` is squarefree (with all large prime
   factors up to the 14-digit prime `a 8 = 94083986096101` certified via
   Lucas primality in the Lean kernel, without `native_decide`).
-/

namespace CampbellA189409

/-- Standalone Mathlib definition of the `n`-th primorial `p_n# = ∏_{k < n} p_k`
(OEIS A002110), matching `Nat.kthPrimorial` from `FormalConjectures/OEIS/189409.lean`. -/
noncomputable def kthPrimorial (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range n, Nat.nth Nat.Prime k

/-- Standalone Mathlib definition of OEIS A189409 (`a n = (p_n#)^2 + 1`),
equivalent to `OeisA189409.a` in `FormalConjectures/OEIS/189409.lean`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (kthPrimorial n) ^ 2 + 1

/-! ### Exact values of the first nine primes and `a 0` .. `a 9` -/

private theorem nth_prime_0 : Nat.nth Nat.Prime 0 = 2 := by
  have hc : Nat.count Nat.Prime 2 = 0 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 2)

private theorem nth_prime_1 : Nat.nth Nat.Prime 1 = 3 := by
  have hc : Nat.count Nat.Prime 3 = 1 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 3)

private theorem nth_prime_2 : Nat.nth Nat.Prime 2 = 5 := by
  have hc : Nat.count Nat.Prime 5 = 2 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 5)

private theorem nth_prime_3 : Nat.nth Nat.Prime 3 = 7 := by
  have hc : Nat.count Nat.Prime 7 = 3 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 7)

private theorem nth_prime_4 : Nat.nth Nat.Prime 4 = 11 := by
  have hc : Nat.count Nat.Prime 11 = 4 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 11)

private theorem nth_prime_5 : Nat.nth Nat.Prime 5 = 13 := by
  have hc : Nat.count Nat.Prime 13 = 5 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 13)

private theorem nth_prime_6 : Nat.nth Nat.Prime 6 = 17 := by
  have hc : Nat.count Nat.Prime 17 = 6 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 17)

private theorem nth_prime_7 : Nat.nth Nat.Prime 7 = 19 := by
  have hc : Nat.count Nat.Prime 19 = 7 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 19)

private theorem nth_prime_8 : Nat.nth Nat.Prime 8 = 23 := by
  have hc : Nat.count Nat.Prime 23 = 8 := by
    simp [Nat.count_succ]; norm_num
  rw [← hc]
  exact Nat.nth_count (by norm_num : Nat.Prime 23)

theorem kthPrimorial_0 : kthPrimorial 0 = 1 := by simp [kthPrimorial]
theorem kthPrimorial_1 : kthPrimorial 1 = 2 := by
  simp [kthPrimorial, nth_prime_0]
theorem kthPrimorial_2 : kthPrimorial 2 = 6 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1]
theorem kthPrimorial_3 : kthPrimorial 3 = 30 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2]
theorem kthPrimorial_4 : kthPrimorial 4 = 210 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3]
theorem kthPrimorial_5 : kthPrimorial 5 = 2310 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3,
    nth_prime_4]
theorem kthPrimorial_6 : kthPrimorial 6 = 30030 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3,
    nth_prime_4, nth_prime_5]
theorem kthPrimorial_7 : kthPrimorial 7 = 510510 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3,
    nth_prime_4, nth_prime_5, nth_prime_6]
theorem kthPrimorial_8 : kthPrimorial 8 = 9699690 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3,
    nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7]
theorem kthPrimorial_9 : kthPrimorial 9 = 223092870 := by
  simp [kthPrimorial, Finset.prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3,
    nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8]

theorem a_0 : a 0 = 2 := by simp [a, kthPrimorial_0]
theorem a_1 : a 1 = 5 := by simp [a, kthPrimorial_1]
theorem a_2 : a 2 = 37 := by simp [a, kthPrimorial_2]
theorem a_3 : a 3 = 901 := by simp [a, kthPrimorial_3]
theorem a_4 : a 4 = 44101 := by simp [a, kthPrimorial_4]
theorem a_5 : a 5 = 5336101 := by simp [a, kthPrimorial_5]
theorem a_6 : a 6 = 901800901 := by simp [a, kthPrimorial_6]
theorem a_7 : a 7 = 260620460101 := by simp [a, kthPrimorial_7]
theorem a_8 : a 8 = 94083986096101 := by simp [a, kthPrimorial_8]
theorem a_9 : a 9 = 49770428644836901 := by simp [a, kthPrimorial_9]

/-! ### Main disproof at `n = 9` -/

theorem a_9_not_squarefree : ¬ Squarefree (a 9) := by
  rw [a_9]
  intro hsq
  have hdvd : 29 * 29 ∣ 49770428644836901 := ⟨59180057841661, by norm_num⟩
  have hu : IsUnit (29 : ℕ) := hsq 29 hdvd
  rw [Nat.isUnit_iff] at hu
  omega

/-- Disproof of `OeisA189409.conjecture_1` (`∀ n : ℕ, Squarefree (a n)`). -/
theorem disproof_conjecture_1 : ¬ (∀ n : ℕ, Squarefree (a n)) := by
  intro hall
  exact a_9_not_squarefree (hall 9)

theorem a_9_factorization : a 9 = 29 ^ 2 * 53 * 1116604864937 := by
  rw [a_9]; norm_num

/-! ### Kernel-verified Lucas primality for exact minimality (`n < 9`) -/

/-- Structurally recursive binary modular exponentiation for fast kernel reduction. -/
private def modPowFuel : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      let half := modPowFuel fuel base (exp / 2) m
      let sq := (half * half) % m
      if exp % 2 = 0 then sq else (sq * base) % m

private theorem modPowFuel_eq (fuel base exp m : ℕ) (hfuel : exp < 2 ^ fuel) :
    modPowFuel fuel base exp m = base ^ exp % m := by
  induction fuel generalizing exp with
  | zero =>
    have he0 : exp = 0 := by omega
    subst he0; simp [modPowFuel]
  | succ f ih =>
    unfold modPowFuel
    split_ifs with he0 he2
    · subst he0; simp
    · have hlt : exp / 2 < 2 ^ f := by
        have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      rw [ih (exp / 2) hlt]
      have hdecomp : exp = exp / 2 + exp / 2 := by omega
      conv_rhs => rw [hdecomp, pow_add]
      rw [Nat.mul_mod]
    · have hlt : exp / 2 < 2 ^ f := by
        have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      rw [ih (exp / 2) hlt]
      have hdecomp : exp = exp / 2 + exp / 2 + 1 := by omega
      conv_rhs => rw [hdecomp, pow_succ, pow_add]
      simp [Nat.mul_mod]

private theorem zmod_pow_eq_one_of_modPow {p a e fuel : ℕ} [NeZero p]
    (hp : 1 < p) (hfuel : e < 2 ^ fuel) (h : modPowFuel fuel a e p = 1) :
    (a : ZMod p) ^ e = 1 := by
  have hm : a ^ e % p = 1 % p := by
    rw [← modPowFuel_eq fuel a e p hfuel, h, Nat.mod_eq_of_lt hp]
  have hcast : ((a ^ e : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hm
  simpa using hcast

private theorem zmod_pow_ne_one_of_modPow {p a e fuel : ℕ} [NeZero p]
    (hp : 1 < p) (hfuel : e < 2 ^ fuel) (h : modPowFuel fuel a e p ≠ 1) :
    (a : ZMod p) ^ e ≠ 1 := by
  intro heq
  have hcast : ((a ^ e : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using heq
  have hm : a ^ e % p = 1 % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  rw [Nat.mod_eq_of_lt hp, ← modPowFuel_eq fuel a e p hfuel] at hm
  exact h hm

private theorem prime_eq_of_prime_dvd_prime {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hd : q ∣ r) : q = r :=
  (hr.eq_one_or_self_of_dvd q hd).resolve_left hq.ne_one

private theorem prime_44101 : Nat.Prime 44101 := by
  apply lucas_primality 44101 (6 : ZMod 44101)
  · exact zmod_pow_eq_one_of_modPow (fuel := 20) (by decide) (by norm_num) (by decide)
  · intro q hq hdvd
    have hfac : 44101 - 1 = 2 ^ 2 * (3 ^ 2 * (5 ^ 2 * 7 ^ 2)) := by norm_num
    rw [hfac] at hdvd
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
      rcases hq.dvd_mul.mp hdvd with h2 | hrest
      · exact Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h2))
      · rcases hq.dvd_mul.mp hrest with h3 | hrest
        · exact Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h3)))
        · rcases hq.dvd_mul.mp hrest with h5 | h7
          · exact Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h5))))
          · exact Or.inr (Or.inr (Or.inr (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h7))))
    rcases hcases with rfl | rfl | rfl | rfl <;>
      exact zmod_pow_ne_one_of_modPow (fuel := 20) (by decide) (by norm_num) (by decide)

private theorem prime_5336101 : Nat.Prime 5336101 := by
  apply lucas_primality 5336101 (6 : ZMod 5336101)
  · exact zmod_pow_eq_one_of_modPow (fuel := 25) (by decide) (by norm_num) (by decide)
  · intro q hq hdvd
    have hfac : 5336101 - 1 = 2 ^ 2 * (3 ^ 2 * (5 ^ 2 * (7 ^ 2 * 11 ^ 2))) := by norm_num
    rw [hfac] at hdvd
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by
      rcases hq.dvd_mul.mp hdvd with h | h
      · exact Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))
      · rcases hq.dvd_mul.mp h with h | h
        · exact Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))
        · rcases hq.dvd_mul.mp h with h | h
          · exact Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))))
          · rcases hq.dvd_mul.mp h with h | h
            · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))))
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      exact zmod_pow_ne_one_of_modPow (fuel := 25) (by decide) (by norm_num) (by decide)

private theorem prime_12353437 : Nat.Prime 12353437 := by
  apply lucas_primality 12353437 (6 : ZMod 12353437)
  · exact zmod_pow_eq_one_of_modPow (fuel := 25) (by decide) (by norm_num) (by decide)
  · intro q hq hdvd
    have hfac : 12353437 - 1 = 2 ^ 2 * (3 ^ 2 * (409 * 839)) := by norm_num
    rw [hfac] at hdvd
    have hcases : q = 2 ∨ q = 3 ∨ q = 409 ∨ q = 839 := by
      rcases hq.dvd_mul.mp hdvd with h | h
      · exact Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))
      · rcases hq.dvd_mul.mp h with h | h
        · exact Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))
        · rcases hq.dvd_mul.mp h with h | h
          · exact Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) h)))
          · exact Or.inr (Or.inr (Or.inr (prime_eq_of_prime_dvd_prime hq (by norm_num) h)))
    rcases hcases with rfl | rfl | rfl | rfl <;>
      exact zmod_pow_ne_one_of_modPow (fuel := 25) (by decide) (by norm_num) (by decide)

private theorem prime_184968389 : Nat.Prime 184968389 := by
  apply lucas_primality 184968389 (2 : ZMod 184968389)
  · exact zmod_pow_eq_one_of_modPow (fuel := 30) (by decide) (by norm_num) (by decide)
  · intro q hq hdvd
    have hfac : 184968389 - 1 = 2 ^ 2 * (11 * (79 * (127 * 419))) := by norm_num
    rw [hfac] at hdvd
    have hcases : q = 2 ∨ q = 11 ∨ q = 79 ∨ q = 127 ∨ q = 419 := by
      rcases hq.dvd_mul.mp hdvd with h | h
      · exact Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))
      · rcases hq.dvd_mul.mp h with h | h
        · exact Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) h))
        · rcases hq.dvd_mul.mp h with h | h
          · exact Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) h)))
          · rcases hq.dvd_mul.mp h with h | h
            · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) h))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (prime_eq_of_prime_dvd_prime hq (by norm_num) h))))
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      exact zmod_pow_ne_one_of_modPow (fuel := 30) (by decide) (by norm_num) (by decide)

set_option maxRecDepth 2000 in
private theorem prime_94083986096101 : Nat.Prime 94083986096101 := by
  apply lucas_primality 94083986096101 (2 : ZMod 94083986096101)
  · exact zmod_pow_eq_one_of_modPow (fuel := 47) (by decide) (by norm_num) (by decide)
  · intro q hq hdvd
    have hfac : 94083986096101 - 1 =
        2 ^ 2 * (3 ^ 2 * (5 ^ 2 * (7 ^ 2 * (11 ^ 2 * (13 ^ 2 * (17 ^ 2 * 19 ^ 2)))))) := by
      norm_num
    rw [hfac] at hdvd
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 := by
      rcases hq.dvd_mul.mp hdvd with h | h
      · exact Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))
      · rcases hq.dvd_mul.mp h with h | h
        · exact Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))
        · rcases hq.dvd_mul.mp h with h | h
          · exact Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))))
          · rcases hq.dvd_mul.mp h with h | h
            · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))))
            · rcases hq.dvd_mul.mp h with h | h
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))))))
              · rcases hq.dvd_mul.mp h with h | h
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h)))))))
                · rcases hq.dvd_mul.mp h with h | h
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))))))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prime_eq_of_prime_dvd_prime hq (by norm_num) (hq.dvd_of_dvd_pow h))))))))
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact zmod_pow_ne_one_of_modPow (fuel := 47) (by decide) (by norm_num) (by decide)

private theorem squarefree_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Squarefree (p * q) := by
  rw [Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr fun h =>
    hne (prime_eq_of_prime_dvd_prime hp hq h))]
  exact ⟨hp.squarefree, hq.squarefree⟩

/-- Every term `a n` for `n < 9` is squarefree. -/
theorem squarefree_lt_9 : ∀ n < 9, Squarefree (a n) := by
  intro n hn
  interval_cases n
  · rw [a_0]; exact (by norm_num : Nat.Prime 2).squarefree
  · rw [a_1]; exact (by norm_num : Nat.Prime 5).squarefree
  · rw [a_2]; exact (by norm_num : Nat.Prime 37).squarefree
  · rw [a_3]
    have : (901 : ℕ) = 17 * 53 := by norm_num
    rw [this]
    exact squarefree_mul_of_primes (by norm_num) (by norm_num) (by decide)
  · rw [a_4]; exact prime_44101.squarefree
  · rw [a_5]; exact prime_5336101.squarefree
  · rw [a_6]
    have : (901800901 : ℕ) = 73 * 12353437 := by norm_num
    rw [this]
    exact squarefree_mul_of_primes (by norm_num) prime_12353437 (by decide)
  · rw [a_7]
    have : (260620460101 : ℕ) = 1409 * 184968389 := by norm_num
    rw [this]
    exact squarefree_mul_of_primes (by norm_num) prime_184968389 (by decide)
  · rw [a_8]; exact prime_94083986096101.squarefree

/-- Exact minimality theorem: `n = 9` is the smallest counterexample to `OeisA189409.conjecture_1`. -/
theorem minimal_counterexample :
    ¬ Squarefree (a 9) ∧ ∀ n < 9, Squarefree (a n) :=
  ⟨a_9_not_squarefree, squarefree_lt_9⟩

end CampbellA189409
