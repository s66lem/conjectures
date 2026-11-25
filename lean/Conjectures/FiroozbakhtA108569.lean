import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Disproof of Firoozbakht's OEIS A108569 Parity Conjecture

Refutes Farideh Firoozbakht's conjecture (OEIS A108569; `FormalConjectures/OEIS/108569.lean`):
except for `n = 1`, every positive integer solution to `φ(n) = φ(n + φ(n))` is even.

We exhibit the odd counterexample `n = 5095354107 = 3 * 1033 * 1644193` and prove the
infinite odd family `n_j = 3^j * 5095354107` for all `j : ℕ`.
-/

namespace FiroozbakhtA108569

def baseN : ℕ := 5095354107

private theorem prime_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_327317 : Nat.Prime 327317 := by norm_num
private theorem prime_1644193 : Nat.Prime 1644193 := by norm_num

theorem totient_baseN : Nat.totient baseN = 3393612288 := by
  have hfac : baseN = 3 * (1033 * 1644193) := by norm_num [baseN]
  have h1 : Nat.Coprime 3 (1033 * 1644193) := by decide
  have h2 : Nat.Coprime 1033 1644193 := by decide
  rw [hfac, Nat.totient_mul h1, Nat.totient_mul h2]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime prime_1033,
      Nat.totient_prime prime_1644193]

theorem totient_baseN_add : Nat.totient (baseN + Nat.totient baseN) = 3393612288 := by
  rw [totient_baseN]
  have hfac : baseN + 3393612288 = 3 * (5 * (7 * (13 * (19 * 327317)))) := by
    norm_num [baseN]
  rw [hfac]
  rw [Nat.totient_mul (by decide),
      Nat.totient_mul (by decide),
      Nat.totient_mul (by decide),
      Nat.totient_mul (by decide),
      Nat.totient_mul (by decide)]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 5),
      Nat.totient_prime (by norm_num : Nat.Prime 7),
      Nat.totient_prime (by norm_num : Nat.Prime 13),
      Nat.totient_prime (by norm_num : Nat.Prime 19),
      Nat.totient_prime prime_327317]

/-- Base counterexample: `n = 5095354107` is odd, `> 1`, and satisfies `φ(n) = φ(n + φ(n))`. -/
theorem baseN_counterexample :
    1 < baseN ∧ ¬ Even baseN ∧ Nat.totient baseN = Nat.totient (baseN + Nat.totient baseN) := by
  refine ⟨by norm_num [baseN], ?_, ?_⟩
  · rw [Nat.not_even_iff_odd]; exact ⟨2547677053, by norm_num [baseN]⟩
  · rw [totient_baseN_add, totient_baseN]

/-- Direct refutation of the OEIS A108569 parity conjecture. -/
theorem disproof_oeis_a108569 :
    ¬ (∀ n : ℕ, 1 < n → Nat.totient n = Nat.totient (n + Nat.totient n) → Even n) := by
  intro h
  exact baseN_counterexample.2.1 (h baseN baseN_counterexample.1 baseN_counterexample.2.2)

private theorem totient_three_mul_of_dvd {m : ℕ} (hm : 3 ∣ m) :
    Nat.totient (3 * m) = 3 * Nat.totient m := by
  simpa using Nat.totient_mul_of_prime_of_dvd (by norm_num : Nat.Prime 3) hm

private theorem totient_three_pow_mul (j : ℕ) {m : ℕ} (hm : 3 ∣ m) :
    Nat.totient (3 ^ j * m) = 3 ^ j * Nat.totient m := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, totient_three_mul_of_dvd (dvd_mul_of_dvd_right hm _), ih]
    ring

/-- Infinite family of odd counterexamples: `n_j = 3^j * 5095354107`. -/
theorem infinite_odd_family (j : ℕ) :
    1 < 3 ^ j * baseN ∧ ¬ Even (3 ^ j * baseN) ∧
      Nat.totient (3 ^ j * baseN) =
        Nat.totient (3 ^ j * baseN + Nat.totient (3 ^ j * baseN)) := by
  have h3pos : 0 < 3 ^ j := by positivity
  have hgt : 1 < 3 ^ j * baseN := by
    have : 1 * 2 ≤ 3 ^ j * baseN := Nat.mul_le_mul h3pos (by norm_num [baseN])
    omega
  have hodd : Odd (3 ^ j * baseN) :=
    Odd.mul (Odd.pow ⟨1, rfl⟩) ⟨2547677053, by norm_num [baseN]⟩
  have hdiv1 : 3 ∣ baseN := ⟨1698451369, by norm_num [baseN]⟩
  have hdiv2 : 3 ∣ (baseN + Nat.totient baseN) := by
    rw [totient_baseN]; exact ⟨2829655465, by norm_num [baseN]⟩
  refine ⟨hgt, Nat.not_even_iff_odd.mpr hodd, ?_⟩
  have h1 : Nat.totient (3 ^ j * baseN) = 3 ^ j * Nat.totient baseN :=
    totient_three_pow_mul j hdiv1
  have h2 : Nat.totient (3 ^ j * (baseN + Nat.totient baseN)) =
      3 ^ j * Nat.totient (baseN + Nat.totient baseN) :=
    totient_three_pow_mul j hdiv2
  rw [h1, ← mul_add, h2]
  exact congrArg (3 ^ j * ·) baseN_counterexample.2.2

end FiroozbakhtA108569
