import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic

/-!
# Proof of Yaqubi–Mirzavaziri Conjecture 6.2 (arXiv:2611.05623v1)

Let `f m = ∏_{j ≥ 1} (1 - q^{mj})`, let `G = f 4 * (f 6)^2 / (f 1 * f 3 * f 12)` be the
generating function for partitions into odd parts with designated summands (`PDO(n)`), and let
`B k n = [q^n] G^k` count ordered `k`-tuples of such partitions of total size `n`.

**Conjecture 6.2 (Yaqubi–Mirzavaziri, 2026).** For every `k ≥ 1`, the largest power of `2`
dividing `B k (4*n + 3)` for all `n ≥ 0` is `2^{v_2(B k 3)}`, except when `k ≡ 1 (mod 8)`
(where it is `2^2`) or `k ≡ 6 (mod 8)` (where it is `2^3`).

This file gives a completely self-contained, unconditional proof in Lean 4:
1. Finite polynomial Jacobi triple product yielding Gauss's identities
   `f 2 * φ(-q) = f 1 ^ 2` and `f 1 * ψ(q) = f 2 ^ 2`.
2. A bijective proof of `ψ(q) * ψ(q^3) = φ(q^6) * ψ(q^4) + q * φ(q^2) * ψ(q^{12})`.
3. Exact 2-dissection of `G` and modulo 4/8 power-series proofs of
   `4 ∣ B 1 (4*n + 3)`, `4 ∣ B 2 (4*n + 3)`, and `8 ∣ B (8*s + 6) (4*n + 3)`.
4. Frobenius congruences, exact formulas for `B k 3` and `B k 7`, and Vandermonde
   periodicity modulo 8 (period 32) and modulo 16 (period 64) for `B k 7`, settling
   Conjecture 6.2 for every `k ≥ 1`.
-/

namespace YaqubiMirzavaziriPDO

open PowerSeries

/-! ## Section 1: Core Power Series Definitions and Coefficient Agreement -/

/-- The Euler product `f_m(q) = ∏_{j ≥ 1} (1 - q^{mj})` defined via Mathlib's pentagonal series. -/
noncomputable def f (m : ℕ) (hm : m ≠ 0) : ℤ⟦X⟧ :=
  (PowerSeries.pentagonalSeries ℤ).expand m hm

/-- The generating function `G(q) = f_4 f_6^2 / (f_1 f_3 f_12)` for `PDO(n)`. -/
noncomputable def G : ℤ⟦X⟧ :=
  f 4 (by decide) * (f 6 (by decide)) ^ 2 *
    PowerSeries.invOfUnit (f 1 (by decide) * f 3 (by decide) * f 12 (by decide)) 1

/-- `B k n = [q^n] G(q)^k`, counting `k`-tuples of odd-part partitions with designated summands. -/
noncomputable def B (k n : ℕ) : ℤ :=
  (G ^ k).coeff n

/-- Ramanujan's theta series `φ(q) = 1 + 2 ∑_{k ≥ 1} q^{k^2}`. -/
noncomputable def phi : ℤ⟦X⟧ :=
  open Classical in
  PowerSeries.mk fun n =>
    if n = 0 then 1 else if ∃ k : ℕ, 0 < k ∧ k * k = n then 2 else 0

/-- `φ(-q) = 1 + 2 ∑_{k ≥ 1} (-1)^k q^{k^2}`. -/
noncomputable def phiNeg : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => (-1 : ℤ) ^ n * phi.coeff n

/-- Ramanujan's theta series `ψ(q) = ∑_{k ≥ 0} q^{k(k+1)/2}`. -/
noncomputable def psi : ℤ⟦X⟧ :=
  open Classical in
  PowerSeries.mk fun n => if ∃ k : ℕ, k * (k + 1) / 2 = n then 1 else 0

@[simp] lemma constantCoeff_pentagonal :
    PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℤ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  have h0 : pentagonal (0 : ℤ) = 0 := by decide
  rw [← h0, PowerSeries.coeff_pentagonalSeries_pentagonal]
  rfl

@[simp] lemma constantCoeff_f (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.constantCoeff (f m hm) = 1 := by
  simp [f]

@[simp] lemma constantCoeff_phi : PowerSeries.constantCoeff phi = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [phi]

@[simp] lemma constantCoeff_phiNeg : PowerSeries.constantCoeff phiNeg = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [phiNeg, phi]

@[simp] lemma constantCoeff_psi : PowerSeries.constantCoeff psi = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [psi, PowerSeries.coeff_mk]
  rw [if_pos ⟨0, by decide⟩]

lemma G_mul_den :
    G * (f 1 (by decide) * f 3 (by decide) * f 12 (by decide)) =
      f 4 (by decide) * (f 6 (by decide)) ^ 2 := by
  unfold G
  rw [mul_assoc, PowerSeries.invOfUnit_mul, mul_one]
  simp

@[simp] lemma constantCoeff_G : PowerSeries.constantCoeff G = 1 := by
  unfold G
  simp

private lemma coeff_X_pow_mul_add {R : Type*} [CommRing R] (n s : ℕ) (p : R⟦X⟧) :
    ((PowerSeries.X : R⟦X⟧) ^ n * p).coeff (n + s) = p.coeff s := by
  rw [add_comm, PowerSeries.coeff_X_pow_mul]

private lemma coeff_X_pow_mul_of_lt {R : Type*} [CommRing R] {n d : ℕ} (h : d < n) (p : R⟦X⟧) :
    ((PowerSeries.X : R⟦X⟧) ^ n * p).coeff d = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma coeff_X_mul_eq {R : Type*} [CommRing R] (n : ℕ) (p : R⟦X⟧) :
    ((PowerSeries.X : R⟦X⟧) * p).coeff n = if 1 ≤ n then p.coeff (n - 1) else 0 := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ m => simp [PowerSeries.coeff_succ_X_mul]

/-- Two power series agree on all coefficients of degree `≤ d`. -/
def AgreeUpto (d : ℕ) (A B : ℤ⟦X⟧) : Prop :=
  ∀ n ≤ d, A.coeff n = B.coeff n

namespace AgreeUpto

lemma refl (d : ℕ) (A : ℤ⟦X⟧) : AgreeUpto d A A := fun _ _ => rfl

lemma symm {d : ℕ} {A B : ℤ⟦X⟧} (h : AgreeUpto d A B) : AgreeUpto d B A :=
  fun n hn => (h n hn).symm

lemma trans {d : ℕ} {A B C : ℤ⟦X⟧} (h1 : AgreeUpto d A B) (h2 : AgreeUpto d B C) :
    AgreeUpto d A C := fun n hn => (h1 n hn).trans (h2 n hn)

lemma add {d : ℕ} {A₁ A₂ B₁ B₂ : ℤ⟦X⟧} (hA : AgreeUpto d A₁ A₂) (hB : AgreeUpto d B₁ B₂) :
    AgreeUpto d (A₁ + B₁) (A₂ + B₂) := by
  intro n hn
  simp only [map_add, hA n hn, hB n hn]

lemma mul {d : ℕ} {A₁ A₂ B₁ B₂ : ℤ⟦X⟧} (hA : AgreeUpto d A₁ A₂) (hB : AgreeUpto d B₁ B₂) :
    AgreeUpto d (A₁ * B₁) (A₂ * B₂) := by
  intro n hn
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [hA x.1 (by omega), hB x.2 (by omega)]

lemma pow {d : ℕ} {A B : ℤ⟦X⟧} (h : AgreeUpto d A B) : ∀ k : ℕ, AgreeUpto d (A ^ k) (B ^ k)
  | 0 => refl d 1
  | k + 1 => by
      rw [pow_succ, pow_succ]
      exact (pow h k).mul h

lemma sum {ι : Type*} (s : Finset ι) {d : ℕ} {F₁ F₂ : ι → ℤ⟦X⟧}
    (h : ∀ i ∈ s, AgreeUpto d (F₁ i) (F₂ i)) :
    AgreeUpto d (∑ i ∈ s, F₁ i) (∑ i ∈ s, F₂ i) := by
  intro n hn
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi n hn

lemma prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {d : ℕ} {F₁ F₂ : ι → ℤ⟦X⟧}
    (h : ∀ i ∈ s, AgreeUpto d (F₁ i) (F₂ i)) :
    AgreeUpto d (∏ i ∈ s, F₁ i) (∏ i ∈ s, F₂ i) := by
  induction s using Finset.induction_on with
  | empty => exact refl d 1
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma cancel_unit_right {d : ℕ} {A B U : ℤ⟦X⟧} (hU : PowerSeries.constantCoeff U = 1)
    (h : AgreeUpto d (A * U) (B * U)) : AgreeUpto d A B := by
  have hA : A = A * U * PowerSeries.invOfUnit U 1 := by
    rw [mul_assoc, PowerSeries.mul_invOfUnit U 1 (by simpa using hU), mul_one]
  have hB : B = B * U * PowerSeries.invOfUnit U 1 := by
    rw [mul_assoc, PowerSeries.mul_invOfUnit U 1 (by simpa using hU), mul_one]
  rw [hA, hB]
  exact h.mul (refl d _)

lemma one_sub_X_pow {d r : ℕ} (h : d < r) : AgreeUpto d (1 - (X : ℤ⟦X⟧) ^ r) 1 := by
  intro n hn
  rw [map_sub, PowerSeries.coeff_X_pow, if_neg (by omega), sub_zero]

lemma one_add_X_pow {d r : ℕ} (h : d < r) : AgreeUpto d (1 + (X : ℤ⟦X⟧) ^ r) 1 := by
  intro n hn
  rw [map_add, PowerSeries.coeff_X_pow, if_neg (by omega), add_zero]

lemma X_pow_zero {d r : ℕ} (h : d < r) : AgreeUpto d ((X : ℤ⟦X⟧) ^ r) 0 := by
  intro n hn
  rw [PowerSeries.coeff_X_pow, if_neg (by omega), map_zero]

end AgreeUpto

lemma agreeUpto_finprod_f1 (d N : ℕ) (hN : d ≤ N) :
    AgreeUpto d (∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (j + 1))) (f 1 one_ne_zero) := by
  intro n hn
  have hev := PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ n
  rw [Filter.eventually_atTop] at hev
  obtain ⟨s₀, hs₀⟩ := hev
  let s := Finset.range N ∪ s₀
  have hs_eq : (∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff n =
      (PowerSeries.pentagonalSeries ℤ).coeff n := hs₀ s Finset.subset_union_right
  have hsplit : ∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) =
      (∏ i ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) *
      (∏ i ∈ s \ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset Finset.subset_union_left]
  have htail : AgreeUpto n (∏ i ∈ s \ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) 1 := by
    have htail' : AgreeUpto n (∏ i ∈ s \ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
        (∏ _i ∈ s \ Finset.range N, (1 : ℤ⟦X⟧)) := by
      refine AgreeUpto.prod (s \ Finset.range N) fun i hi => ?_
      rw [Finset.mem_sdiff, Finset.mem_range] at hi
      exact AgreeUpto.one_sub_X_pow (d := n) (r := i + 1) (by omega)
    simpa using htail'
  have hmul : AgreeUpto n (∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      (∏ i ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) := by
    rw [hsplit]
    simpa using (AgreeUpto.refl n _).mul htail
  have hmain := hmul n le_rfl
  rw [hs_eq] at hmain
  rw [← hmain]
  simp [f]

lemma agreeUpto_finprod_f (m : ℕ) (hm : m ≠ 0) (d N : ℕ) (hN : d ≤ m * N) :
    AgreeUpto d (∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (m * (j + 1)))) (f m hm) := by
  have h1 : ∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (m * (j + 1))) =
      (∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (j + 1))).expand m hm := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  rw [h1]
  intro n hn
  simp only [f, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · have hdiv : n / m ≤ N := Nat.div_le_of_le_mul (le_trans hn hN)
    have hfg := agreeUpto_finprod_f1 N N le_rfl (n / m) hdiv
    simpa [f] using hfg
  · rfl

lemma constantCoeff_finprod_one_sub (m N : ℕ) (hm : 1 ≤ m) :
    PowerSeries.constantCoeff (∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (m * (j + 1)))) = 1 := by
  rw [map_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  have hpos : m * (j + 1) ≠ 0 := by positivity
  simp [map_sub, PowerSeries.constantCoeff_X, zero_pow hpos]

/-! ## Section 2: Finite Polynomial Jacobi Triple Product and Gauss Identities `(J1)`, `(J2)` -/

section JacobiTripleProduct

open Polynomial

private noncomputable abbrev q : ℤ⟦X⟧ := PowerSeries.X
private noncomputable abbrev Z : Polynomial (ℤ⟦X⟧) := Polynomial.X

private noncomputable def Q (j : ℕ) : Polynomial (ℤ⟦X⟧) :=
  (1 + Polynomial.C (q ^ (2 * j + 1)) * Z) * (Z + Polynomial.C (q ^ (2 * j + 1)))

private noncomputable def P (N : ℕ) : Polynomial (ℤ⟦X⟧) :=
  ∏ j ∈ Finset.range N, Q j

private lemma P_zero : P 0 = 1 := by simp [P]
private lemma P_succ (N : ℕ) : P (N + 1) = P N * Q N := by simp [P, Finset.prod_range_succ]

private lemma poly_coeff_mul_X (p : Polynomial (ℤ⟦X⟧)) (m : ℕ) :
    (p * Polynomial.X).coeff m = if 1 ≤ m then p.coeff (m - 1) else 0 := by
  cases m with
  | zero => simp
  | succ m' => simp [Polynomial.coeff_mul_X]

private lemma poly_coeff_mul_X_sq (p : Polynomial (ℤ⟦X⟧)) (m : ℕ) :
    (p * Polynomial.X ^ 2).coeff m = if 2 ≤ m then p.coeff (m - 2) else 0 := by
  rw [sq, ← mul_assoc, poly_coeff_mul_X]
  split_ifs with h1 h2 h2
  · rw [poly_coeff_mul_X, if_pos (by omega)]; congr 1
  · rw [poly_coeff_mul_X, if_neg (by omega)]
  · exfalso; omega
  · rfl

private lemma Q_expand (j : ℕ) :
    Q j = Polynomial.C (q ^ (2 * j + 1)) +
      Polynomial.C (1 + q ^ (4 * j + 2)) * Z +
      Polynomial.C (q ^ (2 * j + 1)) * Z ^ 2 := by
  simp only [Q]
  have hpow : q ^ (2 * j + 1) * q ^ (2 * j + 1) = q ^ (4 * j + 2) := by
    rw [← pow_add]; congr 1; omega
  simp only [map_add, map_one, ← hpow, map_mul]
  ring

private lemma P_palindromic (N : ℕ) :
    (∀ m > 2 * N, (P N).coeff m = 0) ∧
    (∀ m ≤ 2 * N, (P N).coeff (2 * N - m) = (P N).coeff m) ∧
    (P N).coeff (2 * N) = q ^ (N * N) := by
  induction N with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro m hm; rw [P_zero, Polynomial.coeff_one, if_neg (by omega)]
      · intro m hm
        have hm0 : m = 0 := by omega
        simp [hm0]
      · simp [P_zero]
  | succ N ih =>
      rcases ih with ⟨hgt, hpal, hlead⟩
      have hmul_coeff : ∀ m, (P (N + 1)).coeff m =
          (P N).coeff m * q ^ (2 * N + 1) +
          (if 1 ≤ m then (P N).coeff (m - 1) * (1 + q ^ (4 * N + 2)) else 0) +
          (if 2 ≤ m then (P N).coeff (m - 2) * q ^ (2 * N + 1) else 0) := by
        intro m
        rw [P_succ, Q_expand, mul_add, mul_add, Polynomial.coeff_add, Polynomial.coeff_add,
          Polynomial.coeff_mul_C]
        have hc1 : (P N * (Polynomial.C (1 + q ^ (4 * N + 2)) * Polynomial.X)).coeff m =
            if 1 ≤ m then (P N).coeff (m - 1) * (1 + q ^ (4 * N + 2)) else 0 := by
          rw [← mul_assoc, poly_coeff_mul_X]
          split_ifs with h1
          · rw [Polynomial.coeff_mul_C]
          · rfl
        have hc2 : (P N * (Polynomial.C (q ^ (2 * N + 1)) * Polynomial.X ^ 2)).coeff m =
            if 2 ≤ m then (P N).coeff (m - 2) * q ^ (2 * N + 1) else 0 := by
          rw [← mul_assoc, poly_coeff_mul_X_sq]
          split_ifs with h2
          · rw [Polynomial.coeff_mul_C]
          · rfl
        rw [hc1, hc2]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        rw [hmul_coeff]
        have h0 : (P N).coeff m = 0 := hgt m (by omega)
        have h1 : (P N).coeff (m - 1) = 0 := hgt (m - 1) (by omega)
        have h2 : (P N).coeff (m - 2) = 0 := hgt (m - 2) (by omega)
        simp [h0, h1, h2]
      · intro m hm
        rw [hmul_coeff (2 * (N + 1) - m), hmul_coeff m]
        have ht1 : (P N).coeff (2 * (N + 1) - m) = if 2 ≤ m then (P N).coeff (m - 2) else 0 := by
          split_ifs with h2
          · have : 2 * (N + 1) - m = 2 * N - (m - 2) := by omega
            rw [this, hpal (m - 2) (by omega)]
          · exact hgt _ (by omega)
        have ht2 : (if 1 ≤ 2 * (N + 1) - m then (P N).coeff (2 * (N + 1) - m - 1) *
              (1 + q ^ (4 * N + 2)) else 0) =
            (if 1 ≤ m then (P N).coeff (m - 1) * (1 + q ^ (4 * N + 2)) else 0) := by
          by_cases h1 : 1 ≤ m
          · by_cases h1' : 1 ≤ 2 * (N + 1) - m
            · simp only [if_pos h1, if_pos h1']
              have : 2 * (N + 1) - m - 1 = 2 * N - (m - 1) := by omega
              rw [this, hpal (m - 1) (by omega)]
            · simp only [if_pos h1, if_neg h1']
              have : m - 1 > 2 * N := by omega
              rw [hgt (m - 1) this, zero_mul]
          · simp only [if_neg h1, if_pos (by omega : 1 ≤ 2 * (N + 1) - m)]
            rw [hgt _ (by omega), zero_mul]
        have ht3 : (if 2 ≤ 2 * (N + 1) - m then (P N).coeff (2 * (N + 1) - m - 2) *
              q ^ (2 * N + 1) else 0) = (P N).coeff m * q ^ (2 * N + 1) := by
          by_cases h2' : 2 ≤ 2 * (N + 1) - m
          · simp only [if_pos h2']
            have : 2 * (N + 1) - m - 2 = 2 * N - m := by omega
            rw [this, hpal m (by omega)]
          · simp only [if_neg h2']
            rw [hgt m (by omega), zero_mul]
        rw [ht1, ht2, ht3]
        split_ifs <;> ring
      · rw [hmul_coeff]
        have h0 : (P N).coeff (2 * (N + 1)) = 0 := hgt _ (by omega)
        have h1 : (P N).coeff (2 * (N + 1) - 1) = 0 := hgt _ (by omega)
        have h2 : 2 ≤ 2 * (N + 1) := by omega
        have hsub : 2 * (N + 1) - 2 = 2 * N := by omega
        rw [h0, h1, if_pos h2, hsub, hlead]
        simp only [zero_mul, ite_self, add_zero, zero_add]
        rw [← pow_add]
        congr 1
        ring

private lemma P_func_eq (N : ℕ) (hN : 1 ≤ N) :
    (Z + Polynomial.C (q ^ (2 * N - 1))) * (P N).comp (Polynomial.C (q ^ 2) * Z) =
      Polynomial.C (q ^ (2 * N - 1)) * (1 + Polynomial.C (q ^ (2 * N + 1)) * Z) * P N := by
  induction N, hN using Nat.le_induction with
  | base =>
      simp only [P, Q, Finset.prod_range_one, Nat.mul_one]
      simp only [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.one_comp,
        Polynomial.C_comp, Polynomial.X_comp]
      have h1 : Polynomial.C (q ^ 1) * Polynomial.C (q ^ 2) = Polynomial.C (q ^ 3) := by
        rw [← map_mul, ← pow_add]
      have h2 : Polynomial.C (q ^ 2) = Polynomial.C (q ^ 1) * Polynomial.C (q ^ 1) := by
        rw [← map_mul, ← pow_add]
      rw [mul_assoc (Polynomial.C (q ^ 1)), ← mul_assoc (Polynomial.C (q ^ 1)) (Polynomial.C (q ^ 2)),
        h1, h2]
      ring
  | succ N hN ih =>
      rw [P_succ, Polynomial.mul_comp]
      have hQcomp : (Q N).comp (Polynomial.C (q ^ 2) * Z) =
          Polynomial.C (q ^ 2) * (1 + Polynomial.C (q ^ (2 * N + 3)) * Z) *
            (Z + Polynomial.C (q ^ (2 * N - 1))) := by
        simp only [Q, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.one_comp,
          Polynomial.C_comp, Polynomial.X_comp]
        have ha : Polynomial.C (q ^ (2 * N + 1)) * Polynomial.C (q ^ 2) =
            Polynomial.C (q ^ (2 * N + 3)) := by
          rw [← map_mul, ← pow_add]
        have hb : Polynomial.C (q ^ (2 * N + 1)) =
            Polynomial.C (q ^ 2) * Polynomial.C (q ^ (2 * N - 1)) := by
          rw [← map_mul, ← pow_add]; congr 2; omega
        calc
          (1 + Polynomial.C (q ^ (2 * N + 1)) * (Polynomial.C (q ^ 2) * Polynomial.X)) *
              (Polynomial.C (q ^ 2) * Polynomial.X + Polynomial.C (q ^ (2 * N + 1)))
              = (1 + (Polynomial.C (q ^ (2 * N + 1)) * Polynomial.C (q ^ 2)) * Polynomial.X) *
                  (Polynomial.C (q ^ 2) * Polynomial.X +
                    Polynomial.C (q ^ 2) * Polynomial.C (q ^ (2 * N - 1))) := by
                rw [← hb]; ring
          _ = Polynomial.C (q ^ 2) * (1 + Polynomial.C (q ^ (2 * N + 3)) * Polynomial.X) *
                (Polynomial.X + Polynomial.C (q ^ (2 * N - 1))) := by
                rw [ha]; ring
      rw [hQcomp]
      have hrearr :
          (Z + Polynomial.C (q ^ (2 * (N + 1) - 1))) *
            ((P N).comp (Polynomial.C (q ^ 2) * Z) *
              (Polynomial.C (q ^ 2) * (1 + Polynomial.C (q ^ (2 * N + 3)) * Z) *
                (Z + Polynomial.C (q ^ (2 * N - 1))))) =
          (Z + Polynomial.C (q ^ (2 * N + 1))) * Polynomial.C (q ^ 2) *
            (1 + Polynomial.C (q ^ (2 * N + 3)) * Z) *
            ((Z + Polynomial.C (q ^ (2 * N - 1))) * (P N).comp (Polynomial.C (q ^ 2) * Z)) := by
        have hidx : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
        rw [hidx]; ring
      rw [hrearr, ih]
      have hc : Polynomial.C (q ^ 2) * Polynomial.C (q ^ (2 * N - 1)) =
          Polynomial.C (q ^ (2 * (N + 1) - 1)) := by
        rw [← map_mul, ← pow_add]; congr 2; omega
      have hidx2 : 2 * (N + 1) + 1 = 2 * N + 3 := by omega
      rw [hidx2, ← hc]
      simp only [Q]
      ring

private lemma coeff_comp_C_mul_X (p : Polynomial (ℤ⟦X⟧)) (a : ℤ⟦X⟧) (m : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff m = a ^ m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
      simp [Polynomial.add_comp, ih₁, ih₂, mul_add]
  | monomial n c =>
      rw [Polynomial.monomial_comp, mul_pow, ← map_pow, ← mul_assoc, ← map_mul,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      by_cases h : m = n
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h]

private lemma P_coeff_recurrence (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    q ^ (2 * k - 1) * (1 - q ^ (2 * (N + 1 - k))) * (P N).coeff (N + k - 1) =
      (1 - q ^ (2 * (N + k))) * (P N).coeff (N + k) := by
  have hfe := congrArg (fun p => p.coeff (N + k)) (P_func_eq N hN)
  have hm1 : 1 ≤ N + k := by omega
  have hL : ((Z + Polynomial.C (q ^ (2 * N - 1))) *
      (P N).comp (Polynomial.C (q ^ 2) * Z)).coeff (N + k) =
      q ^ (2 * (N + k - 1)) * (P N).coeff (N + k - 1) +
        q ^ (2 * N - 1) * q ^ (2 * (N + k)) * (P N).coeff (N + k) := by
    rw [add_mul, Polynomial.coeff_add, Polynomial.X_mul, poly_coeff_mul_X, if_pos hm1,
      Polynomial.coeff_C_mul, coeff_comp_C_mul_X, coeff_comp_C_mul_X, ← pow_mul, ← pow_mul]
    ring
  have hR : (Polynomial.C (q ^ (2 * N - 1)) * (1 + Polynomial.C (q ^ (2 * N + 1)) * Z) *
      P N).coeff (N + k) =
      q ^ (2 * N - 1) * (P N).coeff (N + k) +
        q ^ (2 * N - 1) * q ^ (2 * N + 1) * (P N).coeff (N + k - 1) := by
    have hrw : Polynomial.C (q ^ (2 * N - 1)) * (1 + Polynomial.C (q ^ (2 * N + 1)) * Z) * P N =
        Polynomial.C (q ^ (2 * N - 1)) * P N +
        Polynomial.C (q ^ (2 * N - 1) * q ^ (2 * N + 1)) * (P N * Z) := by
      simp only [map_mul]; ring
    rw [hrw, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      poly_coeff_mul_X, if_pos hm1]
  rw [hL, hR] at hfe
  have hpow1 : q ^ (2 * (N + k - 1)) = q ^ (2 * N - 1) * q ^ (2 * k - 1) := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : q ^ (2 * N + 1) = q ^ (2 * k - 1) * q ^ (2 * (N + 1 - k)) := by
    rw [← pow_add]; congr 1; omega
  have hfac : q ^ (2 * N - 1) *
      (q ^ (2 * k - 1) * (1 - q ^ (2 * (N + 1 - k))) * (P N).coeff (N + k - 1)) =
      q ^ (2 * N - 1) * ((1 - q ^ (2 * (N + k))) * (P N).coeff (N + k)) := by
    have hfe' : q ^ (2 * (N + k - 1)) * (P N).coeff (N + k - 1) -
        q ^ (2 * N - 1) * q ^ (2 * N + 1) * (P N).coeff (N + k - 1) =
        q ^ (2 * N - 1) * (P N).coeff (N + k) -
        q ^ (2 * N - 1) * q ^ (2 * (N + k)) * (P N).coeff (N + k) := by
      linear_combination hfe
    rw [hpow1, hpow2] at hfe'
    linear_combination hfe'
  exact mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) hfac

private lemma P_coeff_identity (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    (P N).coeff (N + k) *
      (∏ j ∈ Finset.range (N + k), (1 - q ^ (2 * (j + 1)))) *
      (∏ j ∈ Finset.range (N - k), (1 - q ^ (2 * (j + 1)))) =
      q ^ (k * k) * (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1)))) := by
  obtain ⟨t, rfl, htN⟩ : ∃ t, k = N - t ∧ t ≤ N := ⟨N - k, by omega, by omega⟩
  clear hk
  induction t with
  | zero =>
      simp only [Nat.sub_zero, Nat.sub_self, Finset.prod_range_zero, mul_one]
      have h2N : N + N = 2 * N := by omega
      rw [h2N, (P_palindromic N).2.2]
  | succ t ih =>
      have hrec := P_coeff_recurrence N hN (N - t) (by omega) (by omega)
      have hsub1 : N + (N - t) - 1 = N + (N - (t + 1)) := by omega
      have hsub2 : N + 1 - (N - t) = t + 1 := by omega
      have hsub3 : N + (N - t) = (N + (N - (t + 1))) + 1 := by omega
      have hsub4 : N - (N - (t + 1)) = t + 1 := by omega
      have hsub5 : N - (N - t) = t := by omega
      rw [hsub1, hsub2] at hrec
      have hih := ih (by omega)
      rw [hsub3, Finset.prod_range_succ, hsub5] at hih
      have hprod_t : ∏ j ∈ Finset.range (N - (N - (t + 1))), (1 - q ^ (2 * (j + 1))) =
          (∏ j ∈ Finset.range t, (1 - q ^ (2 * (j + 1)))) * (1 - q ^ (2 * (t + 1))) := by
        rw [hsub4, Finset.prod_range_succ]
      have hsq : (N - t) * (N - t) = (2 * (N - t) - 1) + (N - (t + 1)) * (N - (t + 1)) := by
        zify [show t ≤ N by omega, show t + 1 ≤ N by omega, show 1 ≤ 2 * (N - t) by omega]
        ring
      have hstep : q ^ (2 * (N - t) - 1) * (P N).coeff (N + (N - (t + 1))) *
          (1 - q ^ (2 * (t + 1))) =
          (P N).coeff (N + (N - t)) * (1 - q ^ (2 * (N + (N - (t + 1)) + 1))) := by
        rw [← hsub3]
        linear_combination hrec
      have hmul : q ^ (2 * (N - t) - 1) *
          ((P N).coeff (N + (N - (t + 1))) *
            (∏ j ∈ Finset.range (N + (N - (t + 1))), (1 - q ^ (2 * (j + 1)))) *
            (∏ j ∈ Finset.range (N - (N - (t + 1))), (1 - q ^ (2 * (j + 1))))) =
          q ^ (2 * (N - t) - 1) *
            (q ^ ((N - (t + 1)) * (N - (t + 1))) *
              (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1))))) := by
        calc
          q ^ (2 * (N - t) - 1) *
              ((P N).coeff (N + (N - (t + 1))) *
                (∏ j ∈ Finset.range (N + (N - (t + 1))), (1 - q ^ (2 * (j + 1)))) *
                (∏ j ∈ Finset.range (N - (N - (t + 1))), (1 - q ^ (2 * (j + 1)))))
              = (q ^ (2 * (N - t) - 1) * (P N).coeff (N + (N - (t + 1))) *
                  (1 - q ^ (2 * (t + 1)))) *
                (∏ j ∈ Finset.range (N + (N - (t + 1))), (1 - q ^ (2 * (j + 1)))) *
                (∏ j ∈ Finset.range t, (1 - q ^ (2 * (j + 1)))) := by
                rw [hprod_t]; ring
          _ = ((P N).coeff (N + (N - t)) * (1 - q ^ (2 * (N + (N - (t + 1)) + 1)))) *
                (∏ j ∈ Finset.range (N + (N - (t + 1))), (1 - q ^ (2 * (j + 1)))) *
                (∏ j ∈ Finset.range t, (1 - q ^ (2 * (j + 1)))) := by rw [hstep]
          _ = (P N).coeff (N + (N - t)) *
                ((∏ j ∈ Finset.range (N + (N - (t + 1))), (1 - q ^ (2 * (j + 1)))) *
                  (1 - q ^ (2 * (N + (N - (t + 1)) + 1)))) *
                (∏ j ∈ Finset.range t, (1 - q ^ (2 * (j + 1)))) := by ring
          _ = q ^ ((N - t) * (N - t)) *
                (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1)))) := by
                rw [hsub3]; exact hih
          _ = q ^ (2 * (N - t) - 1) *
                (q ^ ((N - (t + 1)) * (N - (t + 1))) *
                  (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1))))) := by
                rw [hsq, pow_add, mul_assoc]
      exact mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) hmul

private lemma P_coeff_mul_f2_agreeUpto {d N k : ℕ} (hN : 1 ≤ N) (hkN : k ≤ N) (hNk : d ≤ 2 * (N - k)) :
    AgreeUpto d ((P N).coeff (N + k) * f 2 (by decide)) (q ^ (k * k)) := by
  have hid := P_coeff_identity N hN k hkN
  have h1 : AgreeUpto d (∏ j ∈ Finset.range (N + k), (1 - q ^ (2 * (j + 1)))) (f 2 (by decide)) :=
    agreeUpto_finprod_f 2 (by decide) d (N + k) (by omega)
  have h2 : AgreeUpto d (∏ j ∈ Finset.range (N - k), (1 - q ^ (2 * (j + 1)))) (f 2 (by decide)) :=
    agreeUpto_finprod_f 2 (by decide) d (N - k) (by omega)
  have h3 : AgreeUpto d (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1)))) (f 2 (by decide)) :=
    agreeUpto_finprod_f 2 (by decide) d (2 * N) (by omega)
  have hlhs : AgreeUpto d
      ((P N).coeff (N + k) * f 2 (by decide) * f 2 (by decide))
      ((P N).coeff (N + k) *
        (∏ j ∈ Finset.range (N + k), (1 - q ^ (2 * (j + 1)))) *
        (∏ j ∈ Finset.range (N - k), (1 - q ^ (2 * (j + 1))))) :=
    ((AgreeUpto.refl d _).mul h1.symm).mul h2.symm
  have hrhs : AgreeUpto d
      (q ^ (k * k) * (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1)))))
      (q ^ (k * k) * f 2 (by decide)) :=
    (AgreeUpto.refl d _).mul h3
  have hcomb : AgreeUpto d ((P N).coeff (N + k) * f 2 (by decide) * f 2 (by decide))
      (q ^ (k * k) * f 2 (by decide)) :=
    (hlhs.trans (by rw [hid]; exact AgreeUpto.refl d _)).trans hrhs
  exact AgreeUpto.cancel_unit_right (constantCoeff_f 2 (by decide)) hcomb

private lemma P_coeff_zero_agreeUpto {d N k : ℕ} (hN : 1 ≤ N) (hkN : k ≤ N) (hkd : d < k * k) :
    AgreeUpto d ((P N).coeff (N + k)) 0 := by
  have hid := P_coeff_identity N hN k hkN
  set U := (∏ j ∈ Finset.range (N + k), (1 - q ^ (2 * (j + 1)))) *
           (∏ j ∈ Finset.range (N - k), (1 - q ^ (2 * (j + 1))))
  have hU : PowerSeries.constantCoeff U = 1 := by
    rw [map_mul, constantCoeff_finprod_one_sub 2 (N + k) (by decide),
      constantCoeff_finprod_one_sub 2 (N - k) (by decide), mul_one]
  have hrhs : AgreeUpto d ((P N).coeff (N + k) * U) (0 * U) := by
    rw [zero_mul]
    have hmul_assoc : (P N).coeff (N + k) * U =
        q ^ (k * k) * (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1)))) := by
      simpa [U, mul_assoc] using hid
    rw [hmul_assoc]
    simpa [zero_mul] using (AgreeUpto.X_pow_zero hkd).mul
      (AgreeUpto.refl d (∏ j ∈ Finset.range (2 * N), (1 - q ^ (2 * (j + 1)))))
  exact AgreeUpto.cancel_unit_right hU hrhs

private lemma P_coeff_symm (N k : ℕ) (hk : k ≤ N) :
    (P N).coeff (N - k) = (P N).coeff (N + k) := by
  have h := (P_palindromic N).2.1 (N + k) (by omega)
  have hsub : 2 * N - (N + k) = N - k := by omega
  rwa [hsub] at h

private lemma eval_P_eq_sum (N : ℕ) (z : ℤ⟦X⟧) :
    (P N).eval z = ∑ m ∈ Finset.range (2 * N + 1), (P N).coeff m * z ^ m := by
  rw [Polynomial.eval_eq_sum_range']
  have hnat : (P N).natDegree ≤ 2 * N := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    exact (P_palindromic N).1
  omega

/-- Gauss identity `(J2)`: `f_2(q) * φ(-q) = f_1(q)^2`. -/
theorem gauss_J2 : f 2 (by decide) * phiNeg = (f 1 (by decide)) ^ 2 := by
  ext d
  let N := 2 * d + 2
  have hN : 1 ≤ N := by omega
  have heval_prod : (-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1) =
      (∏ j ∈ Finset.range N, (1 - q ^ (2 * j + 1))) ^ 2 := by
    rw [P, Polynomial.eval_prod]
    have hneg : (-1 : ℤ⟦X⟧) ^ N = ∏ _j ∈ Finset.range N, (-1 : ℤ⟦X⟧) := by simp
    rw [hneg, ← Finset.prod_mul_distrib, sq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Q]
    ring
  have hodd_even : (∏ j ∈ Finset.range N, (1 - q ^ (2 * j + 1))) *
      (∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1)))) =
      ∏ i ∈ Finset.range (2 * N), (1 - q ^ (i + 1)) := by
    clear hN heval_prod
    generalize N = M
    induction M with
    | zero => simp
    | succ M ih =>
        have h2M : 2 * (M + 1) = 2 * M + 2 := by omega
        rw [h2M, Finset.prod_range_succ, Finset.prod_range_succ,
          Finset.prod_range_succ, Finset.prod_range_succ]
        have h2 : 2 * (M + 1) = 2 * M + 1 + 1 := by omega
        rw [h2, ← ih]
        ring
  have hprod_f1 : AgreeUpto d
      (((-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1)) * f 2 (by decide) ^ 2)
      ((f 1 (by decide)) ^ 2) := by
    rw [heval_prod]
    have hf2 : AgreeUpto d (∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1)))) (f 2 (by decide)) :=
      agreeUpto_finprod_f 2 (by decide) d N (by omega)
    have hf1 : AgreeUpto d (∏ i ∈ Finset.range (2 * N), (1 - q ^ (i + 1))) (f 1 (by decide)) :=
      agreeUpto_finprod_f1 d (2 * N) (by omega)
    have hsq : (∏ j ∈ Finset.range N, (1 - q ^ (2 * j + 1))) ^ 2 *
        (∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1)))) ^ 2 =
        (∏ i ∈ Finset.range (2 * N), (1 - q ^ (i + 1))) ^ 2 := by
      rw [← mul_pow, hodd_even]
    have hstep1 : AgreeUpto d
        ((∏ j ∈ Finset.range N, (1 - q ^ (2 * j + 1))) ^ 2 * f 2 (by decide) ^ 2)
        ((∏ j ∈ Finset.range N, (1 - q ^ (2 * j + 1))) ^ 2 *
          (∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1)))) ^ 2) :=
      (AgreeUpto.refl d _).mul (hf2.symm.pow 2)
    rw [hsq] at hstep1
    exact hstep1.trans (hf1.pow 2)
  have hsum_split : (-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1) =
      (P N).coeff N + ∑ k ∈ Finset.Icc 1 N, 2 * (-1 : ℤ⟦X⟧) ^ k * (P N).coeff (N + k) := by
    rw [eval_P_eq_sum, Finset.mul_sum]
    have hsplit_range : Finset.range (2 * N + 1) =
        insert N ((Finset.Icc 1 N).image (fun k => N - k) ∪ (Finset.Icc 1 N).image (fun k => N + k)) := by
      ext m
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_Icc]
      constructor
      · intro hm
        rcases lt_trichotomy m N with hlt | rfl | hgt
        · right; left; exact ⟨N - m, ⟨by omega, by omega⟩, by omega⟩
        · left; rfl
        · right; right; exact ⟨m - N, ⟨by omega, by omega⟩, by omega⟩
      · rintro (rfl | ⟨k, ⟨_, _⟩, rfl⟩ | ⟨k, ⟨_, _⟩, rfl⟩) <;> omega
    rw [hsplit_range, Finset.sum_insert, Finset.sum_union]
    · have h0 : (-1 : ℤ⟦X⟧) ^ N * ((P N).coeff N * (-1) ^ N) = (P N).coeff N := by
        have : (-1 : ℤ⟦X⟧) ^ N * (-1 : ℤ⟦X⟧) ^ N = 1 := by
          rw [← mul_pow]; norm_num
        linear_combination (P N).coeff N * this
      have hleft : ∑ m ∈ (Finset.Icc 1 N).image (fun k => N - k),
          (-1 : ℤ⟦X⟧) ^ N * ((P N).coeff m * (-1) ^ m) =
          ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ⟦X⟧) ^ k * (P N).coeff (N + k) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          rw [P_coeff_symm N k hk.2]
          have hsign : (-1 : ℤ⟦X⟧) ^ N * (-1 : ℤ⟦X⟧) ^ (N - k) = (-1 : ℤ⟦X⟧) ^ k := by
            have h1 : (-1 : ℤ⟦X⟧) ^ (N - k) * (-1 : ℤ⟦X⟧) ^ k = (-1 : ℤ⟦X⟧) ^ N := by
              rw [← pow_add, Nat.sub_add_cancel hk.2]
            have h2 : (-1 : ℤ⟦X⟧) ^ N * (-1 : ℤ⟦X⟧) ^ N = 1 := by
              rw [← mul_pow]; norm_num
            have h3 : (-1 : ℤ⟦X⟧) ^ k * (-1 : ℤ⟦X⟧) ^ k = 1 := by
              rw [← mul_pow]; norm_num
            calc
              (-1 : ℤ⟦X⟧) ^ N * (-1 : ℤ⟦X⟧) ^ (N - k)
                  = (-1 : ℤ⟦X⟧) ^ N * ((-1 : ℤ⟦X⟧) ^ (N - k) * ((-1 : ℤ⟦X⟧) ^ k * (-1 : ℤ⟦X⟧) ^ k)) := by
                    rw [h3, mul_one]
              _ = ((-1 : ℤ⟦X⟧) ^ N * ((-1 : ℤ⟦X⟧) ^ (N - k) * (-1 : ℤ⟦X⟧) ^ k)) * (-1 : ℤ⟦X⟧) ^ k := by
                    ring
              _ = (-1 : ℤ⟦X⟧) ^ k := by rw [h1, h2, one_mul]
          linear_combination (P N).coeff (N + k) * hsign
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
          dsimp only at hab; omega
      have hright : ∑ m ∈ (Finset.Icc 1 N).image (fun k => N + k),
          (-1 : ℤ⟦X⟧) ^ N * ((P N).coeff m * (-1) ^ m) =
          ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ⟦X⟧) ^ k * (P N).coeff (N + k) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hsign : (-1 : ℤ⟦X⟧) ^ N * (-1 : ℤ⟦X⟧) ^ (N + k) = (-1 : ℤ⟦X⟧) ^ k := by
            have hNN : (-1 : ℤ⟦X⟧) ^ N * (-1 : ℤ⟦X⟧) ^ N = 1 := by
              rw [← mul_pow]; norm_num
            rw [pow_add (-1 : ℤ⟦X⟧) N k, ← mul_assoc, hNN, one_mul]
          linear_combination (P N).coeff (N + k) * hsign
        · intro a _ b _ hab
          dsimp only at hab; omega
      rw [h0, hleft, hright, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_image, Finset.mem_Icc] at hm1 hm2
      rcases hm1 with ⟨a, ⟨_, _⟩, rfl⟩
      rcases hm2 with ⟨b, ⟨_, _⟩, hab⟩
      omega
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
      rintro (⟨a, ⟨_, _⟩, ha⟩ | ⟨a, ⟨_, _⟩, ha⟩) <;> omega
  have hsum_phiNeg : AgreeUpto d (((-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1)) * f 2 (by decide)) phiNeg := by
    rw [hsum_split, add_mul, Finset.sum_mul]
    have h0 : AgreeUpto d ((P N).coeff N * f 2 (by decide)) 1 := by
      simpa using P_coeff_mul_f2_agreeUpto (d := d) (N := N) (k := 0) hN (by omega) (by omega)
    have hterms : AgreeUpto d
        (∑ k ∈ Finset.Icc 1 N, 2 * (-1 : ℤ⟦X⟧) ^ k * (P N).coeff (N + k) * f 2 (by decide))
        (∑ k ∈ Finset.Icc 1 N, 2 * (-1 : ℤ⟦X⟧) ^ k * q ^ (k * k)) := by
      refine AgreeUpto.sum _ fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      by_cases hkd : k ≤ d
      · rw [mul_assoc (2 * (-1 : ℤ⟦X⟧) ^ k)]
        exact (AgreeUpto.refl d _).mul
          (P_coeff_mul_f2_agreeUpto (d := d) (N := N) (k := k) hN hk.2 (by omega))
      · have hsq : d < k * k := by nlinarith
        have hz1 : AgreeUpto d ((P N).coeff (N + k)) 0 :=
          P_coeff_zero_agreeUpto hN hk.2 hsq
        have hz2 : AgreeUpto d (q ^ (k * k)) 0 := AgreeUpto.X_pow_zero hsq
        rw [mul_assoc (2 * (-1 : ℤ⟦X⟧) ^ k)]
        have ha : AgreeUpto d ((2 * (-1 : ℤ⟦X⟧) ^ k) * ((P N).coeff (N + k) * f 2 (by decide))) 0 := by
          simpa using (AgreeUpto.refl d _).mul (hz1.mul (AgreeUpto.refl d _))
        have hb : AgreeUpto d ((2 * (-1 : ℤ⟦X⟧) ^ k) * q ^ (k * k)) 0 := by
          simpa using (AgreeUpto.refl d _).mul hz2
        exact ha.trans hb.symm
    have hphi_sum : AgreeUpto d (1 + ∑ k ∈ Finset.Icc 1 N, 2 * (-1 : ℤ⟦X⟧) ^ k * q ^ (k * k)) phiNeg := by
      intro n hn
      rw [map_add, map_sum, PowerSeries.coeff_one]
      have hterm : ∀ k ∈ Finset.Icc 1 N,
          (2 * (-1 : ℤ⟦X⟧) ^ k * q ^ (k * k)).coeff n =
          if k * k = n then 2 * (-1 : ℤ) ^ k else 0 := by
        intro k _
        have hconst : (2 * (-1 : ℤ⟦X⟧) ^ k) = PowerSeries.C (2 * (-1 : ℤ) ^ k) := by simp
        rw [hconst, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
        by_cases h : n = k * k
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl hterm]
      by_cases hn0 : n = 0
      · subst hn0
        simp [phiNeg, phi]
      · simp only [if_neg hn0, zero_add]
        simp only [phiNeg, phi, PowerSeries.coeff_mk, if_neg hn0]
        by_cases hsq : ∃ k : ℕ, 0 < k ∧ k * k = n
        · rcases hsq with ⟨k₀, hk₀_pos, hk₀_eq⟩
          have hk₀_le : k₀ ≤ N := by
            have : k₀ ≤ k₀ * k₀ := Nat.le_mul_self k₀
            omega
          have hk₀_mem : k₀ ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hk₀_pos, hk₀_le⟩
          rw [Finset.sum_eq_single k₀]
          · rw [if_pos hk₀_eq, if_pos ⟨k₀, hk₀_pos, hk₀_eq⟩]
            have hpar : (-1 : ℤ) ^ n = (-1 : ℤ) ^ k₀ := by
              rw [← hk₀_eq]
              rcases Nat.even_or_odd k₀ with ⟨m, rfl⟩ | ⟨m, rfl⟩
              · have he1 : Even ((m + m) * (m + m)) := ⟨2 * m * m, by ring⟩
                have he2 : Even (m + m) := ⟨m, rfl⟩
                rw [he1.neg_one_pow, he2.neg_one_pow]
              · have ho1 : Odd ((2 * m + 1) * (2 * m + 1)) := ⟨2 * m * m + 2 * m, by ring⟩
                have ho2 : Odd (2 * m + 1) := ⟨m, rfl⟩
                rw [ho1.neg_one_pow, ho2.neg_one_pow]
            rw [hpar]; ring
          · intro k _ hkne
            rw [if_neg]; intro hkeq; exact hkne (by nlinarith)
          · intro hnot; exact absurd hk₀_mem hnot
        · rw [if_neg hsq, mul_zero]
          refine Finset.sum_eq_zero fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          rw [if_neg]; intro hkeq; exact hsq ⟨k, hk.1, hkeq⟩
    exact (h0.add hterms).trans hphi_sum
  have hfinal : AgreeUpto d (f 2 (by decide) * phiNeg) ((f 1 (by decide)) ^ 2) := by
    have hmul : AgreeUpto d
        (f 2 (by decide) * (((-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1)) * f 2 (by decide)))
        (f 2 (by decide) * phiNeg) :=
      (AgreeUpto.refl d _).mul hsum_phiNeg
    have hrew : f 2 (by decide) * (((-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1)) * f 2 (by decide)) =
        ((-1 : ℤ⟦X⟧) ^ N * (P N).eval (-1)) * f 2 (by decide) ^ 2 := by ring
    rw [hrew] at hmul
    exact hmul.symm.trans hprod_f1
  exact hfinal d le_rfl

/-- Gauss identity `(J1)` in expanded form: `f_2(q) * ψ(q^2) = f_4(q)^2`. -/
private theorem gauss_J1_expand2 :
    f 2 (by decide) * psi.expand 2 (by decide) = (f 4 (by decide)) ^ 2 := by
  ext m
  let N := 4 * m + 10
  have hN : 1 ≤ N := by omega
  let D := N + m
  have heval_prod : (P N).eval q =
      2 * q ^ N * (1 + q ^ (2 * N)) * (∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2 := by
    rw [P, Polynomial.eval_prod]
    have hfac : ∀ j ∈ Finset.range N, (Q j).eval q =
        q * (1 + q ^ (2 * (j + 1))) * (1 + q ^ (2 * j)) := by
      intro j _
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_C, Polynomial.eval_X]
      have h1 : q ^ (2 * j + 1) * q = q ^ (2 * (j + 1)) := by ring
      have h2 : q + q ^ (2 * j + 1) = q * (1 + q ^ (2 * j)) := by
        rw [pow_succ']; ring
      rw [h1, h2]; ring
    rw [Finset.prod_congr rfl hfac]
    have hsplit : ∏ j ∈ Finset.range N, (q * (1 + q ^ (2 * (j + 1))) * (1 + q ^ (2 * j))) =
        (∏ _j ∈ Finset.range N, q) *
        (∏ j ∈ Finset.range N, (1 + q ^ (2 * (j + 1)))) *
        (∏ j ∈ Finset.range N, (1 + q ^ (2 * j))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rw [hsplit]
    have hqN : ∏ _j ∈ Finset.range N, q = q ^ N := by simp
    have hN1 : N = (N - 1) + 1 := by omega
    have hp1 : ∏ j ∈ Finset.range N, (1 + q ^ (2 * (j + 1))) =
        (∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) * (1 + q ^ (2 * N)) := by
      conv_lhs => rw [hN1, Finset.prod_range_succ]
      rw [← hN1]
    have hp2 : ∏ j ∈ Finset.range N, (1 + q ^ (2 * j)) =
        2 * ∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1))) := by
      conv_lhs => rw [hN1, Finset.prod_range_succ']
      simp only [mul_zero, pow_zero]
      ring
    rw [hqN, hp1, hp2]; ring
  have hprod_f4 : AgreeUpto D ((P N).eval q * f 2 (by decide) ^ 2)
      (2 * q ^ N * (f 4 (by decide)) ^ 2) := by
    rw [heval_prod]
    have h1add : AgreeUpto m (1 + q ^ (2 * N)) 1 := AgreeUpto.one_add_X_pow (by omega)
    have hf2 : AgreeUpto m (∏ j ∈ Finset.range (N - 1), (1 - q ^ (2 * (j + 1)))) (f 2 (by decide)) :=
      agreeUpto_finprod_f 2 (by decide) m (N - 1) (by omega)
    have hf4 : AgreeUpto m (∏ j ∈ Finset.range (N - 1), (1 - q ^ (4 * (j + 1)))) (f 4 (by decide)) :=
      agreeUpto_finprod_f 4 (by decide) m (N - 1) (by omega)
    have hdiff_sq :
        (∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) *
        (∏ j ∈ Finset.range (N - 1), (1 - q ^ (2 * (j + 1)))) =
        ∏ j ∈ Finset.range (N - 1), (1 - q ^ (4 * (j + 1))) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      have h4 : q ^ (2 * (j + 1)) * q ^ (2 * (j + 1)) = q ^ (4 * (j + 1)) := by
        rw [← pow_add]; congr 1; omega
      linear_combination -h4
    have hinner : AgreeUpto m
        ((1 + q ^ (2 * N)) *
          ((∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2 * f 2 (by decide) ^ 2))
        ((f 4 (by decide)) ^ 2) := by
      have ha : AgreeUpto m
          ((∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2 * f 2 (by decide) ^ 2)
          ((∏ j ∈ Finset.range (N - 1), (1 - q ^ (4 * (j + 1)))) ^ 2) := by
        have hstep := (AgreeUpto.refl m ((∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2)).mul
          (hf2.symm.pow 2)
        have hrhs : (∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2 *
            (∏ j ∈ Finset.range (N - 1), (1 - q ^ (2 * (j + 1)))) ^ 2 =
            (∏ j ∈ Finset.range (N - 1), (1 - q ^ (4 * (j + 1)))) ^ 2 := by
          rw [← mul_pow, hdiff_sq]
        rw [hrhs] at hstep
        exact hstep
      simpa using h1add.mul (ha.trans (hf4.pow 2))
    intro n hn
    have hrew1 : 2 * q ^ N * (1 + q ^ (2 * N)) *
        (∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2 * f 2 (by decide) ^ 2 =
        q ^ N * (2 * ((1 + q ^ (2 * N)) *
          ((∏ j ∈ Finset.range (N - 1), (1 + q ^ (2 * (j + 1)))) ^ 2 * f 2 (by decide) ^ 2))) := by
      ring
    have hrew2 : 2 * q ^ N * (f 4 (by decide)) ^ 2 = q ^ N * (2 * (f 4 (by decide)) ^ 2) := by ring
    rw [hrew1, hrew2]
    by_cases hnN : N ≤ n
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnN
      rw [coeff_X_pow_mul_add, coeff_X_pow_mul_add]
      exact ((AgreeUpto.refl m (2 : ℤ⟦X⟧)).mul hinner) r (by omega)
    · rw [coeff_X_pow_mul_of_lt (by omega), coeff_X_pow_mul_of_lt (by omega)]
  have hsum_psi : AgreeUpto D ((P N).eval q * f 2 (by decide))
      (2 * q ^ N * psi.expand 2 (by decide)) := by
    rw [eval_P_eq_sum, Finset.sum_mul]
    have hsplit : ∑ i ∈ Finset.range (2 * N + 1), (P N).coeff i * q ^ i * f 2 (by decide) =
        (P N).coeff (2 * N) * q ^ (2 * N) * f 2 (by decide) +
        ∑ r ∈ Finset.range N,
          ((P N).coeff (N + r) * q ^ (N + r) * f 2 (by decide) +
           (P N).coeff (N - (r + 1)) * q ^ (N - (r + 1)) * f 2 (by decide)) := by
      rw [Finset.sum_range_succ, add_comm]
      congr 1
      rw [Finset.sum_add_distrib]
      have h2N_range : Finset.range (2 * N) =
          (Finset.range N).image (fun r => N + r) ∪
          (Finset.range N).image (fun r => N - (r + 1)) := by
        ext i
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
        constructor
        · intro hi
          by_cases h : N ≤ i
          · left; exact ⟨i - N, by omega, by omega⟩
          · right; exact ⟨N - 1 - i, by omega, by omega⟩
        · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) <;> omega
      rw [h2N_range, Finset.sum_union]
      · rw [Finset.sum_image, Finset.sum_image]
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_range] at ha hb
          dsimp only at hab; omega
        · intro a _ b _ hab
          dsimp only at hab; omega
      · rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [Finset.mem_image, Finset.mem_range] at hi1 hi2
        rcases hi1 with ⟨a, ha, rfl⟩
        rcases hi2 with ⟨b, hb, hab⟩
        omega
    rw [hsplit]
    have hlast : AgreeUpto D ((P N).coeff (2 * N) * q ^ (2 * N) * f 2 (by decide)) 0 := by
      rw [(P_palindromic N).2.2]
      have hpow : q ^ (N * N) * q ^ (2 * N) = q ^ (N * N + 2 * N) := (pow_add q _ _).symm
      rw [hpow]
      have hbig : D < N * N + 2 * N := by dsimp only [D, N]; nlinarith
      simpa [zero_mul] using (AgreeUpto.X_pow_zero hbig).mul (AgreeUpto.refl D (f 2 (by decide)))
    have hpair : AgreeUpto D
        (∑ r ∈ Finset.range N,
          ((P N).coeff (N + r) * q ^ (N + r) * f 2 (by decide) +
           (P N).coeff (N - (r + 1)) * q ^ (N - (r + 1)) * f 2 (by decide)))
        (∑ r ∈ Finset.range N, 2 * q ^ (N + r * (r + 1))) := by
      refine AgreeUpto.sum _ fun r hr => ?_
      rw [Finset.mem_range] at hr
      rw [P_coeff_symm N (r + 1) (by omega)]
      by_cases hrm : r ≤ m + 1
      · have ha : AgreeUpto (2 * m + 2) ((P N).coeff (N + r) * f 2 (by decide)) (q ^ (r * r)) :=
          P_coeff_mul_f2_agreeUpto hN (by omega) (by omega)
        have hb : AgreeUpto (2 * m + 2) ((P N).coeff (N + (r + 1)) * f 2 (by decide))
            (q ^ ((r + 1) * (r + 1))) :=
          P_coeff_mul_f2_agreeUpto hN (by omega) (by omega)
        have ha_shift : AgreeUpto D ((P N).coeff (N + r) * q ^ (N + r) * f 2 (by decide))
            (q ^ (N + r * (r + 1))) := by
          intro n hn
          have hrew : (P N).coeff (N + r) * q ^ (N + r) * f 2 (by decide) =
              q ^ (N + r) * ((P N).coeff (N + r) * f 2 (by decide)) := by ring
          have hrew2 : q ^ (N + r * (r + 1)) = q ^ (N + r) * q ^ (r * r) := by
            rw [← pow_add]; congr 1; ring
          rw [hrew, hrew2]
          by_cases hle : N + r ≤ n
          · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hle
            rw [coeff_X_pow_mul_add, coeff_X_pow_mul_add]
            exact ha s (by omega)
          · rw [coeff_X_pow_mul_of_lt (by omega), coeff_X_pow_mul_of_lt (by omega)]
        have hb_shift : AgreeUpto D
            ((P N).coeff (N + (r + 1)) * q ^ (N - (r + 1)) * f 2 (by decide))
            (q ^ (N + r * (r + 1))) := by
          intro n hn
          have hrew : (P N).coeff (N + (r + 1)) * q ^ (N - (r + 1)) * f 2 (by decide) =
              q ^ (N - (r + 1)) * ((P N).coeff (N + (r + 1)) * f 2 (by decide)) := by ring
          have hrew2 : q ^ (N + r * (r + 1)) = q ^ (N - (r + 1)) * q ^ ((r + 1) * (r + 1)) := by
            rw [← pow_add]; congr 1
            zify [show r + 1 ≤ N by omega]; ring
          rw [hrew, hrew2]
          by_cases hle : N - (r + 1) ≤ n
          · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hle
            rw [coeff_X_pow_mul_add, coeff_X_pow_mul_add]
            exact hb s (by omega)
          · rw [coeff_X_pow_mul_of_lt (by omega), coeff_X_pow_mul_of_lt (by omega)]
        simpa [two_mul] using ha_shift.add hb_shift
      · have ha : AgreeUpto D ((P N).coeff (N + r) * q ^ (N + r) * f 2 (by decide)) 0 := by
          have hz : AgreeUpto (m + r + 1) ((P N).coeff (N + r)) 0 :=
            P_coeff_zero_agreeUpto hN (by omega) (by nlinarith)
          intro n hn
          have hrew : (P N).coeff (N + r) * q ^ (N + r) * f 2 (by decide) =
              q ^ (N + r) * ((P N).coeff (N + r) * f 2 (by decide)) := by ring
          rw [hrew, map_zero]
          by_cases hle : N + r ≤ n
          · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hle
            rw [coeff_X_pow_mul_add]
            simpa using (hz.mul (AgreeUpto.refl _ (f 2 (by decide)))) s (by omega)
          · rw [coeff_X_pow_mul_of_lt (by omega)]
        have hb : AgreeUpto D
            ((P N).coeff (N + (r + 1)) * q ^ (N - (r + 1)) * f 2 (by decide)) 0 := by
          have hz : AgreeUpto (m + r + 1) ((P N).coeff (N + (r + 1))) 0 :=
            P_coeff_zero_agreeUpto hN (by omega) (by nlinarith)
          intro n hn
          have hrew : (P N).coeff (N + (r + 1)) * q ^ (N - (r + 1)) * f 2 (by decide) =
              q ^ (N - (r + 1)) * ((P N).coeff (N + (r + 1)) * f 2 (by decide)) := by ring
          rw [hrew, map_zero]
          by_cases hle : N - (r + 1) ≤ n
          · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hle
            rw [coeff_X_pow_mul_add]
            simpa using (hz.mul (AgreeUpto.refl _ (f 2 (by decide)))) s (by omega)
          · rw [coeff_X_pow_mul_of_lt (by omega)]
        have hzero_rhs : AgreeUpto D (2 * q ^ (N + r * (r + 1))) 0 := by
          have hbig : D < N + r * (r + 1) := by dsimp only [D]; nlinarith
          simpa [mul_zero] using (AgreeUpto.refl D (2 : ℤ⟦X⟧)).mul (AgreeUpto.X_pow_zero hbig)
        simpa using (ha.add hb).trans hzero_rhs.symm
    have hpsi_sum : AgreeUpto D (∑ r ∈ Finset.range N, 2 * q ^ (N + r * (r + 1)))
        (2 * q ^ N * psi.expand 2 (by decide)) := by
      intro n hn
      rw [map_sum]
      have hterm : ∀ r ∈ Finset.range N,
          (2 * q ^ (N + r * (r + 1))).coeff n = if N + r * (r + 1) = n then 2 else 0 := by
        intro r _
        have hc : (2 : ℤ⟦X⟧) = PowerSeries.C 2 := by simp
        rw [hc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
        by_cases h : n = N + r * (r + 1)
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl hterm]
      have hrew : 2 * q ^ N * psi.expand 2 (by decide) =
          q ^ N * (PowerSeries.C 2 * psi.expand 2 (by decide)) := by simp; ring
      rw [hrew]
      by_cases hnN : N ≤ n
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hnN
        rw [coeff_X_pow_mul_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
        by_cases htri : ∃ r : ℕ, r * (r + 1) = s
        · rcases htri with ⟨r₀, hr₀⟩
          have hr₀N : r₀ ∈ Finset.range N := by
            rw [Finset.mem_range]; dsimp only [D, N] at *; nlinarith
          rw [Finset.sum_eq_single r₀]
          · rw [if_pos (by omega)]
            have hev : 2 ∣ s := by
              rw [← hr₀]
              exact (Nat.even_mul_succ_self r₀).two_dvd
            rw [if_pos hev]
            simp only [psi, PowerSeries.coeff_mk]
            have hhalf : r₀ * (r₀ + 1) / 2 = s / 2 := by rw [hr₀]
            rw [if_pos ⟨r₀, hhalf⟩]; ring
          · intro r _ hrne
            rw [if_neg]; intro heq
            have : r * (r + 1) = r₀ * (r₀ + 1) := by omega
            exact hrne (by nlinarith)
          · intro hnot; exact absurd hr₀N hnot
        · have hzeroL : ∑ r ∈ Finset.range N, (if N + r * (r + 1) = N + s then (2 : ℤ) else 0) = 0 := by
            refine Finset.sum_eq_zero fun r _ => if_neg ?_
            intro heq; exact htri ⟨r, by omega⟩
          rw [hzeroL]
          split_ifs with hev
          · simp only [psi, PowerSeries.coeff_mk]
            rw [if_neg]
            · simp
            · rintro ⟨r, hr⟩
              apply htri; refine ⟨r, ?_⟩
              have heven_r : 2 ∣ r * (r + 1) := (Nat.even_mul_succ_self r).two_dvd
              have h1 := Nat.mul_div_cancel' heven_r
              have h2 := Nat.mul_div_cancel' hev
              omega
          · simp
      · rw [coeff_X_pow_mul_of_lt (by omega)]
        refine Finset.sum_eq_zero fun r _ => if_neg (by omega)
    have hadd := hlast.add hpair
    rw [zero_add] at hadd
    exact hadd.trans hpsi_sum
  have hcomb : AgreeUpto D (2 * q ^ N * (f 2 (by decide) * psi.expand 2 (by decide)))
      (2 * q ^ N * (f 4 (by decide)) ^ 2) := by
    have h1 : AgreeUpto D ((P N).eval q * f 2 (by decide) * f 2 (by decide))
        ((2 * q ^ N * psi.expand 2 (by decide)) * f 2 (by decide)) :=
      hsum_psi.mul (AgreeUpto.refl D _)
    have h2 : (P N).eval q * f 2 (by decide) * f 2 (by decide) =
        (P N).eval q * f 2 (by decide) ^ 2 := by ring
    have h3 : (2 * q ^ N * psi.expand 2 (by decide)) * f 2 (by decide) =
        2 * q ^ N * (f 2 (by decide) * psi.expand 2 (by decide)) := by ring
    rw [h2, h3] at h1
    exact h1.symm.trans hprod_f4
  have hcoeff := hcomb (N + m) le_rfl
  have hrew : ∀ H : ℤ⟦X⟧, (2 * q ^ N * H).coeff (N + m) = 2 * H.coeff m := by
    intro H
    have hc : 2 * q ^ N * H = q ^ N * (PowerSeries.C 2 * H) := by simp; ring
    rw [hc, coeff_X_pow_mul_add, PowerSeries.coeff_C_mul]
  rw [hrew, hrew] at hcoeff
  omega

/-- Gauss identity `(J1)`: `f_1(q) * ψ(q) = f_2(q)^2`. -/
theorem gauss_J1 : f 1 (by decide) * psi = (f 2 (by decide)) ^ 2 := by
  ext n
  have h := congrArg (fun s : ℤ⟦X⟧ => s.coeff (2 * n)) gauss_J1_expand2
  have hf2 : f 2 (by decide) = (f 1 (by decide)).expand 2 (by decide) := by
    rw [f, f, PowerSeries.expand_one_apply]
  have hf4 : f 4 (by decide) = (f 2 (by decide)).expand 2 (by decide) := by
    rw [f, f, ← PowerSeries.expand_mul]
  have hL : (f 2 (by decide) * psi.expand 2 (by decide)) =
      (f 1 (by decide) * psi).expand 2 (by decide) := by
    rw [map_mul, hf2]
  have hR : (f 4 (by decide)) ^ 2 = ((f 2 (by decide)) ^ 2).expand 2 (by decide) := by
    rw [map_pow, hf4]
  rw [hL, hR, PowerSeries.coeff_expand_mul, PowerSeries.coeff_expand_mul] at h
  exact h

end JacobiTripleProduct

/-! ## Section 3: Bijective Proof of `ψ(q) ψ(q^3) = φ(q^6) ψ(q^4) + q φ(q^2) ψ(q^{12})` -/

section PsiProductIdentity

private lemma coeff_psi_eq (n : ℕ) :
    open Classical in
    psi.coeff n = if ∃ a : ℕ, a * (a + 1) / 2 = n then 1 else 0 := by
  simp [psi]

private lemma int_sq_eq_natAbs_sq (u : ℤ) : ((u.natAbs ^ 2 : ℕ) : ℤ) = u ^ 2 := by
  rw [Nat.cast_pow, sq, sq]
  exact Int.natAbs_mul_self' u

private lemma odd_natAbs_eq (z : ℤ) (hz : z % 2 ≠ 0) :
    (2 * (((z.natAbs - 1) / 2 : ℕ) : ℤ) + 1) = (z.natAbs : ℤ) := by
  have h1 : z.natAbs % 2 = 1 := by omega
  have h2 : 2 * ((z.natAbs - 1) / 2) + 1 = z.natAbs := by omega
  exact_mod_cast h2

private lemma odd_natAbs_sq (z : ℤ) (hz : z % 2 ≠ 0) :
    (2 * (((z.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 = z ^ 2 := by
  rw [odd_natAbs_eq z hz]
  exact (Nat.cast_pow _ 2).symm.trans (int_sq_eq_natAbs_sq z)

private lemma coeff_phi_eq_card (m : ℕ) :
    phi.coeff m = (((Finset.Icc (-(m : ℤ)) m).filter (fun u : ℤ => u * u = (m : ℤ))).card : ℤ) := by
  open Classical in
  simp only [phi, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · subst hm
    have hfilt : ((Finset.Icc (0 : ℤ) 0).filter (fun u : ℤ => u * u = 0)) = {0} := by decide
    rw [if_pos rfl, Nat.cast_zero, neg_zero, hfilt]
    norm_num
  · rw [if_neg hm]
    by_cases hsq : ∃ k : ℕ, 0 < k ∧ k * k = m
    · rcases hsq with ⟨k, hk_pos, hk_eq⟩
      rw [if_pos ⟨k, hk_pos, hk_eq⟩]
      have hfilt : ((Finset.Icc (-(m : ℤ)) m).filter (fun u : ℤ => u * u = (m : ℤ))) =
          {(k : ℤ), -(k : ℤ)} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hu⟩
          have hsq' : u * u = (k : ℤ) * (k : ℤ) := by
            rw [hu, ← hk_eq]; push_cast; rfl
          have hfac : (u - k) * (u + k) = 0 := by linarith
          rcases mul_eq_zero.mp hfac with h1 | h2
          · left; omega
          · right; omega
        · rintro (rfl | rfl)
          · refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
            rw [← hk_eq]; push_cast; rfl
          · refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
            rw [← hk_eq]; push_cast; ring
      rw [hfilt, Finset.card_pair (by omega)]
      norm_num
    · rw [if_neg hsq]
      have hfilt : ((Finset.Icc (-(m : ℤ)) m).filter (fun u : ℤ => u * u = (m : ℤ))) = ∅ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
        intro _ hu
        apply hsq
        refine ⟨u.natAbs, ?_, ?_⟩
        · have : u ≠ 0 := by intro h0; subst h0; simp at hu; omega
          exact Int.natAbs_pos.mpr this
        · have h1 : ((u.natAbs * u.natAbs : ℕ) : ℤ) = u * u := by
            rw [Nat.cast_mul]; exact Int.natAbs_mul_self' u
          omega
      rw [hfilt]; norm_num

private def setL (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab =>
    (2 * ab.1 + 1) ^ 2 + 3 * (2 * ab.2 + 1) ^ 2 = 8 * n + 4

private noncomputable def setR1 (n : ℕ) : Finset (ℤ × ℕ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.range (n + 1)).filter fun uc =>
    (2 * (uc.2 : ℤ) + 1) ^ 2 + 12 * uc.1 ^ 2 = 2 * (n : ℤ) + 1

private noncomputable def setR2 (n : ℕ) : Finset (ℤ × ℕ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.range (n + 1)).filter fun vd =>
    4 * vd.1 ^ 2 + 3 * (2 * (vd.2 : ℤ) + 1) ^ 2 = 2 * (n : ℤ) + 1

private def fwdMap (ab : ℕ × ℕ) : (ℤ × ℕ) ⊕ (ℤ × ℕ) :=
  let x : ℤ := 2 * (ab.1 : ℤ) + 1
  let y : ℤ := 2 * (ab.2 : ℤ) + 1
  let yt : ℤ := if (x - y) % 4 = 0 then y else -y
  let p : ℤ := (x + 3 * yt) / 4
  let q' : ℤ := (x - yt) / 4
  if p % 2 ≠ 0 then
    Sum.inl (if 0 < p then q' / 2 else -(q' / 2), (p.natAbs - 1) / 2)
  else
    Sum.inr (if 0 < q' then p / 2 else -(p / 2), (q'.natAbs - 1) / 2)

private def bwdMap : (ℤ × ℕ) ⊕ (ℤ × ℕ) → ℕ × ℕ
  | Sum.inl (u, c) =>
      let s : ℤ := 2 * (c : ℤ) + 1
      (((s + 6 * u).natAbs - 1) / 2, ((s - 2 * u).natAbs - 1) / 2)
  | Sum.inr (v, d) =>
      let t : ℤ := 2 * (d : ℤ) + 1
      (((2 * v + 3 * t).natAbs - 1) / 2, ((2 * v - t).natAbs - 1) / 2)

private lemma parity_helper {p q' : ℤ} {n : ℕ} (hpq : p ^ 2 + 3 * q' ^ 2 = 2 * (n : ℤ) + 1) :
    (p % 2 ≠ 0 → q' % 2 = 0) ∧ (p % 2 = 0 → q' % 2 ≠ 0) := by
  have hmod : ∀ z : ℤ, z ^ 2 % 2 = z % 2 := by
    intro z
    rcases Int.emod_two_eq_zero_or_one z with h | h <;> simp [sq, Int.mul_emod, h]
  have hp2 := hmod p
  have hq2 := hmod q'
  constructor <;> intro hp <;> omega

private lemma fwdMap_decomp (a b n : ℕ)
    (heq : (2 * a + 1) ^ 2 + 3 * (2 * b + 1) ^ 2 = 8 * n + 4) :
    let x : ℤ := 2 * (a : ℤ) + 1
    let y : ℤ := 2 * (b : ℤ) + 1
    let yt : ℤ := if (x - y) % 4 = 0 then y else -y
    let p : ℤ := (x + 3 * yt) / 4
    let q' : ℤ := (x - yt) / 4
    4 * p = x + 3 * yt ∧ 4 * q' = x - yt ∧
    p ^ 2 + 3 * q' ^ 2 = 2 * (n : ℤ) + 1 ∧ yt.natAbs = 2 * b + 1 := by
  dsimp only
  set x : ℤ := 2 * (a : ℤ) + 1
  set y : ℤ := 2 * (b : ℤ) + 1
  set yt : ℤ := if (x - y) % 4 = 0 then y else -y
  set p : ℤ := (x + 3 * yt) / 4
  set q' : ℤ := (x - yt) / 4
  have hxy : x ^ 2 + 3 * y ^ 2 = 8 * (n : ℤ) + 4 := by
    dsimp only [x, y]; exact_mod_cast heq
  have hyt_sq : yt ^ 2 = y ^ 2 := by dsimp [yt]; split_ifs <;> ring
  have hp4 : 4 * p = x + 3 * yt := Int.mul_ediv_cancel' (by dsimp [yt]; split_ifs <;> omega)
  have hq4 : 4 * q' = x - yt := Int.mul_ediv_cancel' (by dsimp [yt]; split_ifs <;> omega)
  have h16 : 16 * (p ^ 2 + 3 * q' ^ 2) = 4 * (x ^ 2 + 3 * yt ^ 2) := by
    have : (4 * p) ^ 2 + 3 * (4 * q') ^ 2 = (x + 3 * yt) ^ 2 + 3 * (x - yt) ^ 2 := by
      rw [hp4, hq4]
    linarith
  have hpq : p ^ 2 + 3 * q' ^ 2 = 2 * (n : ℤ) + 1 := by linarith
  have hyt_abs : yt.natAbs = 2 * b + 1 := by dsimp [yt]; split_ifs <;> omega
  exact ⟨hp4, hq4, hpq, hyt_abs⟩

private lemma fwdMap_mem (n : ℕ) (ab : ℕ × ℕ) (hab : ab ∈ setL n) :
    fwdMap ab ∈ (setR1 n).disjSum (setR2 n) := by
  rcases ab with ⟨a, b⟩
  simp only [setL, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
  obtain ⟨_, heq⟩ := hab
  have hd := fwdMap_decomp a b n heq
  dsimp only at hd
  set x : ℤ := 2 * (a : ℤ) + 1
  set y : ℤ := 2 * (b : ℤ) + 1
  set yt : ℤ := if (x - y) % 4 = 0 then y else -y
  set p : ℤ := (x + 3 * yt) / 4
  set q' : ℤ := (x - yt) / 4
  rcases hd with ⟨hp4, hq4, hpq, _⟩
  have hpar := parity_helper hpq
  change (if p % 2 ≠ 0 then
      Sum.inl (if 0 < p then q' / 2 else -(q' / 2), (p.natAbs - 1) / 2)
    else
      Sum.inr (if 0 < q' then p / 2 else -(p / 2), (q'.natAbs - 1) / 2)) ∈
    (setR1 n).disjSum (setR2 n)
  by_cases hpodd : p % 2 ≠ 0
  · rw [if_pos hpodd, Finset.inl_mem_disjSum]
    simp only [setR1, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    have hqeven : q' % 2 = 0 := hpar.1 hpodd
    have hq2 : 2 * (q' / 2) = q' := by omega
    have hp_sq := odd_natAbs_sq p hpodd
    have hu_sq : (if 0 < p then q' / 2 else -(q' / 2)) ^ 2 = (q' / 2) ^ 2 := by
      split_ifs <;> ring
    have h12 : 12 * (q' / 2) ^ 2 = 3 * q' ^ 2 := by
      conv_rhs => rw [← hq2]
      ring
    have heq1 : (2 * (((p.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 +
        12 * (if 0 < p then q' / 2 else -(q' / 2)) ^ 2 = 2 * (n : ℤ) + 1 := by
      rw [hp_sq, hu_sq]; linarith
    have hq_sq_le : 12 * (q' / 2) ^ 2 ≤ 2 * (n : ℤ) + 1 := by
      have : 0 ≤ p ^ 2 := sq_nonneg p
      linarith
    have hu_bound : -(n : ℤ) ≤ q' / 2 ∧ q' / 2 ≤ (n : ℤ) := by
      constructor <;> nlinarith
    have hp_bound : (p.natAbs - 1) / 2 < n + 1 := by
      have hpn : ((p.natAbs : ℤ)) ^ 2 = p ^ 2 := (Nat.cast_pow _ 2).symm.trans (int_sq_eq_natAbs_sq p)
      have h3 : 0 ≤ 3 * q' ^ 2 := by positivity
      have hle : ((p.natAbs : ℤ)) ^ 2 ≤ 2 * (n : ℤ) + 1 := by linarith
      have hle' : (p.natAbs : ℤ) ≤ 2 * (n : ℤ) + 1 := by nlinarith
      omega
    refine ⟨⟨⟨?_, ?_⟩, hp_bound⟩, heq1⟩
    · split_ifs <;> omega
    · split_ifs <;> omega
  · rw [if_neg hpodd, Finset.inr_mem_disjSum]
    simp only [setR2, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    push Not at hpodd
    have hqodd : q' % 2 ≠ 0 := hpar.2 hpodd
    have hp2 : 2 * (p / 2) = p := by omega
    have hq_sq := odd_natAbs_sq q' hqodd
    have hv_sq : (if 0 < q' then p / 2 else -(p / 2)) ^ 2 = (p / 2) ^ 2 := by
      split_ifs <;> ring
    have h4 : 4 * (p / 2) ^ 2 = p ^ 2 := by
      conv_rhs => rw [← hp2]
      ring
    have heq2 : 4 * (if 0 < q' then p / 2 else -(p / 2)) ^ 2 +
        3 * (2 * (((q'.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 = 2 * (n : ℤ) + 1 := by
      rw [hq_sq, hv_sq]; linarith
    have hv_bound : -(n : ℤ) ≤ p / 2 ∧ p / 2 ≤ (n : ℤ) := by
      have h3 : 0 ≤ 3 * q' ^ 2 := by positivity
      constructor <;> nlinarith
    have hq_bound : (q'.natAbs - 1) / 2 < n + 1 := by
      have hqn : ((q'.natAbs : ℤ)) ^ 2 = q' ^ 2 := (Nat.cast_pow _ 2).symm.trans (int_sq_eq_natAbs_sq q')
      have hp0 : 0 ≤ p ^ 2 := sq_nonneg p
      have hle : 3 * ((q'.natAbs : ℤ)) ^ 2 ≤ 2 * (n : ℤ) + 1 := by linarith
      have hle' : (q'.natAbs : ℤ) ≤ 2 * (n : ℤ) + 1 := by nlinarith
      omega
    refine ⟨⟨⟨?_, ?_⟩, hq_bound⟩, heq2⟩
    · split_ifs <;> omega
    · split_ifs <;> omega

private lemma bwdMap_mem (n : ℕ) (z : (ℤ × ℕ) ⊕ (ℤ × ℕ)) (hz : z ∈ (setR1 n).disjSum (setR2 n)) :
    bwdMap z ∈ setL n := by
  rcases z with ⟨u, c⟩ | ⟨v, d⟩
  · rw [Finset.inl_mem_disjSum] at hz
    simp only [setR1, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hz
    rcases hz with ⟨_, heq⟩
    dsimp only [bwdMap]
    simp only [setL, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    set s : ℤ := 2 * (c : ℤ) + 1
    set x' : ℤ := s + 6 * u
    set y' : ℤ := s - 2 * u
    have hxsq := odd_natAbs_sq x' (by omega)
    have hysq := odd_natAbs_sq y' (by omega)
    have hsum : x' ^ 2 + 3 * y' ^ 2 = 8 * (n : ℤ) + 4 := by
      have halg : x' ^ 2 + 3 * y' ^ 2 = 4 * (s ^ 2 + 12 * u ^ 2) := by dsimp [x', y']; ring
      linarith
    have hnat : (2 * ((x'.natAbs - 1) / 2) + 1) ^ 2 +
        3 * (2 * ((y'.natAbs - 1) / 2) + 1) ^ 2 = 8 * n + 4 := by
      have hz_eq : (2 * (((x'.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 +
          3 * (2 * (((y'.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 = 8 * (n : ℤ) + 4 := by
        rw [hxsq, hysq]; exact hsum
      exact_mod_cast hz_eq
    refine ⟨⟨?_, ?_⟩, hnat⟩ <;> nlinarith
  · rw [Finset.inr_mem_disjSum] at hz
    simp only [setR2, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hz
    rcases hz with ⟨_, heq⟩
    dsimp only [bwdMap]
    simp only [setL, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    set t : ℤ := 2 * (d : ℤ) + 1
    set x' : ℤ := 2 * v + 3 * t
    set y' : ℤ := 2 * v - t
    have hxsq := odd_natAbs_sq x' (by omega)
    have hysq := odd_natAbs_sq y' (by omega)
    have hsum : x' ^ 2 + 3 * y' ^ 2 = 8 * (n : ℤ) + 4 := by
      have halg : x' ^ 2 + 3 * y' ^ 2 = 4 * (4 * v ^ 2 + 3 * t ^ 2) := by dsimp [x', y']; ring
      linarith
    have hnat : (2 * ((x'.natAbs - 1) / 2) + 1) ^ 2 +
        3 * (2 * ((y'.natAbs - 1) / 2) + 1) ^ 2 = 8 * n + 4 := by
      have hz_eq : (2 * (((x'.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 +
          3 * (2 * (((y'.natAbs - 1) / 2 : ℕ) : ℤ) + 1) ^ 2 = 8 * (n : ℤ) + 4 := by
        rw [hxsq, hysq]; exact hsum
      exact_mod_cast hz_eq
    refine ⟨⟨?_, ?_⟩, hnat⟩ <;> nlinarith

private lemma bwdMap_fwdMap (n : ℕ) (ab : ℕ × ℕ) (hab : ab ∈ setL n) :
    bwdMap (fwdMap ab) = ab := by
  rcases ab with ⟨a, b⟩
  simp only [setL, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
  obtain ⟨_, heq⟩ := hab
  have hd := fwdMap_decomp a b n heq
  dsimp only at hd
  set x : ℤ := 2 * (a : ℤ) + 1
  set y : ℤ := 2 * (b : ℤ) + 1
  set yt : ℤ := if (x - y) % 4 = 0 then y else -y
  set p : ℤ := (x + 3 * yt) / 4
  set q' : ℤ := (x - yt) / 4
  rcases hd with ⟨hp4, hq4, hpq, hyt_abs⟩
  have hpar := parity_helper hpq
  change bwdMap (if p % 2 ≠ 0 then
      Sum.inl (if 0 < p then q' / 2 else -(q' / 2), (p.natAbs - 1) / 2)
    else
      Sum.inr (if 0 < q' then p / 2 else -(p / 2), (q'.natAbs - 1) / 2)) = (a, b)
  by_cases hpodd : p % 2 ≠ 0
  · rw [if_pos hpodd]; dsimp only [bwdMap]
    have hqeven : q' % 2 = 0 := hpar.1 hpodd
    rw [odd_natAbs_eq p hpodd]
    ext
    · split_ifs with hppos
      · have h1 : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg (by omega)
        have h2 : p + 6 * (q' / 2) = x := by omega
        rw [h1, h2]; omega
      · have h1 : (p.natAbs : ℤ) = -p := Int.ofNat_natAbs_of_nonpos (by omega)
        have h2 : -p + 6 * -(q' / 2) = -x := by omega
        rw [h1, h2, Int.natAbs_neg]; omega
    · split_ifs with hppos
      · have h1 : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg (by omega)
        have h2 : p - 2 * (q' / 2) = yt := by omega
        rw [h1, h2, hyt_abs]; omega
      · have h1 : (p.natAbs : ℤ) = -p := Int.ofNat_natAbs_of_nonpos (by omega)
        have h2 : -p - 2 * -(q' / 2) = -yt := by omega
        rw [h1, h2, Int.natAbs_neg, hyt_abs]; omega
  · rw [if_neg hpodd]; dsimp only [bwdMap]
    push Not at hpodd
    have hqodd : q' % 2 ≠ 0 := hpar.2 hpodd
    rw [odd_natAbs_eq q' hqodd]
    ext
    · split_ifs with hqpos
      · have h1 : (q'.natAbs : ℤ) = q' := Int.natAbs_of_nonneg (by omega)
        have h2 : 2 * (p / 2) + 3 * q' = x := by omega
        rw [h1, h2]; omega
      · have h1 : (q'.natAbs : ℤ) = -q' := Int.ofNat_natAbs_of_nonpos (by omega)
        have h2 : 2 * -(p / 2) + 3 * -q' = -x := by omega
        rw [h1, h2, Int.natAbs_neg]; omega
    · split_ifs with hqpos
      · have h1 : (q'.natAbs : ℤ) = q' := Int.natAbs_of_nonneg (by omega)
        have h2 : 2 * (p / 2) - q' = yt := by omega
        rw [h1, h2, hyt_abs]; omega
      · have h1 : (q'.natAbs : ℤ) = -q' := Int.ofNat_natAbs_of_nonpos (by omega)
        have h2 : 2 * -(p / 2) - -q' = -yt := by omega
        rw [h1, h2, Int.natAbs_neg, hyt_abs]; omega

private lemma fwdMap_bwdMap (z : (ℤ × ℕ) ⊕ (ℤ × ℕ)) : fwdMap (bwdMap z) = z := by
  rcases z with ⟨u, c⟩ | ⟨v, d⟩
  · dsimp only [bwdMap, fwdMap]
    set s : ℤ := 2 * (c : ℤ) + 1
    set x' : ℤ := s + 6 * u
    set y' : ℤ := s - 2 * u
    rw [odd_natAbs_eq x' (by omega), odd_natAbs_eq y' (by omega)]
    by_cases hxpos : 0 < x'
    · have hx_val : (x'.natAbs : ℤ) = x' := Int.natAbs_of_nonneg (by omega)
      rw [hx_val]
      have hyt_val : (if (x' - (y'.natAbs : ℤ)) % 4 = 0 then (y'.natAbs : ℤ) else -(y'.natAbs : ℤ)) = y' := by
        by_cases hypos : 0 ≤ y'
        · rw [Int.natAbs_of_nonneg hypos, if_pos (by omega)]
        · rw [Int.ofNat_natAbs_of_nonpos (by omega), if_neg (by omega)]; ring
      rw [hyt_val]
      have hp_val : (x' + 3 * y') / 4 = s := by omega
      have hq_val : (x' - y') / 4 = 2 * u := by omega
      rw [hp_val, hq_val, if_pos (by omega), if_pos (by omega)]
      congr 1; ext <;> omega
    · have hx_val : (x'.natAbs : ℤ) = -x' := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [hx_val]
      have hyt_val : (if (-x' - (y'.natAbs : ℤ)) % 4 = 0 then (y'.natAbs : ℤ) else -(y'.natAbs : ℤ)) = -y' := by
        by_cases hypos : 0 ≤ y'
        · rw [Int.natAbs_of_nonneg hypos, if_neg (by omega)]
        · rw [Int.ofNat_natAbs_of_nonpos (by omega), if_pos (by omega)]
      rw [hyt_val]
      have hp_val : (-x' + 3 * -y') / 4 = -s := by omega
      have hq_val : (-x' - -y') / 4 = -(2 * u) := by omega
      rw [hp_val, hq_val, if_pos (by omega), if_neg (by omega)]
      congr 1; ext <;> omega
  · dsimp only [bwdMap, fwdMap]
    set t : ℤ := 2 * (d : ℤ) + 1
    set x' : ℤ := 2 * v + 3 * t
    set y' : ℤ := 2 * v - t
    rw [odd_natAbs_eq x' (by omega), odd_natAbs_eq y' (by omega)]
    by_cases hxpos : 0 < x'
    · have hx_val : (x'.natAbs : ℤ) = x' := Int.natAbs_of_nonneg (by omega)
      rw [hx_val]
      have hyt_val : (if (x' - (y'.natAbs : ℤ)) % 4 = 0 then (y'.natAbs : ℤ) else -(y'.natAbs : ℤ)) = y' := by
        by_cases hypos : 0 ≤ y'
        · rw [Int.natAbs_of_nonneg hypos, if_pos (by omega)]
        · rw [Int.ofNat_natAbs_of_nonpos (by omega), if_neg (by omega)]; ring
      rw [hyt_val]
      have hp_val : (x' + 3 * y') / 4 = 2 * v := by omega
      have hq_val : (x' - y') / 4 = t := by omega
      rw [hp_val, hq_val, if_neg (by omega), if_pos (by omega)]
      congr 1; ext <;> omega
    · have hx_val : (x'.natAbs : ℤ) = -x' := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [hx_val]
      have hyt_val : (if (-x' - (y'.natAbs : ℤ)) % 4 = 0 then (y'.natAbs : ℤ) else -(y'.natAbs : ℤ)) = -y' := by
        by_cases hypos : 0 ≤ y'
        · rw [Int.natAbs_of_nonneg hypos, if_neg (by omega)]
        · rw [Int.ofNat_natAbs_of_nonpos (by omega), if_pos (by omega)]
      rw [hyt_val]
      have hp_val : (-x' + 3 * -y') / 4 = -(2 * v) := by omega
      have hq_val : (-x' - -y') / 4 = -t := by omega
      rw [hp_val, hq_val, if_neg (by omega), if_neg (by omega)]
      congr 1; ext <;> omega

private lemma card_setL_eq (n : ℕ) : (setL n).card = (setR1 n).card + (setR2 n).card := by
  rw [← Finset.card_disjSum]
  exact Finset.card_bij' (fun ab _ => fwdMap ab) (fun z _ => bwdMap z)
    (fun ab hab => fwdMap_mem n ab hab)
    (fun z hz => bwdMap_mem n z hz)
    (fun ab hab => bwdMap_fwdMap n ab hab)
    (fun z _ => fwdMap_bwdMap z)

private lemma tri_iff (a t : ℕ) : a * (a + 1) / 2 = t ↔ (2 * a + 1) ^ 2 = 8 * t + 1 := by
  have hev : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
  have hmul := Nat.mul_div_cancel' hev
  constructor <;> intro h <;> nlinarith

/-- Exact 2-dissection identity: `ψ(q) ψ(q^3) = φ(q^6) ψ(q^4) + q φ(q^2) ψ(q^{12})`. -/
theorem psi_mul_psi3 :
    psi * psi.expand 3 (by decide) =
      phi.expand 6 (by decide) * psi.expand 4 (by decide) +
      X * phi.expand 2 (by decide) * psi.expand 12 (by decide) := by
  open Classical in
  ext n
  let B := n + 1
  have hLHS : (psi * psi.expand 3 (by decide)).coeff n = ((setL n).card : ℤ) := by
    rw [PowerSeries.coeff_mul]
    have hsub : ∀ x ∈ Finset.antidiagonal n,
        psi.coeff x.1 * (psi.expand 3 (by decide)).coeff x.2 =
        ∑ ab ∈ Finset.range B ×ˢ Finset.range B,
          if ab.1 * (ab.1 + 1) / 2 = x.1 ∧ 3 * (ab.2 * (ab.2 + 1) / 2) = x.2 then (1 : ℤ) else 0 := by
      intro x hx
      rw [Finset.mem_antidiagonal] at hx
      rw [coeff_psi_eq, PowerSeries.coeff_expand]
      simp only [Finset.sum_product]
      have h1 : ∀ a ∈ Finset.range B,
          (∑ b ∈ Finset.range B,
            if a * (a + 1) / 2 = x.1 ∧ 3 * (b * (b + 1) / 2) = x.2 then (1 : ℤ) else 0) =
          (if a * (a + 1) / 2 = x.1 then (1 : ℤ) else 0) *
            (∑ b ∈ Finset.range B, if 3 * (b * (b + 1) / 2) = x.2 then (1 : ℤ) else 0) := by
        intro a _; split_ifs with ha <;> simp [ha]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
      congr 1
      · by_cases hex : ∃ a : ℕ, a * (a + 1) / 2 = x.1
        · rcases hex with ⟨a₀, ha₀⟩
          rw [if_pos ⟨a₀, ha₀⟩, Finset.sum_eq_single a₀]
          · simp [ha₀]
          · intro a _ hne; rw [if_neg]; intro heq
            have h1' := (tri_iff a x.1).mp heq
            have h2' := (tri_iff a₀ x.1).mp ha₀
            exact hne (by nlinarith)
          · intro hnot; exfalso; apply hnot
            rw [Finset.mem_range]; have := (tri_iff a₀ x.1).mp ha₀; dsimp only [B]; nlinarith
        · rw [if_neg hex]
          exact (Finset.sum_eq_zero fun a _ => if_neg fun h => hex ⟨a, h⟩).symm
      · split_ifs with hdvd
        · rw [coeff_psi_eq]
          by_cases hex : ∃ b : ℕ, b * (b + 1) / 2 = x.2 / 3
          · rcases hex with ⟨b₀, hb₀⟩
            rw [if_pos ⟨b₀, hb₀⟩, Finset.sum_eq_single b₀]
            · rw [if_pos]; omega
            · intro b _ hne; rw [if_neg]; intro heq
              have h1' := (tri_iff b (x.2 / 3)).mp (by omega)
              have h2' := (tri_iff b₀ (x.2 / 3)).mp hb₀
              exact hne (by nlinarith)
            · intro hnot; exfalso; apply hnot
              rw [Finset.mem_range]
              have hsq := (tri_iff b₀ (x.2 / 3)).mp hb₀
              have hle : x.2 / 3 ≤ n := by omega
              dsimp only [B]; nlinarith
          · rw [if_neg hex]
            exact (Finset.sum_eq_zero fun b _ => if_neg fun h => hex ⟨b, by omega⟩).symm
        · exact (Finset.sum_eq_zero fun b _ => if_neg fun h => hdvd ⟨b * (b + 1) / 2, h.symm⟩).symm
    rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
    have hsum : ∑ ab ∈ Finset.range B ×ˢ Finset.range B,
        (∑ x ∈ Finset.antidiagonal n,
          if ab.1 * (ab.1 + 1) / 2 = x.1 ∧ 3 * (ab.2 * (ab.2 + 1) / 2) = x.2 then (1 : ℤ) else 0) =
        ∑ ab ∈ Finset.range B ×ˢ Finset.range B,
          if (2 * ab.1 + 1) ^ 2 + 3 * (2 * ab.2 + 1) ^ 2 = 8 * n + 4 then (1 : ℤ) else 0 := by
      refine Finset.sum_congr rfl fun ab _ => ?_
      have hcond : (ab.1 * (ab.1 + 1) / 2 + 3 * (ab.2 * (ab.2 + 1) / 2) = n) ↔
          (2 * ab.1 + 1) ^ 2 + 3 * (2 * ab.2 + 1) ^ 2 = 8 * n + 4 := by
        have h1 := (tri_iff ab.1 (ab.1 * (ab.1 + 1) / 2)).mp rfl
        have h2 := (tri_iff ab.2 (ab.2 * (ab.2 + 1) / 2)).mp rfl
        omega
      by_cases h : (2 * ab.1 + 1) ^ 2 + 3 * (2 * ab.2 + 1) ^ 2 = 8 * n + 4
      · rw [if_pos h]
        have hsum_eq := hcond.mpr h
        rw [Finset.sum_eq_single (ab.1 * (ab.1 + 1) / 2, 3 * (ab.2 * (ab.2 + 1) / 2))]
        · simp
        · intro x _ hxne; rw [if_neg]; rintro ⟨h1, h2⟩; apply hxne; ext <;> omega
        · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; exact hsum_eq
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun x hx => if_neg ?_
        rw [Finset.mem_antidiagonal] at hx
        rintro ⟨h1, h2⟩; exact h (hcond.mp (by omega))
    rw [hsum, Finset.sum_boole]; rfl
  have hR1 : (phi.expand 6 (by decide) * psi.expand 4 (by decide)).coeff n = ((setR1 n).card : ℤ) := by
    rw [PowerSeries.coeff_mul]
    have hsub : ∀ x ∈ Finset.antidiagonal n,
        (phi.expand 6 (by decide)).coeff x.1 * (psi.expand 4 (by decide)).coeff x.2 =
        ∑ uc ∈ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.range B,
          if 6 * uc.1 ^ 2 = (x.1 : ℤ) ∧ 4 * (uc.2 * (uc.2 + 1) / 2) = x.2 then (1 : ℤ) else 0 := by
      intro x hx
      rw [Finset.mem_antidiagonal] at hx
      rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      simp only [Finset.sum_product]
      have hfactor : ∀ u ∈ Finset.Icc (-(n : ℤ)) n,
          (∑ c ∈ Finset.range B,
            if 6 * u ^ 2 = (x.1 : ℤ) ∧ 4 * (c * (c + 1) / 2) = x.2 then (1 : ℤ) else 0) =
          (if 6 * u ^ 2 = (x.1 : ℤ) then (1 : ℤ) else 0) *
            (∑ c ∈ Finset.range B, if 4 * (c * (c + 1) / 2) = x.2 then (1 : ℤ) else 0) := by
        intro u _; split_ifs with hu <;> simp [hu]
      rw [Finset.sum_congr rfl hfactor, ← Finset.sum_mul]
      congr 1
      · split_ifs with hdvd
        · rw [coeff_phi_eq_card, Finset.sum_boole]
          congr 1; apply congrArg Finset.card
          ext u
          simp only [Finset.mem_filter, Finset.mem_Icc]
          have hx1 : (x.1 : ℤ) = 6 * ((x.1 / 6 : ℕ) : ℤ) := by
            have := Nat.mul_div_cancel' hdvd; omega
          constructor
          · rintro ⟨⟨_, _⟩, hu⟩; refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith⟩
          · rintro ⟨⟨_, _⟩, hu⟩; refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith⟩
        · refine (Finset.sum_eq_zero fun u _ => if_neg fun h => ?_).symm
          apply hdvd; refine ⟨u.natAbs ^ 2, ?_⟩
          rw [← int_sq_eq_natAbs_sq] at h
          exact_mod_cast h.symm
      · split_ifs with hdvd
        · rw [coeff_psi_eq]
          by_cases hex : ∃ c : ℕ, c * (c + 1) / 2 = x.2 / 4
          · rcases hex with ⟨c₀, hc₀⟩
            rw [if_pos ⟨c₀, hc₀⟩, Finset.sum_eq_single c₀]
            · rw [if_pos]; omega
            · intro c _ hne; rw [if_neg]; intro heq
              have h1' := (tri_iff c (x.2 / 4)).mp (by omega)
              have h2' := (tri_iff c₀ (x.2 / 4)).mp hc₀
              exact hne (by nlinarith)
            · intro hnot; exfalso; apply hnot
              rw [Finset.mem_range]
              have hsq := (tri_iff c₀ (x.2 / 4)).mp hc₀
              have hle : x.2 / 4 ≤ n := by omega
              dsimp only [B]; nlinarith
          · rw [if_neg hex]
            exact (Finset.sum_eq_zero fun c _ => if_neg fun h => hex ⟨c, by omega⟩).symm
        · exact (Finset.sum_eq_zero fun c _ => if_neg fun h => hdvd ⟨c * (c + 1) / 2, h.symm⟩).symm
    rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
    have hsimp : ∑ uc ∈ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.range B,
        (∑ x ∈ Finset.antidiagonal n,
          if 6 * uc.1 ^ 2 = (x.1 : ℤ) ∧ 4 * (uc.2 * (uc.2 + 1) / 2) = x.2 then (1 : ℤ) else 0) =
        ∑ uc ∈ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.range B,
          if (2 * (uc.2 : ℤ) + 1) ^ 2 + 12 * uc.1 ^ 2 = 2 * (n : ℤ) + 1 then (1 : ℤ) else 0 := by
      refine Finset.sum_congr rfl fun uc _ => ?_
      have htri : (2 * (uc.2 : ℤ) + 1) ^ 2 = 8 * ((uc.2 * (uc.2 + 1) / 2 : ℕ) : ℤ) + 1 := by
        exact_mod_cast (tri_iff uc.2 (uc.2 * (uc.2 + 1) / 2)).mp rfl
      by_cases h : (2 * (uc.2 : ℤ) + 1) ^ 2 + 12 * uc.1 ^ 2 = 2 * (n : ℤ) + 1
      · rw [if_pos h]
        have hu6 : (6 * uc.1 ^ 2 : ℤ) = ((6 * uc.1.natAbs ^ 2 : ℕ) : ℤ) := by
          rw [← int_sq_eq_natAbs_sq]; push_cast; rfl
        rw [Finset.sum_eq_single (6 * uc.1.natAbs ^ 2, 4 * (uc.2 * (uc.2 + 1) / 2))]
        · rw [if_pos ⟨hu6, rfl⟩]
        · intro x _ hxne; rw [if_neg]; rintro ⟨h1, h2⟩
          apply hxne; ext
          · omega
          · exact h2.symm
        · intro hnot; exfalso; apply hnot
          rw [Finset.mem_antidiagonal]; omega
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun x hx => if_neg ?_
        rw [Finset.mem_antidiagonal] at hx
        rintro ⟨h1, h2⟩; apply h; omega
    rw [hsimp, Finset.sum_boole]; rfl
  have hR2 : (X * phi.expand 2 (by decide) * psi.expand 12 (by decide)).coeff n = ((setR2 n).card : ℤ) := by
    rw [mul_assoc, coeff_X_mul_eq]
    cases n with
    | zero =>
        rw [if_neg (by omega)]
        have hempty : setR2 0 = ∅ := by
          ext ⟨v, d⟩
          simp only [setR2, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _ heq
          simp only [Nat.cast_zero, mul_zero, zero_add] at heq
          have hv : 0 ≤ v ^ 2 := sq_nonneg v
          have hd0 : (0 : ℤ) ≤ (d : ℤ) := Nat.cast_nonneg d
          have hd : 1 ≤ (2 * (d : ℤ) + 1) ^ 2 := by nlinarith
          linarith
        rw [hempty]; norm_num
    | succ m =>
        rw [if_pos (by omega), show m + 1 - 1 = m by omega, PowerSeries.coeff_mul]
        have hsub : ∀ x ∈ Finset.antidiagonal m,
            (phi.expand 2 (by decide)).coeff x.1 * (psi.expand 12 (by decide)).coeff x.2 =
            ∑ vd ∈ Finset.Icc (-((m + 1 : ℕ) : ℤ)) (m + 1 : ℕ) ×ˢ Finset.range (m + 2),
              if 2 * vd.1 ^ 2 = (x.1 : ℤ) ∧ 12 * (vd.2 * (vd.2 + 1) / 2) = x.2 then (1 : ℤ) else 0 := by
          intro x hx
          rw [Finset.mem_antidiagonal] at hx
          rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
          simp only [Finset.sum_product]
          have hfactor : ∀ v ∈ Finset.Icc (-((m + 1 : ℕ) : ℤ)) (m + 1 : ℕ),
              (∑ d ∈ Finset.range (m + 2),
                if 2 * v ^ 2 = (x.1 : ℤ) ∧ 12 * (d * (d + 1) / 2) = x.2 then (1 : ℤ) else 0) =
              (if 2 * v ^ 2 = (x.1 : ℤ) then (1 : ℤ) else 0) *
                (∑ d ∈ Finset.range (m + 2), if 12 * (d * (d + 1) / 2) = x.2 then (1 : ℤ) else 0) := by
            intro v _; split_ifs with hv <;> simp [hv]
          rw [Finset.sum_congr rfl hfactor, ← Finset.sum_mul]
          congr 1
          · split_ifs with hdvd
            · rw [coeff_phi_eq_card, Finset.sum_boole]
              congr 1; apply congrArg Finset.card
              ext v
              simp only [Finset.mem_filter, Finset.mem_Icc]
              have hx1 : (x.1 : ℤ) = 2 * ((x.1 / 2 : ℕ) : ℤ) := by
                have := Nat.mul_div_cancel' hdvd; omega
              have hx1m : (x.1 / 2 : ℤ) ≤ m + 1 := by omega
              constructor
              · rintro ⟨⟨_, _⟩, hv⟩
                refine ⟨⟨by omega, by omega⟩, by nlinarith⟩
              · rintro ⟨⟨_, _⟩, hv⟩
                have hv_sq : v * v = ((x.1 / 2 : ℕ) : ℤ) := by nlinarith
                refine ⟨⟨by nlinarith, by nlinarith⟩, hv_sq⟩
            · refine (Finset.sum_eq_zero fun v _ => if_neg fun h => ?_).symm
              apply hdvd; refine ⟨v.natAbs ^ 2, ?_⟩
              rw [← int_sq_eq_natAbs_sq] at h; exact_mod_cast h.symm
          · split_ifs with hdvd
            · rw [coeff_psi_eq]
              by_cases hex : ∃ d : ℕ, d * (d + 1) / 2 = x.2 / 12
              · rcases hex with ⟨d₀, hd₀⟩
                rw [if_pos ⟨d₀, hd₀⟩, Finset.sum_eq_single d₀]
                · rw [if_pos]; omega
                · intro d _ hne; rw [if_neg]; intro heq
                  have h1' := (tri_iff d (x.2 / 12)).mp (by omega)
                  have h2' := (tri_iff d₀ (x.2 / 12)).mp hd₀
                  exact hne (by nlinarith)
                · intro hnot; exfalso; apply hnot
                  rw [Finset.mem_range]
                  have hsq := (tri_iff d₀ (x.2 / 12)).mp hd₀
                  have hle : x.2 / 12 ≤ m := by omega
                  nlinarith
              · rw [if_neg hex]
                exact (Finset.sum_eq_zero fun d _ => if_neg fun h => hex ⟨d, by omega⟩).symm
            · exact (Finset.sum_eq_zero fun d _ => if_neg fun h => hdvd ⟨d * (d + 1) / 2, h.symm⟩).symm
        rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
        have hsimp : ∑ vd ∈ Finset.Icc (-((m + 1 : ℕ) : ℤ)) (m + 1 : ℕ) ×ˢ Finset.range (m + 2),
            (∑ x ∈ Finset.antidiagonal m,
              if 2 * vd.1 ^ 2 = (x.1 : ℤ) ∧ 12 * (vd.2 * (vd.2 + 1) / 2) = x.2 then (1 : ℤ) else 0) =
            ∑ vd ∈ Finset.Icc (-((m + 1 : ℕ) : ℤ)) (m + 1 : ℕ) ×ˢ Finset.range (m + 2),
              if 4 * vd.1 ^ 2 + 3 * (2 * (vd.2 : ℤ) + 1) ^ 2 = 2 * ((m + 1 : ℕ) : ℤ) + 1
                then (1 : ℤ) else 0 := by
          refine Finset.sum_congr rfl fun vd _ => ?_
          have htri : (2 * (vd.2 : ℤ) + 1) ^ 2 = 8 * ((vd.2 * (vd.2 + 1) / 2 : ℕ) : ℤ) + 1 := by
            exact_mod_cast (tri_iff vd.2 (vd.2 * (vd.2 + 1) / 2)).mp rfl
          by_cases h : 4 * vd.1 ^ 2 + 3 * (2 * (vd.2 : ℤ) + 1) ^ 2 = 2 * ((m + 1 : ℕ) : ℤ) + 1
          · rw [if_pos h]
            have hv2 : (2 * vd.1 ^ 2 : ℤ) = ((2 * vd.1.natAbs ^ 2 : ℕ) : ℤ) := by
              rw [← int_sq_eq_natAbs_sq]; push_cast; rfl
            rw [Finset.sum_eq_single (2 * vd.1.natAbs ^ 2, 12 * (vd.2 * (vd.2 + 1) / 2))]
            · rw [if_pos ⟨hv2, rfl⟩]
            · intro x _ hxne; rw [if_neg]; rintro ⟨h1, h2⟩
              apply hxne; ext
              · omega
              · exact h2.symm
            · intro hnot; exfalso; apply hnot
              rw [Finset.mem_antidiagonal]; omega
          · rw [if_neg h]
            refine Finset.sum_eq_zero fun x hx => if_neg ?_
            rw [Finset.mem_antidiagonal] at hx
            rintro ⟨h1, h2⟩; apply h; omega
        rw [hsimp, Finset.sum_boole]; rfl
  rw [map_add, hLHS, hR1, hR2]
  exact_mod_cast card_setL_eq n

end PsiProductIdentity

/-! ## Section 4: Exact 2-Dissection of `G` and Congruences `(P1)`, `(P2)`, `(P3)` -/

section Dissections

private noncomputable def invPhiNegF6 : ℤ⟦X⟧ :=
  PowerSeries.invOfUnit (phiNeg * f 6 (by decide)) 1

private noncomputable def E₁ : ℤ⟦X⟧ :=
  phi.expand 3 (by decide) * psi.expand 2 (by decide) * invPhiNegF6

private noncomputable def O₁ : ℤ⟦X⟧ :=
  phi * psi.expand 6 (by decide) * invPhiNegF6

private lemma G_two_dissection :
    G = E₁.expand 2 (by decide) + X * O₁.expand 2 (by decide) := by
  have hf3 : f 3 (by decide) = (f 1 (by decide)).expand 3 (by decide) := by
    rw [f, f, PowerSeries.expand_one_apply]
  have hf6_3 : f 6 (by decide) = (f 2 (by decide)).expand 3 (by decide) := by
    rw [f, f, ← PowerSeries.expand_mul]
  have hf4_2 : f 4 (by decide) = (f 2 (by decide)).expand 2 (by decide) := by
    rw [f, f, ← PowerSeries.expand_mul]
  have hf2_2 : f 2 (by decide) = (f 1 (by decide)).expand 2 (by decide) := by
    rw [f, f, PowerSeries.expand_one_apply]
  have hf12_2 : f 12 (by decide) = (f 6 (by decide)).expand 2 (by decide) := by
    rw [f, f, ← PowerSeries.expand_mul]
  have hJ1_3 : f 3 (by decide) * psi.expand 3 (by decide) = (f 6 (by decide)) ^ 2 := by
    have h := congrArg (PowerSeries.expand 3 (by decide)) gauss_J1
    rw [map_mul, map_pow, ← hf3, ← hf6_3] at h
    exact h
  have hJ2_2 : f 4 (by decide) * phiNeg.expand 2 (by decide) = (f 2 (by decide)) ^ 2 := by
    have h := congrArg (PowerSeries.expand 2 (by decide)) gauss_J2
    rw [map_mul, map_pow, ← hf4_2, ← hf2_2] at h
    exact h
  have hG_psi : G * (phiNeg * f 6 (by decide)).expand 2 (by decide) =
      psi * psi.expand 3 (by decide) := by
    set U := f 1 (by decide) * f 3 (by decide) * f 12 (by decide) * f 4 (by decide)
    have hunit : PowerSeries.constantCoeff U = 1 := by simp [U]
    have hmul : (G * (phiNeg * f 6 (by decide)).expand 2 (by decide)) * U =
        (psi * psi.expand 3 (by decide)) * U := by
      calc
        G * (phiNeg * f 6 (by decide)).expand 2 (by decide) * U
            = (G * (f 1 (by decide) * f 3 (by decide) * f 12 (by decide))) *
              (f 4 (by decide) * phiNeg.expand 2 (by decide)) * f 12 (by decide) := by
                rw [map_mul, ← hf12_2]; dsimp only [U]; ring
        _ = (f 4 (by decide) * (f 6 (by decide)) ^ 2) * (f 2 (by decide)) ^ 2 * f 12 (by decide) := by
                rw [G_mul_den, hJ2_2]
        _ = (f 1 (by decide) * psi) * (f 3 (by decide) * psi.expand 3 (by decide)) *
              f 12 (by decide) * f 4 (by decide) := by
                rw [gauss_J1, hJ1_3]; ring
        _ = (psi * psi.expand 3 (by decide)) * U := by dsimp only [U]; ring
    have hinv := PowerSeries.mul_invOfUnit U 1 (by simpa using hunit)
    calc
      G * (phiNeg * f 6 (by decide)).expand 2 (by decide)
          = (G * (phiNeg * f 6 (by decide)).expand 2 (by decide)) * (U * PowerSeries.invOfUnit U 1) := by
            rw [hinv, mul_one]
      _ = ((G * (phiNeg * f 6 (by decide)).expand 2 (by decide)) * U) * PowerSeries.invOfUnit U 1 := by
            ring
      _ = ((psi * psi.expand 3 (by decide)) * U) * PowerSeries.invOfUnit U 1 := by rw [hmul]
      _ = psi * psi.expand 3 (by decide) := by rw [mul_assoc, hinv, mul_one]
  have hinv_exp : (phiNeg * f 6 (by decide)).expand 2 (by decide) * invPhiNegF6.expand 2 (by decide) = 1 := by
    rw [← map_mul]
    have hmul1 : (phiNeg * f 6 (by decide)) * invPhiNegF6 = 1 :=
      PowerSeries.mul_invOfUnit _ 1 (by simp)
    rw [hmul1, map_one]
  calc
    G = G * ((phiNeg * f 6 (by decide)).expand 2 (by decide) * invPhiNegF6.expand 2 (by decide)) := by
          rw [hinv_exp, mul_one]
    _ = (G * (phiNeg * f 6 (by decide)).expand 2 (by decide)) * invPhiNegF6.expand 2 (by decide) := by ring
    _ = (psi * psi.expand 3 (by decide)) * invPhiNegF6.expand 2 (by decide) := by rw [hG_psi]
    _ = (phi.expand 6 (by decide) * psi.expand 4 (by decide) +
         X * phi.expand 2 (by decide) * psi.expand 12 (by decide)) * invPhiNegF6.expand 2 (by decide) := by
          rw [psi_mul_psi3]
    _ = E₁.expand 2 (by decide) + X * O₁.expand 2 (by decide) := by
          simp only [E₁, O₁, map_mul, ← PowerSeries.expand_mul]
          ring

private noncomputable def Ssq : ℤ⟦X⟧ :=
  open Classical in
  PowerSeries.mk fun n => if ∃ k : ℕ, 0 < k ∧ k * k = n then 1 else 0

private lemma phi_eq_one_add_two_Ssq : phi = 1 + 2 * Ssq := by
  open Classical in
  ext n
  rw [map_add, PowerSeries.coeff_one]
  have h2 : (2 * Ssq).coeff n = 2 * Ssq.coeff n := by
    have : (2 : ℤ⟦X⟧) = PowerSeries.C 2 := by simp
    rw [this, PowerSeries.coeff_C_mul]
  rw [h2]
  simp only [phi, Ssq, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [if_neg hn, zero_add]
    split_ifs <;> ring

private lemma Ssq_odd_part :
    ∀ n : ℕ, Ssq.coeff (2 * n + 1) = (psi.expand 4 (by decide)).coeff n := by
  open Classical in
  intro n
  simp only [Ssq, PowerSeries.coeff_mk, PowerSeries.coeff_expand]
  have hodd_sq : ∀ k : ℕ, k * k = 2 * n + 1 → Odd k := by
    intro k hk
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rcases hev with ⟨m, rfl⟩
    have : (m + m) * (m + m) = 2 * (2 * m * m) := by ring
    omega
  by_cases hex : ∃ k : ℕ, 0 < k ∧ k * k = 2 * n + 1
  · rw [if_pos hex]
    rcases hex with ⟨k, _, hk⟩
    rcases hodd_sq k hk with ⟨m, rfl⟩
    have h8 : 8 * (m * (m + 1) / 2) + 1 = (2 * m + 1) * (2 * m + 1) := by
      have hev : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
      have := Nat.mul_div_cancel' hev; linarith
    have hneq : n = 4 * (m * (m + 1) / 2) := by omega
    have hdvd : 4 ∣ n := ⟨m * (m + 1) / 2, hneq⟩
    rw [if_pos hdvd]
    simp only [psi, PowerSeries.coeff_mk]
    rw [if_pos ⟨m, by omega⟩]
  · rw [if_neg hex]
    split_ifs with hdvd
    · simp only [psi, PowerSeries.coeff_mk]
      rw [if_neg]
      rintro ⟨m, hm⟩
      apply hex; refine ⟨2 * m + 1, by omega, ?_⟩
      have hev : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
      have h1 := Nat.mul_div_cancel' hev
      have h2 := Nat.mul_div_cancel' hdvd
      nlinarith
    · rfl

private lemma map_ZMod_coeff (m : ℕ) (A : ℤ⟦X⟧) (n : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod m)) A).coeff n = (A.coeff n : ZMod m) := by
  simp

private lemma dvd_coeff_iff_map_ZMod_eq_zero (m : ℕ) (A : ℤ⟦X⟧) (n : ℕ) :
    (m : ℤ) ∣ A.coeff n ↔ (PowerSeries.map (Int.castRingHom (ZMod m)) A).coeff n = 0 := by
  rw [map_ZMod_coeff, ZMod.intCast_zmod_eq_zero_iff_dvd]

private lemma two_dvd_coeff_iff (A : ℤ⟦X⟧) (n : ℕ) :
    (2 : ℤ) ∣ A.coeff n ↔ (PowerSeries.map (Int.castRingHom (ZMod 2)) A).coeff n = 0 :=
  dvd_coeff_iff_map_ZMod_eq_zero 2 A n

private lemma four_dvd_coeff_iff (A : ℤ⟦X⟧) (n : ℕ) :
    (4 : ℤ) ∣ A.coeff n ↔ (PowerSeries.map (Int.castRingHom (ZMod 4)) A).coeff n = 0 :=
  dvd_coeff_iff_map_ZMod_eq_zero 4 A n

private lemma four_eq_zero_zmod4 : (4 : (ZMod 4)⟦X⟧) = 0 := by
  change PowerSeries.C (4 : ZMod 4) = 0
  rw [show (4 : ZMod 4) = 0 by decide, map_zero]

private lemma two_eq_zero_zmod2 : (2 : (ZMod 2)⟦X⟧) = 0 := by
  change PowerSeries.C (2 : ZMod 2) = 0
  rw [show (2 : ZMod 2) = 0 by decide, map_zero]

private lemma phi_mod4_eq_phiNeg :
    PowerSeries.map (Int.castRingHom (ZMod 4)) phi =
      PowerSeries.map (Int.castRingHom (ZMod 4)) phiNeg := by
  open Classical in
  ext n
  rw [map_ZMod_coeff, map_ZMod_coeff]
  simp only [phiNeg, phi, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [if_neg hn]
    split_ifs
    · rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow]; norm_num
      · rw [ho.neg_one_pow]; decide
    · simp

private lemma phi_sq_mod4 :
    (PowerSeries.map (Int.castRingHom (ZMod 4)) phi) ^ 2 = 1 := by
  rw [phi_eq_one_add_two_Ssq, map_add, map_one, map_mul, map_ofNat]
  calc
    (1 + 2 * PowerSeries.map (Int.castRingHom (ZMod 4)) Ssq) ^ 2
        = 1 + 4 * PowerSeries.map (Int.castRingHom (ZMod 4)) Ssq +
          4 * (PowerSeries.map (Int.castRingHom (ZMod 4)) Ssq) ^ 2 := by ring
    _ = 1 := by rw [four_eq_zero_zmod4]; ring

private lemma inv_phiNeg_mod4 :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (PowerSeries.invOfUnit phiNeg 1) =
      PowerSeries.map (Int.castRingHom (ZMod 4)) phi := by
  have hmul : PowerSeries.map (Int.castRingHom (ZMod 4)) phiNeg *
      PowerSeries.map (Int.castRingHom (ZMod 4)) (PowerSeries.invOfUnit phiNeg 1) = 1 := by
    rw [← map_mul, PowerSeries.mul_invOfUnit phiNeg 1 (by simp), map_one]
  calc
    PowerSeries.map (Int.castRingHom (ZMod 4)) (PowerSeries.invOfUnit phiNeg 1)
        = (PowerSeries.map (Int.castRingHom (ZMod 4)) phi) ^ 2 *
            PowerSeries.map (Int.castRingHom (ZMod 4)) (PowerSeries.invOfUnit phiNeg 1) := by
          rw [phi_sq_mod4, one_mul]
    _ = PowerSeries.map (Int.castRingHom (ZMod 4)) phi *
          (PowerSeries.map (Int.castRingHom (ZMod 4)) phiNeg *
            PowerSeries.map (Int.castRingHom (ZMod 4)) (PowerSeries.invOfUnit phiNeg 1)) := by
          rw [sq, ← phi_mod4_eq_phiNeg]; ring
    _ = PowerSeries.map (Int.castRingHom (ZMod 4)) phi := by rw [hmul, mul_one]

private lemma invPhiNegF6_eq_mul :
    invPhiNegF6 = PowerSeries.invOfUnit phiNeg 1 * PowerSeries.invOfUnit (f 6 (by decide)) 1 := by
  have h1 : (phiNeg * f 6 (by decide)) *
      (PowerSeries.invOfUnit phiNeg 1 * PowerSeries.invOfUnit (f 6 (by decide)) 1) = 1 := by
    calc
      (phiNeg * f 6 (by decide)) *
          (PowerSeries.invOfUnit phiNeg 1 * PowerSeries.invOfUnit (f 6 (by decide)) 1)
          = (phiNeg * PowerSeries.invOfUnit phiNeg 1) *
            (f 6 (by decide) * PowerSeries.invOfUnit (f 6 (by decide)) 1) := by ring
      _ = 1 := by
          rw [PowerSeries.mul_invOfUnit _ 1 (by simp), PowerSeries.mul_invOfUnit _ 1 (by simp), mul_one]
  calc
    invPhiNegF6 = invPhiNegF6 * ((phiNeg * f 6 (by decide)) *
        (PowerSeries.invOfUnit phiNeg 1 * PowerSeries.invOfUnit (f 6 (by decide)) 1)) := by
          rw [h1, mul_one]
    _ = (invPhiNegF6 * (phiNeg * f 6 (by decide))) *
        (PowerSeries.invOfUnit phiNeg 1 * PowerSeries.invOfUnit (f 6 (by decide)) 1) := by ring
    _ = PowerSeries.invOfUnit phiNeg 1 * PowerSeries.invOfUnit (f 6 (by decide)) 1 := by
          rw [invPhiNegF6, PowerSeries.invOfUnit_mul _ 1 (by simp), one_mul]

private lemma inv_f6_eq_expand2 :
    PowerSeries.invOfUnit (f 6 (by decide)) 1 =
      (PowerSeries.invOfUnit (f 3 (by decide)) 1).expand 2 (by decide) := by
  have hf6 : f 6 (by decide) = (f 3 (by decide)).expand 2 (by decide) := by
    rw [f, f, ← PowerSeries.expand_mul]
  have h1 : f 6 (by decide) * (PowerSeries.invOfUnit (f 3 (by decide)) 1).expand 2 (by decide) = 1 := by
    rw [hf6, ← map_mul, PowerSeries.mul_invOfUnit _ 1 (by simp), map_one]
  calc
    PowerSeries.invOfUnit (f 6 (by decide)) 1
        = PowerSeries.invOfUnit (f 6 (by decide)) 1 *
          (f 6 (by decide) * (PowerSeries.invOfUnit (f 3 (by decide)) 1).expand 2 (by decide)) := by
            rw [h1, mul_one]
    _ = (PowerSeries.invOfUnit (f 6 (by decide)) 1 * f 6 (by decide)) *
          (PowerSeries.invOfUnit (f 3 (by decide)) 1).expand 2 (by decide) := by ring
    _ = (PowerSeries.invOfUnit (f 3 (by decide)) 1).expand 2 (by decide) := by
          rw [PowerSeries.invOfUnit_mul _ 1 (by simp), one_mul]

private noncomputable def aBase : ℤ⟦X⟧ := psi * PowerSeries.invOfUnit (f 3 (by decide)) 1
private noncomputable def bBase : ℤ⟦X⟧ := psi.expand 3 (by decide) * PowerSeries.invOfUnit (f 3 (by decide)) 1

private lemma E1_eq_factors :
    E₁ = phi.expand 3 (by decide) * PowerSeries.invOfUnit phiNeg 1 * aBase.expand 2 (by decide) := by
  rw [E₁, invPhiNegF6_eq_mul, inv_f6_eq_expand2]
  simp only [aBase, map_mul]
  ring

private lemma O1_eq_factors :
    O₁ = phi * PowerSeries.invOfUnit phiNeg 1 * bBase.expand 2 (by decide) := by
  rw [O₁, invPhiNegF6_eq_mul, inv_f6_eq_expand2]
  simp only [bBase, map_mul, ← PowerSeries.expand_mul]
  ring

private lemma O1_mod4 :
    PowerSeries.map (Int.castRingHom (ZMod 4)) O₁ =
      PowerSeries.map (Int.castRingHom (ZMod 4)) (bBase.expand 2 (by decide)) := by
  rw [O1_eq_factors, map_mul, map_mul, inv_phiNeg_mod4, ← sq, phi_sq_mod4, one_mul]

/-- `(P1)` (Baruah–Ojah): `4 ∣ B 1 (4*n + 3)` for every `n`. -/
theorem cong_P1 (n : ℕ) : (4 : ℤ) ∣ B 1 (4 * n + 3) := by
  rw [B, pow_one, G_two_dissection, map_add]
  have h1 : (E₁.expand 2 (by decide)).coeff (4 * n + 3) = 0 :=
    PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)
  have h2 : (X * O₁.expand 2 (by decide)).coeff (4 * n + 3) = O₁.coeff (2 * n + 1) := by
    rw [coeff_X_mul_eq]
    have hidx : 4 * n + 3 - 1 = 2 * (2 * n + 1) := by omega
    rw [if_pos (by omega), hidx, PowerSeries.coeff_expand_mul]
  rw [h1, zero_add, h2, four_dvd_coeff_iff, O1_mod4, PowerSeries.map_expand]
  exact PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)

private noncomputable def E₂ : ℤ⟦X⟧ := E₁ ^ 2 + X * O₁ ^ 2
private noncomputable def W₂ : ℤ⟦X⟧ := E₁ * O₁

private lemma G_sq_dissection :
    G ^ 2 = E₂.expand 2 (by decide) + 2 * X * W₂.expand 2 (by decide) := by
  rw [G_two_dissection]
  simp only [E₂, W₂, map_add, map_mul, map_pow, PowerSeries.expand_X]
  ring

private lemma phi_mod2 : PowerSeries.map (Int.castRingHom (ZMod 2)) phi = 1 := by
  rw [phi_eq_one_add_two_Ssq, map_add, map_one, map_mul, map_ofNat, two_eq_zero_zmod2, zero_mul, add_zero]

private lemma phiNeg_mod2 : PowerSeries.map (Int.castRingHom (ZMod 2)) phiNeg = 1 := by
  open Classical in
  ext n
  rw [map_ZMod_coeff, PowerSeries.coeff_one]
  simp only [phiNeg, phi, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [if_neg hn]
    split_ifs
    · have h2 : (2 : ZMod 2) = 0 := by decide
      simp [Int.cast_mul, h2]
    · simp

private lemma inv_phiNeg_mod2 :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (PowerSeries.invOfUnit phiNeg 1) = 1 := by
  have hmul : PowerSeries.map (Int.castRingHom (ZMod 2)) phiNeg *
      PowerSeries.map (Int.castRingHom (ZMod 2)) (PowerSeries.invOfUnit phiNeg 1) = 1 := by
    rw [← map_mul, PowerSeries.mul_invOfUnit phiNeg 1 (by simp), map_one]
  rwa [phiNeg_mod2, one_mul] at hmul

/-- `(P2)`: `4 ∣ B 2 (4*n + 3)` for every `n`. -/
theorem cong_P2 (n : ℕ) : (4 : ℤ) ∣ B 2 (4 * n + 3) := by
  rw [B, G_sq_dissection, map_add]
  have h1 : (E₂.expand 2 (by decide)).coeff (4 * n + 3) = 0 :=
    PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)
  have h2 : (2 * X * W₂.expand 2 (by decide)).coeff (4 * n + 3) = 2 * W₂.coeff (2 * n + 1) := by
    have hrw : 2 * X * W₂.expand 2 (by decide) =
        PowerSeries.C 2 * (X * W₂.expand 2 (by decide)) := by simp; ring
    rw [hrw, PowerSeries.coeff_C_mul, coeff_X_mul_eq, if_pos (by omega)]
    have hidx : 4 * n + 3 - 1 = 2 * (2 * n + 1) := by omega
    rw [hidx, PowerSeries.coeff_expand_mul]
  rw [h1, zero_add, h2]
  have hW2_even : (2 : ℤ) ∣ W₂.coeff (2 * n + 1) := by
    rw [two_dvd_coeff_iff]
    have hWmod2 : PowerSeries.map (Int.castRingHom (ZMod 2)) W₂ =
        (PowerSeries.map (Int.castRingHom (ZMod 2)) (aBase * bBase)).expand 2 (by decide) := by
      rw [W₂, E1_eq_factors, O1_eq_factors]
      simp only [map_mul, PowerSeries.map_expand, phi_mod2, inv_phiNeg_mod2, map_one, one_mul, mul_one]
    rw [hWmod2]
    exact PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)
  rcases hW2_even with ⟨c, hc⟩
  exact ⟨c, by omega⟩

private lemma zmod2_sq_eq_expand2 (H : (ZMod 2)⟦X⟧) : H ^ 2 = H.expand 2 (by decide) := by
  ext n
  rw [sq, PowerSeries.coeff_mul, PowerSeries.coeff_expand]
  have hpair : ∑ x ∈ Finset.antidiagonal n, H.coeff x.1 * H.coeff x.2 =
      if 2 ∣ n then H.coeff (n / 2) * H.coeff (n / 2) else 0 := by
    have hsum : ∑ x ∈ Finset.antidiagonal n, H.coeff x.1 * H.coeff x.2 =
        (∑ x ∈ (Finset.antidiagonal n).filter (fun x => x.1 = x.2), H.coeff x.1 * H.coeff x.2) +
        (∑ x ∈ (Finset.antidiagonal n).filter (fun x => x.1 < x.2), H.coeff x.1 * H.coeff x.2) +
        (∑ x ∈ (Finset.antidiagonal n).filter (fun x => x.2 < x.1), H.coeff x.1 * H.coeff x.2) := by
      rw [add_assoc]
      have hpart1 := (Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal n)
        (fun x => x.1 = x.2) (fun x => H.coeff x.1 * H.coeff x.2)).symm
      rw [hpart1]
      congr 1
      have hpart2 := (Finset.sum_filter_add_sum_filter_not
        ((Finset.antidiagonal n).filter (fun x => ¬ x.1 = x.2))
        (fun x => x.1 < x.2) (fun x => H.coeff x.1 * H.coeff x.2)).symm
      rw [hpart2]
      congr 1
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext ⟨a, b⟩; simp only [Finset.mem_filter]; constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext ⟨a, b⟩; simp only [Finset.mem_filter]; constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, by omega⟩
    rw [hsum]
    have hgt_eq_lt :
        ∑ x ∈ (Finset.antidiagonal n).filter (fun x => x.2 < x.1), H.coeff x.1 * H.coeff x.2 =
        ∑ x ∈ (Finset.antidiagonal n).filter (fun x => x.1 < x.2), H.coeff x.1 * H.coeff x.2 := by
      refine Finset.sum_bij (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
      · intro ⟨a, b⟩ h
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h ⊢; omega
      · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h; simp only [Prod.mk.injEq] at h; ext <;> omega
      · intro ⟨a, b⟩ h
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h
        exact ⟨(b, a), by simp only [Finset.mem_filter, Finset.mem_antidiagonal]; omega, rfl⟩
      · intro ⟨a, b⟩ _; ring
    rw [hgt_eq_lt, add_assoc]
    have hdouble_zero : ∀ z : ZMod 2, z + z = 0 := by intro z; fin_cases z <;> rfl
    rw [hdouble_zero, add_zero]
    split_ifs with hdvd
    · rw [Finset.sum_eq_single (n / 2, n / 2)]
      · intro ⟨a, b⟩ h hne
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h
        exfalso; apply hne; ext <;> omega
      · intro hnot; exfalso; apply hnot
        simp only [Finset.mem_filter, Finset.mem_antidiagonal]
        rcases hdvd with ⟨k, rfl⟩
        exact ⟨by omega, trivial⟩
    · refine Finset.sum_eq_zero fun ⟨a, b⟩ h => ?_
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h
      exfalso; apply hdvd; exact ⟨a, by omega⟩
  rw [hpair]
  split_ifs
  · have hsq : ∀ z : ZMod 2, z * z = z := by intro z; fin_cases z <;> rfl
    exact hsq _
  · rfl

/-- Standard Frobenius congruence: for any `H ∈ ℤ⟦X⟧` and `j ≥ 1`,
`H(q)^{2^j} ≡ H(q^2)^{2^{j-1}} (mod 2^j)`. -/
theorem frobenius_pow_two (H : ℤ⟦X⟧) (j : ℕ) (hj : 1 ≤ j) (n : ℕ) :
    ((2 : ℤ) ^ j) ∣ (H ^ (2 ^ j) - (H.expand 2 (by decide)) ^ (2 ^ (j - 1))).coeff n := by
  induction j, hj using Nat.le_induction generalizing n with
  | base =>
      simp only [pow_one, Nat.sub_self, pow_zero]
      rw [two_dvd_coeff_iff]
      simp only [map_sub, map_pow, PowerSeries.map_expand, zmod2_sq_eq_expand2, sub_self, map_zero]
  | succ j hj ih =>
      set A := H ^ (2 ^ j)
      set B' := (H.expand 2 (by decide)) ^ (2 ^ (j - 1))
      have hpowA : H ^ (2 ^ (j + 1)) = A ^ 2 := by
        dsimp only [A]; rw [pow_succ, pow_mul]
      have hpowB : (H.expand 2 (by decide)) ^ (2 ^ j) = B' ^ 2 := by
        dsimp only [B']
        conv_lhs => rw [show j = (j - 1) + 1 by omega]
        rw [pow_succ, pow_mul]
      have hdiff : H ^ (2 ^ (j + 1)) - (H.expand 2 (by decide)) ^ (2 ^ j) =
          (A - B') * ((A - B') + 2 * B') := by
        rw [hpowA, hpowB]; ring
      rw [show j + 1 - 1 = j by omega, hdiff, PowerSeries.coeff_mul]
      refine Finset.dvd_sum fun x _ => ?_
      have hd1 : (2 : ℤ) ^ j ∣ (A - B').coeff x.1 := ih x.1
      have hd2 : (2 : ℤ) ∣ ((A - B') + 2 * B').coeff x.2 := by
        rw [map_add]
        have h21 : (2 : ℤ) ∣ (A - B').coeff x.2 :=
          dvd_trans (dvd_pow_self 2 (by omega : j ≠ 0)) (ih x.2)
        have h22 : (2 : ℤ) ∣ (2 * B').coeff x.2 := by
          have : (2 * B').coeff x.2 = 2 * B'.coeff x.2 := by
            have hC : (2 : ℤ⟦X⟧) = PowerSeries.C 2 := by simp
            rw [hC, PowerSeries.coeff_C_mul]
          rw [this]; exact dvd_mul_right 2 _
        exact dvd_add h21 h22
      rcases hd1 with ⟨c1, hc1⟩
      rcases hd2 with ⟨c2, hc2⟩
      refine ⟨c1 * c2, ?_⟩
      rw [hc1, hc2, pow_succ]; ring

private noncomputable def Mseries : ℤ⟦X⟧ :=
  (Ssq.expand 3 (by decide) + Ssq) *
    (aBase.expand 2 (by decide) * bBase.expand 2 (by decide) *
      ((aBase.expand 2 (by decide)) ^ 4 + X ^ 2 * (bBase.expand 2 (by decide)) ^ 4)) +
  X * (aBase.expand 2 (by decide)) ^ 3 * (bBase.expand 2 (by decide)) ^ 3

private lemma Mseries_odd_even (n : ℕ) : (2 : ℤ) ∣ Mseries.coeff (2 * n + 1) := by
  rw [two_dvd_coeff_iff]
  set r2 : ℤ⟦X⟧ →+* (ZMod 2)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hSodd : ∀ k : ℕ, (Ssq.expand 3 (by decide) + Ssq).coeff (2 * k + 1) =
      (X * psi.expand 12 (by decide) + psi.expand 4 (by decide)).coeff k := by
    intro k
    rw [map_add, map_add, Ssq_odd_part]
    congr 1
    rw [PowerSeries.coeff_expand, coeff_X_mul_eq]
    by_cases hdvd : 3 ∣ 2 * k + 1
    · rw [if_pos hdvd, if_pos (by omega : 1 ≤ k)]
      have hodd_q : (2 * k + 1) / 3 = 2 * ((k - 1) / 3) + 1 := by omega
      rw [hodd_q, Ssq_odd_part, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      by_cases h1 : 4 ∣ (k - 1) / 3
      · have h2 : 12 ∣ k - 1 := by rcases h1 with ⟨c, hc⟩; exact ⟨c, by omega⟩
        rw [if_pos h1, if_pos h2]; congr 1; rw [Nat.div_div_eq_div_mul]
      · have h2 : ¬ 12 ∣ k - 1 := by intro h2; apply h1; rcases h2 with ⟨c, hc⟩; exact ⟨c, by omega⟩
        rw [if_neg h1, if_neg h2]
    · rw [if_neg hdvd]
      split_ifs with hk1
      · rw [PowerSeries.coeff_expand, if_neg]
        intro h12; apply hdvd; rcases h12 with ⟨c, hc⟩; exact ⟨8 * c + 1, by omega⟩
      · rfl
  have hodd_mul_even : ∀ (H E Hodd : ℤ⟦X⟧),
      (∀ k, H.coeff (2 * k + 1) = Hodd.coeff k) →
      (H * E.expand 2 (by decide)).coeff (2 * n + 1) = (Hodd * E).coeff n := by
    intro H E Hodd hH
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [← Finset.sum_filter_of_ne (p := fun x : ℕ × ℕ => 2 ∣ x.2)]
    · refine Finset.sum_bij (fun x _ => (x.1 / 2, x.2 / 2)) ?_ ?_ ?_ ?_
      · intro ⟨i, j⟩ hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx ⊢; omega
      · intro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h₁ h₂
        simp only [Prod.mk.injEq] at heq
        ext <;> omega
      · intro ⟨a, b⟩ hy
        rw [Finset.mem_antidiagonal] at hy
        refine ⟨(2 * a + 1, 2 * b), ?_, by ext <;> omega⟩
        simp only [Finset.mem_filter, Finset.mem_antidiagonal]; exact ⟨by omega, dvd_mul_right 2 b⟩
      · intro ⟨i, j⟩ hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        have hi : i = 2 * (i / 2) + 1 := by omega
        have hj : j = 2 * (j / 2) := by omega
        conv_lhs => rw [hi, hj]
        rw [hH, PowerSeries.coeff_expand_mul]
    · intro ⟨i, j⟩ _ hne
      by_contra hndvd
      exact hne (by rw [PowerSeries.coeff_expand_of_not_dvd 2 (by decide) E hndvd, mul_zero])
  set Ebase : ℤ⟦X⟧ := aBase * bBase * (aBase ^ 4 + X * bBase ^ 4)
  have hM_coeff : Mseries.coeff (2 * n + 1) =
      ((X * psi.expand 12 (by decide) + psi.expand 4 (by decide)) * Ebase +
        aBase ^ 3 * bBase ^ 3).coeff n := by
    have hE_exp : aBase.expand 2 (by decide) * bBase.expand 2 (by decide) *
        ((aBase.expand 2 (by decide)) ^ 4 + X ^ 2 * (bBase.expand 2 (by decide)) ^ 4) =
        Ebase.expand 2 (by decide) := by
      simp only [Ebase, map_add, map_mul, map_pow, PowerSeries.expand_X]
    have hterm2 : (X * (aBase.expand 2 (by decide)) ^ 3 * (bBase.expand 2 (by decide)) ^ 3).coeff (2 * n + 1) =
        (aBase ^ 3 * bBase ^ 3).coeff n := by
      have hrew : X * (aBase.expand 2 (by decide)) ^ 3 * (bBase.expand 2 (by decide)) ^ 3 =
          X * (aBase ^ 3 * bBase ^ 3).expand 2 (by decide) := by
        simp only [map_mul, map_pow]; ring
      rw [hrew, coeff_X_mul_eq, if_pos (by omega)]
      have hidx : 2 * n + 1 - 1 = 2 * n := by omega
      rw [hidx, PowerSeries.coeff_expand_mul]
    rw [Mseries, map_add, hE_exp, hodd_mul_even _ Ebase _ hSodd, hterm2, map_add]
  rw [map_ZMod_coeff, hM_coeff, ← map_ZMod_coeff]
  have hpsi_mod2 : r2 (psi * psi.expand 3 (by decide)) =
      r2 (psi.expand 4 (by decide) + X * psi.expand 12 (by decide)) := by
    have h := congrArg r2 psi_mul_psi3
    simp only [r2, map_add, map_mul, PowerSeries.map_expand, PowerSeries.map_X,
      phi_mod2, map_one, one_mul, mul_one] at h ⊢
    exact h
  have hpow4_mod2 : ∀ H : (ZMod 2)⟦X⟧, H ^ 4 = H.expand 4 (by decide) := by
    intro H
    calc
      H ^ 4 = (H ^ 2) ^ 2 := by ring
      _ = (H.expand 2 (by decide)).expand 2 (by decide) := by
            rw [zmod2_sq_eq_expand2, zmod2_sq_eq_expand2]
      _ = H.expand 4 (by decide) := by rw [← PowerSeries.expand_mul]
  set P2 := r2 psi
  set P3_2 := r2 (psi.expand 3 (by decide))
  set I2 := r2 (PowerSeries.invOfUnit (f 3 (by decide)) 1)
  have ha2 : r2 aBase = P2 * I2 := by simp [aBase, P2, I2, r2]
  have hb2 : r2 bBase = P3_2 * I2 := by simp [bBase, P3_2, I2, r2]
  have hsum_sq : r2 (psi.expand 4 (by decide) + X * psi.expand 12 (by decide)) = P2 * P3_2 := by
    simpa [P2, P3_2, r2] using hpsi_mod2.symm
  have ha4_b4 : (r2 aBase) ^ 4 + X * (r2 bBase) ^ 4 = (P2 * P3_2) * I2 ^ 4 := by
    rw [ha2, hb2, mul_pow, mul_pow, hpow4_mod2 P2, hpow4_mod2 P3_2]
    have h1 : P2.expand 4 (by decide) = r2 (psi.expand 4 (by decide)) := by
      simp [P2, r2, PowerSeries.map_expand]
    have h2 : P3_2.expand 4 (by decide) = r2 (psi.expand 12 (by decide)) := by
      simp [P3_2, r2, PowerSeries.map_expand, ← PowerSeries.expand_mul]
    rw [h1, h2]
    calc
      r2 (psi.expand 4 (by decide)) * I2 ^ 4 + X * (r2 (psi.expand 12 (by decide)) * I2 ^ 4)
          = r2 (psi.expand 4 (by decide) + X * psi.expand 12 (by decide)) * I2 ^ 4 := by
            simp [r2]; ring
      _ = P2 * P3_2 * I2 ^ 4 := by rw [hsum_sq]
  have hzero : r2 ((X * psi.expand 12 (by decide) + psi.expand 4 (by decide)) * Ebase +
      aBase ^ 3 * bBase ^ 3) = 0 := by
    have hcomm : r2 (X * psi.expand 12 (by decide) + psi.expand 4 (by decide)) = P2 * P3_2 := by
      rw [add_comm]; exact hsum_sq
    have hEbase2 : r2 Ebase = (P2 * P3_2) ^ 2 * I2 ^ 6 := by
      dsimp only [Ebase]
      rw [map_mul, map_mul, map_add, map_pow, map_mul, PowerSeries.map_X, map_pow,
        ha4_b4, ha2, hb2]
      ring
    calc
      r2 ((X * psi.expand 12 (by decide) + psi.expand 4 (by decide)) * Ebase +
          aBase ^ 3 * bBase ^ 3)
          = r2 (X * psi.expand 12 (by decide) + psi.expand 4 (by decide)) * r2 Ebase +
            (r2 aBase) ^ 3 * (r2 bBase) ^ 3 := by simp [r2]
      _ = (P2 * P3_2) * ((P2 * P3_2) ^ 2 * I2 ^ 6) + (P2 * I2) ^ 3 * (P3_2 * I2) ^ 3 := by
            rw [hcomm, hEbase2, ha2, hb2]
      _ = 2 * ((P2 * P3_2) ^ 3 * I2 ^ 6) := by ring
      _ = 0 := by rw [two_eq_zero_zmod2, zero_mul]
  rw [hzero, map_zero]

private lemma W2_mul_E2_sq_odd_mod4 (n : ℕ) : (4 : ℤ) ∣ (W₂ * E₂ ^ 2).coeff (2 * n + 1) := by
  rw [four_dvd_coeff_iff]
  set r4 : ℤ⟦X⟧ →+* (ZMod 4)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 4))
  have h2r : r4 2 = 2 := map_ofNat r4 2
  have hXr : r4 X = X := PowerSeries.map_X _
  have hA : r4 E₁ = r4 (phi.expand 3 (by decide)) * r4 phi * r4 (aBase.expand 2 (by decide)) := by
    rw [E1_eq_factors, map_mul, map_mul, inv_phiNeg_mod4]
  have hB : r4 O₁ = r4 (bBase.expand 2 (by decide)) := O1_mod4
  have hphi3_sq : (r4 (phi.expand 3 (by decide))) ^ 2 = 1 := by
    rw [PowerSeries.map_expand, ← map_pow, phi_sq_mod4, map_one]
  have hE1_sq : (r4 E₁) ^ 2 = (r4 (aBase.expand 2 (by decide))) ^ 2 := by
    rw [hA, mul_pow, mul_pow, hphi3_sq, phi_sq_mod4, one_mul, one_mul]
  have hE2_mod4 : r4 E₂ = (r4 (aBase.expand 2 (by decide))) ^ 2 +
      X * (r4 (bBase.expand 2 (by decide))) ^ 2 := by
    rw [E₂, map_add, map_pow, map_mul, hXr, map_pow, hE1_sq, hB]
  have hE2_sq_mod4 : (r4 E₂) ^ 2 =
      (r4 (aBase.expand 2 (by decide))) ^ 4 +
      X ^ 2 * (r4 (bBase.expand 2 (by decide))) ^ 4 +
      2 * X * (r4 (aBase.expand 2 (by decide))) ^ 2 * (r4 (bBase.expand 2 (by decide))) ^ 2 := by
    rw [hE2_mod4]; ring
  have hphi_prod : r4 (phi.expand 3 (by decide)) * r4 phi =
      1 + 2 * (r4 (Ssq.expand 3 (by decide)) + r4 Ssq) := by
    have hphi3 : phi.expand 3 (by decide) = 1 + 2 * Ssq.expand 3 (by decide) := by
      rw [phi_eq_one_add_two_Ssq, map_add, map_one, map_mul, map_ofNat]
    rw [hphi3, phi_eq_one_add_two_Ssq, map_add, map_one, map_mul, h2r, map_add, map_one, map_mul, h2r]
    calc
      (1 + 2 * r4 (Ssq.expand 3 (by decide))) * (1 + 2 * r4 Ssq)
          = 1 + 2 * (r4 (Ssq.expand 3 (by decide)) + r4 Ssq) +
            4 * (r4 (Ssq.expand 3 (by decide)) * r4 Ssq) := by ring
      _ = 1 + 2 * (r4 (Ssq.expand 3 (by decide)) + r4 Ssq) := by rw [four_eq_zero_zmod4]; ring
  have hW2_mod4 : r4 W₂ =
      (1 + 2 * (r4 (Ssq.expand 3 (by decide)) + r4 Ssq)) *
      r4 (aBase.expand 2 (by decide)) * r4 (bBase.expand 2 (by decide)) := by
    rw [W₂, map_mul, hA, hB, hphi_prod]
  set A4 := r4 (aBase.expand 2 (by decide))
  set B4 := r4 (bBase.expand 2 (by decide))
  set S4 := r4 (Ssq.expand 3 (by decide)) + r4 Ssq
  have hprod_mod4 : r4 (W₂ * E₂ ^ 2) =
      A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4) +
      2 * (S4 * (A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4)) + X * A4 ^ 3 * B4 ^ 3) := by
    rw [map_mul, map_pow, hW2_mod4, hE2_sq_mod4]
    calc
      (1 + 2 * S4) * A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4 + 2 * X * A4 ^ 2 * B4 ^ 2)
          = A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4) +
            2 * (S4 * (A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4)) + X * A4 ^ 3 * B4 ^ 3) +
            4 * (S4 * X * A4 ^ 3 * B4 ^ 3) := by ring
      _ = A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4) +
            2 * (S4 * (A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4)) + X * A4 ^ 3 * B4 ^ 3) := by
          rw [four_eq_zero_zmod4]; ring
  rw [hprod_mod4, map_add]
  have heven_part : (A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4)).coeff (2 * n + 1) = 0 := by
    have hexp : A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4) =
        (r4 (aBase * bBase * (aBase ^ 4 + X * bBase ^ 4))).expand 2 (by decide) := by
      simp only [A4, B4, r4, map_add, map_mul, map_pow, PowerSeries.map_expand,
        PowerSeries.map_X, PowerSeries.expand_X]
    rw [hexp]
    exact PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)
  rw [heven_part, zero_add]
  have hM_eq : 2 * (S4 * (A4 * B4 * (A4 ^ 4 + X ^ 2 * B4 ^ 4)) + X * A4 ^ 3 * B4 ^ 3) =
      r4 (2 * Mseries) := by
    simp only [Mseries, S4, A4, B4, map_add, map_mul, map_pow, h2r, hXr]
  rw [hM_eq, map_ZMod_coeff]
  have h2M : (2 * Mseries).coeff (2 * n + 1) = 2 * Mseries.coeff (2 * n + 1) := by
    have hC : (2 : ℤ⟦X⟧) = PowerSeries.C 2 := by simp
    rw [hC, PowerSeries.coeff_C_mul]
  rw [h2M]
  rcases Mseries_odd_even n with ⟨c, hc⟩
  rw [hc]
  have hcast : ((2 * (2 * c) : ℤ) : ZMod 4) = 0 := by
    have : (2 * (2 * c) : ℤ) = 4 * c := by ring
    rw [this, Int.cast_mul]
    rw [show ((4 : ℤ) : ZMod 4) = 0 by decide, zero_mul]
  exact hcast

/-- `(P3)`: `8 ∣ B (8*s + 6) (4*n + 3)` for every `s` and `n`. -/
theorem cong_P3 (s n : ℕ) : (8 : ℤ) ∣ B (8 * s + 6) (4 * n + 3) := by
  rw [B]
  have hexp : G ^ (8 * s + 6) = (G ^ 2) ^ (4 * s + 3) := by
    rw [← pow_mul]; congr 1; omega
  rw [hexp, G_sq_dissection, add_comm (E₂.expand 2 (by decide)), add_pow, map_sum]
  refine Finset.dvd_sum fun j hj => ?_
  by_cases hj3 : 3 ≤ j
  · have hpow2 : (2 * X * W₂.expand 2 (by decide)) ^ j =
        PowerSeries.C ((2 : ℤ) ^ j) * (X * W₂.expand 2 (by decide)) ^ j := by
      rw [mul_assoc, mul_pow]
      have hC : (2 : ℤ⟦X⟧) ^ j = PowerSeries.C ((2 : ℤ) ^ j) := by simp
      rw [hC]
    rw [hpow2, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul]
    have hd8 : (8 : ℤ) ∣ (2 : ℤ) ^ j := by
      have : (2 : ℤ) ^ j = 8 * (2 : ℤ) ^ (j - 3) := by
        calc
          (2 : ℤ) ^ j = (2 : ℤ) ^ (3 + (j - 3)) := by congr 1; omega
          _ = (2 : ℤ) ^ 3 * (2 : ℤ) ^ (j - 3) := pow_add 2 3 (j - 3)
          _ = 8 * (2 : ℤ) ^ (j - 3) := by norm_num
      exact ⟨(2 : ℤ) ^ (j - 3), this⟩
    exact dvd_mul_of_dvd_left hd8 _
  · interval_cases j
    · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      rw [← map_pow, PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)]
      exact dvd_zero 8
    · simp only [pow_one, Nat.choose_one_right]
      have hsub : 4 * s + 3 - 1 = 4 * s + 2 := by omega
      rw [hsub]
      have hrew : 2 * X * W₂.expand 2 (by decide) * (E₂.expand 2 (by decide)) ^ (4 * s + 2) *
          ((4 * s + 3 : ℕ) : ℤ⟦X⟧) =
          PowerSeries.C (2 * ((4 * s + 3 : ℕ) : ℤ)) *
            (X * (W₂ * E₂ ^ (4 * s + 2)).expand 2 (by decide)) := by
        simp only [map_mul, map_pow, map_ofNat, map_natCast]
        ring
      rw [hrew, PowerSeries.coeff_C_mul, coeff_X_mul_eq, if_pos (by omega)]
      have hidx : 4 * n + 3 - 1 = 2 * (2 * n + 1) := by omega
      rw [hidx, PowerSeries.coeff_expand_mul]
      have hd4 : (4 : ℤ) ∣ (W₂ * E₂ ^ (4 * s + 2)).coeff (2 * n + 1) := by
        rw [four_dvd_coeff_iff]
        set r4 : ℤ⟦X⟧ →+* (ZMod 4)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 4))
        have hE4 : r4 (E₂ ^ 4) = (r4 (E₂ ^ 2)).expand 2 (by decide) := by
          have hf := frobenius_pow_two E₂ 2 (by decide)
          have heq : r4 (E₂ ^ 4 - (E₂.expand 2 (by decide)) ^ 2) = 0 := by
            ext m
            rw [map_ZMod_coeff, map_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
            simpa using hf m
          rw [map_sub, sub_eq_zero] at heq
          rw [heq]
          simp [r4, PowerSeries.map_expand]
        have hsplit : W₂ * E₂ ^ (4 * s + 2) = (W₂ * E₂ ^ 2) * (E₂ ^ 4) ^ s := by
          rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; omega
        rw [hsplit, map_mul, map_pow, hE4, ← map_pow, PowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        by_cases h2 : 2 ∣ x.2
        · have hx1_odd : x.1 = 2 * (x.1 / 2) + 1 := by omega
          rw [hx1_odd]
          have h0 : (r4 (W₂ * E₂ ^ 2)).coeff (2 * (x.1 / 2) + 1) = 0 :=
            (four_dvd_coeff_iff _ _).mp (W2_mul_E2_sq_odd_mod4 (x.1 / 2))
          rw [h0, zero_mul]
        · rw [PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ h2, mul_zero]
      rcases hd4 with ⟨c, hc⟩
      refine ⟨((4 * s + 3 : ℕ) : ℤ) * c, ?_⟩
      rw [hc]; ring
    · have heven : (2 * X * W₂.expand 2 (by decide)) ^ 2 *
          (E₂.expand 2 (by decide)) ^ (4 * s + 3 - 2) * (((4 * s + 3).choose 2 : ℕ) : ℤ⟦X⟧) =
          (4 * X * W₂ ^ 2 * E₂ ^ (4 * s + 3 - 2) * (((4 * s + 3).choose 2 : ℕ) : ℤ⟦X⟧)).expand 2 (by decide) := by
        simp only [map_mul, map_pow, PowerSeries.expand_X, map_ofNat, map_natCast]
        ring
      rw [heven, PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)]
      exact dvd_zero 8

end Dissections

/-! ## Section 5: Frobenius Reductions, `B k 3`, `B k 7`, and Proof of Conjecture 6.2 -/

section MainProof

/-- **Lemma 2 (uniform odd-index bound):** for every `k ≥ 1` and every `m`,
`2^{v_2(k)} ∣ B k (2*m + 1)`. -/
theorem dvd_B_odd (k m : ℕ) (_hk : 1 ≤ k) :
    ((2 : ℤ) ^ padicValNat 2 k) ∣ B k (2 * m + 1) := by
  set a := padicValNat 2 k
  by_cases ha : a = 0
  · rw [ha, pow_zero]; exact one_dvd _
  · have ha1 : 1 ≤ a := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2 ^ a ∣ k := pow_padicValNat_dvd
    rcases hdvd with ⟨r, hr⟩
    rw [B, hr, pow_mul]
    rw [show ((2 : ℤ) ^ a) = (((2 ^ a : ℕ) : ℤ)) by push_cast; rfl,
      dvd_coeff_iff_map_ZMod_eq_zero]
    set rM : ℤ⟦X⟧ →+* (ZMod (2 ^ a))⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod (2 ^ a)))
    have hfrob : rM (G ^ (2 ^ a)) = (rM (G ^ (2 ^ (a - 1)))).expand 2 (by decide) := by
      have hf := frobenius_pow_two G a ha1
      have hsub : rM (G ^ (2 ^ a) - (G.expand 2 (by decide)) ^ (2 ^ (a - 1))) = 0 := by
        ext n
        rw [map_ZMod_coeff, map_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa using hf n
      rw [map_sub, sub_eq_zero] at hsub
      rw [hsub]
      simp [rM, PowerSeries.map_expand]
    rw [map_pow, hfrob, ← map_pow]
    exact PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)

private lemma coeff_mul_expand4_three_eq_zero {M : ℕ} (R U : (ZMod M)⟦X⟧)
    (hR : ∀ j, R.coeff (4 * j + 3) = 0) (n : ℕ) :
    (R * U.expand 4 (by decide)).coeff (4 * n + 3) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h4 : 4 ∣ x.2
  · have hi : x.1 = 4 * (x.1 / 4) + 3 := by omega
    rw [hi, hR, zero_mul]
  · rw [PowerSeries.coeff_expand_of_not_dvd 4 (by decide) _ h4, mul_zero]

private lemma G4_mod2 :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (G ^ 4) =
      (PowerSeries.map (Int.castRingHom (ZMod 2)) G).expand 4 (by decide) := by
  set r2 : ℤ⟦X⟧ →+* (ZMod 2)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 2))
  calc
    r2 (G ^ 4) = ((r2 G) ^ 2) ^ 2 := by rw [map_pow]; ring
    _ = ((r2 G).expand 2 (by decide)).expand 2 (by decide) := by
          rw [zmod2_sq_eq_expand2, zmod2_sq_eq_expand2]
    _ = (r2 G).expand 4 (by decide) := by rw [← PowerSeries.expand_mul]

private lemma G8_mod4 :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (G ^ 8) =
      (PowerSeries.map (Int.castRingHom (ZMod 4)) (G ^ 2)).expand 4 (by decide) := by
  set r4 : ℤ⟦X⟧ →+* (ZMod 4)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 4))
  have hG4 : r4 (G ^ 4) = (r4 (G ^ 2)).expand 2 (by decide) := by
    have hf := frobenius_pow_two G 2 (by decide)
    have hsub : r4 (G ^ 4 - (G.expand 2 (by decide)) ^ 2) = 0 := by
      ext m
      rw [map_ZMod_coeff, map_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using hf m
    rw [map_sub, sub_eq_zero] at hsub
    rw [hsub]; simp [r4, PowerSeries.map_expand]
  calc
    r4 (G ^ 8) = (r4 (G ^ 4)) ^ 2 := by rw [← map_pow, ← pow_mul]
    _ = ((r4 (G ^ 2)).expand 2 (by decide)) ^ 2 := by rw [hG4]
    _ = (r4 (G ^ 4)).expand 2 (by decide) := by
          rw [← map_pow, ← map_pow]; congr 2; ring
    _ = ((r4 (G ^ 2)).expand 2 (by decide)).expand 2 (by decide) := by rw [hG4]
    _ = (r4 (G ^ 2)).expand 4 (by decide) := by rw [← PowerSeries.expand_mul]

/-- **Lemma 3(a):** `k ≡ 1 (mod 4) → 2 ∣ B k (4*n + 3)`. -/
theorem cong_mod2_1mod4 {k : ℕ} (hk : k % 4 = 1) (n : ℕ) : (2 : ℤ) ∣ B k (4 * n + 3) := by
  rw [B, two_dvd_coeff_iff]
  set r2 : ℤ⟦X⟧ →+* (ZMod 2)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hsplit : k = 1 + 4 * (k / 4) := by omega
  rw [hsplit, pow_add, pow_one, pow_mul, map_mul, map_pow, G4_mod2, ← map_pow]
  refine coeff_mul_expand4_three_eq_zero (r2 G) ((r2 G) ^ (k / 4)) ?_ n
  intro j
  rw [← two_dvd_coeff_iff]
  exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) (by simpa [B] using cong_P1 j)

/-- **Lemma 3(b):** `k ≡ 1 (mod 8) → 4 ∣ B k (4*n + 3)`. -/
theorem cong_mod4_1mod8 {k : ℕ} (hk : k % 8 = 1) (n : ℕ) : (4 : ℤ) ∣ B k (4 * n + 3) := by
  rw [B, four_dvd_coeff_iff]
  set r4 : ℤ⟦X⟧ →+* (ZMod 4)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 4))
  have hsplit : k = 1 + 8 * (k / 8) := by omega
  rw [hsplit, pow_add, pow_one, pow_mul, map_mul, map_pow, G8_mod4, ← map_pow]
  refine coeff_mul_expand4_three_eq_zero (r4 G) ((r4 (G ^ 2)) ^ (k / 8)) ?_ n
  intro j
  rw [← four_dvd_coeff_iff]
  simpa [B] using cong_P1 j

/-- **Lemma 3(c):** `k ≡ 2 (mod 8) → 4 ∣ B k (4*n + 3)`. -/
theorem cong_mod4_2mod8 {k : ℕ} (hk : k % 8 = 2) (n : ℕ) : (4 : ℤ) ∣ B k (4 * n + 3) := by
  rw [B, four_dvd_coeff_iff]
  set r4 : ℤ⟦X⟧ →+* (ZMod 4)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 4))
  have hsplit : k = 2 + 8 * (k / 8) := by omega
  rw [hsplit, pow_add, pow_mul, map_mul, map_pow r4 (G ^ 8), G8_mod4, ← map_pow]
  refine coeff_mul_expand4_three_eq_zero (r4 (G ^ 2)) ((r4 (G ^ 2)) ^ (k / 8)) ?_ n
  intro j
  rw [← four_dvd_coeff_iff]
  simpa [B] using cong_P2 j

-- Fast computable degree-7 truncated series arithmetic over `Fin 8 → ℤ`.
private def tOne : Fin 8 → ℤ := fun n => if n.1 = 0 then 1 else 0

private def tMul (a b : Fin 8 → ℤ) : Fin 8 → ℤ :=
  fun n => ∑ i : Fin 8, if h : i.1 ≤ n.1 then a i * b ⟨n.1 - i.1, by omega⟩ else 0

private def tPow (a : Fin 8 → ℤ) : ℕ → (Fin 8 → ℤ)
  | 0 => tOne
  | k + 1 => tMul (tPow a k) a

private def vecF1 : Fin 8 → ℤ := ![1, -1, -1, 0, 0, 1, 0, 1]
private def vecF3 : Fin 8 → ℤ := ![1, 0, 0, -1, 0, 0, -1, 0]
private def vecF4 : Fin 8 → ℤ := ![1, 0, 0, 0, -1, 0, 0, 0]
private def vecF6 : Fin 8 → ℤ := ![1, 0, 0, 0, 0, 0, -1, 0]
private def vecG0 : Fin 8 → ℤ := ![1, 1, 2, 4, 5, 8, 12, 16]
private def vecGm1 : Fin 8 → ℤ := ![0, 1, 2, 4, 5, 8, 12, 16]

private lemma coeff_mul_eq_tMul {A B : ℤ⟦X⟧} {a b : Fin 8 → ℤ}
    (hA : ∀ n : Fin 8, A.coeff n.1 = a n) (hB : ∀ n : Fin 8, B.coeff n.1 = b n) :
    ∀ n : Fin 8, (A * B).coeff n.1 = tMul a b n := by
  intro n
  rw [PowerSeries.coeff_mul, tMul]
  rw [← Finset.sum_filter_of_ne (p := fun i : Fin 8 => i.1 ≤ n.1)]
  · refine Finset.sum_bij (fun x hx => ⟨x.1, by rw [Finset.mem_antidiagonal] at hx; omega⟩) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_antidiagonal] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_antidiagonal] at hx₁ hx₂
      simp only [Fin.mk.injEq] at heq
      ext <;> omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨(i.1, n.1 - i.1), by rw [Finset.mem_antidiagonal]; omega, by ext; rfl⟩
    · intro x hx
      rw [Finset.mem_antidiagonal] at hx
      have hle : x.1 ≤ n.1 := by omega
      have hx2 : x.2 = n.1 - x.1 := by omega
      rw [dif_pos hle, hA ⟨x.1, by omega⟩]
      congr 1
      exact (congrArg (fun k => B.coeff k) hx2).trans (hB ⟨n.1 - x.1, by omega⟩)
  · intro i _ hne
    by_contra hnot
    exact hne (dif_neg hnot)

private lemma coeff_pow_eq_tPow {A : ℤ⟦X⟧} {a : Fin 8 → ℤ}
    (hA : ∀ n : Fin 8, A.coeff n.1 = a n) :
    ∀ k : ℕ, ∀ n : Fin 8, (A ^ k).coeff n.1 = tPow a k n
  | 0, n => by
      simp only [pow_zero, tPow, tOne, PowerSeries.coeff_one]
  | k + 1, n => by
      rw [pow_succ, tPow]
      exact coeff_mul_eq_tMul (coeff_pow_eq_tPow hA k) hA n

private lemma pentagonal_coeff_le7 (n : Fin 8) :
    (PowerSeries.pentagonalSeries ℤ).coeff n.1 = vecF1 n := by
  have h0 : pentagonal (0 : ℤ) = 0 := by decide
  have h1 : pentagonal (1 : ℤ) = 1 := by decide
  have hm1 : pentagonal (-1 : ℤ) = 2 := by decide
  have h2 : pentagonal (2 : ℤ) = 5 := by decide
  have hm2 : pentagonal (-2 : ℤ) = 7 := by decide
  have hnot : ∀ m : ℕ, m ∈ ({3, 4, 6} : Finset ℕ) → m ∉ Set.range pentagonal := by
    intro m hm hmem
    rcases hmem with ⟨k, hk⟩
    have hbig : ∀ z : ℤ, z ≤ -3 ∨ 3 ≤ z → 12 ≤ pentagonal z := by
      intro z hz
      have hp : (2 : ℤ) * (pentagonal z : ℤ) = z * (3 * z - 1) := by
        simp only [pentagonal]
        have hev : 2 ∣ z * (3 * z - 1) := by
          rcases Int.even_or_odd z with ⟨t, rfl⟩ | ⟨t, rfl⟩
          · exact ⟨t * (3 * (t + t) - 1), by ring⟩
          · exact ⟨(2 * t + 1) * (3 * t + 1), by ring⟩
        have hnn : 0 ≤ z * (3 * z - 1) / 2 := by
          apply Int.ediv_nonneg
          · rcases hz with h | h <;> nlinarith
          · norm_num
        rw [Int.toNat_of_nonneg hnn]
        exact Int.mul_ediv_cancel' hev
      rcases hz with h | h <;> nlinarith
    have hsmall : k ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
      by_contra hnotmem
      have hge3 : k ≤ -3 ∨ 3 ≤ k := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hnotmem
        omega
      have h12 := hbig k hge3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    fin_cases hsmall <;> simp_all [pentagonal] <;> omega
  fin_cases n
  · change (PowerSeries.pentagonalSeries ℤ).coeff 0 = 1
    rw [← h0, PowerSeries.coeff_pentagonalSeries_pentagonal]; decide
  · change (PowerSeries.pentagonalSeries ℤ).coeff 1 = -1
    rw [← h1, PowerSeries.coeff_pentagonalSeries_pentagonal]; decide
  · change (PowerSeries.pentagonalSeries ℤ).coeff 2 = -1
    rw [← hm1, PowerSeries.coeff_pentagonalSeries_pentagonal]; decide
  · change (PowerSeries.pentagonalSeries ℤ).coeff 3 = 0
    exact PowerSeries.coeff_pentagonalSeries_eq_zero ℤ (hnot 3 (by decide))
  · change (PowerSeries.pentagonalSeries ℤ).coeff 4 = 0
    exact PowerSeries.coeff_pentagonalSeries_eq_zero ℤ (hnot 4 (by decide))
  · change (PowerSeries.pentagonalSeries ℤ).coeff 5 = 1
    rw [← h2, PowerSeries.coeff_pentagonalSeries_pentagonal]; decide
  · change (PowerSeries.pentagonalSeries ℤ).coeff 6 = 0
    exact PowerSeries.coeff_pentagonalSeries_eq_zero ℤ (hnot 6 (by decide))
  · change (PowerSeries.pentagonalSeries ℤ).coeff 7 = 1
    rw [← hm2, PowerSeries.coeff_pentagonalSeries_pentagonal]; decide

private lemma coeff_f1_le7 (n : Fin 8) : (f 1 (by decide)).coeff n.1 = vecF1 n := by
  simpa [f] using pentagonal_coeff_le7 n

private lemma coeff_f3_le7 (n : Fin 8) : (f 3 (by decide)).coeff n.1 = vecF3 n := by
  rw [f, PowerSeries.coeff_expand]
  have hp0 := pentagonal_coeff_le7 ⟨0, by decide⟩
  have hp1 := pentagonal_coeff_le7 ⟨1, by decide⟩
  have hp2 := pentagonal_coeff_le7 ⟨2, by decide⟩
  fin_cases n <;> simp [hp0, hp1, hp2, vecF1, vecF3]

private lemma coeff_f4_le7 (n : Fin 8) : (f 4 (by decide)).coeff n.1 = vecF4 n := by
  rw [f, PowerSeries.coeff_expand]
  have hp0 := pentagonal_coeff_le7 ⟨0, by decide⟩
  have hp1 := pentagonal_coeff_le7 ⟨1, by decide⟩
  fin_cases n <;> simp [hp0, hp1, vecF1, vecF4]

private lemma coeff_f6_le7 (n : Fin 8) : (f 6 (by decide)).coeff n.1 = vecF6 n := by
  rw [f, PowerSeries.coeff_expand]
  have hp0 := pentagonal_coeff_le7 ⟨0, by decide⟩
  have hp1 := pentagonal_coeff_le7 ⟨1, by decide⟩
  fin_cases n <;> simp [hp0, hp1, vecF1, vecF6]

private lemma coeff_f12_le7 (n : Fin 8) : (f 12 (by decide)).coeff n.1 = tOne n := by
  rw [f, PowerSeries.coeff_expand]
  have hp0 := pentagonal_coeff_le7 ⟨0, by decide⟩
  fin_cases n <;> simp [hp0, vecF1, tOne]

private lemma coeff_G_le7 (n : Fin 8) : G.coeff n.1 = vecG0 n := by
  let G0 : ℤ⟦X⟧ := PowerSeries.mk fun m => if h : m < 8 then vecG0 ⟨m, h⟩ else 0
  have hG0 : ∀ m : Fin 8, G0.coeff m.1 = vecG0 m := by intro m; simp [G0, m.2]
  have hden : ∀ m : Fin 8,
      (f 1 (by decide) * f 3 (by decide) * f 12 (by decide)).coeff m.1 =
      tMul (tMul vecF1 vecF3) tOne m :=
    coeff_mul_eq_tMul (coeff_mul_eq_tMul coeff_f1_le7 coeff_f3_le7) coeff_f12_le7
  have hnum : ∀ m : Fin 8,
      (f 4 (by decide) * (f 6 (by decide)) ^ 2).coeff m.1 =
      tMul vecF4 (tPow vecF6 2) m :=
    coeff_mul_eq_tMul coeff_f4_le7 (coeff_pow_eq_tPow coeff_f6_le7 2)
  have hvec : ∀ m : Fin 8,
      tMul vecG0 (tMul (tMul vecF1 vecF3) tOne) m = tMul vecF4 (tPow vecF6 2) m := by decide
  have hagree : AgreeUpto 7
      (G * (f 1 (by decide) * f 3 (by decide) * f 12 (by decide)))
      (G0 * (f 1 (by decide) * f 3 (by decide) * f 12 (by decide))) := by
    intro m hm
    let mf : Fin 8 := ⟨m, by omega⟩
    rw [G_mul_den, hnum mf, coeff_mul_eq_tMul hG0 hden mf, hvec mf]
  have hG_eq := AgreeUpto.cancel_unit_right (by simp) hagree
  exact (hG_eq n.1 (by omega)).trans (hG0 n)

private lemma coeff_Gm1_le7 (n : Fin 8) : (G - 1).coeff n.1 = vecGm1 n := by
  rw [map_sub, coeff_G_le7 n, PowerSeries.coeff_one]
  fin_cases n <;> decide

/-- Binomial expansion of `B k n = ∑_{i=0}^n C(k, i) * [q^n](G - 1)^i`. -/
theorem B_eq_sum_choose (k n : ℕ) :
    B k n = ∑ i ∈ Finset.range (n + 1), ((k.choose i : ℕ) : ℤ) * ((G - 1) ^ i).coeff n := by
  have hG1 : PowerSeries.constantCoeff (G - 1) = 0 := by simp [constantCoeff_G]
  have hshift : ∃ H : ℤ⟦X⟧, G - 1 = X * H := by
    refine ⟨PowerSeries.mk fun m => (G - 1).coeff (m + 1), ?_⟩
    have h := PowerSeries.sub_const_eq_X_mul_shift (G - 1)
    rw [hG1, map_zero, sub_zero] at h
    exact h
  rcases hshift with ⟨H, hH⟩
  have hvanish : ∀ i > n, ((G - 1) ^ i).coeff n = 0 := by
    intro i hi
    rw [hH, mul_pow, coeff_X_pow_mul_of_lt hi]
  rw [B]
  have hGpow : G ^ k = ((G - 1) + 1) ^ k := by ring
  rw [hGpow, add_pow, map_sum]
  have hterm : ∀ i : ℕ, (((G - 1) ^ i * 1 ^ (k - i) * ((k.choose i : ℕ) : ℤ⟦X⟧)).coeff n) =
      ((k.choose i : ℕ) : ℤ) * ((G - 1) ^ i).coeff n := by
    intro i
    simp only [one_pow, mul_one]
    have hC : ((k.choose i : ℕ) : ℤ⟦X⟧) = PowerSeries.C ((k.choose i : ℕ) : ℤ) := by simp
    rw [mul_comm, hC, PowerSeries.coeff_C_mul]
  simp_rw [hterm]
  by_cases hkn : k ≤ n
  · refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  · symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [hvanish i (by omega), mul_zero]

private lemma two_mul_choose_two (k : ℕ) :
    2 * (k.choose 2 : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_one_right]
      push_cast; linarith

private lemma six_mul_choose_three (k : ℕ) :
    6 * (k.choose 3 : ℤ) = (k : ℤ) * ((k : ℤ) - 1) * ((k : ℤ) - 2) := by
  induction k with
  | zero => simp
  | succ m ih =>
      have h2 := two_mul_choose_two m
      rw [Nat.choose_succ_succ, Nat.cast_add]
      push_cast; linarith

/-- **Lemma 1:** `6 * B k 3 = k * (k + 2) * (k + 7)` for every `k`. -/
theorem six_mul_B_three (k : ℕ) :
    6 * B k 3 = (k : ℤ) * (k + 2) * (k + 7) := by
  rw [B_eq_sum_choose, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hc0 : ((G - 1) ^ 0).coeff 3 = 0 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 0 ⟨3, by decide⟩).trans (by decide)
  have hc1 : ((G - 1) ^ 1).coeff 3 = 4 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 1 ⟨3, by decide⟩).trans (by decide)
  have hc2 : ((G - 1) ^ 2).coeff 3 = 4 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 2 ⟨3, by decide⟩).trans (by decide)
  have hc3 : ((G - 1) ^ 3).coeff 3 = 1 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 3 ⟨3, by decide⟩).trans (by decide)
  rw [hc0, hc1, hc2, hc3]
  have hC1 : (k.choose 1 : ℤ) = k := by simp
  linear_combination 24 * hC1 + 12 * two_mul_choose_two k + six_mul_choose_three k

lemma B_three_pos {k : ℕ} (hk : 1 ≤ k) : 0 < B k 3 := by
  have h := six_mul_B_three k
  have hpos : (0 : ℤ) < (k : ℤ) * (k + 2) * (k + 7) := by positivity
  omega

/-- Closed binomial formula for `B k 7`. -/
theorem B_seven_formula (k : ℕ) :
    B k 7 =
      16 * (k.choose 1 : ℤ) + 96 * (k.choose 2 : ℤ) + 180 * (k.choose 3 : ℤ) +
      148 * (k.choose 4 : ℤ) + 60 * (k.choose 5 : ℤ) + 12 * (k.choose 6 : ℤ) +
      (k.choose 7 : ℤ) := by
  rw [B_eq_sum_choose]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hc0 : ((G - 1) ^ 0).coeff 7 = 0 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 0 ⟨7, by decide⟩).trans (by decide)
  have hc1 : ((G - 1) ^ 1).coeff 7 = 16 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 1 ⟨7, by decide⟩).trans (by decide)
  have hc2 : ((G - 1) ^ 2).coeff 7 = 96 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 2 ⟨7, by decide⟩).trans (by decide)
  have hc3 : ((G - 1) ^ 3).coeff 7 = 180 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 3 ⟨7, by decide⟩).trans (by decide)
  have hc4 : ((G - 1) ^ 4).coeff 7 = 148 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 4 ⟨7, by decide⟩).trans (by decide)
  have hc5 : ((G - 1) ^ 5).coeff 7 = 60 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 5 ⟨7, by decide⟩).trans (by decide)
  have hc6 : ((G - 1) ^ 6).coeff 7 = 12 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 6 ⟨7, by decide⟩).trans (by decide)
  have hc7 : ((G - 1) ^ 7).coeff 7 = 1 :=
    (coeff_pow_eq_tPow coeff_Gm1_le7 7 ⟨7, by decide⟩).trans (by decide)
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  ring

private lemma choose_add_period_mod (P M : ℕ) (hP : ∀ j, 1 ≤ j → j ≤ 7 → M ∣ P.choose j)
    (k i : ℕ) (hi : i ≤ 7) :
    ((k + P).choose i : ℤ) ≡ (k.choose i : ℤ) [ZMOD M] := by
  rw [add_comm, Nat.add_choose_eq]
  have hsplit : Finset.antidiagonal i =
      insert (0, i) ((Finset.antidiagonal i).erase (0, i)) :=
    (Finset.insert_erase (by simp)).symm
  rw [hsplit, Finset.sum_insert (Finset.notMem_erase _ _), Nat.choose_zero_right, one_mul]
  rw [Nat.cast_add, Int.ModEq]
  have hdvd_rest : (M : ℤ) ∣ (((Finset.antidiagonal i).erase (0, i)).sum
      fun x => P.choose x.1 * k.choose x.2 : ℕ) := by
    rw [Nat.cast_sum]
    refine Finset.dvd_sum fun x hx => ?_
    rw [Finset.mem_erase, Finset.mem_antidiagonal] at hx
    have hx1_pos : 1 ≤ x.1 := by
      by_contra h0
      have hx1 : x.1 = 0 := by omega
      have hx2 : x.2 = i := by omega
      exact hx.1 (by ext <;> omega)
    have hd : M ∣ P.choose x.1 := hP x.1 hx1_pos (by omega)
    rw [Nat.cast_mul]
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _
  rcases hdvd_rest with ⟨c, hc⟩
  rw [hc, Int.add_mul_emod_self_left]

private lemma B_seven_period32_mod8 (k : ℕ) : B (k + 32) 7 ≡ B k 7 [ZMOD 8] := by
  have hP : ∀ j, 1 ≤ j → j ≤ 7 → 8 ∣ (32 : ℕ).choose j := by
    intro j hj1 hj7; interval_cases j <;> decide
  have hC := fun i (hi : i ≤ 7) => choose_add_period_mod 32 8 hP k i hi
  rw [B_seven_formula (k + 32), B_seven_formula k]
  exact (((((( (Int.ModEq.mul_left 16 (hC 1 (by decide))).add
    (Int.ModEq.mul_left 96 (hC 2 (by decide))) ).add
    (Int.ModEq.mul_left 180 (hC 3 (by decide))) ).add
    (Int.ModEq.mul_left 148 (hC 4 (by decide))) ).add
    (Int.ModEq.mul_left 60 (hC 5 (by decide))) ).add
    (Int.ModEq.mul_left 12 (hC 6 (by decide))) ).add
    (hC 7 (by decide)))

private lemma B_seven_period64_mod16 (k : ℕ) : B (k + 64) 7 ≡ B k 7 [ZMOD 16] := by
  have hP : ∀ j, 1 ≤ j → j ≤ 7 → 16 ∣ (64 : ℕ).choose j := by
    intro j hj1 hj7; interval_cases j <;> decide
  have hC := fun i (hi : i ≤ 7) => choose_add_period_mod 64 16 hP k i hi
  rw [B_seven_formula (k + 64), B_seven_formula k]
  exact (((((( (Int.ModEq.mul_left 16 (hC 1 (by decide))).add
    (Int.ModEq.mul_left 96 (hC 2 (by decide))) ).add
    (Int.ModEq.mul_left 180 (hC 3 (by decide))) ).add
    (Int.ModEq.mul_left 148 (hC 4 (by decide))) ).add
    (Int.ModEq.mul_left 60 (hC 5 (by decide))) ).add
    (Int.ModEq.mul_left 12 (hC 6 (by decide))) ).add
    (hC 7 (by decide)))

private lemma B_seven_mod8_eq_mod32 (k : ℕ) : B k 7 ≡ B (k % 32) 7 [ZMOD 8] := by
  have hdiv : k = k % 32 + 32 * (k / 32) := (Nat.mod_add_div k 32).symm
  conv_lhs => rw [hdiv]
  generalize k / 32 = q
  induction q with
  | zero => simp
  | succ q ih =>
      have hrew : k % 32 + 32 * (q + 1) = (k % 32 + 32 * q) + 32 := by ring
      rw [hrew]
      exact (B_seven_period32_mod8 _).trans ih

private lemma B_seven_mod16_eq_mod64 (k : ℕ) : B k 7 ≡ B (k % 64) 7 [ZMOD 16] := by
  have hdiv : k = k % 64 + 64 * (k / 64) := (Nat.mod_add_div k 64).symm
  conv_lhs => rw [hdiv]
  generalize k / 64 = q
  induction q with
  | zero => simp
  | succ q ih =>
      have hrew : k % 64 + 64 * (q + 1) = (k % 64 + 64 * q) + 64 := by ring
      rw [hrew]
      exact (B_seven_period64_mod16 _).trans ih

/-- **Lemma 4 (exactness witness for `k ≡ 9 mod 16`):** `¬ 8 ∣ B k 7`. -/
theorem not_eight_dvd_B_seven_9mod16 {k : ℕ} (hk : k % 16 = 9) : ¬ (8 : ℤ) ∣ B k 7 := by
  have hmod : B k 7 % 8 = B (k % 32) 7 % 8 := B_seven_mod8_eq_mod32 k
  have hcases : k % 32 = 9 ∨ k % 32 = 25 := by omega
  have hval : B k 7 % 8 = 4 := by
    rw [hmod]
    rcases hcases with h9 | h25
    · rw [h9, B_seven_formula]; decide
    · rw [h25, B_seven_formula]; decide
  omega

/-- **Exactness witness for `k ≡ 14 mod 16`:** `¬ 16 ∣ B k 7`. -/
theorem not_sixteen_dvd_B_seven_14mod16 {k : ℕ} (hk : k % 16 = 14) : ¬ (16 : ℤ) ∣ B k 7 := by
  have hmod : B k 7 % 16 = B (k % 64) 7 % 16 := B_seven_mod16_eq_mod64 k
  have hcases : k % 64 = 14 ∨ k % 64 = 30 ∨ k % 64 = 46 ∨ k % 64 = 62 := by omega
  have hval : B k 7 % 16 = 8 := by
    rw [hmod]
    rcases hcases with h14 | h30 | h46 | h62
    · rw [h14, B_seven_formula]; decide
    · rw [h30, B_seven_formula]; decide
    · rw [h46, B_seven_formula]; decide
    · rw [h62, B_seven_formula]; decide
  omega

private lemma padicValNat_two_of_odd {m : ℕ} (hm : m % 2 = 1) : padicValNat 2 m = 0 := by
  apply padicValNat.eq_zero_of_not_dvd; omega

private lemma padicValNat_two_eq_of_exact {m e : ℕ} (hm : m ≠ 0)
    (hd : 2 ^ e ∣ m) (hnd : ¬ 2 ^ (e + 1) ∣ m) : padicValNat 2 m = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : e ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm).mp hd
  have hlt : padicValNat 2 m < e + 1 := by
    by_contra hge
    exact hnd ((padicValNat_dvd_iff_le hm).mpr (by omega))
  omega

private lemma padicValNat_B_three_add_one {k : ℕ} (hk : 1 ≤ k) :
    1 + padicValNat 2 (B k 3).natAbs =
      padicValNat 2 k + padicValNat 2 (k + 2) + padicValNat 2 (k + 7) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos := B_three_pos hk
  have hnat : 6 * (B k 3).natAbs = k * (k + 2) * (k + 7) := by
    have h6 := six_mul_B_three k
    have hnn : ((B k 3).natAbs : ℤ) = B k 3 := Int.natAbs_of_nonneg (by omega)
    have hz : ((6 * (B k 3).natAbs : ℕ) : ℤ) = ((k * (k + 2) * (k + 7) : ℕ) : ℤ) := by
      push_cast; rw [abs_of_pos hpos]; exact h6
    exact_mod_cast hz
  have hne : (B k 3).natAbs ≠ 0 := by omega
  have h6 : padicValNat 2 6 = 1 := padicValNat_two_eq_of_exact (by decide) (by decide) (by decide)
  calc
    1 + padicValNat 2 (B k 3).natAbs
        = padicValNat 2 6 + padicValNat 2 (B k 3).natAbs := by rw [h6]
    _ = padicValNat 2 (6 * (B k 3).natAbs) := (padicValNat.mul (by decide) hne).symm
    _ = padicValNat 2 (k * (k + 2) * (k + 7)) := by rw [hnat]
    _ = padicValNat 2 (k * (k + 2)) + padicValNat 2 (k + 7) :=
          padicValNat.mul (by positivity) (by positivity)
    _ = padicValNat 2 k + padicValNat 2 (k + 2) + padicValNat 2 (k + 7) := by
          rw [padicValNat.mul (by omega) (by omega)]

private lemma not_pow_succ_dvd_B_three {k : ℕ} (hk : 1 ≤ k) :
    ¬ ((2 : ℤ) ^ (padicValNat 2 (B k 3).natAbs + 1)) ∣ B k 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos := B_three_pos hk
  intro hdvd
  have hnat : 2 ^ (padicValNat 2 (B k 3).natAbs + 1) ∣ (B k 3).natAbs := by
    have hcast : ((2 ^ (padicValNat 2 (B k 3).natAbs + 1) : ℕ) : ℤ) ∣ ((B k 3).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg (by omega)]; exact_mod_cast hdvd
    exact Int.natCast_dvd_natCast.mp hcast
  have hle := (padicValNat_dvd_iff_le (by omega : (B k 3).natAbs ≠ 0)).mp hnat
  omega

/-- The exponent predicted by Yaqubi–Mirzavaziri Conjecture 6.2:
`v_2(B_k(3))`, except `2` when `k ≡ 1 (mod 8)` and `3` when `k ≡ 6 (mod 8)`. -/
noncomputable def conjExp (k : ℕ) : ℕ :=
  if k % 8 = 1 then 2
  else if k % 8 = 6 then 3
  else padicValNat 2 (B k 3).natAbs

/-- Explicit formula for `conjExp k` by residue class modulo `8`. -/
theorem conjExp_explicit {k : ℕ} (hk : 1 ≤ k) :
    conjExp k =
      if k % 4 = 3 then 0
      else if k % 8 = 5 then 1
      else if k % 8 = 1 ∨ k % 8 = 2 then 2
      else if k % 8 = 6 then 3
      else padicValNat 2 k := by
  have hval := padicValNat_B_three_add_one hk
  unfold conjExp
  have hm8 : k % 8 < 8 := Nat.mod_lt k (by decide)
  interval_cases h : k % 8
  · have hk2 : padicValNat 2 (k + 2) = 1 :=
      padicValNat_two_eq_of_exact (by omega) ⟨k / 2 + 1, by omega⟩ (by intro ⟨c, hc⟩; omega)
    have hk7 : padicValNat 2 (k + 7) = 0 := padicValNat_two_of_odd (by omega)
    simp [show k % 4 ≠ 3 by omega]; omega
  · simp [show k % 4 ≠ 3 by omega]
  · have hk0 : padicValNat 2 k = 1 :=
      padicValNat_two_eq_of_exact (by omega) ⟨k / 2, by omega⟩ (by intro ⟨c, hc⟩; omega)
    have hk2 : padicValNat 2 (k + 2) = 2 :=
      padicValNat_two_eq_of_exact (by omega) ⟨k / 4 + 1, by omega⟩ (by intro ⟨c, hc⟩; omega)
    have hk7 : padicValNat 2 (k + 7) = 0 := padicValNat_two_of_odd (by omega)
    simp [show k % 4 ≠ 3 by omega]; omega
  · have hk0 : padicValNat 2 k = 0 := padicValNat_two_of_odd (by omega)
    have hk2 : padicValNat 2 (k + 2) = 0 := padicValNat_two_of_odd (by omega)
    have hk7 : padicValNat 2 (k + 7) = 1 :=
      padicValNat_two_eq_of_exact (by omega) ⟨(k + 7) / 2, by omega⟩ (by intro ⟨c, hc⟩; omega)
    have h31 : (3 : ℕ) ≠ 1 := by decide
    have h36 : (3 : ℕ) ≠ 6 := by decide
    simp only [show k % 4 = 3 by omega, h31, h36, ↓reduceIte]; omega
  · have hk2 : padicValNat 2 (k + 2) = 1 :=
      padicValNat_two_eq_of_exact (by omega) ⟨k / 2 + 1, by omega⟩ (by intro ⟨c, hc⟩; omega)
    have hk7 : padicValNat 2 (k + 7) = 0 := padicValNat_two_of_odd (by omega)
    simp [show k % 4 ≠ 3 by omega]; omega
  · have hk0 : padicValNat 2 k = 0 := padicValNat_two_of_odd (by omega)
    have hk2 : padicValNat 2 (k + 2) = 0 := padicValNat_two_of_odd (by omega)
    have hk7 : padicValNat 2 (k + 7) = 2 :=
      padicValNat_two_eq_of_exact (by omega) ⟨(k + 7) / 4, by omega⟩ (by intro ⟨c, hc⟩; omega)
    simp [show k % 4 ≠ 3 by omega]; omega
  · simp [show k % 4 ≠ 3 by omega]
  · have hk0 : padicValNat 2 k = 0 := padicValNat_two_of_odd (by omega)
    have hk2 : padicValNat 2 (k + 2) = 0 := padicValNat_two_of_odd (by omega)
    have hk7 : padicValNat 2 (k + 7) = 1 :=
      padicValNat_two_eq_of_exact (by omega) ⟨(k + 7) / 2, by omega⟩ (by intro ⟨c, hc⟩; omega)
    have h71 : (7 : ℕ) ≠ 1 := by decide
    have h76 : (7 : ℕ) ≠ 6 := by decide
    simp only [show k % 4 = 3 by omega, h71, h76, ↓reduceIte]; omega

/-- **Main Theorem (Yaqubi–Mirzavaziri Conjecture 6.2, arXiv:2611.05623v1).**
For every `k ≥ 1`, `2 ^ (conjExp k)` is the exact largest power of `2` dividing `B k (4*n + 3)`
for all `n ≥ 0`. -/
theorem yaqubi_mirzavaziri_conjecture_6_2 (k : ℕ) (hk : 1 ≤ k) :
    (∀ n : ℕ, ((2 : ℤ) ^ conjExp k) ∣ B k (4 * n + 3)) ∧
    (∃ n : ℕ, ¬ ((2 : ℤ) ^ (conjExp k + 1)) ∣ B k (4 * n + 3)) := by
  have hexp := conjExp_explicit hk
  have hval := padicValNat_B_three_add_one hk
  have hupper0 := not_pow_succ_dvd_B_three hk
  have hm8 : k % 8 < 8 := Nat.mod_lt k (by decide)
  interval_cases h : k % 8
  · have he : conjExp k = padicValNat 2 k := by
      rw [hexp]; simp [show k % 4 ≠ 3 by omega]
    have hB3 : padicValNat 2 (B k 3).natAbs = padicValNat 2 k := by
      have : conjExp k = padicValNat 2 (B k 3).natAbs := by simp [conjExp, h]
      omega
    rw [he]
    refine ⟨fun n => ?_, ⟨0, by simpa [hB3] using hupper0⟩⟩
    simpa [show 4 * n + 3 = 2 * (2 * n + 1) + 1 by omega] using dvd_B_odd k (2 * n + 1) hk
  · have he : conjExp k = 2 := by simp [conjExp, h]
    rw [he]
    refine ⟨fun n => by simpa using cong_mod4_1mod8 h n, ?_⟩
    by_cases h16 : k % 16 = 1
    · refine ⟨0, ?_⟩
      have hk0 : padicValNat 2 k = 0 := padicValNat_two_of_odd (by omega)
      have hk2 : padicValNat 2 (k + 2) = 0 := padicValNat_two_of_odd (by omega)
      have hk7 : padicValNat 2 (k + 7) = 3 :=
        padicValNat_two_eq_of_exact (by omega) ⟨(k + 7) / 8, by omega⟩ (by intro ⟨c, hc⟩; omega)
      have hB3 : padicValNat 2 (B k 3).natAbs = 2 := by omega
      simpa [hB3] using hupper0
    · have h9 : k % 16 = 9 := by omega
      exact ⟨1, by simpa using not_eight_dvd_B_seven_9mod16 h9⟩
  · have he : conjExp k = 2 := by
      rw [hexp]; simp [show k % 4 ≠ 3 by omega]
    have hB3 : padicValNat 2 (B k 3).natAbs = 2 := by
      have : conjExp k = padicValNat 2 (B k 3).natAbs := by simp [conjExp, h]
      omega
    rw [he]
    exact ⟨fun n => by simpa using cong_mod4_2mod8 h n, ⟨0, by simpa [hB3] using hupper0⟩⟩
  · have he : conjExp k = 0 := by
      rw [hexp]; simp [show k % 4 = 3 by omega]
    have hB3 : padicValNat 2 (B k 3).natAbs = 0 := by
      have : conjExp k = padicValNat 2 (B k 3).natAbs := by simp [conjExp, h]
      omega
    rw [he]
    exact ⟨fun _ => by simp, ⟨0, by simpa [hB3] using hupper0⟩⟩
  · have he : conjExp k = padicValNat 2 k := by
      rw [hexp]; simp [show k % 4 ≠ 3 by omega]
    have hB3 : padicValNat 2 (B k 3).natAbs = padicValNat 2 k := by
      have : conjExp k = padicValNat 2 (B k 3).natAbs := by simp [conjExp, h]
      omega
    rw [he]
    refine ⟨fun n => ?_, ⟨0, by simpa [hB3] using hupper0⟩⟩
    simpa [show 4 * n + 3 = 2 * (2 * n + 1) + 1 by omega] using dvd_B_odd k (2 * n + 1) hk
  · have he : conjExp k = 1 := by
      rw [hexp]; simp [show k % 4 ≠ 3 by omega]
    have hB3 : padicValNat 2 (B k 3).natAbs = 1 := by
      have : conjExp k = padicValNat 2 (B k 3).natAbs := by simp [conjExp, h]
      omega
    rw [he]
    exact ⟨fun n => by simpa using cong_mod2_1mod4 (by omega) n,
      ⟨0, by simpa [hB3] using hupper0⟩⟩
  · have he : conjExp k = 3 := by simp [conjExp, h]
    rw [he]
    refine ⟨fun n => ?_, ?_⟩
    · have hk_eq : k = 8 * (k / 8) + 6 := by omega
      rw [hk_eq]; simpa using cong_P3 (k / 8) n
    · by_cases h16 : k % 16 = 6
      · refine ⟨0, ?_⟩
        have hk0 : padicValNat 2 k = 1 :=
          padicValNat_two_eq_of_exact (by omega) ⟨k / 2, by omega⟩ (by intro ⟨c, hc⟩; omega)
        have hk2 : padicValNat 2 (k + 2) = 3 :=
          padicValNat_two_eq_of_exact (by omega) ⟨(k + 2) / 8, by omega⟩ (by intro ⟨c, hc⟩; omega)
        have hk7 : padicValNat 2 (k + 7) = 0 := padicValNat_two_of_odd (by omega)
        have hB3 : padicValNat 2 (B k 3).natAbs = 3 := by omega
        simpa [hB3] using hupper0
      · have h14 : k % 16 = 14 := by omega
        exact ⟨1, by simpa using not_sixteen_dvd_B_seven_14mod16 h14⟩
  · have he : conjExp k = 0 := by
      rw [hexp]; simp [show k % 4 = 3 by omega]
    have hB3 : padicValNat 2 (B k 3).natAbs = 0 := by
      have : conjExp k = padicValNat 2 (B k 3).natAbs := by simp [conjExp, h]
      omega
    rw [he]
    exact ⟨fun _ => by simp, ⟨0, by simpa [hB3] using hupper0⟩⟩

end MainProof

end YaqubiMirzavaziriPDO
