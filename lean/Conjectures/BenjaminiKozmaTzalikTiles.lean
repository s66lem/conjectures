import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Tiles of `ℤ` Inside `{1, 2, 4, …, 2^n}`: Disproof and Complete Size Spectrum
# (Benjamini–Kozma–Tzalik, EJC 33(3), 2026, #P3.28, Question 9)

This file formalizes the negative resolution of the second part of Question 9 of
I. Benjamini, G. Kozma, and E. Tzalik, *The number of tiles of `ℤ^d`*,
*Electron. J. Combin.* **33(3)** (2026), #P3.28 (arXiv:2303.07956v2, Section 3; Question 13 in v1):

> **Question 9.** How many tiles are contained in the set `{1, 2, 4, …, 2^n}`?
> Are the only such tiles the sets of size 1 and 2?

Main formalized theorems (standard axioms only):
1. `bkt_q9_disproof`: `{1, 4, 16} ⊆ {1, 2, 4, 8, 16}` has cardinality `3` and tiles `ℤ` by
   translations with complement `T = {-1, 0, 1} + 9ℤ`. Thus the answer to the second part of
   Question 9 is **NO** for every `n ≥ 4`.
2. `odd_size_power_of_two_tile_exists`: For every odd `k ≥ 1`, there exists a `k`-element subset
   of `{2^j : j ∈ ℕ}` that tiles `ℤ` (explicit construction `{2^(r*d) : d < k}` with
   `r = φ(k)`, proved via Euler's theorem and an elementary lifting-the-exponent lemma).
3. `even_size_ge_four_no_power_of_two_tile`: For every even `k ≥ 4`, NO `k`-element subset of
   `{2^j : j ∈ ℕ}` tiles `ℤ` (proved via dilation normalization, Newman's periodicity theorem,
   Coven–Meyerowitz's cyclotomic prime-power divisibility criterion (T1), and the alternating
   coefficient sum obstruction for `Φ_{2^j}(X) = X^{2^{j-1}} + 1`).
4. `power_of_two_tile_size_iff`: Complete size spectrum — a `k`-element subset of `{2^j : j ∈ ℕ}`
   tiles `ℤ` **if and only if** `k = 1 ∨ k = 2 ∨ Odd k`.
-/

namespace BenjaminiKozmaTzalikTiles

open scoped BigOperators
open Polynomial

/-- A set `S ⊆ ℤ` tiles `ℤ` by translations if there is `T ⊆ ℤ` such that every `z ∈ ℤ`
can be written uniquely as `s + t` with `s ∈ S` and `t ∈ T` (Benjamini–Kozma–Tzalik §1). -/
def Tiles (S : Set ℤ) : Prop :=
  ∃ T : Set ℤ, ∀ z : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ S ∧ p.2 ∈ T ∧ p.1 + p.2 = z

/-- `IsPow2Set S` says every element of the finite set `S : Finset ℕ` is a power of 2. -/
def IsPow2Set (S : Finset ℕ) : Prop :=
  ∀ s ∈ S, ∃ j : ℕ, s = 2 ^ j

/-! ### Part 1: Explicit 3-element counterexample `{1, 4, 16}` (disproves BKT Question 9) -/

/-- **Theorem 1 (Negative answer to Benjamini–Kozma–Tzalik Question 9):**
The 3-element set `{1, 4, 16} ⊆ {1, 2, 4, 8, 16}` tiles `ℤ` via `T = {-1, 0, 1} + 9ℤ`. -/
theorem bkt_q9_disproof :
    ({1, 4, 16} : Set ℤ) ⊆ {x : ℤ | ∃ j ≤ 4, x = (2 : ℤ) ^ j} ∧
    Tiles ({1, 4, 16} : Set ℤ) ∧
    ({1, 4, 16} : Set ℤ).ncard = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨4, by norm_num, by norm_num⟩
  · refine ⟨{t : ℤ | t % 9 = 8 ∨ t % 9 = 0 ∨ t % 9 = 1}, fun z => ?_⟩
    have hcases : z % 9 < 3 ∨ (3 ≤ z % 9 ∧ z % 9 < 6) ∨ 6 ≤ z % 9 := by omega
    rcases hcases with h | ⟨h1, h2⟩ | h
    · refine ⟨(1, z - 1), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, true_or, true_and]
        exact ⟨by omega, by ring⟩
      · rintro ⟨s, t⟩ ⟨hs, ht, he⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hs ht
        ext <;> dsimp only <;> omega
    · refine ⟨(4, z - 4), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact ⟨Or.inr (Or.inl trivial), by omega, by ring⟩
      · rintro ⟨s, t⟩ ⟨hs, ht, he⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hs ht
        ext <;> dsimp only <;> omega
    · refine ⟨(16, z - 16), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact ⟨Or.inr (Or.inr trivial), by omega, by ring⟩
      · rintro ⟨s, t⟩ ⟨hs, ht, he⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hs ht
        ext <;> dsimp only <;> omega
  · simp [Set.ncard_insert_of_notMem, Set.ncard_singleton]

/-! ### Part 2: Elementary Lifting-the-Exponent and Existence for Every Odd Size `k ≥ 1` -/

/-- Geometric sum `f q m = ∑_{j < m} q^j` (so `(q - 1) * f q m = q^m - 1`). -/
private def geomSumNat (q m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, q ^ j

private lemma geomSumNat_mul_pred (q m : ℕ) (hq : 1 ≤ q) :
    (q - 1) * geomSumNat q m = q ^ m - 1 := by
  induction m with
  | zero => simp [geomSumNat]
  | succ m ih =>
    unfold geomSumNat at ih ⊢
    rw [Finset.sum_range_succ, mul_add, ih]
    have hqm : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
    have hqms : 1 ≤ q ^ (m + 1) := Nat.one_le_pow (m + 1) q (by omega)
    zify [hq, hqm, hqms]
    ring

private lemma geomSumNat_add (q a b : ℕ) :
    geomSumNat q (a + b) = geomSumNat q a + q ^ a * geomSumNat q b := by
  unfold geomSumNat
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]

private lemma geomSumNat_mul (q a b : ℕ) :
    geomSumNat q (a * b) = geomSumNat q a * geomSumNat (q ^ a) b := by
  induction b with
  | zero => simp [geomSumNat]
  | succ b ih =>
    rw [Nat.mul_succ, geomSumNat_add, ih]
    unfold geomSumNat
    rw [Finset.sum_range_succ, mul_add, ← pow_mul, mul_comm (q ^ (a * b))]

private lemma geomSumNat_mod_prime {p q m : ℕ} (hdvd : p ∣ q - 1) (hq : 1 ≤ q) :
    geomSumNat q m % p = m % p := by
  induction m with
  | zero => simp [geomSumNat]
  | succ m ih =>
    unfold geomSumNat at ih ⊢
    rw [Finset.sum_range_succ]
    have hq1 : q ≡ 1 [MOD p] := by
      rcases hdvd with ⟨t, ht⟩
      have hqeq : q = 1 + p * t := by omega
      rw [hqeq, Nat.ModEq, Nat.add_mul_mod_self_left]
    have hpow : q ^ m % p = 1 % p := by
      have h1 : q ^ m ≡ 1 ^ m [MOD p] := hq1.pow m
      simpa [Nat.ModEq, one_pow] using h1
    rw [Nat.add_mod, ih, hpow, ← Nat.add_mod]

private lemma modEq_finset_sum {α : Type*} (s : Finset α) (f g : α → ℕ) (m : ℕ)
    (h : ∀ x ∈ s, f x ≡ g x [MOD m]) :
    (∑ x ∈ s, f x) ≡ (∑ x ∈ s, g x) [MOD m] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma geomSumNat_prime_step {p x : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hx : 1 ≤ x) (hdvd : p ∣ x - 1) :
    p ∣ geomSumNat x p ∧ ¬ (p ^ 2 ∣ geomSumNat x p) := by
  rcases hdvd with ⟨t, ht⟩
  have hxeq : x = 1 + p * t := by omega
  have hpow_mod : ∀ i : ℕ, (1 + p * t) ^ i ≡ 1 + i * (p * t) [MOD p ^ 2] := by
    intro i
    induction i with
    | zero => simp [Nat.ModEq]
    | succ i ih =>
      rw [pow_succ]
      have h1 : (1 + p * t) ^ i * (1 + p * t) ≡ (1 + i * (p * t)) * (1 + p * t) [MOD p ^ 2] :=
        ih.mul_right _
      have h2 : (1 + i * (p * t)) * (1 + p * t) =
          1 + (i + 1) * (p * t) + p ^ 2 * (i * t * t) := by ring
      rw [h2] at h1
      have h3 : 1 + (i + 1) * (p * t) + p ^ 2 * (i * t * t) ≡ 1 + (i + 1) * (p * t) [MOD p ^ 2] := by
        rw [Nat.ModEq, Nat.add_mul_mod_self_left]
      exact h1.trans h3
  have hsum_mod : geomSumNat x p ≡ ∑ i ∈ Finset.range p, (1 + i * (p * t)) [MOD p ^ 2] := by
    unfold geomSumNat
    rw [hxeq]
    exact modEq_finset_sum (Finset.range p) _ _ (p ^ 2) fun i _ => hpow_mod i
  have hsum_eval : ∑ i ∈ Finset.range p, (1 + i * (p * t)) =
      p + (∑ i ∈ Finset.range p, i) * (p * t) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      ← Finset.sum_mul]
  have htri : p ∣ ∑ i ∈ Finset.range p, i := by
    have h2 := Finset.sum_range_id_mul_two p
    have hodd_p : Odd p := hp.odd_of_ne_two hodd
    have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd_p
    have hdiv : p ∣ (∑ i ∈ Finset.range p, i) * 2 := by
      rw [h2]; exact dvd_mul_right p (p - 1)
    exact hcop.dvd_of_dvd_mul_right hdiv
  rcases htri with ⟨c, hc⟩
  have hfinal : geomSumNat x p ≡ p [MOD p ^ 2] := by
    rw [hsum_eval, hc] at hsum_mod
    have hrew : p + p * c * (p * t) = p + p ^ 2 * (c * t) := by ring
    rw [hrew] at hsum_mod
    have h3 : p + p ^ 2 * (c * t) ≡ p [MOD p ^ 2] := by
      rw [Nat.ModEq, Nat.add_mul_mod_self_left]
    exact hsum_mod.trans h3
  constructor
  · have hmodp : geomSumNat x p % p = p % p :=
      hfinal.of_dvd (dvd_pow_self p (by decide : 2 ≠ 0))
    rw [Nat.mod_self] at hmodp
    exact Nat.dvd_of_mod_eq_zero hmodp
  · intro hsq
    have h0 : geomSumNat x p % p ^ 2 = 0 := Nat.mod_eq_zero_of_dvd hsq
    have hpmod : p % p ^ 2 = p := Nat.mod_eq_of_lt (by nlinarith [hp.two_le])
    have : p = 0 := by rw [Nat.ModEq, h0, hpmod] at hfinal; exact hfinal.symm
    exact hp.ne_zero this

/-- Elementary Lifting-the-Exponent lemma for `geomSumNat q m = (q^m - 1) / (q - 1)`:
if `p` is an odd prime with `p ∣ q - 1`, then `v_p(geomSumNat q m) = v_p(m)` for all `m ≥ 1`. -/
private lemma factorization_geomSumNat_eq {p q : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hq : 1 ≤ q) (hdvd : p ∣ q - 1) :
    ∀ m : ℕ, 0 < m → (geomSumNat q m).factorization p = m.factorization p := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hpm : p ∣ m
    · rcases hpm with ⟨a, rfl⟩
      have ha_pos : 0 < a := Nat.pos_of_mul_pos_left hm
      have ha_lt : a < p * a := by nlinarith [hp.two_le]
      rw [mul_comm p a, geomSumNat_mul]
      have hqa_ge : 1 ≤ q ^ a := Nat.one_le_pow a q (by omega)
      have hqa_dvd : p ∣ q ^ a - 1 := by
        rw [← geomSumNat_mul_pred q a hq]
        exact dvd_mul_of_dvd_left hdvd _
      have hstep := geomSumNat_prime_step hp hodd hqa_ge hqa_dvd
      have hg_pos : 0 < geomSumNat (q ^ a) p := by
        unfold geomSumNat
        have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
        exact lt_of_lt_of_le (by simp) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0)
      have hfa_pos : 0 < geomSumNat q a := by
        unfold geomSumNat
        have h0 : 0 ∈ Finset.range a := Finset.mem_range.mpr ha_pos
        exact lt_of_lt_of_le (by simp) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0)
      have hfac1 : (geomSumNat (q ^ a) p).factorization p = 1 := by
        have hge1 : 1 ≤ (geomSumNat (q ^ a) p).factorization p :=
          (hp.pow_dvd_iff_le_factorization hg_pos.ne').mp (by simpa using hstep.1)
        have hlt2 : ¬ 2 ≤ (geomSumNat (q ^ a) p).factorization p := fun h2 =>
          hstep.2 ((hp.pow_dvd_iff_le_factorization hg_pos.ne').mpr h2)
        omega
      rw [Nat.factorization_mul hfa_pos.ne' hg_pos.ne', Finsupp.add_apply, ih a ha_lt ha_pos,
        hfac1, Nat.factorization_mul ha_pos.ne' hp.ne_zero, Finsupp.add_apply,
        hp.factorization_self]
    · have hndvd_f : ¬ p ∣ geomSumNat q m := by
        intro hf
        have h1 := geomSumNat_mod_prime hdvd hq (m := m)
        rw [Nat.mod_eq_zero_of_dvd hf] at h1
        exact hpm (Nat.dvd_of_mod_eq_zero h1.symm)
      rw [Nat.factorization_eq_zero_of_not_dvd hndvd_f, Nat.factorization_eq_zero_of_not_dvd hpm]

/-- **Theorem 2a (Every Odd Size Occurs):**
For every odd `k ≥ 1`, there exists a `k`-element subset of `{2^j : j ∈ ℕ}` that tiles `ℤ`. -/
theorem odd_size_power_of_two_tile_exists {k : ℕ} (hk : Odd k) :
    ∃ S : Finset ℕ, S.card = k ∧ IsPow2Set S ∧ Tiles (S.image (Nat.cast : ℕ → ℤ) : Set ℤ) := by
  have hk_pos : 0 < k := by rcases hk with ⟨m, rfl⟩; omega
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨{1}, by simp, ?_, Set.univ, fun z => ?_⟩
    · intro s hs; simp only [Finset.mem_singleton] at hs; exact ⟨0, by omega⟩
    · refine ⟨(1, z - 1), by simp, ?_⟩
      rintro ⟨s, t⟩ ⟨hs, _, he⟩
      simp only [Finset.coe_image, Finset.coe_singleton, Set.image_singleton,
        Set.mem_singleton_iff] at hs
      ext <;> dsimp only <;> omega
  · have hk3 : 3 ≤ k := by rcases hk with ⟨m, rfl⟩; omega
    let r : ℕ := Nat.totient k
    have hr_pos : 0 < r := Nat.totient_pos.mpr hk_pos
    let q : ℕ := 2 ^ r
    have hq_ge2 : 2 ≤ q := by
      have : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr_pos
      simpa using this
    let g : ℕ := q - 1
    have hg_pos : 0 < g := by omega
    have hcop2k : Nat.Coprime 2 k := Nat.coprime_two_left.mpr hk
    have hkdvd_g : k ∣ g := by
      have heul : 2 ^ r ≡ 1 [MOD k] := Nat.ModEq.pow_totient hcop2k
      have hmod : q % k = 1 % k := heul
      have h1lt : 1 < k := by omega
      rw [Nat.mod_eq_of_lt h1lt] at hmod
      have hq_eq : q = k * (q / k) + q % k := (Nat.div_add_mod q k).symm
      rw [hmod] at hq_eq
      exact ⟨q / k, by dsimp only [g]; omega⟩
    have hcopqk : Nat.Coprime q k := hcop2k.pow_left r
    -- Show `d ↦ (geomSumNat q d : ZMod k)` is injective on `Fin k`
    have hf_inj : Function.Injective (fun d : Fin k => (geomSumNat q d.val : ZMod k)) := by
      intro d₁ d₂ hEq
      by_contra hne
      have hlt_or : d₁.val < d₂.val ∨ d₂.val < d₁.val := by omega
      suffices hcontra : ∀ (a b : Fin k), a.val < b.val →
          (geomSumNat q a.val : ZMod k) = (geomSumNat q b.val : ZMod k) → False by
        rcases hlt_or with hlt | hlt
        · exact hcontra d₁ d₂ hlt hEq
        · exact hcontra d₂ d₁ hlt hEq.symm
      intro a b hab hZ
      set m := b.val - a.val
      have hm_pos : 0 < m := by omega
      have hm_lt : m < k := by omega
      have hb_eq : b.val = a.val + m := by omega
      have hsplit : geomSumNat q b.val = geomSumNat q a.val + q ^ a.val * geomSumNat q m := by
        rw [hb_eq, geomSumNat_add]
      have hkdvd_prod : k ∣ q ^ a.val * geomSumNat q m := by
        rw [hsplit, Nat.cast_add] at hZ
        have hz0 : ((q ^ a.val * geomSumNat q m : ℕ) : ZMod k) = 0 := by linear_combination -hZ
        exact (ZMod.natCast_eq_zero_iff _ _).mp hz0
      have hkdvd_fm : k ∣ geomSumNat q m :=
        (hcopqk.pow_left a.val).symm.dvd_of_dvd_mul_left hkdvd_prod
      have hfm_pos : 0 < geomSumNat q m := by
        unfold geomSumNat
        exact lt_of_lt_of_le (by simp)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hm_pos))
      have hkdvd_m : k ∣ m := by
        rw [← Nat.factorization_le_iff_dvd hk_pos.ne' hm_pos.ne']
        intro p
        by_cases hp : p.Prime
        · by_cases hpk : p ∣ k
          · have hodd_p : p ≠ 2 := by
              intro h2; subst h2
              rcases hk with ⟨u, rfl⟩; omega
            have hpg : p ∣ q - 1 := dvd_trans hpk hkdvd_g
            have hle := (Nat.factorization_le_iff_dvd hk_pos.ne' hfm_pos.ne').mpr hkdvd_fm p
            rwa [factorization_geomSumNat_eq hp hodd_p (by omega) hpg m hm_pos] at hle
          · simp [Nat.factorization_eq_zero_of_not_dvd hpk]
        · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
      have := Nat.le_of_dvd hm_pos hkdvd_m
      omega
    have hf_bij : Function.Bijective (fun d : Fin k => (geomSumNat q d.val : ZMod k)) := by
      have : NeZero k := ⟨hk_pos.ne'⟩
      exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hf_inj, by rw [Fintype.card_fin, ZMod.card]⟩
    -- Build `S = {q^d : d < k}`
    let S : Finset ℕ := (Finset.range k).image (fun d => q ^ d)
    have hpow_inj : Function.Injective (fun d : ℕ => q ^ d) :=
      Nat.pow_right_injective hq_ge2
    have hScard : S.card = k := by
      rw [Finset.card_image_of_injective _ hpow_inj, Finset.card_range]
    have hSpow2 : IsPow2Set S := by
      intro s hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨d, _, rfl⟩
      exact ⟨r * d, by dsimp only [q]; rw [pow_mul]⟩
    refine ⟨S, hScard, hSpow2, ?_⟩
    -- Tiling complement: `T = {t : ℤ | (t + 1) % (g * k) < g}`
    let M : ℤ := (g : ℤ) * (k : ℤ)
    have hM_pos : 0 < M := by positivity
    refine ⟨{t : ℤ | (t + 1) % M < (g : ℤ)}, fun z => ?_⟩
    let j : ℤ := z % (g : ℤ)
    let u : ℤ := z / (g : ℤ)
    have hj0 : 0 ≤ j := Int.emod_nonneg z (by omega)
    have hjlt : j < (g : ℤ) := Int.emod_lt_of_pos z (by omega)
    have hzu : z = (g : ℤ) * u + j := (Int.mul_ediv_add_emod z (g : ℤ)).symm
    obtain ⟨d, hd⟩ := hf_bij.2 (u : ZMod k)
    dsimp only at hd
    have hqd_eq : ((q ^ d.val : ℕ) : ℤ) = 1 + (g : ℤ) * (geomSumNat q d.val : ℤ) := by
      have h1 := geomSumNat_mul_pred q d.val (by omega)
      have hqm : 1 ≤ q ^ d.val := Nat.one_le_pow d.val q (by omega)
      have h1z := congrArg (Nat.cast : ℕ → ℤ) h1
      have hq1 : 1 ≤ q := by omega
      push_cast [hq1, hqm] at h1z
      dsimp only [g]
      omega
    have hkdvd_u : (k : ℤ) ∣ (u - (geomSumNat q d.val : ℤ)) := by
      have h0 : ((u - (geomSumNat q d.val : ℤ) : ℤ) : ZMod k) = 0 := by
        push_cast; rw [hd]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    rcases hkdvd_u with ⟨w, hw⟩
    refine ⟨(((q ^ d.val : ℕ) : ℤ), z - ((q ^ d.val : ℕ) : ℤ)), ?_, ?_⟩
    · refine ⟨?_, ?_, by ring⟩
      · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, S, Finset.mem_range]
        exact ⟨q ^ d.val, ⟨d.val, d.isLt, rfl⟩, rfl⟩
      · simp only [Set.mem_ofPred_eq]
        have ht1 : (z - ((q ^ d.val : ℕ) : ℤ)) + 1 = j + M * w := by
          dsimp only [M]; nlinarith
        rw [ht1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hj0 (by nlinarith)]
        exact hjlt
    · rintro ⟨s, t⟩ ⟨hs, ht, hsum⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, S, Finset.mem_range] at hs
      rcases hs with ⟨_, ⟨d', hd'lt, rfl⟩, rfl⟩
      simp only [Set.mem_ofPred_eq] at ht
      dsimp only at hsum
      have hqd'_eq : ((q ^ d' : ℕ) : ℤ) = 1 + (g : ℤ) * (geomSumNat q d' : ℤ) := by
        have h1 := geomSumNat_mul_pred q d' (by omega)
        have hqm : 1 ≤ q ^ d' := Nat.one_le_pow d' q (by omega)
        have h1z := congrArg (Nat.cast : ℕ → ℤ) h1
        have hq1 : 1 ≤ q := by omega
        push_cast [hq1, hqm] at h1z
        dsimp only [g]
        omega
      let rt : ℤ := (t + 1) % M
      let wt : ℤ := (t + 1) / M
      have hrt0 : 0 ≤ rt := Int.emod_nonneg _ hM_pos.ne'
      have hrtg : rt < (g : ℤ) := ht
      have ht_eq : t + 1 = M * wt + rt := (Int.mul_ediv_add_emod (t + 1) M).symm
      have hz_eq : z = (g : ℤ) * ((geomSumNat q d' : ℤ) + (k : ℤ) * wt) + rt := by
        dsimp only [M] at ht_eq; nlinarith
      have hrt_eq_j : rt = j := by
        have := congrArg (· % (g : ℤ)) hz_eq
        rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt hrt0 hrtg] at this
        exact this.symm
      have hu_eq : u = (geomSumNat q d' : ℤ) + (k : ℤ) * wt := by
        have : (g : ℤ) * u = (g : ℤ) * ((geomSumNat q d' : ℤ) + (k : ℤ) * wt) := by
          linarith
        exact mul_left_cancel₀ (by omega : (g : ℤ) ≠ 0) this
      have hd'_zmod : (geomSumNat q d' : ZMod k) = (u : ZMod k) := by
        rw [hu_eq]; push_cast; simp
      have hd'_eq : (⟨d', hd'lt⟩ : Fin k) = d := hf_inj (hd'_zmod.trans hd.symm)
      have hd'val : d' = d.val := congrArg Fin.val hd'_eq
      subst hd'val
      ext
      · rfl
      · dsimp only; linarith

/-! ### Part 3: Impossibility for Every Even Size `k ≥ 4` (Newman Periodicity + Coven–Meyerowitz T1) -/

/-- Dividing a tiling set `S ⊆ dℤ` (`d > 0`) by `d` preserves `Tiles`. -/
private lemma tiles_of_mul_pos {S : Set ℤ} {d : ℤ} (hd : 0 < d)
    (h : Tiles ((fun x => d * x) '' S)) : Tiles S := by
  rcases h with ⟨T, hT⟩
  refine ⟨{t : ℤ | d * t ∈ T}, fun z => ?_⟩
  obtain ⟨⟨ds, t⟩, ⟨⟨s, hs, rfl⟩, ht, hsum⟩, huniq⟩ := hT (d * z)
  dsimp only at ht hsum
  have ht_eq : t = d * (z - s) := by linarith
  refine ⟨(s, z - s), ⟨hs, by simp only [Set.mem_ofPred_eq, ← ht_eq]; exact ht, by ring⟩, ?_⟩
  rintro ⟨s', t'⟩ ⟨hs', ht', hsum'⟩
  simp only [Set.mem_ofPred_eq] at ht'
  dsimp only at hs' hsum'
  have heq := huniq (d * s', d * t') ⟨⟨s', hs', rfl⟩, ht', by dsimp only; rw [← mul_add, hsum']⟩
  have hs_eq : d * s' = d * s := congrArg Prod.fst heq
  have hs'eq : s' = s := mul_left_cancel₀ hd.ne' hs_eq
  ext <;> dsimp only <;> linarith

/-- Every nonempty finite power-of-2 tile can be normalized (dividing by its minimum element)
to a power-of-2 tile of the same cardinality containing `1`. -/
private lemma normalize_pow2_tile {S : Finset ℕ} (hne : S.Nonempty) (hpow : IsPow2Set S)
    (htiles : Tiles (S.image (Nat.cast : ℕ → ℤ) : Set ℤ)) :
    ∃ S' : Finset ℕ, S'.card = S.card ∧ IsPow2Set S' ∧ 1 ∈ S' ∧
      Tiles (S'.image (Nat.cast : ℕ → ℤ) : Set ℤ) := by
  let m := S.min' hne
  have hm_mem : m ∈ S := Finset.min'_mem S hne
  obtain ⟨e, he⟩ := hpow m hm_mem
  have hm_pos : 0 < m := by rw [he]; positivity
  let S' : Finset ℕ := S.image (fun s => s / m)
  have hdiv : ∀ s ∈ S, m ∣ s := by
    intro s hs
    obtain ⟨j, rfl⟩ := hpow s hs
    have hle : 2 ^ e ≤ 2 ^ j := by rw [← he]; exact Finset.min'_le S _ hs
    have hej : e ≤ j := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
    rw [he]
    exact Nat.pow_dvd_pow 2 hej
  have hinj : Set.InjOn (fun s => s / m) (S : Set ℕ) := by
    intro s₁ hs₁ s₂ hs₂ hEq
    dsimp only at hEq
    have h1 := Nat.mul_div_cancel' (hdiv s₁ hs₁)
    have h2 := Nat.mul_div_cancel' (hdiv s₂ hs₂)
    rw [← h1, ← h2, hEq]
  have hcard : S'.card = S.card := Finset.card_image_of_injOn hinj
  have hpow' : IsPow2Set S' := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨s, hs, rfl⟩
    obtain ⟨j, rfl⟩ := hpow s hs
    have hle : 2 ^ e ≤ 2 ^ j := by rw [← he]; exact Finset.min'_le S _ hs
    have hej : e ≤ j := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
    refine ⟨j - e, ?_⟩
    rw [he, Nat.pow_div hej (by decide)]
  have h1mem : 1 ∈ S' := by
    rw [Finset.mem_image]
    exact ⟨m, hm_mem, Nat.div_self hm_pos⟩
  have hset_eq : (S.image (Nat.cast : ℕ → ℤ) : Set ℤ) =
      (fun x => (m : ℤ) * x) '' (S'.image (Nat.cast : ℕ → ℤ) : Set ℤ) := by
    ext z
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, S']
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨((s / m : ℕ) : ℤ), ⟨s / m, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
      exact_mod_cast Nat.mul_div_cancel' (hdiv s hs)
    · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      exact_mod_cast (Nat.mul_div_cancel' (hdiv s hs)).symm
  rw [hset_eq] at htiles
  exact ⟨S', hcard, hpow', h1mem, tiles_of_mul_pos (Int.natCast_pos.mpr hm_pos) htiles⟩

/-- **Newman's Periodicity Theorem (1977):** Any translation tiling of `ℤ` by a finite nonempty
subset `S ⊆ ℕ` is periodic with some positive period `M > 0`. -/
private lemma tiling_periodic {S : Finset ℕ} (hne : S.Nonempty)
    (T : Set ℤ) (hT : ∀ z : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ (S.image (Nat.cast : ℕ → ℤ) : Set ℤ) ∧ p.2 ∈ T ∧ p.1 + p.2 = z) :
    ∃ M : ℕ, 0 < M ∧ ∀ y : ℤ, y + (M : ℤ) ∈ T ↔ y ∈ T := by
  let smin := S.min' hne
  let smax := S.max' hne
  have hsmin_mem : smin ∈ S := Finset.min'_mem S hne
  have hsmax_mem : smax ∈ S := Finset.max'_mem S hne
  let D : ℕ := smax - smin
  have hle_max : ∀ s ∈ S, s ≤ smax := fun s hs => Finset.le_max' S s hs
  have hmin_le : ∀ s ∈ S, smin ≤ s := fun s hs => Finset.min'_le S s hs
  have hfwd : ∀ y : ℤ, y ∈ T ↔ ∀ s ∈ S, s ≠ smin → y + (smin : ℤ) - (s : ℤ) ∉ T := by
    intro y
    constructor
    · intro hy s hs hne_s ht
      obtain ⟨⟨s₀, t₀⟩, _, huniq⟩ := hT (y + (smin : ℤ))
      have h1 := huniq ((smin : ℤ), y) ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hsmin_mem), hy, by ring⟩
      have h2 := huniq ((s : ℤ), y + (smin : ℤ) - (s : ℤ)) ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hs), ht, by ring⟩
      have heq : (s : ℤ) = (smin : ℤ) := congrArg Prod.fst (h2.trans h1.symm)
      exact hne_s (Int.ofNat.inj heq)
    · intro hnone
      obtain ⟨⟨s₀, t₀⟩, ⟨hs₀, ht₀, hsum⟩, _⟩ := hT (y + (smin : ℤ))
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs₀
      rcases hs₀ with ⟨s, hs, rfl⟩
      by_cases hseq : s = smin
      · subst hseq
        have : t₀ = y := by linarith
        rwa [← this]
      · exfalso
        have : t₀ = y + (smin : ℤ) - (s : ℤ) := by linarith
        exact hnone s hs hseq (this ▸ ht₀)
  have hbwd : ∀ y : ℤ, y ∈ T ↔ ∀ s ∈ S, s ≠ smax → y + (smax : ℤ) - (s : ℤ) ∉ T := by
    intro y
    constructor
    · intro hy s hs hne_s ht
      obtain ⟨⟨s₀, t₀⟩, _, huniq⟩ := hT (y + (smax : ℤ))
      have h1 := huniq ((smax : ℤ), y) ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hsmax_mem), hy, by ring⟩
      have h2 := huniq ((s : ℤ), y + (smax : ℤ) - (s : ℤ)) ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hs), ht, by ring⟩
      have heq : (s : ℤ) = (smax : ℤ) := congrArg Prod.fst (h2.trans h1.symm)
      exact hne_s (Int.ofNat.inj heq)
    · intro hnone
      obtain ⟨⟨s₀, t₀⟩, ⟨hs₀, ht₀, hsum⟩, _⟩ := hT (y + (smax : ℤ))
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs₀
      rcases hs₀ with ⟨s, hs, rfl⟩
      by_cases hseq : s = smax
      · subst hseq
        have : t₀ = y := by linarith
        rwa [← this]
      · exfalso
        have : t₀ = y + (smax : ℤ) - (s : ℤ) := by linarith
        exact hnone s hs hseq (this ▸ ht₀)
  classical
  let win : ℕ → (Fin D → Bool) := fun a i => decide ((a : ℤ) + (i.val : ℤ) ∈ T)
  obtain ⟨a, b, hab, hwin⟩ := Finite.exists_ne_map_eq_of_infinite win
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm hwin.symm (by omega)
  let M : ℕ := b - a
  have hM_pos : 0 < M := by omega
  have hwin_eq : ∀ i : ℕ, i < D → ((a : ℤ) + (i : ℤ) + (M : ℤ) ∈ T ↔ (a : ℤ) + (i : ℤ) ∈ T) := by
    intro i hi
    have h1 := congrFun hwin ⟨i, hi⟩
    simp only [win, decide_eq_decide] at h1
    have hba : (a : ℤ) + (i : ℤ) + (M : ℤ) = (b : ℤ) + (i : ℤ) := by
      dsimp only [M]; omega
    rw [hba]
    exact h1.symm
  have hfwd_all : ∀ n : ℕ, (a : ℤ) + (n : ℤ) + (M : ℤ) ∈ T ↔ (a : ℤ) + (n : ℤ) ∈ T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnD : n < D
      · exact hwin_eq n hnD
      · rw [hfwd ((a : ℤ) + (n : ℤ) + (M : ℤ)), hfwd ((a : ℤ) + (n : ℤ))]
        refine forall₂_congr fun s hs => forall_congr' fun hne_s => not_congr ?_
        have hs_gt : smin < s := lt_of_le_of_ne (hmin_le s hs) (Ne.symm hne_s)
        have hs_le : s ≤ smax := hle_max s hs
        set n' := n - (s - smin)
        have hn'_lt : n' < n := by omega
        have heq1 : (a : ℤ) + (n : ℤ) + (M : ℤ) + (smin : ℤ) - (s : ℤ) =
            (a : ℤ) + (n' : ℤ) + (M : ℤ) := by omega
        have heq2 : (a : ℤ) + (n : ℤ) + (smin : ℤ) - (s : ℤ) = (a : ℤ) + (n' : ℤ) := by omega
        rw [heq1, heq2]
        exact ih n' hn'_lt
  have hbwd_all : ∀ n : ℕ, (a : ℤ) - (n : ℤ) + (M : ℤ) ∈ T ↔ (a : ℤ) - (n : ℤ) ∈ T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn0 : n = 0
      · subst hn0; simpa using hfwd_all 0
      · rw [hbwd ((a : ℤ) - (n : ℤ) + (M : ℤ)), hbwd ((a : ℤ) - (n : ℤ))]
        refine forall₂_congr fun s hs => forall_congr' fun hne_s => not_congr ?_
        have hs_lt : s < smax := lt_of_le_of_ne (hle_max s hs) hne_s
        have hs_ge : smin ≤ s := hmin_le s hs
        by_cases hsign : n ≤ smax - s
        · set m := (smax - s) - n
          have heq1 : (a : ℤ) - (n : ℤ) + (M : ℤ) + (smax : ℤ) - (s : ℤ) =
              (a : ℤ) + (m : ℤ) + (M : ℤ) := by omega
          have heq2 : (a : ℤ) - (n : ℤ) + (smax : ℤ) - (s : ℤ) = (a : ℤ) + (m : ℤ) := by omega
          rw [heq1, heq2]
          exact hfwd_all m
        · set n' := n - (smax - s)
          have hn'_lt : n' < n := by omega
          have heq1 : (a : ℤ) - (n : ℤ) + (M : ℤ) + (smax : ℤ) - (s : ℤ) =
              (a : ℤ) - (n' : ℤ) + (M : ℤ) := by omega
          have heq2 : (a : ℤ) - (n : ℤ) + (smax : ℤ) - (s : ℤ) = (a : ℤ) - (n' : ℤ) := by omega
          rw [heq1, heq2]
          exact ih n' hn'_lt
  refine ⟨M, hM_pos, fun y => ?_⟩
  by_cases hy : (a : ℤ) ≤ y
  · set n := (y - (a : ℤ)).toNat
    have hy_eq : y = (a : ℤ) + (n : ℤ) := by omega
    rw [hy_eq]; exact hfwd_all n
  · set n := ((a : ℤ) - y).toNat
    have hy_eq : y = (a : ℤ) - (n : ℤ) := by omega
    rw [hy_eq]; exact hbwd_all n

/-- Divisibility by a monic integer polynomial transfers from `ℚ[X]` back to `ℤ[X]`. -/
private lemma int_dvd_of_rat_dvd_of_monic {Φ P : ℤ[X]} (hmon : Φ.Monic)
    (hdvd : Φ.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ)) :
    Φ ∣ P := by
  by_cases h1 : Φ = 1
  · subst h1; exact one_dvd P
  let R := P %ₘ Φ
  have hrem := Polynomial.modByMonic_add_div P Φ
  have hdeg : R.degree < Φ.degree := Polynomial.degree_modByMonic_lt P hmon
  have hR_dvd : Φ.map (Int.castRingHom ℚ) ∣ R.map (Int.castRingHom ℚ) := by
    have hmap := congrArg (Polynomial.map (Int.castRingHom ℚ)) hrem
    simp only [Polynomial.map_add, Polynomial.map_mul] at hmap
    have : R.map (Int.castRingHom ℚ) = P.map (Int.castRingHom ℚ) -
        Φ.map (Int.castRingHom ℚ) * (P /ₘ Φ).map (Int.castRingHom ℚ) := by
      dsimp only [R]; linear_combination hmap
    rw [this]
    exact dvd_sub hdvd (dvd_mul_right _ _)
  have hR_zero : R = 0 := by
    by_contra hRne
    have hRmap_ne : R.map (Int.castRingHom ℚ) ≠ 0 := by
      intro h0
      apply hRne
      ext i
      have := congrArg (fun f => f.coeff i) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, Int.cast_eq_zero] at this
      exact this
    have hdeg_le : (Φ.map (Int.castRingHom ℚ)).degree ≤ (R.map (Int.castRingHom ℚ)).degree :=
      Polynomial.degree_le_of_dvd hR_dvd hRmap_ne
    have hdeg_Phi : (Φ.map (Int.castRingHom ℚ)).degree = Φ.degree :=
      Polynomial.degree_map_eq_of_injective Int.cast_injective Φ
    have hdeg_R : (R.map (Int.castRingHom ℚ)).degree = R.degree :=
      Polynomial.degree_map_eq_of_injective Int.cast_injective R
    rw [hdeg_Phi, hdeg_R] at hdeg_le
    exact not_lt_of_ge hdeg_le hdeg
  rw [show P %ₘ Φ = 0 from hR_zero, zero_add] at hrem
  exact ⟨P /ₘ Φ, hrem.symm⟩

/-- Explicit geometric-sum formula `Φ_{p^k}(X) = ∑_{i < p} X^{i * p^{k-1}}` over any integral domain. -/
private lemma cyclotomic_prime_pow_eq_sum {R : Type*} [CommRing R] [IsDomain R]
    {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Polynomial.cyclotomic (p ^ k) R = ∑ i ∈ Finset.range p, (X : R[X]) ^ (i * p ^ (k - 1)) := by
  have hp_pos : 0 < p := hp.pos
  have hk1 : k = (k - 1) + 1 := by omega
  have hprod1 : ∏ d ∈ (p ^ k).divisors, Polynomial.cyclotomic d R = X ^ (p ^ k) - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one (pow_pos hp_pos k) R
  have hprod2 : ∏ d ∈ (p ^ (k - 1)).divisors, Polynomial.cyclotomic d R = X ^ (p ^ (k - 1)) - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one (pow_pos hp_pos (k - 1)) R
  have hdiv_eq : (p ^ k).divisors = insert (p ^ k) (p ^ (k - 1)).divisors := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, ne_eq, pow_eq_zero_iff', hp.ne_zero,
      false_and, not_false_eq_true, and_true]
    constructor
    · intro hd
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
      by_cases hjk : j = k
      · exact Or.inl (by rw [hjk])
      · exact Or.inr (Nat.pow_dvd_pow p (by omega))
    · rintro (rfl | hd)
      · exact dvd_refl _
      · exact dvd_trans hd (Nat.pow_dvd_pow p (by omega))
  have hnotmem : p ^ k ∉ (p ^ (k - 1)).divisors := by
    simp only [Nat.mem_divisors, not_and]
    intro hd _
    have hle := Nat.le_of_dvd (by positivity) hd
    have : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  rw [hdiv_eq, Finset.prod_insert hnotmem, hprod2] at hprod1
  have hfactor :
      (∑ i ∈ Finset.range p, (X : R[X]) ^ (i * p ^ (k - 1))) * (X ^ (p ^ (k - 1)) - 1) =
        X ^ (p ^ k) - 1 := by
    have hgeom := geom_sum_mul ((X : R[X]) ^ (p ^ (k - 1))) p
    have hsum_eq : ∑ i ∈ Finset.range p, ((X : R[X]) ^ (p ^ (k - 1))) ^ i =
        ∑ i ∈ Finset.range p, (X : R[X]) ^ (i * p ^ (k - 1)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, mul_comm]
    rw [hsum_eq, ← pow_mul, mul_comm (p ^ (k - 1)) p, ← pow_succ', ← hk1] at hgeom
    exact hgeom
  have hne : (X ^ (p ^ (k - 1)) - 1 : R[X]) ≠ 0 := by
    intro h0
    have hpow_ne : p ^ (k - 1) ≠ 0 := (pow_pos hp_pos (k - 1)).ne'
    have hev := congrArg (Polynomial.eval 0) h0
    simp [zero_pow hpow_ne] at hev
  exact mul_right_cancel₀ hne (hprod1.trans hfactor.symm)

private lemma eval_one_cyclotomic_prime_pow_domain {R : Type*} [CommRing R] [IsDomain R]
    {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (Polynomial.cyclotomic (p ^ k) R).eval 1 = (p : R) := by
  rw [cyclotomic_prime_pow_eq_sum hp hk, Polynomial.eval_finsetSum]
  simp

/-- `Φ_{2^j}(X) = X^{2^{j-1}} + 1` in `ℤ[X]` for every `j ≥ 1`. -/
private lemma cyclotomic_two_pow (j : ℕ) (hj : 1 ≤ j) :
    Polynomial.cyclotomic (2 ^ j) ℤ = X ^ (2 ^ (j - 1)) + 1 := by
  rw [cyclotomic_prime_pow_eq_sum Nat.prime_two hj, Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- Alternating coefficient sum along residue class `r < h` modulo `h` vanishes on every
multiple of `X^h + 1` in `ℤ[X]`. -/
private lemma alt_sum_mul_X_pow_add_one_eq_zero {h r : ℕ} (hr : r < h) (Q : ℤ[X])
    (N : ℕ) (hN : Q.natDegree + h < N * h) :
    ∑ m ∈ Finset.range N, ((-1 : ℤ) ^ m) * ((X ^ h + 1) * Q).coeff (m * h + r) = 0 := by
  have hcoeff : ∀ m : ℕ, ((X ^ h + 1) * Q).coeff (m * h + r) =
      (if m = 0 then 0 else Q.coeff ((m - 1) * h + r)) + Q.coeff (m * h + r) := by
    intro m
    rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
    by_cases hm : m = 0
    · subst hm
      simp only [zero_mul, zero_add, ↓reduceIte]
      rw [if_neg (by omega : ¬ h ≤ r), zero_add]
    · have hge : h ≤ m * h + r := by
        have : 1 ≤ m := by omega
        nlinarith
      rw [if_pos hge, if_neg hm]
      have hsub : m * h + r - h = (m - 1) * h + r := by
        cases m with
        | zero => exact absurd rfl hm
        | succ m' =>
          simp only [Nat.succ_mul, Nat.add_sub_cancel]
          omega
      rw [hsub]
  have htele : ∀ K : ℕ,
      ∑ m ∈ Finset.range K, ((-1 : ℤ) ^ m) * ((X ^ h + 1) * Q).coeff (m * h + r) =
        if K = 0 then 0 else ((-1 : ℤ) ^ (K - 1)) * Q.coeff ((K - 1) * h + r) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, hcoeff K]
      cases K with
      | zero => simp
      | succ K' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [pow_succ]
        ring
  rw [htele N]
  by_cases hN0 : N = 0
  · simp [hN0]
  · rw [if_neg hN0]
    have hmul_sub : (N - 1) * h + h = N * h := by
      cases N with
      | zero => exact absurd rfl hN0
      | succ N' => rw [Nat.add_sub_cancel, Nat.succ_mul]
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    · have hlt : Q.natDegree < (N - 1) * h + r := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

/-- Mask polynomial `S(X) = ∑_{s ∈ S} X^s ∈ ℤ[X]`. -/
private noncomputable def maskPoly (S : Finset ℕ) : ℤ[X] :=
  ∑ s ∈ S, (X : ℤ[X]) ^ s

private lemma maskPoly_coeff (S : Finset ℕ) (n : ℕ) :
    (maskPoly S).coeff n = if n ∈ S then 1 else 0 := by
  unfold maskPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  by_cases hn : n ∈ S
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b _ hbn; rw [if_neg (Ne.symm hbn)]
    · intro h; exact absurd hn h
  · rw [if_neg hn]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg (fun h : n = b => hn (h.symm ▸ hb))]

private lemma maskPoly_eval_one (S : Finset ℕ) :
    (maskPoly S).eval 1 = (S.card : ℤ) := by
  unfold maskPoly
  rw [Polynomial.eval_finsetSum]
  simp

/-- **Key Obstruction:** If `S ⊆ {2^c : c ∈ ℕ}` has `1 ∈ S` and `|S| ≥ 3`, then NO
`2`-power cyclotomic polynomial `Φ_{2^j}(X)` (`j ≥ 1`) divides `maskPoly S` in `ℤ[X]`. -/
private lemma not_cyclotomic_two_pow_dvd_maskPoly {S : Finset ℕ} (hpow : IsPow2Set S)
    (h1 : 1 ∈ S) (hcard : 3 ≤ S.card) (j : ℕ) (hj : 1 ≤ j) :
    ¬ (Polynomial.cyclotomic (2 ^ j) ℤ ∣ maskPoly S) := by
  rw [cyclotomic_two_pow j hj]
  rintro ⟨Q, hQ⟩
  let h : ℕ := 2 ^ (j - 1)
  have hh_pos : 0 < h := by positivity
  let M_max : ℕ := S.sup id
  let N : ℕ := max (Q.natDegree + h) (M_max + 1) + 1
  have hNh : Q.natDegree + h < N * h := by
    have h1le : 1 ≤ h := hh_pos
    have hNgt : Q.natDegree + h < N := Nat.lt_succ_of_le (le_max_left _ _)
    nlinarith
  have hNM : ∀ s ∈ S, s < N * h := by
    intro s hs
    have hsle : s ≤ M_max := Finset.le_sup (f := id) hs
    have h1le : 1 ≤ h := hh_pos
    have hNgt : M_max + 1 < N := Nat.lt_succ_of_le (le_max_right _ _)
    nlinarith
  by_cases hj1 : j = 1
  · subst hj1
    have hh1 : h = 1 := rfl
    have hzero := alt_sum_mul_X_pow_add_one_eq_zero (h := 1) (r := 0) (by decide) Q N (by omega)
    have hQ1 : maskPoly S = (X ^ 1 + 1) * Q := hQ
    rw [← hQ1] at hzero
    have hsum_eq : ∑ m ∈ Finset.range N, ((-1 : ℤ) ^ m) * (maskPoly S).coeff (m * 1 + 0) =
        ∑ s ∈ S, (-1 : ℤ) ^ s := by
      have hsub : S ⊆ Finset.range N := fun s hs => Finset.mem_range.mpr (by simpa [hh1] using hNM s hs)
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun m hm => ?_
        simp only [mul_one, add_zero, maskPoly_coeff, if_pos hm, mul_one]
      · intro m _ hm
        simp only [mul_one, add_zero, maskPoly_coeff, if_neg hm, mul_zero]
    rw [hsum_eq] at hzero
    rw [← Finset.add_sum_erase _ _ h1] at hzero
    have heven : ∀ s ∈ S.erase 1, (-1 : ℤ) ^ s = 1 := by
      intro s hs
      rw [Finset.mem_erase] at hs
      obtain ⟨c, rfl⟩ := hpow s hs.2
      have hc : 1 ≤ c := by
        cases c with
        | zero => exact absurd rfl hs.1
        | succ _ => omega
      have h2dvd : 2 ∣ 2 ^ c := dvd_pow_self 2 (by omega)
      exact Even.neg_one_pow (even_iff_two_dvd.mpr h2dvd)
    rw [Finset.sum_congr rfl heven, Finset.sum_const, nsmul_eq_mul, mul_one] at hzero
    have hcard_er : (S.erase 1).card = S.card - 1 := Finset.card_erase_of_mem h1
    omega
  · have hj2 : 2 ≤ j := by omega
    have hh_ge2 : 2 ≤ h := by
      dsimp only [h]
      have : 2 ^ 1 ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    have hh_even : 2 ∣ h := dvd_pow_self 2 (by omega)
    have hzero := alt_sum_mul_X_pow_add_one_eq_zero (h := h) (r := 1) (by omega) Q N (by omega)
    rw [← hQ] at hzero
    have hzero_tail : ∀ m ∈ Finset.range N, m ≠ 0 → (maskPoly S).coeff (m * h + 1) = 0 := by
      intro m _ hm
      rw [maskPoly_coeff, if_neg]
      intro hmem
      obtain ⟨c, hc⟩ := hpow (m * h + 1) hmem
      cases c with
      | zero =>
        simp only [pow_zero] at hc
        have : 1 ≤ m := by omega
        nlinarith
      | succ c' =>
        have h2l : 2 ∣ 2 ^ (c' + 1) := dvd_pow_self 2 (by omega)
        rw [← hc] at h2l
        have h2m : 2 ∣ m * h := dvd_mul_of_dvd_right hh_even m
        have h21 : 2 ∣ 1 := (Nat.dvd_add_right h2m).mp h2l
        omega
    have h0mem : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single 0] at hzero
    · simp only [pow_zero, zero_mul, zero_add, one_mul, maskPoly_coeff, if_pos h1] at hzero
      omega
    · intro m hm hm0
      rw [hzero_tail m hm hm0, mul_zero]
    · intro h0; exact absurd h0mem h0

private lemma minFac_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (p ^ k).minFac = p := by
  have hne1 : p ^ k ≠ 1 := by
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hmf_prime : (p ^ k).minFac.Prime := Nat.minFac_prime hne1
  have hmf_dvd : (p ^ k).minFac ∣ p ^ k := Nat.minFac_dvd (p ^ k)
  have hmf_dvd_p : (p ^ k).minFac ∣ p := hmf_prime.dvd_of_dvd_pow hmf_dvd
  exact (Nat.prime_dvd_prime_iff_eq hmf_prime hp).mp hmf_dvd_p

/-- Product of `p` over all prime powers `p^a` (`a ≥ 1`) dividing `M` equals `M`. -/
private lemma prod_primePow_divisors_eq (M : ℕ) (hM : 0 < M) :
    ∏ q ∈ M.divisors.filter IsPrimePow, q.minFac = M := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases hM1 : M = 1
    · subst hM1; simp [not_isPrimePow_one]
    · let p := M.minFac
      have hp : p.Prime := Nat.minFac_prime hM1
      let a := M.factorization p
      have ha_pos : 0 < a := hp.factorization_pos_of_dvd hM.ne' (Nat.minFac_dvd M)
      let M' := M / p ^ a
      have hpa_dvd : p ^ a ∣ M := Nat.ordProj_dvd M p
      have hM_eq : M = p ^ a * M' := (Nat.mul_div_cancel' hpa_dvd).symm
      have hM'_pos : 0 < M' := Nat.pos_of_mul_pos_left (hM_eq ▸ hM)
      have hcop : Nat.Coprime (p ^ a) M' := by
        have hndvd : ¬ p ∣ M' := by
          intro hpm'
          have h1 : p ^ (a + 1) ∣ M := by
            rw [hM_eq, pow_succ]
            exact mul_dvd_mul_left (p ^ a) hpm'
          have := (hp.pow_dvd_iff_le_factorization hM.ne').mp h1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hndvd).pow_left a
      have hM'_lt : M' < M := by
        have : 2 ≤ p ^ a := le_trans hp.two_le (Nat.le_self_pow ha_pos.ne' p)
        nlinarith
      let Pset : Finset ℕ := (Finset.Icc 1 a).image (fun j => p ^ j)
      let Qset : Finset ℕ := M'.divisors.filter IsPrimePow
      have hdisj : Disjoint Pset Qset := by
        rw [Finset.disjoint_left]
        intro q hqP hqQ
        rw [Finset.mem_image] at hqP
        rcases hqP with ⟨j, hj, rfl⟩
        rw [Finset.mem_Icc] at hj
        have hqdvd : p ^ j ∣ M' := (Nat.mem_divisors.mp (Finset.mem_filter.mp hqQ).1).1
        have hpdvd : p ∣ M' := dvd_trans (dvd_pow_self p (by omega)) hqdvd
        have hg : p ∣ Nat.gcd (p ^ a) M' := Nat.dvd_gcd (dvd_pow_self p ha_pos.ne') hpdvd
        rw [hcop.gcd_eq_one] at hg
        have := Nat.le_of_dvd (by decide) hg
        have := hp.two_le
        omega
      have hunion : M.divisors.filter IsPrimePow = Pset ∪ Qset := by
        ext q
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_union, Pset, Qset,
          Finset.mem_image, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hqM, _⟩, hpp⟩
          rcases hpp with ⟨r, k, hr, hk, rfl⟩
          have hrp : r.Prime := hr.nat_prime
          by_cases hr_eq : r = p
          · subst hr_eq
            left
            have hkle : k ≤ a := (hp.pow_dvd_iff_le_factorization hM.ne').mp hqM
            exact ⟨k, ⟨hk, hkle⟩, rfl⟩
          · right
            have hcop_rk : Nat.Coprime (r ^ k) (p ^ a) :=
              ((hrp.coprime_iff_not_dvd.mpr fun h => hr_eq ((Nat.prime_dvd_prime_iff_eq hrp hp).mp h)).pow_left k).pow_right a
            have hqM' : r ^ k ∣ M' := hcop_rk.dvd_of_dvd_mul_left (hM_eq ▸ hqM)
            exact ⟨⟨hqM', hM'_pos.ne'⟩, ⟨r, k, hr, hk, rfl⟩⟩
        · rintro (⟨j, ⟨hj1, hja⟩, rfl⟩ | ⟨⟨hqM', _⟩, hpp⟩)
          · refine ⟨⟨dvd_trans (Nat.pow_dvd_pow p hja) hpa_dvd, hM.ne'⟩, ?_⟩
            exact hp.isPrimePow.pow (by omega)
          · exact ⟨⟨dvd_trans hqM' (hM_eq ▸ dvd_mul_left M' (p ^ a)), hM.ne'⟩, hpp⟩
      rw [hunion, Finset.prod_union hdisj, ih M' hM'_lt hM'_pos]
      have hPprod : ∏ q ∈ Pset, q.minFac = p ^ a := by
        dsimp only [Pset]
        rw [Finset.prod_image (fun x _ y _ h => Nat.pow_right_injective hp.two_le h)]
        have hmf : ∀ j ∈ Finset.Icc 1 a, (p ^ j).minFac = p := fun j hj =>
          minFac_prime_pow hp (Finset.mem_Icc.mp hj).1
        rw [Finset.prod_congr rfl hmf, Finset.prod_const, Nat.card_Icc]
        simp
      rw [hPprod, ← hM_eq]

/-- **Coven–Meyerowitz (T1) for periodic tilings of `ℤ`:**
If a finite nonempty `S ⊆ ℕ` tiles `ℤ` periodically with period `M > 0`, then
`∏_{q ∈ Q_S} q.minFac = S.card`, where `Q_S = {q prime power ∣ M : Φ_q ∣ maskPoly S}`.
In particular, if `2 ∣ S.card`, some `Φ_{2^j}` (`j ≥ 1`) divides `maskPoly S` in `ℤ[X]`. -/
private lemma coven_meyerowitz_T1_even {S : Finset ℕ} (hne : S.Nonempty)
    (heven : 2 ∣ S.card)
    (htiles : Tiles (S.image (Nat.cast : ℕ → ℤ) : Set ℤ)) :
    ∃ j : ℕ, 1 ≤ j ∧ Polynomial.cyclotomic (2 ^ j) ℤ ∣ maskPoly S := by
  rcases htiles with ⟨T, hT⟩
  obtain ⟨M, hM_pos, hper⟩ := tiling_periodic hne T hT
  have hper_mul : ∀ (y : ℤ) (k : ℤ), y + k * (M : ℤ) ∈ T ↔ y ∈ T := by
    intro y k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have : y + ((n : ℤ) + 1) * (M : ℤ) = (y + (n : ℤ) * (M : ℤ)) + (M : ℤ) := by ring
      rw [this, hper, ih]
    | pred n ih =>
      have : y + (-(n : ℤ) - 1) * (M : ℤ) + (M : ℤ) = y + (-(n : ℤ)) * (M : ℤ) := by ring
      rw [← hper, this, ih]
  classical
  let A : Finset ℕ := (Finset.range M).filter (fun a => (a : ℤ) ∈ T)
  have hbij : ∀ r < M, ∃! p : ℕ × ℕ, p ∈ S ×ˢ A ∧ (p.1 + p.2) % M = r := by
    intro r hr
    obtain ⟨⟨sZ, tZ⟩, ⟨hsZ, htZ, hsum⟩, huniq⟩ := hT (r : ℤ)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hsZ
    rcases hsZ with ⟨s, hs, rfl⟩
    let a : ℕ := (tZ % (M : ℤ)).toNat
    have ha_lt : a < M := by
      have h1 : 0 ≤ tZ % (M : ℤ) := Int.emod_nonneg tZ (by omega)
      have h2 : tZ % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos tZ (by omega)
      omega
    have ha_eq : (a : ℤ) = tZ % (M : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg tZ (by omega))
    have ha_memT : (a : ℤ) ∈ T := by
      have hdiv : (a : ℤ) + (tZ / (M : ℤ)) * (M : ℤ) = tZ := by
        rw [ha_eq, mul_comm]; exact Int.emod_add_mul_ediv tZ (M : ℤ)
      rw [← hper_mul (a : ℤ) (tZ / (M : ℤ)), hdiv]
      exact htZ
    have ha_memA : a ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_memT⟩
    have hmod_r : (s + a) % M = r := by
      have hz : ((s : ℤ) + (a : ℤ)) % (M : ℤ) = (r : ℤ) := by
        rw [ha_eq]
        have h1 : ((s : ℤ) + tZ % (M : ℤ)) % (M : ℤ) = ((s : ℤ) + tZ) % (M : ℤ) := by
          simp [Int.add_emod]
        rw [h1, hsum, Int.emod_eq_of_lt (by omega) (by omega)]
      exact_mod_cast hz
    refine ⟨(s, a), ⟨Finset.mem_product.mpr ⟨hs, ha_memA⟩, hmod_r⟩, ?_⟩
    rintro ⟨s', a'⟩ ⟨hmem', hmod'⟩
    rw [Finset.mem_product] at hmem'
    rcases hmem' with ⟨hs', ha'⟩
    rw [Finset.mem_filter, Finset.mem_range] at ha'
    have hdivZ : (M : ℤ) ∣ ((r : ℤ) - ((s' : ℤ) + (a' : ℤ))) := by
      have hm2 : ((s' : ℤ) + (a' : ℤ)) % (M : ℤ) = (r : ℤ) := by exact_mod_cast hmod'
      exact Int.dvd_of_emod_eq_zero (by
        rw [Int.sub_emod, hm2, Int.emod_eq_of_lt (Int.natCast_nonneg r) (Int.ofNat_lt.mpr hr),
          sub_self, Int.zero_emod])
    rcases hdivZ with ⟨qZ, hqZ⟩
    have ht'_mem : (a' : ℤ) + qZ * (M : ℤ) ∈ T := (hper_mul (a' : ℤ) qZ).mpr ha'.2
    have hsum' : (s' : ℤ) + ((a' : ℤ) + qZ * (M : ℤ)) = (r : ℤ) := by linarith
    have heq_pair := huniq ((s' : ℤ), (a' : ℤ) + qZ * (M : ℤ))
      ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hs'), ht'_mem, hsum'⟩
    have hs'_eq : s' = s := Int.ofNat.inj (congrArg Prod.fst heq_pair)
    have ht'_eq : (a' : ℤ) + qZ * (M : ℤ) = tZ := congrArg Prod.snd heq_pair
    have ha'_eq : a' = a := by
      have h1 : ((a' : ℤ) + qZ * (M : ℤ)) % (M : ℤ) = (a' : ℤ) := by
        rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [ht'_eq] at h1
      omega
    exact Prod.ext hs'_eq ha'_eq
  have hcard_mul : S.card * A.card = M := by
    have h1 : (S ×ˢ A).card = (Finset.range M).card := by
      refine Finset.card_bij (fun p _ => (p.1 + p.2) % M) ?_ ?_ ?_
      · intro p _; exact Finset.mem_range.mpr (Nat.mod_lt _ hM_pos)
      · intro p₁ hp₁ p₂ hp₂ hEq
        obtain ⟨p₀, _, huniq⟩ := hbij ((p₁.1 + p₁.2) % M) (Nat.mod_lt _ hM_pos)
        exact (huniq p₁ ⟨hp₁, rfl⟩).trans (huniq p₂ ⟨hp₂, hEq.symm⟩).symm
      · intro r hr
        obtain ⟨p, ⟨hp, hmod⟩, _⟩ := hbij r (Finset.mem_range.mp hr)
        exact ⟨p, hp, hmod⟩
    simpa [Finset.card_product, Finset.card_range] using h1
  have hpoly_dvd : ((X : ℤ[X]) ^ M - 1) ∣ (maskPoly S * maskPoly A - ∑ r ∈ Finset.range M, (X : ℤ[X]) ^ r) := by
    have hsum_rem : ∑ p ∈ S ×ˢ A, (X : ℤ[X]) ^ ((p.1 + p.2) % M) =
        ∑ r ∈ Finset.range M, (X : ℤ[X]) ^ r := by
      refine Finset.sum_bij (fun p _ => (p.1 + p.2) % M) ?_ ?_ ?_ ?_
      · intro p _; exact Finset.mem_range.mpr (Nat.mod_lt _ hM_pos)
      · intro p₁ hp₁ p₂ hp₂ hEq
        obtain ⟨p₀, _, huniq⟩ := hbij ((p₁.1 + p₁.2) % M) (Nat.mod_lt _ hM_pos)
        exact (huniq p₁ ⟨hp₁, rfl⟩).trans (huniq p₂ ⟨hp₂, hEq.symm⟩).symm
      · intro r hr
        obtain ⟨p, ⟨hp, hmod⟩, _⟩ := hbij r (Finset.mem_range.mp hr)
        exact ⟨p, hp, hmod⟩
      · intro _ _; rfl
    have hprod_expand : maskPoly S * maskPoly A = ∑ p ∈ S ×ˢ A, (X : ℤ[X]) ^ (p.1 + p.2) := by
      unfold maskPoly
      rw [Finset.sum_mul, Finset.sum_product]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => (pow_add X s a).symm
    rw [hprod_expand, ← hsum_rem, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun p _ => ?_
    set n := p.1 + p.2
    have hdiv : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
    have hpow_dvd : ((X : ℤ[X]) ^ M - 1) ∣ (X : ℤ[X]) ^ (M * (n / M)) - 1 := by
      rw [pow_mul]
      exact sub_one_dvd_pow_sub_one ((X : ℤ[X]) ^ M) (n / M)
    have hrew : (X : ℤ[X]) ^ n - X ^ (n % M) = X ^ (n % M) * (X ^ (M * (n / M)) - 1) := by
      have h1 : (X : ℤ[X]) ^ n = X ^ (M * (n / M)) * X ^ (n % M) := by
        rw [← pow_add, ← hdiv]
      rw [h1]; ring
    rw [hrew]
    exact dvd_mul_of_dvd_right hpow_dvd _
  let PP : Finset ℕ := M.divisors.filter IsPrimePow
  have hcyc_dvd_either : ∀ q ∈ PP,
      Polynomial.cyclotomic q ℤ ∣ maskPoly S ∨ Polynomial.cyclotomic q ℤ ∣ maskPoly A := by
    intro q hq
    rw [Finset.mem_filter, Nat.mem_divisors] at hq
    rcases hq with ⟨⟨hqM, _⟩, hpp⟩
    have hq_pos : 0 < q := hpp.pos
    have hPhi_dvd_XM : Polynomial.cyclotomic q ℤ ∣ (X : ℤ[X]) ^ M - 1 :=
      Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ |>.trans
        (by
          rcases hqM with ⟨t, rfl⟩
          rw [pow_mul]
          exact sub_one_dvd_pow_sub_one ((X : ℤ[X]) ^ q) t)
    have hPhi_map : (Polynomial.cyclotomic q ℤ).map (Int.castRingHom ℚ) = Polynomial.cyclotomic q ℚ :=
      Polynomial.map_cyclotomic q (Int.castRingHom ℚ)
    have hirr : Irreducible (Polynomial.cyclotomic q ℚ) :=
      Polynomial.cyclotomic.irreducible_rat hq_pos
    have hPhi_dvd_sum : Polynomial.cyclotomic q ℚ ∣ ∑ r ∈ Finset.range M, (X : ℚ[X]) ^ r := by
      have hgeom : (X - 1 : ℚ[X]) * (∑ r ∈ Finset.range M, (X : ℚ[X]) ^ r) = X ^ M - 1 := by
        rw [mul_comm]; exact geom_sum_mul (X : ℚ[X]) M
      have h1 : Polynomial.cyclotomic q ℚ ∣ (X : ℚ[X]) ^ M - 1 := by
        rw [← hPhi_map]
        simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one] using
          Polynomial.map_dvd (Int.castRingHom ℚ) hPhi_dvd_XM
      rw [← hgeom] at h1
      rcases hirr.prime.dvd_or_dvd h1 with hX1 | hsum
      · exfalso
        rcases hX1 with ⟨U, hU⟩
        have hX1_ne : (X - 1 : ℚ[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
        have hPhi_ne : Polynomial.cyclotomic q ℚ ≠ 0 := (Polynomial.cyclotomic.monic q ℚ).ne_zero
        have hU_ne : U ≠ 0 := fun h0 => hX1_ne (by rw [hU, h0, mul_zero])
        have hdeg_eq : (X - 1 : ℚ[X]).natDegree =
            (Polynomial.cyclotomic q ℚ).natDegree + U.natDegree := by
          rw [hU, Polynomial.natDegree_mul hPhi_ne hU_ne]
        have hdeg_Phi : 1 ≤ (Polynomial.cyclotomic q ℚ).natDegree := by
          rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.mpr hq_pos
        have hdegX1 : (X - 1 : ℚ[X]).natDegree = 1 := by
          simpa using Polynomial.natDegree_X_sub_C (1 : ℚ)
        have hU_deg0 : U.natDegree = 0 := by omega
        have hU_C : U = C (U.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hU_deg0
        have hU0_ne : U.coeff 0 ≠ 0 := fun h0 => hU_ne (by rw [hU_C, h0, map_zero])
        have heval := congrArg (Polynomial.eval (1 : ℚ)) hU
        rw [hU_C] at heval
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, sub_self,
          Polynomial.eval_mul, Polynomial.eval_C] at heval
        have hPhi_zero : (Polynomial.cyclotomic q ℚ).eval 1 = 0 :=
          (mul_eq_zero.mp heval.symm).resolve_right hU0_ne
        rcases hpp with ⟨p, k, hp, hk, rfl⟩
        have hp_nat : p.Prime := hp.nat_prime
        rw [eval_one_cyclotomic_prime_pow_domain hp_nat hk] at hPhi_zero
        exact Nat.cast_ne_zero.mpr hp_nat.ne_zero hPhi_zero
      · exact hsum
    have hPhi_dvd_prod : Polynomial.cyclotomic q ℚ ∣
        (maskPoly S).map (Int.castRingHom ℚ) * (maskPoly A).map (Int.castRingHom ℚ) := by
      have hdiff : Polynomial.cyclotomic q ℚ ∣
          (maskPoly S).map (Int.castRingHom ℚ) * (maskPoly A).map (Int.castRingHom ℚ) -
            ∑ r ∈ Finset.range M, (X : ℚ[X]) ^ r := by
        have h1 := Polynomial.map_dvd (Int.castRingHom ℚ) (dvd_trans hPhi_dvd_XM hpoly_dvd)
        simpa [hPhi_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sum,
          Polynomial.map_pow, Polynomial.map_X] using h1
      have := dvd_add hdiff hPhi_dvd_sum
      simpa using this
    rcases hirr.prime.dvd_or_dvd hPhi_dvd_prod with hS | hA
    · left
      exact int_dvd_of_rat_dvd_of_monic (Polynomial.cyclotomic.monic q ℤ) (by rwa [hPhi_map])
    · right
      exact int_dvd_of_rat_dvd_of_monic (Polynomial.cyclotomic.monic q ℤ) (by rwa [hPhi_map])
  let QS : Finset ℕ := PP.filter (fun q => Polynomial.cyclotomic q ℤ ∣ maskPoly S)
  let QA : Finset ℕ := PP.filter (fun q => Polynomial.cyclotomic q ℤ ∣ maskPoly A)
  have hsqfree_XM : Squarefree ((X : ℚ[X]) ^ M - 1) := by
    have hsep : ((X : ℚ[X]) ^ M - C (1 : ℚ)).Separable :=
      Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hM_pos.ne') one_ne_zero
    simpa using hsep.squarefree
  have hcop_cyc : ∀ {q₁ q₂ : ℕ}, q₁ ∈ PP → q₂ ∈ PP → q₁ ≠ q₂ →
      IsCoprime (Polynomial.cyclotomic q₁ ℚ) (Polynomial.cyclotomic q₂ ℚ) := by
    intro q₁ q₂ hq₁ hq₂ hne
    have h1 : 0 < q₁ := (Finset.mem_filter.mp hq₁).2.pos
    have hd1 : q₁ ∈ M.divisors := (Finset.mem_filter.mp hq₁).1
    have hd2 : q₂ ∈ M.divisors := (Finset.mem_filter.mp hq₂).1
    have hirr1 := Polynomial.cyclotomic.irreducible_rat h1
    refine (hirr1.coprime_iff_not_dvd).mpr fun hdvd => ?_
    have hprod_div : Polynomial.cyclotomic q₁ ℚ * Polynomial.cyclotomic q₂ ℚ ∣ (X : ℚ[X]) ^ M - 1 := by
      rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hM_pos ℚ]
      have hsub : ({q₁, q₂} : Finset ℕ) ⊆ M.divisors := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hmul := Finset.prod_dvd_prod_of_subset {q₁, q₂} M.divisors (fun d => Polynomial.cyclotomic d ℚ) hsub
      rwa [Finset.prod_pair hne] at hmul
    have hsq_dvd : Polynomial.cyclotomic q₁ ℚ * Polynomial.cyclotomic q₁ ℚ ∣ (X : ℚ[X]) ^ M - 1 :=
      dvd_trans (mul_dvd_mul_left _ hdvd) hprod_div
    exact hirr1.not_isUnit (hsqfree_XM _ hsq_dvd)
  have hprod_dvd : ∀ (Q : Finset ℕ) (P : ℤ[X]), Q ⊆ PP →
      (∀ q ∈ Q, Polynomial.cyclotomic q ℤ ∣ P) →
      (∏ q ∈ Q, Polynomial.cyclotomic q ℤ) ∣ P := by
    intro Q P hQsub hQdvd
    have hmon : (∏ q ∈ Q, Polynomial.cyclotomic q ℤ).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun q _ => Polynomial.cyclotomic.monic q ℤ
    refine int_dvd_of_rat_dvd_of_monic hmon ?_
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_cyclotomic]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro q₁ hq₁ q₂ hq₂ hne
      exact hcop_cyc (hQsub hq₁) (hQsub hq₂) hne
    · intro q hq
      rw [← Polynomial.map_cyclotomic q (Int.castRingHom ℚ)]
      exact Polynomial.map_dvd (Int.castRingHom ℚ) (hQdvd q hq)
  have hPS_dvd : (∏ q ∈ QS, Polynomial.cyclotomic q ℤ) ∣ maskPoly S :=
    hprod_dvd QS (maskPoly S) (Finset.filter_subset _ _) fun q hq => (Finset.mem_filter.mp hq).2
  have hPA_dvd : (∏ q ∈ QA, Polynomial.cyclotomic q ℤ) ∣ maskPoly A :=
    hprod_dvd QA (maskPoly A) (Finset.filter_subset _ _) fun q hq => (Finset.mem_filter.mp hq).2
  have heval_pp : ∀ q ∈ PP, (Polynomial.cyclotomic q ℤ).eval 1 = (q.minFac : ℤ) := by
    intro q hq
    rcases (Finset.mem_filter.mp hq).2 with ⟨p, k, hp, hk, rfl⟩
    have hp_nat : p.Prime := hp.nat_prime
    rw [eval_one_cyclotomic_prime_pow_domain hp_nat hk, minFac_prime_pow hp_nat hk]
  have hS_dvd_nat : (∏ q ∈ QS, q.minFac) ∣ S.card := by
    have h1 := Polynomial.eval_dvd (x := (1 : ℤ)) hPS_dvd
    rw [Polynomial.eval_prod, maskPoly_eval_one] at h1
    have h2 : (∏ q ∈ QS, (Polynomial.cyclotomic q ℤ).eval 1) = ((∏ q ∈ QS, q.minFac : ℕ) : ℤ) := by
      push_cast
      exact Finset.prod_congr rfl fun q hq => heval_pp q (Finset.filter_subset _ _ hq)
    rw [h2] at h1
    exact Int.ofNat_dvd.mp h1
  have hA_dvd_nat : (∏ q ∈ QA, q.minFac) ∣ A.card := by
    have h1 := Polynomial.eval_dvd (x := (1 : ℤ)) hPA_dvd
    rw [Polynomial.eval_prod, maskPoly_eval_one] at h1
    have h2 : (∏ q ∈ QA, (Polynomial.cyclotomic q ℤ).eval 1) = ((∏ q ∈ QA, q.minFac : ℕ) : ℤ) := by
      push_cast
      exact Finset.prod_congr rfl fun q hq => heval_pp q (Finset.filter_subset _ _ hq)
    rw [h2] at h1
    exact Int.ofNat_dvd.mp h1
  have hM_dvd : M ∣ (∏ q ∈ QS, q.minFac) * (∏ q ∈ QA, q.minFac) := by
    rw [← prod_primePow_divisors_eq M hM_pos]
    have hcov : PP ⊆ QS ∪ QA := by
      intro q hq
      rw [Finset.mem_union]
      rcases hcyc_dvd_either q hq with hS | hA
      · exact Or.inl (Finset.mem_filter.mpr ⟨hq, hS⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hq, hA⟩)
    have h1 : (∏ q ∈ PP, q.minFac) ∣ (∏ q ∈ QS ∪ QA, q.minFac) :=
      Finset.prod_dvd_prod_of_subset PP (QS ∪ QA) _ hcov
    have h2 : (∏ q ∈ QS ∪ QA, q.minFac) ∣ (∏ q ∈ QS, q.minFac) * (∏ q ∈ QA, q.minFac) := by
      rw [← Finset.prod_union_inter]
      exact dvd_mul_right _ _
    exact dvd_trans h1 h2
  have hprodS_pos : 0 < ∏ q ∈ QS, q.minFac := Finset.prod_pos fun q _ => Nat.minFac_pos q
  have hprodA_pos : 0 < ∏ q ∈ QA, q.minFac := Finset.prod_pos fun q _ => Nat.minFac_pos q
  have hScard_pos : 0 < S.card := hne.card_pos
  have hAcard_pos : 0 < A.card := Nat.pos_of_mul_pos_left (hcard_mul.symm ▸ hM_pos)
  have hS_le : ∏ q ∈ QS, q.minFac ≤ S.card := Nat.le_of_dvd hScard_pos hS_dvd_nat
  have hA_le : ∏ q ∈ QA, q.minFac ≤ A.card := Nat.le_of_dvd hAcard_pos hA_dvd_nat
  have hM_le : M ≤ (∏ q ∈ QS, q.minFac) * (∏ q ∈ QA, q.minFac) :=
    Nat.le_of_dvd (mul_pos hprodS_pos hprodA_pos) hM_dvd
  have hprodS_eq : ∏ q ∈ QS, q.minFac = S.card := by nlinarith
  have h2dvd_prod : 2 ∣ ∏ q ∈ QS, q.minFac := hprodS_eq ▸ heven
  obtain ⟨q, hqQS, h2q⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h2dvd_prod
  have hqPP := (Finset.mem_filter.mp hqQS).1
  have hqS := (Finset.mem_filter.mp hqQS).2
  rcases (Finset.mem_filter.mp hqPP).2 with ⟨p, j, hp, hj, rfl⟩
  have hp_nat : p.Prime := hp.nat_prime
  rw [minFac_prime_pow hp_nat hj] at h2q
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp_nat).mp h2q).symm
  subst hp2
  exact ⟨j, hj, hqS⟩

/-- **Theorem 2b (No Even Size `k ≥ 4` Occurs):**
For every even `k ≥ 4`, NO `k`-element subset of `{2^j : j ∈ ℕ}` tiles `ℤ`. -/
theorem even_size_ge_four_no_power_of_two_tile {k : ℕ} (heven : Even k) (hk4 : 4 ≤ k)
    (S : Finset ℕ) (hcard : S.card = k) (hpow : IsPow2Set S) :
    ¬ Tiles (S.image (Nat.cast : ℕ → ℤ) : Set ℤ) := by
  intro htiles
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨S', hcard', hpow', h1', htiles'⟩ := normalize_pow2_tile hne hpow htiles
  have hne' : S'.Nonempty := Finset.card_pos.mp (by omega)
  have h2dvd : 2 ∣ S'.card := by
    rw [hcard', hcard]
    exact even_iff_two_dvd.mp heven
  obtain ⟨j, hj, hdvd⟩ := coven_meyerowitz_T1_even hne' h2dvd htiles'
  exact not_cyclotomic_two_pow_dvd_maskPoly hpow' h1' (by omega) j hj hdvd

/-! ### Part 4: Complete Size Spectrum (`k ∈ {1, 2}` or `k` odd) -/

/-- **Theorem 3 (Complete Size Spectrum for Power-of-2 Tiles of `ℤ`):**
For every `k : ℕ`, there exists a `k`-element subset of `{2^j : j ∈ ℕ}` that tiles `ℤ`
**if and only if** `k = 1 ∨ k = 2 ∨ Odd k`. -/
theorem power_of_two_tile_size_iff (k : ℕ) :
    (∃ S : Finset ℕ, S.card = k ∧ IsPow2Set S ∧ Tiles (S.image (Nat.cast : ℕ → ℤ) : Set ℤ)) ↔
      k = 1 ∨ k = 2 ∨ Odd k := by
  constructor
  · rintro ⟨S, hcard, hpow, htiles⟩
    by_cases hk0 : k = 0
    · exfalso
      subst hk0
      have hSempty : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hSempty
      rcases htiles with ⟨T, hT⟩
      obtain ⟨⟨s, _⟩, ⟨hs, _, _⟩, _⟩ := hT 0
      simp at hs
    · by_cases hodd : Odd k
      · exact Or.inr (Or.inr hodd)
      · have heven : Even k := Nat.not_odd_iff_even.mp hodd
        by_cases hk2 : k = 2
        · exact Or.inr (Or.inl hk2)
        · exfalso
          have hk4 : 4 ≤ k := by rcases heven with ⟨m, rfl⟩; omega
          exact even_size_ge_four_no_power_of_two_tile heven hk4 S hcard hpow htiles
  · rintro (rfl | rfl | hodd)
    · exact odd_size_power_of_two_tile_exists (by decide)
    · refine ⟨{1, 2}, by decide, ?_, {t : ℤ | t % 2 = 0}, fun z => ?_⟩
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · by_cases hze : z % 2 = 0
        · refine ⟨(2, z - 2), ?_, ?_⟩
          · simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
              Set.image_singleton, Nat.cast_one, Nat.cast_ofNat, Set.mem_insert_iff,
              Set.mem_singleton_iff, Set.mem_ofPred_eq]
            exact ⟨Or.inr trivial, by omega, by ring⟩
          · rintro ⟨s, t⟩ ⟨hs, ht, hsum⟩
            simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
              Set.image_singleton, Nat.cast_one, Nat.cast_ofNat, Set.mem_insert_iff,
              Set.mem_singleton_iff, Set.mem_ofPred_eq] at hs ht
            ext <;> dsimp only <;> omega
        · refine ⟨(1, z - 1), ?_, ?_⟩
          · simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
              Set.image_singleton, Nat.cast_one, Nat.cast_ofNat, Set.mem_insert_iff,
              Set.mem_singleton_iff, Set.mem_ofPred_eq]
            exact ⟨Or.inl trivial, by omega, by ring⟩
          · rintro ⟨s, t⟩ ⟨hs, ht, hsum⟩
            simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
              Set.image_singleton, Nat.cast_one, Nat.cast_ofNat, Set.mem_insert_iff,
              Set.mem_singleton_iff, Set.mem_ofPred_eq] at hs ht
            ext <;> dsimp only <;> omega
    · exact odd_size_power_of_two_tile_exists hodd

end BenjaminiKozmaTzalikTiles
