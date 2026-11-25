import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option maxRecDepth 20000

/-!
# Complete Resolution of Conjecture 7.4 of Gil–Liang–Odetola–Weiner (`arXiv:2609.01562v1`)

In *Points of maximal traffic on a grid with obstruction* (`arXiv:2609.01562v1`, Section 7,
Conjecture 7.4), Gil, Liang, Odetola, and Weiner define for `n ≥ 2` and `1 ≤ a < n / 2`:
- `D(n) = (1 / n) * (2n - 2).choose (n - 1)`
- `G(n, a) = ((n - 2a + 1) / (n - a)) * n.choose a * (n - 2).choose (a - 1)`
- `R_n(a) = G(n, a) / D(n)`

and conjecture that `R_n(a) < 1` for every `n ≥ 496` and every `1 ≤ a < n / 2` (so the
antidiagonal traffic anomaly disappears for all `n ≥ 496`).

We prove Conjecture 7.4 completely, using only standard axioms `[propext, Classical.choice, Quot.sound]`,
with zero `sorry` and zero `native_decide`:
1. Exact algebraic equivalence `R_paper n a = trafficRatio n a` and `trafficRatio n a < 1 ↔ trafficInequality n a`.
2. Sharpness at `n = 495, a = 240`: `1 < R_paper 495 240`.
3. Unimodality in `a` + certified incremental kernel recurrence covering all `496 ≤ n ≤ 799`.
4. Elementary analytic proof (zero Stirling, zero `π`) covering all `n ≥ 800`.
-/

namespace GilAntidiagonalTraffic

/-! ### Verbatim paper definitions and exact integer/rational equivalence -/

/-- The paper's denominator `D(n) = (1 / n) * choose(2n - 2, n - 1)`. -/
def D_paper (n : ℕ) : ℚ :=
  ((2 * n - 2).choose (n - 1) : ℚ) / (n : ℚ)

/-- The paper's numerator `G(n, a) = ((n - 2a + 1) / (n - a)) * choose(n, a) * choose(n - 2, a - 1)`. -/
def G_paper (n a : ℕ) : ℚ :=
  ((n - 2 * a + 1 : ℕ) : ℚ) / ((n - a : ℕ) : ℚ) * (n.choose a : ℚ) * ((n - 2).choose (a - 1) : ℚ)

/-- The paper's ratio `R_n(a) = G(n, a) / D(n)`. -/
def R_paper (n a : ℕ) : ℚ :=
  G_paper n a / D_paper n

/-- The numerator factor controlling the ratio in Conjecture 7.4. -/
def trafficF (n a : ℕ) : ℕ := a * (n - 2 * a + 1) * (n.choose a) ^ 2

/-- The exact integer form of `R_n(a) < 1`. -/
def trafficInequality (n a : ℕ) : Prop :=
  2 * (2 * n - 1) * a * (n - 2 * a + 1) * (n.choose a) ^ 2 <
    n * (n - 1) * (2 * n).choose n

/-- Simplified rational form of `R_n(a)`. -/
def trafficRatio (n a : ℕ) : ℚ :=
  ((2 * (2 * n - 1) * a * (n - 2 * a + 1) * (n.choose a) ^ 2 : ℕ) : ℚ) /
    ((n * (n - 1) * (2 * n).choose n : ℕ) : ℚ)

/-- Conjecture 7.4, in the exact integer form equivalent to `R_n(a) < 1`. -/
def conjecture74 : Prop :=
  ∀ n a : ℕ, 496 ≤ n → 1 ≤ a → 2 * a < n → trafficInequality n a

/-! ### Elementary binomial identities -/

private theorem choose_step_right (n k : ℕ) :
    (k + 1) * n.choose (k + 1) = (n - k) * n.choose k := by
  have := Nat.choose_succ_right_eq n k
  linarith

private theorem choose_step_top_succ (n k : ℕ) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  by_cases hk : k ≤ n
  · have h1 := choose_step_right n k
    rw [Nat.choose_succ_succ, mul_add, h1]
    have : (k + 1) + (n - k) = n + 1 := by omega
    calc
      (k + 1) * n.choose k + (n - k) * n.choose k
          = ((k + 1) + (n - k)) * n.choose k := by ring
      _ = (n + 1) * n.choose k := by rw [this]
  · have hlt1 : n < k := by omega
    have hlt2 : n + 1 < k + 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hlt1, Nat.choose_eq_zero_of_lt hlt2, mul_zero, mul_zero]

private theorem choose_step_top_same (n k : ℕ) (hk : k ≤ n) :
    (n + 1 - k) * (n + 1).choose k = (n + 1) * n.choose k := by
  have h1 := choose_step_top_succ n (n - k)
  have hsub : n - k + 1 = n + 1 - k := by omega
  rw [hsub] at h1
  rw [Nat.choose_symm hk] at h1
  have hk1 : k ≤ n + 1 := by omega
  rw [Nat.choose_symm hk1] at h1
  exact h1

private theorem central_step_odd (m : ℕ) :
    (m + 1) * (2 * m + 1).choose m = (2 * m + 1) * (2 * m).choose m := by
  have h := choose_step_top_same (2 * m) m (by omega)
  have hsub : 2 * m + 1 - m = m + 1 := by omega
  rw [hsub] at h
  exact h

private theorem central_step_even (m : ℕ) :
    (m + 1) * (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
  have h1 := choose_step_top_succ (2 * m + 1) m
  have h2 := central_step_odd m
  have hmul : (m + 1) * ((m + 1) * (2 * m + 2).choose (m + 1)) =
      (m + 1) * (2 * (2 * m + 1) * (2 * m).choose m) := by
    calc
      (m + 1) * ((m + 1) * (2 * m + 2).choose (m + 1))
          = (m + 1) * ((2 * m + 2) * (2 * m + 1).choose m) := by rw [h1]
      _ = 2 * (m + 1) * ((m + 1) * (2 * m + 1).choose m) := by ring
      _ = 2 * (m + 1) * ((2 * m + 1) * (2 * m).choose m) := by rw [h2]
      _ = (m + 1) * (2 * (2 * m + 1) * (2 * m).choose m) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) hmul

private theorem central_double_step_odd (m : ℕ) :
    (2 * m + 1) * (4 * m + 2).choose (2 * m + 1) = 2 * (4 * m + 1) * (4 * m).choose (2 * m) := by
  have h := central_step_even (2 * m)
  have h1 : 2 * (2 * m) + 2 = 4 * m + 2 := by omega
  have h2 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h3 : 2 * (2 * m) = 4 * m := by omega
  rw [h1, h2, h3] at h
  exact h

private theorem central_double_step_even (m : ℕ) :
    (m + 1) * (2 * m + 1) * (4 * m + 4).choose (2 * m + 2) =
      2 * (4 * m + 3) * (4 * m + 1) * (4 * m).choose (2 * m) := by
  have h1 := central_step_even (2 * m + 1)
  have h2 := central_double_step_odd m
  have heq1 : 2 * (2 * m + 1) + 2 = 4 * m + 4 := by omega
  have heq2 : 2 * (2 * m + 1) + 1 = 4 * m + 3 := by omega
  have heq3 : 2 * (2 * m + 1) = 4 * m + 2 := by omega
  rw [heq1, heq2, heq3] at h1
  have hmul : 2 * ((m + 1) * (2 * m + 1) * (4 * m + 4).choose (2 * m + 2)) =
      2 * (2 * (4 * m + 3) * (4 * m + 1) * (4 * m).choose (2 * m)) := by
    calc
      2 * ((m + 1) * (2 * m + 1) * (4 * m + 4).choose (2 * m + 2))
          = (2 * m + 1) * ((2 * m + 1 + 1) * (4 * m + 4).choose (2 * m + 2)) := by ring
      _ = (2 * m + 1) * (2 * (4 * m + 3) * (4 * m + 2).choose (2 * m + 1)) := by rw [h1]
      _ = 2 * (4 * m + 3) * ((2 * m + 1) * (4 * m + 2).choose (2 * m + 1)) := by ring
      _ = 2 * (4 * m + 3) * (2 * (4 * m + 1) * (4 * m).choose (2 * m)) := by rw [h2]
      _ = 2 * (2 * (4 * m + 3) * (4 * m + 1) * (4 * m).choose (2 * m)) := by ring
  omega

private theorem paper_absorb_G (n a : ℕ) (hn : 2 ≤ n) (ha : 1 ≤ a) (hna : a < n) :
    n * (n - 1) * (n - 2).choose (a - 1) = a * (n - a) * n.choose a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hbm : b ≤ m := by omega
  have h1 := choose_step_top_succ (m + 1) b
  have h2 := choose_step_top_same m b hbm
  have hsub1 : m + 2 - 1 = m + 1 := by omega
  have hsub2 : m + 2 - 2 = m := by omega
  have hsub3 : b + 1 - 1 = b := by omega
  have hsub4 : m + 2 - (b + 1) = m + 1 - b := by omega
  rw [hsub1, hsub2, hsub3, hsub4]
  calc
    (m + 2) * (m + 1) * m.choose b
        = (m + 2) * ((m + 1) * m.choose b) := by ring
    _ = (m + 2) * ((m + 1 - b) * (m + 1).choose b) := by rw [h2]
    _ = (m + 1 - b) * ((m + 2) * (m + 1).choose b) := by ring
    _ = (m + 1 - b) * ((b + 1) * (m + 2).choose (b + 1)) := by rw [h1]
    _ = (b + 1) * (m + 1 - b) * (m + 2).choose (b + 1) := by ring

private theorem paper_absorb_D (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (2 * n - 2).choose (n - 1) = n * (2 * n).choose n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := central_step_even m
  have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have h3 : m + 1 - 1 = m := by omega
  have h4 : 2 * (m + 1) = 2 * m + 2 := by omega
  rw [h1, h2, h3, h4]
  exact h.symm

/-- Lemma 1: The paper's ratio `R_paper n a = G_paper n a / D_paper n` equals `trafficRatio n a`. -/
theorem R_paper_eq_trafficRatio (n a : ℕ) (hn : 2 ≤ n) (ha : 1 ≤ a) (hna : 2 * a < n) :
    R_paper n a = trafficRatio n a := by
  have hG_nat := paper_absorb_G n a hn ha (by omega)
  have hD_nat := paper_absorb_D n (by omega)
  have hG : ((n : ℚ) * ((n - 1 : ℕ) : ℚ) * ((n - 2).choose (a - 1) : ℚ)) =
      (a : ℚ) * ((n - a : ℕ) : ℚ) * (n.choose a : ℚ) := by exact_mod_cast hG_nat
  have hD : (2 * ((2 * n - 1 : ℕ) : ℚ) * ((2 * n - 2).choose (n - 1) : ℚ)) =
      (n : ℚ) * ((2 * n).choose n : ℚ) := by exact_mod_cast hD_nat
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn1 : ((n - 1 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < n - 1 := by omega
    positivity
  have hna0 : ((n - a : ℕ) : ℚ) ≠ 0 := by
    have : 0 < n - a := by omega
    positivity
  have h2n1 : ((2 * n - 1 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < 2 * n - 1 := by omega
    positivity
  have hc2n : ((2 * n).choose n : ℚ) ≠ 0 := by
    have : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
    positivity
  have hG_eq : ((n - 2).choose (a - 1) : ℚ) =
      (a : ℚ) * ((n - a : ℕ) : ℚ) * (n.choose a : ℚ) / ((n : ℚ) * ((n - 1 : ℕ) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero hn0 hn1)]
    linarith
  have hD_eq : ((2 * n - 2).choose (n - 1) : ℚ) =
      (n : ℚ) * ((2 * n).choose n : ℚ) / (2 * ((2 * n - 1 : ℕ) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by norm_num) h2n1)]
    linarith
  simp only [R_paper, G_paper, D_paper, trafficRatio]
  rw [hG_eq, hD_eq]
  push_cast
  field_simp [hn0, hn1, hna0, h2n1, hc2n]

theorem trafficRatio_lt_one_iff (n a : ℕ) (hn : 2 ≤ n) :
    trafficRatio n a < 1 ↔ trafficInequality n a := by
  have hden : 0 < n * (n - 1) * (2 * n).choose n := by
    have hc : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hc
  simp only [trafficRatio, trafficInequality]
  rw [div_lt_one (by exact_mod_cast hden)]
  norm_cast

/-- Rational and integer formulations of the conjecture agree on its domain. -/
theorem conjecture74_iff_rational :
    conjecture74 ↔
      ∀ n a : ℕ, 496 ≤ n → 1 ≤ a → 2 * a < n → trafficRatio n a < 1 := by
  constructor
  · intro h n a hn ha hna
    exact (trafficRatio_lt_one_iff n a (by omega)).2 (h n a hn ha hna)
  · intro h n a hn ha hna
    exact (trafficRatio_lt_one_iff n a (by omega)).1 (h n a hn ha hna)

/-- Sharpness witness immediately below `496`: `¬ trafficInequality 495 240`. -/
theorem sharpness_495_240 : ¬ trafficInequality 495 240 := by
  norm_num [trafficInequality, Nat.choose_eq_descFactorial_div_factorial]

/-- Sharpness in terms of the paper's ratio: `1 < R_paper 495 240`. -/
theorem sharpness_R_paper_495_240 : 1 < R_paper 495 240 := by
  rw [R_paper_eq_trafficRatio 495 240 (by omega) (by omega) (by omega)]
  norm_num [trafficRatio, Nat.choose_eq_descFactorial_div_factorial]

/-! ### Part I: Unimodality in `a` and certified finite check for `496 ≤ n ≤ 799` -/

/-- Decidable step condition equivalent to `trafficF n (a + 1) ≤ trafficF n a`. -/
def stepLe (n a : ℕ) : Prop :=
  (n - 2 * a - 1) * (n - a) ^ 2 ≤ a * (a + 1) * (n - 2 * a + 1)

/-- Decidable step condition equivalent to `trafficF n a ≤ trafficF n (a + 1)`. -/
def stepGe (n a : ℕ) : Prop :=
  a * (a + 1) * (n - 2 * a + 1) ≤ (n - 2 * a - 1) * (n - a) ^ 2

instance (n a : ℕ) : Decidable (stepLe n a) := inferInstanceAs (Decidable (_ ≤ _))
instance (n a : ℕ) : Decidable (stepGe n a) := inferInstanceAs (Decidable (_ ≤ _))

private theorem trafficF_step_eq (n a : ℕ) (hna : 2 * (a + 1) < n) :
    (a + 1) * trafficF n (a + 1) = (n - 2 * a - 1) * (n - a) ^ 2 * (n.choose a) ^ 2 ∧
    (a + 1) * trafficF n a = a * (a + 1) * (n - 2 * a + 1) * (n.choose a) ^ 2 := by
  have hch := choose_step_right n a
  have hsub : n - 2 * (a + 1) + 1 = n - 2 * a - 1 := by omega
  constructor
  · simp only [trafficF, hsub]
    calc
      (a + 1) * ((a + 1) * (n - 2 * a - 1) * (n.choose (a + 1)) ^ 2)
          = (n - 2 * a - 1) * ((a + 1) * n.choose (a + 1)) ^ 2 := by ring
      _ = (n - 2 * a - 1) * ((n - a) * n.choose a) ^ 2 := by rw [hch]
      _ = (n - 2 * a - 1) * (n - a) ^ 2 * (n.choose a) ^ 2 := by ring
  · simp only [trafficF]
    ring

private theorem trafficF_succ_le_of_stepLe {n a : ℕ} (hna : 2 * (a + 1) < n)
    (h : stepLe n a) : trafficF n (a + 1) ≤ trafficF n a := by
  have ⟨h1, h2⟩ := trafficF_step_eq n a hna
  have hmul : (a + 1) * trafficF n (a + 1) ≤ (a + 1) * trafficF n a := by
    rw [h1, h2]
    exact Nat.mul_le_mul_right ((n.choose a) ^ 2) h
  exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos a)

private theorem trafficF_le_succ_of_stepGe {n a : ℕ} (hna : 2 * (a + 1) < n)
    (h : stepGe n a) : trafficF n a ≤ trafficF n (a + 1) := by
  have ⟨h1, h2⟩ := trafficF_step_eq n a hna
  have hmul : (a + 1) * trafficF n a ≤ (a + 1) * trafficF n (a + 1) := by
    rw [h1, h2]
    exact Nat.mul_le_mul_right ((n.choose a) ^ 2) h
  exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos a)

private theorem stepLe_succ {n a : ℕ} (hna : 2 * (a + 2) < n) (h : stepLe n a) :
    stepLe n (a + 1) := by
  unfold stepLe at h ⊢
  set d : ℕ := n - 2 * a
  have hd : 5 ≤ d := by omega
  have hs1 : n - 2 * a - 1 = d - 1 := by omega
  have hs2 : n - 2 * a + 1 = d + 1 := by omega
  have hs3 : n - 2 * (a + 1) - 1 = d - 3 := by omega
  have hs4 : n - 2 * (a + 1) + 1 = d - 1 := by omega
  rw [hs1, hs2] at h
  rw [hs3, hs4]
  have hsq : (d - 3) * (d + 1) ≤ (d - 1) * (d - 1) := by
    zify [show 3 ≤ d by omega, show 1 ≤ d by omega]
    nlinarith
  have hmul : (d - 1) * ((d - 3) * (n - a) ^ 2) ≤ (d - 1) * (a * (a + 1) * (d - 1)) := by
    calc
      (d - 1) * ((d - 3) * (n - a) ^ 2)
          = (d - 3) * ((d - 1) * (n - a) ^ 2) := by ring
      _ ≤ (d - 3) * (a * (a + 1) * (d + 1)) := Nat.mul_le_mul_left (d - 3) h
      _ = a * (a + 1) * ((d - 3) * (d + 1)) := by ring
      _ ≤ a * (a + 1) * ((d - 1) * (d - 1)) := Nat.mul_le_mul_left _ hsq
      _ = (d - 1) * (a * (a + 1) * (d - 1)) := by ring
  have hmid : (d - 3) * (n - a) ^ 2 ≤ a * (a + 1) * (d - 1) :=
    Nat.le_of_mul_le_mul_left hmul (by omega)
  have hna_le : (n - (a + 1)) ^ 2 ≤ (n - a) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have ha_le : a * (a + 1) ≤ (a + 1) * (a + 2) := by nlinarith
  calc
    (d - 3) * (n - (a + 1)) ^ 2 ≤ (d - 3) * (n - a) ^ 2 := Nat.mul_le_mul_left _ hna_le
    _ ≤ a * (a + 1) * (d - 1) := hmid
    _ ≤ (a + 1) * (a + 2) * (d - 1) := Nat.mul_le_mul_right _ ha_le

private theorem stepGe_pred {n a : ℕ} (hna : 2 * (a + 2) < n) (h : stepGe n (a + 1)) :
    stepGe n a := by
  unfold stepGe at h ⊢
  set d : ℕ := n - 2 * a
  have hd : 5 ≤ d := by omega
  have hs1 : n - 2 * a - 1 = d - 1 := by omega
  have hs2 : n - 2 * a + 1 = d + 1 := by omega
  have hs3 : n - 2 * (a + 1) - 1 = d - 3 := by omega
  have hs4 : n - 2 * (a + 1) + 1 = d - 1 := by omega
  rw [hs3, hs4] at h
  rw [hs1, hs2]
  have hsq : (d - 3) * (d + 1) ≤ (d - 1) * (d - 1) := by
    zify [show 3 ≤ d by omega, show 1 ≤ d by omega]
    nlinarith
  have hna_le : (n - (a + 1)) ^ 2 ≤ (n - a) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have ha_le : a * (a + 1) ≤ (a + 1) * (a + 2) := by nlinarith
  have hmid : a * (a + 1) * (d - 1) ≤ (d - 3) * (n - a) ^ 2 := by
    calc
      a * (a + 1) * (d - 1) ≤ (a + 1) * (a + 2) * (d - 1) := Nat.mul_le_mul_right _ ha_le
      _ ≤ (d - 3) * (n - (a + 1)) ^ 2 := h
      _ ≤ (d - 3) * (n - a) ^ 2 := Nat.mul_le_mul_left _ hna_le
  have hmul : (d - 1) * (a * (a + 1) * (d + 1)) ≤ (d - 1) * ((d - 1) * (n - a) ^ 2) := by
    calc
      (d - 1) * (a * (a + 1) * (d + 1))
          = (d + 1) * (a * (a + 1) * (d - 1)) := by ring
      _ ≤ (d + 1) * ((d - 3) * (n - a) ^ 2) := Nat.mul_le_mul_left _ hmid
      _ = ((d - 3) * (d + 1)) * (n - a) ^ 2 := by ring
      _ ≤ ((d - 1) * (d - 1)) * (n - a) ^ 2 := Nat.mul_le_mul_right _ hsq
      _ = (d - 1) * ((d - 1) * (n - a) ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

private theorem trafficF_le_of_ge_peak {n p a : ℕ} (hpa : p ≤ a) (hna : 2 * a < n)
    (hp : 2 * (p + 1) < n → stepLe n p) : trafficF n a ≤ trafficF n p := by
  induction a, hpa using Nat.le_induction with
  | base => exact le_rfl
  | succ k hpk ih =>
    have hstep : stepLe n k := by
      clear ih
      induction k, hpk using Nat.le_induction with
      | base => exact hp hna
      | succ j hpj ihj => exact stepLe_succ (by omega) (ihj (by omega))
    exact (trafficF_succ_le_of_stepLe hna hstep).trans (ih (by omega))

private theorem stepGe_of_le (n a b : ℕ) (hab : a ≤ b) (hnb : 2 * (b + 1) < n)
    (hb : stepGe n b) : stepGe n a := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d generalizing a with
  | zero => simpa using hb
  | succ d ih =>
    have h1 : stepGe n (a + 1) := by
      have heq : a + 1 + d = a + (d + 1) := by omega
      exact ih (a + 1) (by omega) (by omega) (by rw [heq]; exact hb)
    exact stepGe_pred (by omega) h1

private theorem trafficF_le_of_le_peak (n p a : ℕ) (ha : 1 ≤ a) (hap : a ≤ p) (hnp : 2 * p < n)
    (hp : 2 ≤ p → stepGe n (p - 1)) : trafficF n a ≤ trafficF n p := by
  obtain ⟨d, rfl⟩ : ∃ d, p = a + d := ⟨p - a, by omega⟩
  induction d generalizing a with
  | zero => simp
  | succ d ih =>
    have htop : stepGe n (a + d) := by
      have h2 : 2 ≤ a + (d + 1) := by omega
      have hsub : a + (d + 1) - 1 = a + d := by omega
      simpa [hsub] using hp h2
    have hstep : stepGe n a := stepGe_of_le n a (a + d) (by omega) (by omega) htop
    have hnext : trafficF n (a + 1) ≤ trafficF n (a + (d + 1)) := by
      have heq : a + 1 + d = a + (d + 1) := by omega
      rw [← heq]
      exact ih (a + 1) (by omega) (by omega) (by rw [heq]; exact hnp) (by rw [heq]; exact hp)
    exact (trafficF_le_succ_of_stepGe (by omega) hstep).trans hnext

private theorem trafficInequality_of_peak {n p : ℕ} (hnp : 2 * p < n)
    (hL : 2 ≤ p → stepGe n (p - 1)) (hR : 2 * (p + 1) < n → stepLe n p)
    (hpeak : trafficInequality n p) :
    ∀ a, 1 ≤ a → 2 * a < n → trafficInequality n a := by
  intro a ha hna
  have hFle : trafficF n a ≤ trafficF n p := by
    rcases le_total a p with hap | hpa
    · exact trafficF_le_of_le_peak n p a ha hap hnp hL
    · exact trafficF_le_of_ge_peak hpa hna hR
  unfold trafficInequality at hpeak ⊢
  have h1 : 2 * (2 * n - 1) * a * (n - 2 * a + 1) * (n.choose a) ^ 2 =
      2 * (2 * n - 1) * trafficF n a := by unfold trafficF; ring
  have h2 : 2 * (2 * n - 1) * p * (n - 2 * p + 1) * (n.choose p) ^ 2 =
      2 * (2 * n - 1) * trafficF n p := by unfold trafficF; ring
  rw [h1]
  rw [h2] at hpeak
  exact (Nat.mul_le_mul_left (2 * (2 * n - 1)) hFle).trans_lt hpeak

/-- Fast primitive Boolean version of `stepLe` (avoids `Decidable` / `HPow` overhead in kernel reduction). -/
def stepLeB (n a : ℕ) : Bool :=
  let na := n - a
  Nat.ble ((n - 2 * a - 1) * (na * na)) (a * (a + 1) * (n - 2 * a + 1))

/-- Fast primitive Boolean version of `stepGe`. -/
def stepGeB (n a : ℕ) : Bool :=
  let na := n - a
  Nat.ble (a * (a + 1) * (n - 2 * a + 1)) ((n - 2 * a - 1) * (na * na))

private theorem stepLeB_eq_true_iff (n a : ℕ) : stepLeB n a = true ↔ stepLe n a := by
  simp only [stepLeB, stepLe, Nat.ble_eq, sq]

private theorem stepGeB_eq_true_iff (n a : ℕ) : stepGeB n a = true ↔ stepGe n a := by
  simp only [stepGeB, stepGe, Nat.ble_eq, sq]

/-- Certified incremental kernel checker for `trafficInequality` on `[n, n + k)`. -/
def checkRange : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, n, a, cna, c2nn =>
      let okBounds := Nat.ble 1 a && Nat.blt (2 * a) n
      let okL := !(Nat.ble 2 a) || stepGeB n (a - 1)
      let okR := !(Nat.blt (2 * (a + 1)) n) || stepLeB n a
      let okIneq := Nat.blt (2 * (2 * n - 1) * a * (n - 2 * a + 1) * (cna * cna)) (n * (n - 1) * c2nn)
      let n' := n + 1
      let c2nn' := (c2nn * 2 * (2 * n + 1)) / (n + 1)
      let moveUp := Nat.blt (2 * (a + 1)) n' && !(stepLeB n' a)
      let a' := if moveUp then a + 1 else a
      let cna' := if moveUp then (cna * (n + 1)) / (a + 1) else (cna * (n + 1)) / (n + 1 - a)
      okBounds && okL && okR && okIneq && checkRange k n' a' cna' c2nn'

private theorem checkRange_sound :
    ∀ k n a cna c2nn,
      cna = n.choose a →
      c2nn = (2 * n).choose n →
      checkRange k n a cna c2nn = true →
      ∀ m, n ≤ m → m < n + k → ∀ b, 1 ≤ b → 2 * b < m → trafficInequality m b := by
  intro k
  induction k with
  | zero =>
    intro n a cna c2nn _ _ _ m hnm hlt
    omega
  | succ k ih =>
    intro n a cna c2nn hcna hc2nn hchk m hnm hlt b hb hmb
    simp only [checkRange, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Nat.ble_eq, Nat.blt_eq, Bool.eq_false_iff] at hchk
    obtain ⟨⟨⟨⟨⟨ha1, hna⟩, hL0⟩, hR0⟩, hineq⟩, hrest⟩ := hchk
    have hL : 2 ≤ a → stepGe n (a - 1) := by
      intro h2
      rcases hL0 with hno | hyes
      · exact absurd (Nat.ble_eq.mpr h2) hno
      · exact (stepGeB_eq_true_iff n (a - 1)).mp hyes
    have hR : 2 * (a + 1) < n → stepLe n a := by
      intro hlt2
      rcases hR0 with hno | hyes
      · exact absurd (Nat.blt_eq.mpr hlt2) hno
      · exact (stepLeB_eq_true_iff n a).mp hyes
    rcases eq_or_lt_of_le hnm with rfl | hgt
    · rw [hcna, hc2nn, ← sq] at hineq
      exact trafficInequality_of_peak hna hL hR hineq b hb hmb
    · have hc2nn' : (c2nn * 2 * (2 * n + 1)) / (n + 1) = (2 * (n + 1)).choose (n + 1) := by
        rw [hc2nn]
        have h := central_step_even n
        have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [h2]
        have hmul : (2 * n).choose n * 2 * (2 * n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := by
          linarith
        rw [hmul, Nat.mul_div_cancel _ (Nat.succ_pos n)]
      split_ifs at hrest
      · have hcna' : (cna * (n + 1)) / (a + 1) = (n + 1).choose (a + 1) := by
          rw [hcna]
          have h := choose_step_top_succ n a
          have hmul : n.choose a * (n + 1) = (n + 1).choose (a + 1) * (a + 1) := by linarith
          rw [hmul, Nat.mul_div_cancel _ (Nat.succ_pos a)]
        exact ih (n + 1) (a + 1) _ _ hcna' hc2nn' hrest m (by omega) (by omega) b hb hmb
      · have hcna' : (cna * (n + 1)) / (n + 1 - a) = (n + 1).choose a := by
          rw [hcna]
          have h := choose_step_top_same n a (by omega)
          have hmul : n.choose a * (n + 1) = (n + 1).choose a * (n + 1 - a) := by linarith
          rw [hmul, Nat.mul_div_cancel _ (by omega)]
        exact ih (n + 1) a _ _ hcna' hc2nn' hrest m (by omega) (by omega) b hb hmb

private def c496_val : ℕ :=
  5662243041988935509026628692733817300862954292122413524657941858240522712264688442022458627732727933598364386111203757050143668845400929519806199427

private def c992_val : ℕ :=
  1060060067382756316424861696906071639868410380648024020270959555048347723565611575606573627198464645296816394131541244771661364550317779351650431375072199477983616735556152693409557806152064364380299929750807339795143305361442863857964712798807170223368505718348980891060898373654627944063232428000

private theorem c496_eq : c496_val = (496).choose 240 := by
  norm_num [c496_val, Nat.choose_eq_descFactorial_div_factorial]

private theorem c992_eq : c992_val = (2 * 496).choose 496 := by
  norm_num [c992_val, Nat.choose_eq_descFactorial_div_factorial]

private theorem checkRange_496_800 : checkRange 304 496 240 c496_val c992_val = true := by
  decide

/-- Finite range `496 ≤ n < 800`: verified in the kernel via unimodality and exact recurrence. -/
theorem trafficInequality_of_lt_800 {n a : ℕ} (hn1 : 496 ≤ n) (hn2 : n < 800)
    (ha : 1 ≤ a) (hna : 2 * a < n) : trafficInequality n a :=
  checkRange_sound 304 496 240 c496_val c992_val c496_eq c992_eq checkRange_496_800
    n hn1 (by omega) a ha hna

/-! ### Part II: Elementary analytic proof for all `n ≥ 800` (Lemmas 2–5) -/

/-- Central binomial ratio `W(n) = choose(n, ⌊n/2⌋)^2 / choose(2n, n)`. -/
noncomputable def W (n : ℕ) : ℝ :=
  ((n.choose (n / 2) : ℝ) ^ 2) / ((2 * n).choose n : ℝ)

private theorem W_pos (n : ℕ) : 0 < W n := by
  unfold W
  have h1 : 0 < n.choose (n / 2) := Nat.choose_pos (Nat.div_le_self n 2)
  have h2 : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
  positivity

private theorem W_even_mono (m : ℕ) (hm : 1 ≤ m) :
    ((2 * m + 3 : ℝ) * (W (2 * m + 2)) ^ 2) ≤ (2 * m + 1 : ℝ) * (W (2 * m)) ^ 2 := by
  have h1 : ((m + 1 : ℝ) * ((2 * m + 2).choose (m + 1) : ℝ)) =
      2 * (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) := by
    exact_mod_cast central_step_even m
  have h2 : ((m + 1 : ℝ) * (2 * m + 1 : ℝ) * ((4 * m + 4).choose (2 * m + 2) : ℝ)) =
      2 * (4 * m + 3 : ℝ) * (4 * m + 1 : ℝ) * ((4 * m).choose (2 * m) : ℝ) := by
    exact_mod_cast central_double_step_even m
  have hdiv1 : (2 * m + 2) / 2 = m + 1 := by omega
  have hdiv2 : (2 * m) / 2 = m := by omega
  have hmul1 : 2 * (2 * m + 2) = 4 * m + 4 := by omega
  have hmul2 : 2 * (2 * m) = 4 * m := by omega
  have hWrel : W (2 * m + 2) =
      (2 * (2 * m + 1 : ℝ) ^ 3 / ((m + 1 : ℝ) * (4 * m + 1 : ℝ) * (4 * m + 3 : ℝ))) * W (2 * m) := by
    unfold W
    rw [hdiv1, hdiv2, hmul1, hmul2]
    have hc1 : ((2 * m).choose m : ℝ) ≠ 0 := by
      have : 0 < (2 * m).choose m := Nat.choose_pos (by omega); positivity
    have hc2 : ((4 * m).choose (2 * m) : ℝ) ≠ 0 := by
      have : 0 < (4 * m).choose (2 * m) := Nat.choose_pos (by omega); positivity
    have hc3 : ((4 * m + 4).choose (2 * m + 2) : ℝ) ≠ 0 := by
      have : 0 < (4 * m + 4).choose (2 * m + 2) := Nat.choose_pos (by omega); positivity
    have heq1 : ((2 * m + 2).choose (m + 1) : ℝ) =
        2 * (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) / (m + 1 : ℝ) := by
      rw [eq_div_iff (by positivity)]; linarith
    have heq2 : ((4 * m + 4).choose (2 * m + 2) : ℝ) =
        2 * (4 * m + 3 : ℝ) * (4 * m + 1 : ℝ) * ((4 * m).choose (2 * m) : ℝ) /
          ((m + 1 : ℝ) * (2 * m + 1 : ℝ)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [heq1, heq2]
    field_simp
  rw [hWrel]
  have hW2 : 0 ≤ (W (2 * m)) ^ 2 := sq_nonneg _
  have hpoly : 4 * (2 * (m : ℝ) + 3) * (2 * m + 1) ^ 5 ≤
      ((m : ℝ) + 1) ^ 2 * (4 * m + 1) ^ 2 * (4 * m + 3) ^ 2 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    set u : ℝ := (m : ℝ) - 1
    have hu : 0 ≤ u := by linarith
    have hdiff : ((m : ℝ) + 1) ^ 2 * (4 * m + 1) ^ 2 * (4 * m + 3) ^ 2 -
        4 * (2 * (m : ℝ) + 3) * (2 * m + 1) ^ 5 =
        32 * u ^ 4 + 160 * u ^ 3 + 281 * u ^ 2 + 196 * u + 40 := by
      simp only [u]; ring
    nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
  have hfrac : (2 * (m : ℝ) + 3) *
      (2 * (2 * m + 1 : ℝ) ^ 3 / ((m + 1 : ℝ) * (4 * m + 1 : ℝ) * (4 * m + 3 : ℝ))) ^ 2 ≤
      2 * m + 1 := by
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    have hmul : (2 * (m : ℝ) + 3) * (2 * (2 * m + 1 : ℝ) ^ 3) ^ 2 =
        (2 * m + 1) * (4 * (2 * m + 3) * (2 * m + 1) ^ 5) := by ring
    have hrhs : (2 * (m : ℝ) + 1) * ((m + 1 : ℝ) * (4 * m + 1) * (4 * m + 3)) ^ 2 =
        (2 * m + 1) * ((m + 1) ^ 2 * (4 * m + 1) ^ 2 * (4 * m + 3) ^ 2) := by ring
    rw [hmul, hrhs]
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  calc
    (2 * (m : ℝ) + 3) *
        (2 * (2 * m + 1 : ℝ) ^ 3 / ((m + 1 : ℝ) * (4 * m + 1 : ℝ) * (4 * m + 3 : ℝ)) * W (2 * m)) ^ 2
        = ((2 * m + 3) *
            (2 * (2 * m + 1 : ℝ) ^ 3 / ((m + 1 : ℝ) * (4 * m + 1 : ℝ) * (4 * m + 3 : ℝ))) ^ 2) *
          (W (2 * m)) ^ 2 := by ring
    _ ≤ (2 * m + 1) * (W (2 * m)) ^ 2 := mul_le_mul_of_nonneg_right hfrac hW2

private theorem W_odd_le_even (m : ℕ) :
    ((2 * m + 2 : ℝ) * (W (2 * m + 1)) ^ 2) ≤ (2 * m + 1 : ℝ) * (W (2 * m)) ^ 2 := by
  have h1 : ((m + 1 : ℝ) * ((2 * m + 1).choose m : ℝ)) =
      (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) := by
    exact_mod_cast central_step_odd m
  have h2 : ((2 * m + 1 : ℝ) * ((4 * m + 2).choose (2 * m + 1) : ℝ)) =
      2 * (4 * m + 1 : ℝ) * ((4 * m).choose (2 * m) : ℝ) := by
    exact_mod_cast central_double_step_odd m
  have hdiv1 : (2 * m + 1) / 2 = m := by omega
  have hdiv2 : (2 * m) / 2 = m := by omega
  have hmul1 : 2 * (2 * m + 1) = 4 * m + 2 := by omega
  have hmul2 : 2 * (2 * m) = 4 * m := by omega
  have hWrel : W (2 * m + 1) =
      ((2 * m + 1 : ℝ) ^ 3 / (2 * (m + 1 : ℝ) ^ 2 * (4 * m + 1 : ℝ))) * W (2 * m) := by
    unfold W
    rw [hdiv1, hdiv2, hmul1, hmul2]
    have hc2 : ((4 * m).choose (2 * m) : ℝ) ≠ 0 := by
      have : 0 < (4 * m).choose (2 * m) := Nat.choose_pos (by omega); positivity
    have heq1 : ((2 * m + 1).choose m : ℝ) =
        (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) / (m + 1 : ℝ) := by
      rw [eq_div_iff (by positivity)]; linarith
    have heq2 : ((4 * m + 2).choose (2 * m + 1) : ℝ) =
        2 * (4 * m + 1 : ℝ) * ((4 * m).choose (2 * m) : ℝ) / (2 * m + 1 : ℝ) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [heq1, heq2]
    field_simp
  rw [hWrel]
  have hW2 : 0 ≤ (W (2 * m)) ^ 2 := sq_nonneg _
  have hpoly : (2 * (m : ℝ) + 1) ^ 5 ≤ 2 * (m + 1) ^ 3 * (4 * m + 1) ^ 2 := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hdiff : 2 * ((m : ℝ) + 1) ^ 3 * (4 * m + 1) ^ 2 - (2 * m + 1) ^ 5 =
        32 * m ^ 4 + 66 * m ^ 3 + 46 * m ^ 2 + 12 * m + 1 := by ring
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg ((m : ℝ) ^ 2)]
  have hfrac : (2 * (m : ℝ) + 2) *
      ((2 * m + 1 : ℝ) ^ 3 / (2 * (m + 1 : ℝ) ^ 2 * (4 * m + 1 : ℝ))) ^ 2 ≤
      2 * m + 1 := by
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    have hlhs : (2 * (m : ℝ) + 2) * ((2 * m + 1 : ℝ) ^ 3) ^ 2 =
        2 * (m + 1) * (2 * m + 1) * (2 * m + 1) ^ 5 := by ring
    have hrhs : (2 * (m : ℝ) + 1) * (2 * (m + 1 : ℝ) ^ 2 * (4 * m + 1)) ^ 2 =
        2 * (m + 1) * (2 * m + 1) * (2 * (m + 1) ^ 3 * (4 * m + 1) ^ 2) := by ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  calc
    (2 * (m : ℝ) + 2) *
        ((2 * m + 1 : ℝ) ^ 3 / (2 * (m + 1 : ℝ) ^ 2 * (4 * m + 1 : ℝ)) * W (2 * m)) ^ 2
        = ((2 * m + 2) *
            ((2 * m + 1 : ℝ) ^ 3 / (2 * (m + 1 : ℝ) ^ 2 * (4 * m + 1 : ℝ))) ^ 2) *
          (W (2 * m)) ^ 2 := by ring
    _ ≤ (2 * m + 1) * (W (2 * m)) ^ 2 := mul_le_mul_of_nonneg_right hfrac hW2

private theorem W_200_bound : (201 : ℝ) * (W 200) ^ 2 < 51 / 40 := by
  unfold W
  have hdiv : (200 : ℕ) / 2 = 100 := by norm_num
  have hmul : 2 * 200 = 400 := by norm_num
  rw [hdiv, hmul, div_pow, mul_div_assoc', div_lt_iff₀ (by
    have : 0 < (400).choose 200 := Nat.choose_pos (by omega)
    positivity)]
  have hnat : 40 * 201 * ((200).choose 100) ^ 4 < 51 * ((400).choose 200) ^ 2 := by
    norm_num [Nat.choose_eq_descFactorial_div_factorial]
  have hr : (40 : ℝ) * 201 * (((200).choose 100 : ℝ) ^ 4) < 51 * (((400).choose 200 : ℝ) ^ 2) := by
    exact_mod_cast hnat
  linarith [show (((200).choose 100 : ℝ) ^ 2) ^ 2 = ((200).choose 100 : ℝ) ^ 4 by ring]

/-- Lemma 2: `(n + 1) * W(n)^2 < 51 / 40` for all `n ≥ 200`. -/
theorem W_bound {n : ℕ} (hn : 200 ≤ n) :
    ((n : ℝ) + 1) * (W n) ^ 2 < 51 / 40 := by
  have heven : ∀ m : ℕ, 100 ≤ m → (2 * (m : ℝ) + 1) * (W (2 * m)) ^ 2 ≤ (201 : ℝ) * (W 200) ^ 2 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hstep := W_even_mono k (by omega)
      push_cast at hstep ⊢
      have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h2k]
      linarith
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 100 ≤ m := by omega
    have h := heven m hm
    have heq : m + m = 2 * m := by omega
    rw [heq]
    push_cast
    linarith [W_200_bound]
  · have hm : 100 ≤ m := by omega
    have h1 := W_odd_le_even m
    have h2 := heven m hm
    push_cast
    linarith [W_200_bound]

/-- Lemma 3a: `(1 - x) / (1 + x) ≤ exp (-2x)` for all `x ≥ 0`. -/
private theorem one_sub_div_one_add_le_exp {x : ℝ} (hx : 0 ≤ x) :
    (1 - x) / (1 + x) ≤ Real.exp (-2 * x) := by
  have hpos : 0 < 1 + x := by linarith
  rw [div_le_iff₀ hpos]
  let g : ℝ → ℝ := fun t => (1 + t) * Real.exp (-2 * t) - (1 - t)
  have hg_deriv : ∀ t : ℝ,
      HasDerivAt g (1 - (1 + 2 * t) * Real.exp (-2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-2 * s)) (Real.exp (-2 * t) * (-2)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-2)).exp
    have h3 : HasDerivAt (fun s : ℝ => (1 + s) * Real.exp (-2 * s))
        (1 * Real.exp (-2 * t) + (1 + t) * (Real.exp (-2 * t) * (-2))) t := h1.mul h2
    have h4 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hsub : HasDerivAt g (1 * Real.exp (-2 * t) + (1 + t) * (Real.exp (-2 * t) * (-2)) - (-1)) t :=
      h3.sub h4
    have heq : 1 * Real.exp (-2 * t) + (1 + t) * (Real.exp (-2 * t) * (-2)) - (-1) =
        1 - (1 + 2 * t) * Real.exp (-2 * t) := by ring
    rw [heq] at hsub
    exact hsub
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hg_deriv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg_deriv t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hg_deriv t).deriv]
      have hexp : 1 + 2 * t ≤ Real.exp (2 * t) := by
        have := Real.add_one_le_exp (2 * t); linarith
      have hmul : (1 + 2 * t) * Real.exp (-2 * t) ≤ Real.exp (2 * t) * Real.exp (-2 * t) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      rw [← Real.exp_add] at hmul
      have h0 : (2 : ℝ) * t + (-2 * t) = 0 := by ring
      rw [h0, Real.exp_zero] at hmul
      linarith
  have h0x := hg_mono (Set.mem_Ici.mpr le_rfl) hx hx
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0] at h0x
  dsimp [g] at h0x
  linarith

private theorem choose_ratio_le_even (m k : ℕ) (hk : k ≤ m) :
    (((2 * m).choose (m - k) : ℝ) / ((2 * m).choose m : ℝ)) ≤
      Real.exp (- (2 * (k : ℝ) ^ 2) / (2 * m + 1 : ℝ)) := by
  induction k with
  | zero =>
    have hc : ((2 * m).choose m : ℝ) ≠ 0 := by
      have : 0 < (2 * m).choose m := Nat.choose_pos (by omega); positivity
    simp [hc]
  | succ k ih =>
    have hkm : k ≤ m := by omega
    have ih' := ih hkm
    have hstep_nat : (m + k + 1) * (2 * m).choose (m - (k + 1)) =
        (m - k) * (2 * m).choose (m - k) := by
      have h := choose_step_right (2 * m) (m - (k + 1))
      have h1 : m - (k + 1) + 1 = m - k := by omega
      have h2 : 2 * m - (m - (k + 1)) = m + k + 1 := by omega
      rw [h1, h2] at h
      exact h.symm
    have hstep : (((2 * m).choose (m - (k + 1)) : ℝ) / ((2 * m).choose m : ℝ)) =
        (((m - k : ℕ) : ℝ) / ((m + k + 1 : ℕ) : ℝ)) *
          (((2 * m).choose (m - k) : ℝ) / ((2 * m).choose m : ℝ)) := by
      have hstep_r : ((m + k + 1 : ℕ) : ℝ) * ((2 * m).choose (m - (k + 1)) : ℝ) =
          ((m - k : ℕ) : ℝ) * ((2 * m).choose (m - k) : ℝ) := by exact_mod_cast hstep_nat
      have heq : ((2 * m).choose (m - (k + 1)) : ℝ) =
          ((m - k : ℕ) : ℝ) * ((2 * m).choose (m - k) : ℝ) / ((m + k + 1 : ℕ) : ℝ) := by
        rw [eq_div_iff (by positivity)]
        linarith
      rw [heq]
      ring
    let x : ℝ := (2 * (k : ℝ) + 1) / (2 * m + 1)
    have hx0 : 0 ≤ x := by positivity
    have hfrac_eq : ((m - k : ℕ) : ℝ) / ((m + k + 1 : ℕ) : ℝ) = (1 - x) / (1 + x) := by
      have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by exact Nat.cast_sub hkm
      rw [hcast]
      push_cast
      simp only [x]
      field_simp
      ring
    have hexp_step : ((m - k : ℕ) : ℝ) / ((m + k + 1 : ℕ) : ℝ) ≤ Real.exp (-2 * x) := by
      rw [hfrac_eq]
      exact one_sub_div_one_add_le_exp hx0
    have hnonneg : 0 ≤ ((2 * m).choose (m - k) : ℝ) / ((2 * m).choose m : ℝ) := by positivity
    rw [hstep]
    calc
      (((m - k : ℕ) : ℝ) / ((m + k + 1 : ℕ) : ℝ)) *
          (((2 * m).choose (m - k) : ℝ) / ((2 * m).choose m : ℝ))
          ≤ Real.exp (-2 * x) * Real.exp (- (2 * (k : ℝ) ^ 2) / (2 * m + 1 : ℝ)) :=
            mul_le_mul hexp_step ih' hnonneg (Real.exp_pos _).le
      _ = Real.exp (-2 * x + (- (2 * (k : ℝ) ^ 2) / (2 * m + 1 : ℝ))) := (Real.exp_add _ _).symm
      _ = Real.exp (- (2 * ((k + 1 : ℕ) : ℝ) ^ 2) / (2 * m + 1 : ℝ)) := by
            congr 1
            simp only [x]
            push_cast
            field_simp
            ring

private theorem choose_ratio_le_odd (m k : ℕ) (hk : k ≤ m) :
    (((2 * m + 1).choose (m - k) : ℝ) / ((2 * m + 1).choose m : ℝ)) ≤
      Real.exp (- (2 * (k : ℝ) * (k + 1)) / (2 * m + 2 : ℝ)) := by
  induction k with
  | zero =>
    have hc : ((2 * m + 1).choose m : ℝ) ≠ 0 := by
      have : 0 < (2 * m + 1).choose m := Nat.choose_pos (by omega); positivity
    simp [hc]
  | succ k ih =>
    have hkm : k ≤ m := by omega
    have ih' := ih hkm
    have hstep_nat : (m + k + 2) * (2 * m + 1).choose (m - (k + 1)) =
        (m - k) * (2 * m + 1).choose (m - k) := by
      have h := choose_step_right (2 * m + 1) (m - (k + 1))
      have h1 : m - (k + 1) + 1 = m - k := by omega
      have h2 : 2 * m + 1 - (m - (k + 1)) = m + k + 2 := by omega
      rw [h1, h2] at h
      exact h.symm
    have hstep : (((2 * m + 1).choose (m - (k + 1)) : ℝ) / ((2 * m + 1).choose m : ℝ)) =
        (((m - k : ℕ) : ℝ) / ((m + k + 2 : ℕ) : ℝ)) *
          (((2 * m + 1).choose (m - k) : ℝ) / ((2 * m + 1).choose m : ℝ)) := by
      have hstep_r : ((m + k + 2 : ℕ) : ℝ) * ((2 * m + 1).choose (m - (k + 1)) : ℝ) =
          ((m - k : ℕ) : ℝ) * ((2 * m + 1).choose (m - k) : ℝ) := by exact_mod_cast hstep_nat
      have heq : ((2 * m + 1).choose (m - (k + 1)) : ℝ) =
          ((m - k : ℕ) : ℝ) * ((2 * m + 1).choose (m - k) : ℝ) / ((m + k + 2 : ℕ) : ℝ) := by
        rw [eq_div_iff (by positivity)]
        linarith
      rw [heq]
      ring
    let y : ℝ := (2 * ((k : ℝ) + 1)) / (2 * m + 2)
    have hy0 : 0 ≤ y := by positivity
    have hfrac_eq : ((m - k : ℕ) : ℝ) / ((m + k + 2 : ℕ) : ℝ) = (1 - y) / (1 + y) := by
      have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by exact Nat.cast_sub hkm
      rw [hcast]
      push_cast
      simp only [y]
      field_simp
      ring
    have hexp_step : ((m - k : ℕ) : ℝ) / ((m + k + 2 : ℕ) : ℝ) ≤ Real.exp (-2 * y) := by
      rw [hfrac_eq]
      exact one_sub_div_one_add_le_exp hy0
    have hnonneg : 0 ≤ ((2 * m + 1).choose (m - k) : ℝ) / ((2 * m + 1).choose m : ℝ) := by positivity
    rw [hstep]
    calc
      (((m - k : ℕ) : ℝ) / ((m + k + 2 : ℕ) : ℝ)) *
          (((2 * m + 1).choose (m - k) : ℝ) / ((2 * m + 1).choose m : ℝ))
          ≤ Real.exp (-2 * y) * Real.exp (- (2 * (k : ℝ) * (k + 1)) / (2 * m + 2 : ℝ)) :=
            mul_le_mul hexp_step ih' hnonneg (Real.exp_pos _).le
      _ = Real.exp (-2 * y + (- (2 * (k : ℝ) * (k + 1)) / (2 * m + 2 : ℝ))) := (Real.exp_add _ _).symm
      _ = Real.exp (- (2 * ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / (2 * m + 2 : ℝ)) := by
            congr 1
            simp only [y]
            push_cast
            field_simp
            ring

/-- Lemma 3b: `(choose(n, a) / choose(n, ⌊n/2⌋))^2 ≤ exp (-((n - 2a)^2 - 1) / (n + 1))`. -/
theorem choose_ratio_sq_le_exp {n a : ℕ} (hna : 2 * a < n) :
    ((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2 ≤
      Real.exp (- ((((n - 2 * a : ℕ) : ℝ) ^ 2 - 1) / ((n : ℝ) + 1))) := by
  set d : ℕ := n - 2 * a
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h2m : m + m = 2 * m := by omega
    rw [h2m]
    have ham : a ≤ m := by omega
    set k : ℕ := m - a
    have ha_eq : a = m - k := by omega
    have hd_eq : d = 2 * k := by omega
    have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv, ha_eq]
    have h1 := choose_ratio_le_even m k (by omega)
    have hsq : (((2 * m).choose (m - k) : ℝ) / ((2 * m).choose m : ℝ)) ^ 2 ≤
        (Real.exp (- (2 * (k : ℝ) ^ 2) / (2 * m + 1 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [← Real.exp_nat_mul] at hsq
    refine hsq.trans (Real.exp_le_exp.mpr ?_)
    rw [hd_eq]
    push_cast
    rw [← neg_div, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 1)]
    nlinarith
  · have ham : a ≤ m := by omega
    set k : ℕ := m - a
    have ha_eq : a = m - k := by omega
    have hd_eq : d = 2 * k + 1 := by omega
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv, ha_eq]
    have h1 := choose_ratio_le_odd m k (by omega)
    have hsq : (((2 * m + 1).choose (m - k) : ℝ) / ((2 * m + 1).choose m : ℝ)) ^ 2 ≤
        (Real.exp (- (2 * (k : ℝ) * (k + 1)) / (2 * m + 2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [← Real.exp_nat_mul] at hsq
    refine hsq.trans (Real.exp_le_exp.mpr ?_)
    rw [hd_eq]
    push_cast
    have heq : (2 : ℝ) * (-(2 * (k : ℝ) * ((k : ℝ) + 1)) / (2 * (m : ℝ) + 2)) =
        -(((2 * (k : ℝ) + 1) ^ 2 - 1) / (2 * (m : ℝ) + 1 + 1)) := by
      field_simp
      ring
    linarith

/-- Lemma 4: `(t + ε(1 - t^2)) exp(-t^2) ≤ exp(-1/2) (1/√2 + ε/2 + 2ε^2)` for `ε > 0`. -/
theorem quad_exp_bound (t ε : ℝ) (hε : 0 < ε) :
    (t + ε * (1 - t ^ 2)) * Real.exp (-t ^ 2) ≤
      Real.exp (-1 / 2) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2) := by
  set c : ℝ := 1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcpos : 0 < c := by positivity
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2_gt : (9 / 8 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hdisc : 1 ≤ 2 * c ^ 2 - 2 * c * ε - 4 * ε ^ 2 := by
    have hident : 2 * c ^ 2 - 2 * c * ε - 4 * ε ^ 2 =
        1 + (4 * Real.sqrt 2 - 9 / 2) * ε ^ 2 + 8 * ε ^ 4 := by
      simp only [c]
      have hsq3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, hsq2]
      field_simp [hs2.ne']
      ring_nf
      simp only [hsq2, hsq3]
      ring
    rw [hident]
    have hcoeff : 0 < 4 * Real.sqrt 2 - 9 / 2 := by linarith
    nlinarith [sq_nonneg ε, sq_nonneg (ε ^ 2)]
  have hquad : t + ε * (1 - t ^ 2) ≤ c * (t ^ 2 + 1 / 2) := by
    have hnonneg : 0 ≤ 4 * (c + ε) * ((c + ε) * t ^ 2 - t + (c / 2 - ε)) := by
      have hid : 4 * (c + ε) * ((c + ε) * t ^ 2 - t + (c / 2 - ε)) =
          (2 * (c + ε) * t - 1) ^ 2 + (2 * c ^ 2 - 2 * c * ε - 4 * ε ^ 2 - 1) := by ring
      rw [hid]
      nlinarith [sq_nonneg (2 * (c + ε) * t - 1)]
    have h4pos : 0 < 4 * (c + ε) := by linarith
    have hq : 0 ≤ (c + ε) * t ^ 2 - t + (c / 2 - ε) := by nlinarith
    linarith
  have hexp : t ^ 2 + 1 / 2 ≤ Real.exp (t ^ 2 - 1 / 2) := by
    have := Real.add_one_le_exp (t ^ 2 - 1 / 2)
    linarith
  have hstep : t + ε * (1 - t ^ 2) ≤ c * Real.exp (t ^ 2 - 1 / 2) :=
    hquad.trans (mul_le_mul_of_nonneg_left hexp hcpos.le)
  have hmul := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-t ^ 2)).le
  calc
    (t + ε * (1 - t ^ 2)) * Real.exp (-t ^ 2)
        ≤ c * Real.exp (t ^ 2 - 1 / 2) * Real.exp (-t ^ 2) := hmul
    _ = c * (Real.exp (t ^ 2 - 1 / 2) * Real.exp (-t ^ 2)) := by ring
    _ = c * Real.exp (-1 / 2) := by
          rw [← Real.exp_add]
          congr 2
          ring
    _ = Real.exp (-1 / 2) * c := by ring

private theorem exp_inv_801_le : Real.exp (1 / 801 : ℝ) ≤ 801 / 800 := by
  have h := Real.add_one_le_exp (-1 / 801 : ℝ)
  have h1 : (800 / 801 : ℝ) ≤ Real.exp (-1 / 801 : ℝ) := by linarith
  have hmul : (800 / 801 : ℝ) * Real.exp (1 / 801 : ℝ) ≤
      Real.exp (-1 / 801 : ℝ) * Real.exp (1 / 801 : ℝ) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  linarith

private theorem exp_neg_half_lt : Real.exp (-1 / 2 : ℝ) < 128 / 211 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 6
  have hval : (211 / 128 : ℝ) < ∑ i ∈ Finset.range 6, (1 / 2 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hgt : (211 / 128 : ℝ) < Real.exp (1 / 2 : ℝ) := hval.trans_le hsum
  have hmul : (211 / 128 : ℝ) * Real.exp (-1 / 2 : ℝ) <
      Real.exp (1 / 2 : ℝ) * Real.exp (-1 / 2 : ℝ) :=
    mul_lt_mul_of_pos_right hgt (Real.exp_pos _)
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  linarith

/-- Lemma 5: For every `n ≥ 800` and `1 ≤ a < n / 2`, `trafficInequality n a` holds. -/
theorem trafficInequality_of_ge_800 {n a : ℕ} (hn : 800 ≤ n) (ha : 1 ≤ a) (hna : 2 * a < n) :
    trafficInequality n a := by
  rw [← trafficRatio_lt_one_iff n a (by omega)]
  suffices hR : (trafficRatio n a : ℝ) < 1 by exact_mod_cast hR
  set d : ℕ := n - 2 * a
  have hd_pos : 1 ≤ d := by omega
  have hd_cast : (d : ℝ) = (n : ℝ) - 2 * (a : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub (show 2 * a ≤ n by omega)]
    push_cast
    rfl
  set s : ℝ := Real.sqrt ((n : ℝ) + 1)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs_sq : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  set ε : ℝ := 1 / s
  have hε_pos : 0 < ε := by positivity
  set t : ℝ := (d : ℝ) * ε
  -- Refactor `trafficRatio n a` as in Lemma 1
  have hfac : (trafficRatio n a : ℝ) =
      ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1)) *
      (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
      (s * W n) *
      (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2) := by
    unfold trafficRatio W
    have hn_sub1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
    have h2n_sub1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ 2 * n by omega)]; push_cast; rfl
    have h2a_eq : (n : ℝ) - (d : ℝ) = 2 * (a : ℝ) := by linarith
    have hc_mid : (n.choose (n / 2) : ℝ) ≠ 0 := by
      have : 0 < n.choose (n / 2) := Nat.choose_pos (Nat.div_le_self n 2); positivity
    have hc_2n : ((2 * n).choose n : ℝ) ≠ 0 := by
      have : 0 < (2 * n).choose n := Nat.choose_pos (by omega); positivity
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    have hn1_ne : (n : ℝ) - 1 ≠ 0 := by
      have : (800 : ℝ) ≤ n := by exact_mod_cast hn
      exact ne_of_gt (by linarith)
    push_cast
    rw [hn_sub1, h2n_sub1, h2a_eq]
    change 2 * (2 * (n : ℝ) - 1) * (a : ℝ) * ((d : ℝ) + 1) * (n.choose a : ℝ) ^ 2 /
        ((n : ℝ) * ((n : ℝ) - 1) * ((2 * n).choose n : ℝ)) = _
    field_simp [hc_mid, hc_2n, hn_ne, hn1_ne, hs_pos.ne']
  -- Individual factor bounds
  have hpoly_lt : ((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s) < t + ε * (1 - t ^ 2) := by
    have hnum : ((n : ℝ) - d) * ((d : ℝ) + 1) < (n : ℝ) * ((d : ℝ) + 1 - (d : ℝ) ^ 2 / ((n : ℝ) + 1)) := by
      have h1 : (n : ℝ) * ((d : ℝ) + 1 - (d : ℝ) ^ 2 / ((n : ℝ) + 1)) - ((n : ℝ) - d) * ((d : ℝ) + 1) =
          (d : ℝ) ^ 2 / ((n : ℝ) + 1) + (d : ℝ) := by
        field_simp
        ring
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd_pos
      have hpos : 0 < (d : ℝ) ^ 2 / ((n : ℝ) + 1) + (d : ℝ) := by positivity
      linarith
    have hrhs_eq : t + ε * (1 - t ^ 2) =
        ((n : ℝ) * ((d : ℝ) + 1 - (d : ℝ) ^ 2 / ((n : ℝ) + 1))) / ((n : ℝ) * s) := by
      simp only [t, ε]
      field_simp [hs_pos.ne']
      nlinarith [hs_sq]
    rw [hrhs_eq]
    exact div_lt_div_of_pos_right hnum (by positivity)
  have hW_lt : s * W n < Real.sqrt (51 / 40) := by
    have hWb := W_bound (n := n) (by omega)
    have hsq_lt : (s * W n) ^ 2 < 51 / 40 := by
      rw [mul_pow, hs_sq]; exact hWb
    have hnonneg : 0 ≤ s * W n := mul_nonneg hs_pos.le (W_pos n).le
    rw [Real.lt_sqrt hnonneg]
    exact hsq_lt
  have htail_le : ((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2 ≤
      Real.exp (ε ^ 2) * Real.exp (-t ^ 2) := by
    have h3 := choose_ratio_sq_le_exp hna
    have hexp_eq : -(((d : ℝ) ^ 2 - 1) / ((n : ℝ) + 1)) = ε ^ 2 + (-t ^ 2) := by
      simp only [t, ε]
      field_simp [hs_pos.ne']
      nlinarith [hs_sq]
    rw [← Real.exp_add, ← hexp_eq]
    exact h3
  have hquad_le := quad_exp_bound t ε hε_pos
  have hpref_le : (2 * (n : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1599 / 799 := by
    have hnR : (800 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hε2_le : ε ^ 2 ≤ 1 / 801 := by
    have hnR : (800 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [ε, one_div, inv_pow, hs_sq]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hs_gt : (28 : ℝ) < s := by
    have hnR : (800 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hε_lt : ε < 1 / 28 := by
    simp only [ε]
    exact div_lt_div_of_pos_left (by norm_num) (by norm_num) hs_gt
  have hexp_ε2 : Real.exp (ε ^ 2) ≤ 801 / 800 :=
    (Real.exp_le_exp.mpr hε2_le).trans exp_inv_801_le
  have hsqrt2_gt : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hinv_sqrt2 : 1 / Real.sqrt 2 < 10000 / 14142 := by
    have := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1) (by norm_num) hsqrt2_gt
    linarith
  have hc_lt : 1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2 < 10000 / 14142 + 1 / 56 + 2 / 801 := by
    linarith
  -- Combine all bounds
  have hmid_pos : 0 < ((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s) := by
    have : (n : ℝ) - d = 2 * a := by linarith
    rw [this]; positivity
  have hpref_pos : 0 < (2 * (n : ℝ) - 1) / ((n : ℝ) - 1) := by
    have hnR : (800 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_pos (by linarith) (by linarith)
  have hstep1 : (trafficRatio n a : ℝ) <
      (1599 / 799 : ℝ) * Real.sqrt (51 / 40) * (801 / 800) * (128 / 211) *
        (10000 / 14142 + 1 / 56 + 2 / 801) := by
    rw [hfac]
    have hA : (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
        (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2) <
        Real.exp (ε ^ 2) * Real.exp (-1 / 2) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2) := by
      calc
        (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
            (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2)
            ≤ (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
                (Real.exp (ε ^ 2) * Real.exp (-t ^ 2)) :=
              mul_le_mul_of_nonneg_left htail_le hmid_pos.le
        _ < (t + ε * (1 - t ^ 2)) * (Real.exp (ε ^ 2) * Real.exp (-t ^ 2)) :=
              mul_lt_mul_of_pos_right hpoly_lt (by positivity)
        _ = Real.exp (ε ^ 2) * ((t + ε * (1 - t ^ 2)) * Real.exp (-t ^ 2)) := by ring
        _ ≤ Real.exp (ε ^ 2) * (Real.exp (-1 / 2) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2)) :=
              mul_le_mul_of_nonneg_left hquad_le (Real.exp_pos _).le
        _ = Real.exp (ε ^ 2) * Real.exp (-1 / 2) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2) := by ring
    have hB : Real.exp (ε ^ 2) * Real.exp (-1 / 2) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2) <
        (801 / 800 : ℝ) * (128 / 211) * (10000 / 14142 + 1 / 56 + 2 / 801) := by
      have hB1 : Real.exp (ε ^ 2) * Real.exp (-1 / 2) < (801 / 800 : ℝ) * (128 / 211) := by
        calc
          Real.exp (ε ^ 2) * Real.exp (-1 / 2)
              ≤ (801 / 800 : ℝ) * Real.exp (-1 / 2) :=
                mul_le_mul_of_nonneg_right hexp_ε2 (Real.exp_pos _).le
          _ < (801 / 800 : ℝ) * (128 / 211) :=
                mul_lt_mul_of_pos_left exp_neg_half_lt (by norm_num)
      have hc0 : 0 < 1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2 := by positivity
      calc
        Real.exp (ε ^ 2) * Real.exp (-1 / 2) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2)
            < (801 / 800 : ℝ) * (128 / 211) * (1 / Real.sqrt 2 + ε / 2 + 2 * ε ^ 2) :=
              mul_lt_mul_of_pos_right hB1 hc0
        _ < (801 / 800 : ℝ) * (128 / 211) * (10000 / 14142 + 1 / 56 + 2 / 801) :=
              mul_lt_mul_of_pos_left hc_lt (by norm_num)
    have hC : ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1)) * (s * W n) <
        (1599 / 799 : ℝ) * Real.sqrt (51 / 40) := by
      calc
        ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1)) * (s * W n)
            ≤ (1599 / 799 : ℝ) * (s * W n) :=
              mul_le_mul_of_nonneg_right hpref_le (mul_nonneg hs_pos.le (W_pos n).le)
        _ < (1599 / 799 : ℝ) * Real.sqrt (51 / 40) :=
              mul_lt_mul_of_pos_left hW_lt (by norm_num)
    have hAB : (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
        (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2) <
        (801 / 800 : ℝ) * (128 / 211) * (10000 / 14142 + 1 / 56 + 2 / 801) := hA.trans hB
    have hAB_nonneg : 0 ≤ (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
        (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2) := by positivity
    calc
      ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1)) *
          (((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) * (s * W n) *
          (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2)
          = (((2 * (n : ℝ) - 1) / ((n : ℝ) - 1)) * (s * W n)) *
            ((((n : ℝ) - d) * ((d : ℝ) + 1) / ((n : ℝ) * s)) *
              (((n.choose a : ℝ) / (n.choose (n / 2) : ℝ)) ^ 2)) := by ring
      _ < ((1599 / 799 : ℝ) * Real.sqrt (51 / 40)) *
            ((801 / 800 : ℝ) * (128 / 211) * (10000 / 14142 + 1 / 56 + 2 / 801)) :=
            mul_lt_mul'' hC hAB (mul_nonneg hpref_pos.le (mul_nonneg hs_pos.le (W_pos n).le)) hAB_nonneg
      _ = (1599 / 799 : ℝ) * Real.sqrt (51 / 40) * (801 / 800) * (128 / 211) *
            (10000 / 14142 + 1 / 56 + 2 / 801) := by ring
  have hfinal : (1599 / 799 : ℝ) * Real.sqrt (51 / 40) * (801 / 800) * (128 / 211) *
      (10000 / 14142 + 1 / 56 + 2 / 801) < 1 := by
    have hsq_lt : ((1599 / 799 : ℝ) * Real.sqrt (51 / 40) * (801 / 800) * (128 / 211) *
        (10000 / 14142 + 1 / 56 + 2 / 801)) ^ 2 < 1 ^ 2 := by
      have hsq51 : (Real.sqrt (51 / 40 : ℝ)) ^ 2 = 51 / 40 := Real.sq_sqrt (by norm_num)
      calc
        ((1599 / 799 : ℝ) * Real.sqrt (51 / 40) * (801 / 800) * (128 / 211) *
            (10000 / 14142 + 1 / 56 + 2 / 801)) ^ 2
            = (1599 / 799 : ℝ) ^ 2 * (Real.sqrt (51 / 40)) ^ 2 * (801 / 800) ^ 2 *
                (128 / 211) ^ 2 * (10000 / 14142 + 1 / 56 + 2 / 801) ^ 2 := by ring
        _ = (1599 / 799 : ℝ) ^ 2 * (51 / 40) * (801 / 800) ^ 2 *
              (128 / 211) ^ 2 * (10000 / 14142 + 1 / 56 + 2 / 801) ^ 2 := by rw [hsq51]
        _ < 1 ^ 2 := by norm_num
    nlinarith [show (0 : ℝ) ≤ (1599 / 799 : ℝ) * Real.sqrt (51 / 40) * (801 / 800) *
      (128 / 211) * (10000 / 14142 + 1 / 56 + 2 / 801) by positivity]
  exact hstep1.trans hfinal

/-! ### Main Theorem: Complete Resolution of Conjecture 7.4 -/

/-- **Main Theorem (Conjecture 7.4, integer form):**
For every `n ≥ 496` and `1 ≤ a < n / 2`, `trafficInequality n a` holds. -/
theorem conjecture74_proved : conjecture74 := by
  intro n a hn ha hna
  by_cases hlt : n < 800
  · exact trafficInequality_of_lt_800 hn hlt ha hna
  · exact trafficInequality_of_ge_800 (by omega) ha hna

/-- **Main Theorem (Conjecture 7.4, verbatim paper ratio `R_n(a) = G(n, a) / D(n) < 1`):**
For every `n ≥ 496` and `1 ≤ a < n / 2`, `R_paper n a < 1`. -/
theorem conjecture74_paper :
    ∀ n a : ℕ, 496 ≤ n → 1 ≤ a → 2 * a < n → R_paper n a < 1 := by
  intro n a hn ha hna
  rw [R_paper_eq_trafficRatio n a (by omega) ha hna]
  exact (conjecture74_iff_rational.mp conjecture74_proved) n a hn ha hna

end GilAntidiagonalTraffic
