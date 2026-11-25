import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Proof of Manabe's Conjecture 57 (Admissible Angle Conjecture) and Extensions

Formalization of the complete proof of Conjecture 57 of Hikaru Manabe,
*Purely Periodic Three-move Subtraction Games* (`arXiv:2609.05358v2`),
in a strictly stronger form:

For every triple of positive integers `1 ≤ a < b < c` (without requiring
`a ≥ 2`, `gcd(a, b, c) = 1`, `c ≠ a + b`, or minimality of the period),
the set of `P`-positions `W = {x : ℕ | grundy a b c x = 0}` of the three-move
subtraction game `S = {a, b, c}` satisfies:
- `W` is `(a + b)`-periodic iff `ρ ∈ Θ_{a+b}` (extending Lemma 54 / Prop. 55 to all `c > b`);
- `W` is `(c + a)`-periodic iff `ρ ∈ Θ_{c+a}`;
- `W` is `(c + b)`-periodic iff `ρ ∈ Θ_{c+b}`,
where `ρ = c % (a + b)` and `Θ_{a+b}, Θ_{c+a}, Θ_{c+b}` are defined verbatim
by Definition 19 (`(T0)`, `(T1)`, `(T2)`) and formula `(4)` of `arXiv:2609.05358v2`.

We also formalize:
- the exact closed-form cyclic-interval characterization of `Θ_{c+b}`;
- the full Sprague–Grundy statement (`manabe_conjecture_57`);
- two partial period exclusions toward Conjecture 56: no pure period in `(c - a, c + a)`,
  and an extended Fine–Wilf theorem showing any pure period `p` with
  `c ≥ p + (a + b) - gcd(p, a + b)` forces `ρ ∈ Θ_{a+b}` (including `a + b ∣ p`).
-/

namespace ManabeSubtraction

/-- Exact `P`-position indicator for the 3-move subtraction game `{a, b, c}` (when `0 < a < b < c`). -/
def isP (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) : ℕ → Bool
  | x =>
    let ma := if _h : a ≤ x then isP a b c ha hab hbc (x - a) else false
    let mb := if _h : b ≤ x then isP a b c ha hab hbc (x - b) else false
    let mc := if _h : c ≤ x then isP a b c ha hab hbc (x - c) else false
    !(ma || mb || mc)
termination_by x => x
decreasing_by
  all_goals omega

/-- Exact `P`-position indicator for the base 2-move subtraction game `{a, b}` (when `0 < a < b`). -/
def isPB (a b : ℕ) (ha : 0 < a) (hab : a < b) : ℕ → Bool
  | x =>
    let ma := if _h : a ≤ x then isPB a b ha hab (x - a) else false
    let mb := if _h : b ≤ x then isPB a b ha hab (x - b) else false
    !(ma || mb)
termination_by x => x
decreasing_by
  all_goals omega

/-- Minimum excluded natural number of a 3-element optional set (at most 3). -/
def mex3 (o1 o2 o3 : Option ℕ) : ℕ :=
  let mem (v : ℕ) : Bool := (o1 == some v) || (o2 == some v) || (o3 == some v)
  if !mem 0 then 0
  else if !mem 1 then 1
  else if !mem 2 then 2
  else 3

/-- Exact Sprague–Grundy nim-value `G_S(x)` of the 3-move subtraction game `{a, b, c}`. -/
def grundy (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) : ℕ → ℕ
  | x =>
    let o1 := if _h : a ≤ x then some (grundy a b c ha hab hbc (x - a)) else none
    let o2 := if _h : b ≤ x then some (grundy a b c ha hab hbc (x - b)) else none
    let o3 := if _h : c ≤ x then some (grundy a b c ha hab hbc (x - c)) else none
    mex3 o1 o2 o3
termination_by x => x
decreasing_by
  all_goals omega

lemma mex3_eq_zero_iff (o1 o2 o3 : Option ℕ) :
    mex3 o1 o2 o3 = 0 ↔ o1 ≠ some 0 ∧ o2 ≠ some 0 ∧ o3 ≠ some 0 := by
  unfold mex3
  dsimp only
  split_ifs <;> simp_all

/-- A position has nim-value `0` iff it is a `P`-position (`isP = true`). -/
theorem grundy_eq_zero_iff_isP (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (x : ℕ) :
    grundy a b c ha hab hbc x = 0 ↔ isP a b c ha hab hbc x = true := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    rw [grundy.eq_def, isP.eq_def]
    dsimp only
    rw [mex3_eq_zero_iff]
    have h1 : (if h : a ≤ x then some (grundy a b c ha hab hbc (x - a)) else none) ≠ some 0 ↔
        (if h : a ≤ x then isP a b c ha hab hbc (x - a) else false) = false := by
      split_ifs with h
      · simp [ih (x - a) (by omega)]
      · simp
    have h2 : (if h : b ≤ x then some (grundy a b c ha hab hbc (x - b)) else none) ≠ some 0 ↔
        (if h : b ≤ x then isP a b c ha hab hbc (x - b) else false) = false := by
      split_ifs with h
      · simp [ih (x - b) (by omega)]
      · simp
    have h3 : (if h : c ≤ x then some (grundy a b c ha hab hbc (x - c)) else none) ≠ some 0 ↔
        (if h : c ≤ x then isP a b c ha hab hbc (x - c) else false) = false := by
      split_ifs with h
      · simp [ih (x - c) (by omega)]
      · simp
    rw [h1, h2, h3]
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, and_assoc]

lemma isP_iff (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (x : ℕ) :
    isP a b c ha hab hbc x = true ↔
      (a ≤ x → isP a b c ha hab hbc (x - a) = false) ∧
      (b ≤ x → isP a b c ha hab hbc (x - b) = false) ∧
      (c ≤ x → isP a b c ha hab hbc (x - c) = false) := by
  rw [isP.eq_def]
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simpa [h] using h1
    · simpa [h] using h2
    · simpa [h] using h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · split_ifs with h; exact h1 h; rfl
    · split_ifs with h; exact h2 h; rfl
    · split_ifs with h; exact h3 h; rfl

lemma isPB_iff (a b : ℕ) (ha : 0 < a) (hab : a < b) (x : ℕ) :
    isPB a b ha hab x = true ↔
      (a ≤ x → isPB a b ha hab (x - a) = false) ∧
      (b ≤ x → isPB a b ha hab (x - b) = false) := by
  rw [isPB.eq_def]
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa [h] using h1
    · simpa [h] using h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · split_ifs with h; exact h1 h; rfl
    · split_ifs with h; exact h2 h; rfl

/-- Manabe Lemma 4 (uniqueness of an independent and dominating kernel for `{a, b, c}`). -/
lemma isP_unique (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (T : ℕ → Bool)
    (hind : ∀ x, T x = true →
      (a ≤ x → T (x - a) = false) ∧
      (b ≤ x → T (x - b) = false) ∧
      (c ≤ x → T (x - c) = false))
    (hdom : ∀ x, T x = false →
      (a ≤ x ∧ T (x - a) = true) ∨
      (b ≤ x ∧ T (x - b) = true) ∨
      (c ≤ x ∧ T (x - c) = true)) :
    ∀ x, isP a b c ha hab hbc x = T x := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    cases hTx : T x
    · rcases hdom x hTx with ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩
      · have hih := ih (x - a) (by omega)
        rw [ht] at hih
        cases hpx : isP a b c ha hab hbc x
        · rfl
        · exfalso; have h' := ((isP_iff a b c ha hab hbc x).mp hpx).1 h; rw [hih] at h'; simp at h'
      · have hih := ih (x - b) (by omega)
        rw [ht] at hih
        cases hpx : isP a b c ha hab hbc x
        · rfl
        · exfalso; have h' := ((isP_iff a b c ha hab hbc x).mp hpx).2.1 h; rw [hih] at h'; simp at h'
      · have hih := ih (x - c) (by omega)
        rw [ht] at hih
        cases hpx : isP a b c ha hab hbc x
        · rfl
        · exfalso; have h' := ((isP_iff a b c ha hab hbc x).mp hpx).2.2 h; rw [hih] at h'; simp at h'
    · obtain ⟨h1, h2, h3⟩ := hind x hTx
      rw [isP_iff]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [ih (x - a) (by omega)]; exact h1 h
      · rw [ih (x - b) (by omega)]; exact h2 h
      · rw [ih (x - c) (by omega)]; exact h3 h

lemma isPB_unique (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (T : ℕ → Bool)
    (hind : ∀ x, T x = true →
      (a ≤ x → T (x - a) = false) ∧ (b ≤ x → T (x - b) = false))
    (hdom : ∀ x, T x = false →
      (a ≤ x ∧ T (x - a) = true) ∨ (b ≤ x ∧ T (x - b) = true)) :
    ∀ x, isPB a b ha hab x = T x := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    cases hTx : T x
    · rcases hdom x hTx with ⟨h, ht⟩ | ⟨h, ht⟩
      · have hih := ih (x - a) (by omega)
        rw [ht] at hih
        cases hpx : isPB a b ha hab x
        · rfl
        · exfalso; have h' := ((isPB_iff a b ha hab x).mp hpx).1 h; rw [hih] at h'; simp at h'
      · have hih := ih (x - b) (by omega)
        rw [ht] at hih
        cases hpx : isPB a b ha hab x
        · rfl
        · exfalso; have h' := ((isPB_iff a b ha hab x).mp hpx).2 h; rw [hih] at h'; simp at h'
    · obtain ⟨h1, h2⟩ := hind x hTx
      rw [isPB_iff]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [ih (x - a) (by omega)]; exact h1 h
      · rw [ih (x - b) (by omega)]; exact h2 h

/-! ## Section 1: Base pattern `Z`, gap set `D`, arc `Λ`, and admissible angle sets `Θ_P` -/

/-- Base pattern `Z = {u ∈ [0, b) : ⌊u / a⌋ even}` on `ℤ / (a + b)ℤ`. -/
def Z (a b u : ℕ) : Prop :=
  u < b ∧ (u / a) % 2 = 0

instance (a b u : ℕ) : Decidable (Z a b u) := by
  unfold Z; infer_instance

/-- Gap set `D = [a, b) \ Z`. -/
def D (a b u : ℕ) : Prop :=
  a ≤ u ∧ u < b ∧ ¬ Z a b u

/-- Difference `δ = b - a`, quotient `η = ⌊δ / a⌋`, remainder `ε = δ mod a`. -/
def delta (a b : ℕ) : ℕ := b - a
def eta (a b : ℕ) : ℕ := (b - a) / a
def eps (a b : ℕ) : ℕ := (b - a) % a

/-- Arc `Λ` defined verbatim by formula `(4)` of `arXiv:2609.05358v2`. -/
def Lambda (a b u : ℕ) : Prop :=
  if eta a b % 2 = 0 then
    (eta a b + 1) * a ≤ u ∧ u < (eta a b + 1) * a + eps a b
  else
    eta a b * a + eps a b ≤ u ∧ u < (eta a b + 1) * a

/-- Verbatim Definition 19 `(T0)`: `ρ ∈ Θ_{a+b} ⇔ Z ∩ (Z + ρ) = ∅` mod `a + b`. -/
def Theta_ab (a b rho : ℕ) : Prop :=
  ∀ z, z < a + b → Z a b z → ¬ Z a b ((z + rho) % (a + b))

/-- Verbatim Definition 19 `(T1)`: `ρ ∈ Θ_{c+a} ⇔ Z ∩ [0, δ) ∩ (Z + (δ - ρ)) = ∅` mod `a + b`. -/
def Theta_ca (a b rho : ℕ) : Prop :=
  ∀ h, h < delta a b → Z a b h →
    ∀ z, z < a + b → Z a b z → (z + delta a b) % (a + b) ≠ (h + rho) % (a + b)

/-- Verbatim Definition 19 `(T2)`: `ρ ∈ Θ_{c+b} ⇔ (ρ + Λ) ∩ Z = ∅ ∧ (ρ + D) ∩ Λ = ∅` mod `a + b`. -/
def Theta_cb (a b rho : ℕ) : Prop :=
  (∀ l, Lambda a b l → ¬ Z a b ((rho + l) % (a + b))) ∧
  (∀ d, D a b d → ¬ Lambda a b ((rho + d) % (a + b)))

/-- Pure `P`-position periodicity of `{a, b, c}` with period `P`. -/
def PurelyPeriodicP (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (P : ℕ) : Prop :=
  ∀ x, isP a b c ha hab hbc (x + P) = isP a b c ha hab hbc x

/-- Pure Sprague–Grundy periodicity of `{a, b, c}` with period `P`. -/
def PurelyPeriodicG (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (P : ℕ) : Prop :=
  ∀ x, grundy a b c ha hab hbc (x + P) = grundy a b c ha hab hbc x

lemma purelyPeriodicP_of_G (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) {P : ℕ}
    (hG : PurelyPeriodicG a b c ha hab hbc P) :
    PurelyPeriodicP a b c ha hab hbc P := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [← grundy_eq_zero_iff_isP, ← grundy_eq_zero_iff_isP, hG x]

lemma div_sub_self_odd {a u : ℕ} (ha : 0 < a) (hu : a ≤ u) :
    (u - a) / a + 1 = u / a := by
  have h1 : (u - a + a) / a = (u - a) / a + 1 := Nat.add_div_right (u - a) ha
  rw [Nat.sub_add_cancel hu] at h1; exact h1.symm

lemma div_add_self {a u : ℕ} (ha : 0 < a) :
    (u + a) / a = u / a + 1 :=
  Nat.add_div_right u ha

lemma sub_mod_of_le_mod {x s P : ℕ} (hP : 0 < P) (h : s ≤ x % P) :
    (x - s) % P = x % P - s := by
  have hx := Nat.div_add_mod' x P
  have hr := Nat.mod_lt x hP
  have : x - s = x / P * P + (x % P - s) := by omega
  rw [this, Nat.mul_add_mod_of_lt (by omega)]

lemma sub_mod_of_mod_lt {x s P : ℕ} (hsP : s ≤ P) (hsx : s ≤ x) (h : x % P < s) :
    (x - s) % P = x % P + (P - s) := by
  have hx := Nat.div_add_mod' x P
  obtain ⟨k, hk⟩ : ∃ k, x / P = k + 1 := by
    rcases hq : x / P with _ | k
    · rw [hq, Nat.zero_mul] at hx; omega
    · exact ⟨k, rfl⟩
  rw [hk, Nat.add_one_mul] at hx
  have : x - s = k * P + (x % P + (P - s)) := by omega
  rw [this, Nat.mul_add_mod_of_lt (by omega)]

lemma add_mod_cancel {x y d m : ℕ} (hx : x < m) (hy : y < m)
    (hxy : (x + d) % m = (y + d) % m) : x = y := by
  have h1 : (x : ℤ) % m = (y : ℤ) % m := by
    have : ((x : ℤ) + d) % m = ((y : ℤ) + d) % m := by exact_mod_cast hxy
    have hsub' : (((x : ℤ) + d) - ((y : ℤ) + d)) % m = 0 := by
      rw [Int.sub_emod, this, sub_self, Int.zero_emod]
    have : ((x : ℤ) - y) % m = 0 := by simpa using hsub'
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr this
  have hx' : (x : ℤ) % m = x := Int.emod_eq_of_lt (by omega) (by omega)
  have hy' : (y : ℤ) % m = y := Int.emod_eq_of_lt (by omega) (by omega)
  omega

/-- **F1.** `W_B = Z + (a + b)ℕ`. -/
theorem F1 (a b : ℕ) (ha : 0 < a) (hab : a < b) (x : ℕ) :
    isPB a b ha hab x = decide (Z a b (x % (a + b))) := by
  apply isPB_unique a b ha hab (fun y => decide (Z a b (y % (a + b))))
  · intro y hy
    have hZ : Z a b (y % (a + b)) := of_decide_eq_true hy
    obtain ⟨hub, hpar⟩ := hZ
    have hu_lt : y % (a + b) < a + b := Nat.mod_lt y (by omega)
    constructor
    · intro hay
      rw [decide_eq_false_iff_not]
      rintro ⟨hlt, hpar'⟩
      by_cases hua : a ≤ y % (a + b)
      · rw [sub_mod_of_le_mod (by omega) hua] at hpar'
        have hstep := div_sub_self_odd ha hua
        omega
      · rw [sub_mod_of_mod_lt (by omega) hay (by omega)] at hlt
        omega
    · intro hby
      rw [decide_eq_false_iff_not]
      rintro ⟨hlt, hpar'⟩
      rw [sub_mod_of_mod_lt (by omega) hby (by omega)] at hlt hpar'
      have e : y % (a + b) + (a + b - b) = y % (a + b) + a := by omega
      rw [e, div_add_self ha] at hpar'
      omega
  · intro y hy
    have hnZ : ¬ Z a b (y % (a + b)) := of_decide_eq_false hy
    have hu_lt : y % (a + b) < a + b := Nat.mod_lt y (by omega)
    have hx := Nat.div_add_mod' y (a + b)
    by_cases hub : y % (a + b) < b
    · left
      have hodd : (y % (a + b) / a) % 2 = 1 := by
        unfold Z at hnZ; omega
      have hua : a ≤ y % (a + b) := by
        by_contra hlt
        have : y % (a + b) / a = 0 := Nat.div_eq_of_lt (by omega)
        omega
      refine ⟨by omega, decide_eq_true ?_⟩
      rw [sub_mod_of_le_mod (by omega) hua]
      have hstep := div_sub_self_odd ha hua
      exact ⟨by omega, by omega⟩
    · right
      refine ⟨by omega, decide_eq_true ?_⟩
      rw [sub_mod_of_le_mod (by omega) (by omega)]
      have hdiv0 : (y % (a + b) - b) / a = 0 := Nat.div_eq_of_lt (by omega)
      exact ⟨by omega, by omega⟩

lemma Z_of_lt_a {a b u : ℕ} (hab : a < b) (hu : u < a) : Z a b u := by
  exact ⟨by omega, by rw [Nat.div_eq_of_lt hu]⟩

/-- **F2.** On `ℤ / (a + b)ℤ`, `r ∈ Z → (r + a) % (a + b) ∉ Z`. -/
lemma F2 {a b r : ℕ} (ha : 0 < a) (hr : Z a b r) : ¬ Z a b ((r + a) % (a + b)) := by
  obtain ⟨hrb, hpar⟩ := hr
  rw [Nat.mod_eq_of_lt (by omega)]
  rintro ⟨hlt, hpar'⟩
  have := div_add_self (u := r) ha
  omega

lemma eta_mul_add_eps (a b : ℕ) : eta a b * a + eps a b = delta a b := by
  unfold eta eps delta
  rw [Nat.mul_comm]
  exact Nat.div_add_mod (b - a) a

lemma eps_lt_a {a b : ℕ} (ha : 0 < a) : eps a b < a :=
  Nat.mod_lt (b - a) ha

/-- **F3a.** `Λ = [δ, b) \ Z`. -/
lemma Lambda_iff_interval {a b u : ℕ} (ha : 0 < a) (hab : a < b) :
    Lambda a b u ↔ delta a b ≤ u ∧ u < b ∧ ¬ Z a b u := by
  have hde := eta_mul_add_eps a b
  have heps := eps_lt_a (b := b) ha
  have hdb : delta a b + a = b := by unfold delta; omega
  have hm : (eta a b + 1) * a = eta a b * a + a := Nat.succ_mul _ _
  unfold Lambda Z
  split_ifs with heven
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, by omega, ?_⟩
      rintro ⟨_, hpar⟩
      have hq : u / a = eta a b + 1 := by
        have hge : eta a b + 1 ≤ u / a := (Nat.le_div_iff_mul_le ha).mpr h1
        have hlt : u / a < eta a b + 2 := (Nat.div_lt_iff_lt_mul ha).mpr (by nlinarith)
        omega
      omega
    · rintro ⟨h1, h2, hnot⟩
      by_cases hlt : u < (eta a b + 1) * a
      · exfalso
        apply hnot
        refine ⟨h2, ?_⟩
        have hq : u / a = eta a b := by
          have hge : eta a b ≤ u / a := (Nat.le_div_iff_mul_le ha).mpr (by omega)
          have hlt' : u / a < eta a b + 1 := (Nat.div_lt_iff_lt_mul ha).mpr hlt
          omega
        omega
      · exact ⟨by omega, by omega⟩
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, by omega, ?_⟩
      rintro ⟨_, hpar⟩
      have hq : u / a = eta a b := by
        have hge : eta a b ≤ u / a := (Nat.le_div_iff_mul_le ha).mpr (by omega)
        have hlt : u / a < eta a b + 1 := (Nat.div_lt_iff_lt_mul ha).mpr h2
        omega
      omega
    · rintro ⟨h1, h2, hnot⟩
      by_cases hlt : u < (eta a b + 1) * a
      · exact ⟨by omega, hlt⟩
      · exfalso
        apply hnot
        refine ⟨h2, ?_⟩
        have hq : u / a = eta a b + 1 := by
          have hge : eta a b + 1 ≤ u / a := (Nat.le_div_iff_mul_le ha).mpr (by omega)
          have hlt' : u / a < eta a b + 2 := (Nat.div_lt_iff_lt_mul ha).mpr (by nlinarith)
          omega
        omega

/-- **F3b.** `Λ = {w < a + b : w ∉ Z ∧ (w + a) % (a + b) ∉ Z}`. -/
lemma Lambda_iff_double_outside {a b w : ℕ} (ha : 0 < a) (hab : a < b) (hw : w < a + b) :
    Lambda a b w ↔ ¬ Z a b w ∧ ¬ Z a b ((w + a) % (a + b)) := by
  rw [Lambda_iff_interval ha hab]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h3, ?_⟩
    have hge : b ≤ w + a := by unfold delta at h1; omega
    rw [Nat.mod_eq_of_lt (by omega)]
    rintro ⟨hlt, _⟩
    omega
  · rintro ⟨h1, h2⟩
    by_cases hwb : w < b
    · by_cases hwd : delta a b ≤ w
      · exact ⟨hwd, hwb, h1⟩
      · exfalso
        apply h2
        rw [Nat.mod_eq_of_lt (by omega)]
        have hodd : (w / a) % 2 = 1 := by unfold Z at h1; omega
        refine ⟨by unfold delta at hwd; omega, ?_⟩
        rw [div_add_self ha]; omega
    · exfalso
      apply h2
      have hmod : (w + a) % (a + b) = w - b := by
        have : w + a = 1 * (a + b) + (w - b) := by omega
        rw [this, Nat.mul_add_mod_of_lt (by omega)]
      rw [hmod]
      exact Z_of_lt_a hab (by omega)

lemma Lambda_subset_D {a b u : ℕ} (ha : 0 < a) (hab : a < b) (hu : Lambda a b u) :
    D a b u := by
  rw [Lambda_iff_interval ha hab] at hu
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨?_, h2, h3⟩
  by_contra hlt
  exact h3 (Z_of_lt_a hab (by omega))

lemma Lambda_lt_b {a b u : ℕ} (ha : 0 < a) (hab : a < b) (hu : Lambda a b u) : u < b :=
  ((Lambda_iff_interval ha hab).mp hu).2.1

/-! ## Section 2: First `c + b` positions of `W` -/

/-- **L1a.** Below `c`, the 3-move game agrees with the base 2-move game. -/
lemma L1_below (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ∀ x, x < c → isP a b c ha hab hbc x = isPB a b ha hab x := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hxc
    rw [isP.eq_def, isPB.eq_def]
    have hcnot : ¬ c ≤ x := by omega
    simp only [hcnot, ↓reduceDIte, Bool.or_false]
    congr 1
    congr 1
    · split_ifs with h
      · exact ih (x - a) (by omega) (by omega)
      · rfl
    · split_ifs with h
      · exact ih (x - b) (by omega) (by omega)
      · rfl

/-- **L1b.** `W ∩ [c, c + a) = ∅`. -/
lemma L1_gap (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {x : ℕ} (h1 : c ≤ x) (h2 : x < c + a) :
    isP a b c ha hab hbc x = false := by
  by_contra htrue
  have hp : isP a b c ha hab hbc x = true := by cases h : isP a b c ha hab hbc x <;> simp_all
  have hsub := ((isP_iff a b c ha hab hbc x).mp hp).2.2 h1
  rw [L1_below a b c ha hab hbc (x - c) (by omega), F1 a b ha hab (x - c)] at hsub
  have hlt : x - c < a := by omega
  have hmod : (x - c) % (a + b) = x - c := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hsub
  have hZ := Z_of_lt_a hab hlt
  simp [hZ] at hsub

/-- **L2.** `W ∩ [c + a, c + b) = {c + u : u ∈ D, (ρ + u + a) % (a + b) ∉ Z}`. -/
theorem L2 (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {u : ℕ} (hua : a ≤ u) (hub : u < b) :
    isP a b c ha hab hbc (c + u) = true ↔
      D a b u ∧ ¬ Z a b ((c % (a + b) + u + a) % (a + b)) := by
  have hmod_b : (c + u - b) % (a + b) = (c % (a + b) + u + a) % (a + b) := by
    have h1 : c + u - b + (a + b) = c + u + a := by omega
    calc (c + u - b) % (a + b)
        = (c + u - b + (a + b)) % (a + b) := (Nat.add_mod_right _ _).symm
      _ = (c + u + a) % (a + b) := by rw [h1]
      _ = (c % (a + b) + u + a) % (a + b) := by
            rw [Nat.add_assoc, Nat.add_assoc, Nat.mod_add_mod]
  have hxb_lt : c + u - b < c := by omega
  have hxb : isP a b c ha hab hbc (c + u - b) = false ↔
      ¬ Z a b ((c % (a + b) + u + a) % (a + b)) := by
    rw [L1_below a b c ha hab hbc (c + u - b) hxb_lt, F1 a b ha hab, hmod_b]
    simp
  have hxc : isP a b c ha hab hbc (c + u - c) = false ↔ ¬ Z a b u := by
    have hsub : c + u - c = u := by omega
    rw [hsub, L1_below a b c ha hab hbc u (by omega), F1 a b ha hab,
        Nat.mod_eq_of_lt (by omega)]
    simp
  rw [isP_iff a b c ha hab hbc (c + u)]
  constructor
  · rintro ⟨_, h2, h3⟩
    have hnZ : ¬ Z a b u := hxc.mp (h3 (by omega))
    have hnZ2 : ¬ Z a b ((c % (a + b) + u + a) % (a + b)) := hxb.mp (h2 (by omega))
    exact ⟨⟨hua, hub, hnZ⟩, hnZ2⟩
  · rintro ⟨⟨_, _, hnZ⟩, hnZ2⟩
    refine ⟨fun _ => ?_, fun _ => hxb.mpr hnZ2, fun _ => hxc.mpr hnZ⟩
    -- Show `isP (c + u - a) = false` because `(c + u - a) - c = u - a ∈ Z ⊆ W`.
    by_contra hnotf
    have hpt : isP a b c ha hab hbc (c + u - a) = true := by
      cases h : isP a b c ha hab hbc (c + u - a) <;> simp_all
    have hmove := ((isP_iff a b c ha hab hbc (c + u - a)).mp hpt).2.2 (by omega)
    have hsub : c + u - a - c = u - a := by omega
    rw [hsub, L1_below a b c ha hab hbc (u - a) (by omega), F1 a b ha hab,
        Nat.mod_eq_of_lt (by omega)] at hmove
    have hodd : (u / a) % 2 = 1 := by unfold Z at hnZ; omega
    have hstep := div_sub_self_odd ha hua
    have hZua : Z a b (u - a) := ⟨by omega, by omega⟩
    simp [hZua] at hmove

/-! ## Section 3: Join Lemma and Exact Periodicity Criteria (Theorems A0, A1, A2) -/

/-- **Join Lemma.** For `P > c`, `W` is `P`-periodic iff no `h, h' < P` in `W` satisfy
`h' - h ∈ {P - a, P - b, P - c}`. -/
theorem join_lemma (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) {P : ℕ} (hP : c < P) :
    PurelyPeriodicP a b c ha hab hbc P ↔
      ∀ h h', h < P → h' < P →
        isP a b c ha hab hbc h = true → isP a b c ha hab hbc h' = true →
        h' ≠ h + (P - a) ∧ h' ≠ h + (P - b) ∧ h' ≠ h + (P - c) := by
  constructor
  · intro hper h h' hh hh' hph hph'
    have hnext : isP a b c ha hab hbc (h + P) = true := by rw [hper h]; exact hph
    obtain ⟨h1, h2, h3⟩ := (isP_iff a b c ha hab hbc (h + P)).mp hnext
    refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
    · have e : h + P - a = h' := by omega
      have hx := h1 (by omega); rw [e, hph'] at hx; simp at hx
    · have e : h + P - b = h' := by omega
      have hx := h2 (by omega); rw [e, hph'] at hx; simp at hx
    · have e : h + P - c = h' := by omega
      have hx := h3 (by omega); rw [e, hph'] at hx; simp at hx
  · intro hno
    let T (x : ℕ) : Bool := isP a b c ha hab hbc (x % P)
    have hstep : ∀ s, (s = a ∨ s = b ∨ s = c) →
        ∀ x, T x = true → s ≤ x → T (x - s) = false := by
      intro s hs x hTx hsx
      have hsP : s < P := by rcases hs with rfl | rfl | rfl <;> omega
      have hr : x % P < P := Nat.mod_lt x (by omega)
      dsimp only [T] at hTx ⊢
      by_cases hrs : s ≤ x % P
      · rw [sub_mod_of_le_mod (by omega) hrs]
        obtain ⟨h1, h2, h3⟩ := (isP_iff a b c ha hab hbc _).mp hTx
        rcases hs with rfl | rfl | rfl
        · exact h1 hrs
        · exact h2 hrs
        · exact h3 hrs
      · rw [sub_mod_of_mod_lt hsP.le hsx (by omega)]
        cases ht : isP a b c ha hab hbc (x % P + (P - s))
        · rfl
        · obtain ⟨n1, n2, n3⟩ := hno (x % P) (x % P + (P - s)) hr (by omega) hTx ht
          rcases hs with rfl | rfl | rfl
          · exact absurd rfl n1
          · exact absurd rfl n2
          · exact absurd rfl n3
    have heq : ∀ x, isP a b c ha hab hbc x = T x := by
      apply isP_unique a b c ha hab hbc T
      · intro x hTx
        exact ⟨hstep a (Or.inl rfl) x hTx,
               hstep b (Or.inr (Or.inl rfl)) x hTx,
               hstep c (Or.inr (Or.inr rfl)) x hTx⟩
      · intro x hTx
        dsimp only [T] at hTx ⊢
        have hx := Nat.div_add_mod' x P
        have hr : x % P < P := Nat.mod_lt x (by omega)
        have hnot : ¬ (isP a b c ha hab hbc (x % P) = true) := by simp [hTx]
        rw [isP_iff] at hnot
        by_cases h1 : a ≤ x % P ∧ isP a b c ha hab hbc (x % P - a) = true
        · left
          refine ⟨by omega, ?_⟩
          rw [sub_mod_of_le_mod (by omega) h1.1]; exact h1.2
        · by_cases h2 : b ≤ x % P ∧ isP a b c ha hab hbc (x % P - b) = true
          · right; left
            refine ⟨by omega, ?_⟩
            rw [sub_mod_of_le_mod (by omega) h2.1]; exact h2.2
          · right; right
            have h3 : c ≤ x % P ∧ isP a b c ha hab hbc (x % P - c) = true := by
              by_contra h3
              apply hnot
              refine ⟨fun ha' => ?_, fun hb' => ?_, fun hc' => ?_⟩
              · cases hv : isP a b c ha hab hbc (x % P - a); rfl; exact False.elim (h1 ⟨ha', hv⟩)
              · cases hv : isP a b c ha hab hbc (x % P - b); rfl; exact False.elim (h2 ⟨hb', hv⟩)
              · cases hv : isP a b c ha hab hbc (x % P - c); rfl; exact False.elim (h3 ⟨hc', hv⟩)
            refine ⟨by omega, ?_⟩
            rw [sub_mod_of_le_mod (by omega) h3.1]; exact h3.2
    intro x
    rw [heq (x + P), heq x]
    dsimp [T]
    rw [Nat.add_mod_right]

/-- **Theorem A0 (period `a + b`, for every `c > b`).**
`W` is `(a + b)`-periodic iff `ρ ∈ Θ_{a+b}`, removing the `c ≥ 2(a + b)` hypothesis of Lemma 54. -/
theorem period_ab_iff (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    PurelyPeriodicP a b c ha hab hbc (a + b) ↔ Theta_ab a b (c % (a + b)) := by
  constructor
  · intro hper
    -- First show `W x = W_B x` for all `x < a + b`, hence for all `x`.
    have hinit : ∀ x, x < a + b → isP a b c ha hab hbc x = isPB a b ha hab x := by
      intro x hx
      by_cases hxc : x < c
      · exact L1_below a b c ha hab hbc x hxc
      · rw [L1_gap a b c ha hab hbc (by omega) (by omega), F1 a b ha hab,
            Nat.mod_eq_of_lt hx]
        symm
        rw [decide_eq_false_iff_not]
        unfold Z
        omega
    have hall : ∀ x, isP a b c ha hab hbc x = isPB a b ha hab x := by
      intro x
      have hper' : ∀ k r, isP a b c ha hab hbc (r + k * (a + b)) = isP a b c ha hab hbc r := by
        intro k r
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
      have hdiv : x = x % (a + b) + (x / (a + b)) * (a + b) := by
        have := Nat.div_add_mod' x (a + b); omega
      rw [hdiv, hper', hinit (x % (a + b)) (Nat.mod_lt x (by omega)),
          F1 a b ha hab, F1 a b ha hab, Nat.add_mul_mod_self_right, Nat.mod_mod]
    intro z hz hZz hZzr
    have h1 : isP a b c ha hab hbc z = true := by
      rw [hall, F1 a b ha hab, Nat.mod_eq_of_lt hz]; exact decide_eq_true hZz
    have h2 : isP a b c ha hab hbc (z + c) = true := by
      rw [hall, F1 a b ha hab]
      have hmod : (z + c) % (a + b) = (z + c % (a + b)) % (a + b) := by
        rw [Nat.add_mod_mod]
      rw [hmod]
      exact decide_eq_true hZzr
    have hbad := ((isP_iff a b c ha hab hbc (z + c)).mp h2).2.2 (by omega)
    have hsub : z + c - c = z := by omega
    rw [hsub, h1] at hbad
    contradiction
  · intro hTh
    -- Show `isP = isPB`, which is `(a + b)`-periodic.
    have hall : ∀ x, isP a b c ha hab hbc x = isPB a b ha hab x := by
      apply isP_unique a b c ha hab hbc (isPB a b ha hab)
      · intro x hx
        obtain ⟨h1, h2⟩ := (isPB_iff a b ha hab x).mp hx
        refine ⟨h1, h2, fun hcx => ?_⟩
        rw [F1 a b ha hab] at hx ⊢
        have hZx : Z a b (x % (a + b)) := of_decide_eq_true hx
        simp only [decide_eq_false_iff_not]
        intro hZsub
        have hmod : ((x - c) % (a + b) + c % (a + b)) % (a + b) = x % (a + b) := by
          rw [← Nat.add_mod, Nat.sub_add_cancel hcx]
        have hcontra := hTh ((x - c) % (a + b)) (Nat.mod_lt _ (by omega)) hZsub
        rw [hmod] at hcontra
        exact hcontra hZx
      · intro x hx
        have hnot : ¬ (isPB a b ha hab x = true) := by simp [hx]
        rw [isPB_iff] at hnot
        by_cases h1 : a ≤ x ∧ isPB a b ha hab (x - a) = true
        · exact Or.inl h1
        · right; left
          by_contra h2
          apply hnot
          refine ⟨fun ha' => ?_, fun hb' => ?_⟩
          · cases hv : isPB a b ha hab (x - a); rfl; exact False.elim (h1 ⟨ha', hv⟩)
          · cases hv : isPB a b ha hab (x - b); rfl; exact False.elim (h2 ⟨hb', hv⟩)
    intro x
    rw [hall, hall, F1 a b ha hab, F1 a b ha hab, Nat.add_mod_right]

/-- **Theorem A1 (period `c + a`).** For every `1 ≤ a < b < c`, `W` is `(c + a)`-periodic iff `ρ ∈ Θ_{c+a}`. -/
theorem period_ca_iff (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    PurelyPeriodicP a b c ha hab hbc (c + a) ↔ Theta_ca a b (c % (a + b)) := by
  rw [join_lemma a b c ha hab hbc (by omega)]
  have hPa : c + a - a = c := by omega
  have hPb : c + a - b = c - delta a b := by unfold delta; omega
  have hPc : c + a - c = a := by omega
  constructor
  · intro hno h hh hZh z hz hZz heq
    have hlt1 : h < c := by unfold delta at hh; omega
    have hlt2 : h + (c - delta a b) < c := by unfold delta at hh ⊢; omega
    have hph : isP a b c ha hab hbc h = true := by
      rw [L1_below a b c ha hab hbc h hlt1, F1 a b ha hab, Nat.mod_eq_of_lt (by unfold delta at hh; omega)]
      exact decide_eq_true hZh
    have hmod2 : (h + (c - delta a b)) % (a + b) = z := by
      have h1 : (h + (c - delta a b) + delta a b) % (a + b) = (h + c % (a + b)) % (a + b) := by
        have : h + (c - delta a b) + delta a b = h + c := by unfold delta; omega
        rw [this, Nat.add_mod_mod]
      rw [← heq] at h1
      -- Cancel `+ delta a b` mod `a + b`
      have hsub : ((h + (c - delta a b)) % (a + b) + delta a b) % (a + b) =
          (z + delta a b) % (a + b) := by
        rw [Nat.add_mod (h + (c - delta a b)) (delta a b)] at h1
        rw [Nat.add_mod ((h + (c - delta a b)) % (a + b)) (delta a b), Nat.mod_mod]
        exact h1
      exact add_mod_cancel (Nat.mod_lt _ (by omega)) hz hsub
    have hph' : isP a b c ha hab hbc (h + (c - delta a b)) = true := by
      rw [L1_below a b c ha hab hbc _ hlt2, F1 a b ha hab, hmod2]
      exact decide_eq_true hZz
    have := (hno h (h + (c - delta a b)) (by omega) (by omega) hph hph').2.1
    rw [hPb] at this
    exact this rfl
  · intro hTh h h' hh hh' hph hph'
    -- `h' = h + c` and `h' = h + a` are already moves in `S`, impossible inside `W`.
    refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
    · have hbad := ((isP_iff a b c ha hab hbc h').mp hph').2.2 (by omega)
      have : h' - c = h := by omega
      rw [this, hph] at hbad; contradiction
    · -- Only `h' = h + (c - delta a b)` remains.
      have hh'_lt : h' < c := by
        by_contra hge
        have := L1_gap a b c ha hab hbc (by omega) hh'
        rw [this] at hph'; contradiction
      have hh_lt : h < delta a b := by unfold delta at hPb ⊢; omega
      have hZh : Z a b h := by
        rw [L1_below a b c ha hab hbc h (by unfold delta at hh_lt; omega),
            F1 a b ha hab, Nat.mod_eq_of_lt (by unfold delta at hh_lt; omega)] at hph
        exact of_decide_eq_true hph
      have hZh' : Z a b (h' % (a + b)) := by
        rw [L1_below a b c ha hab hbc h' hh'_lt, F1 a b ha hab] at hph'
        exact of_decide_eq_true hph'
      apply hTh h hh_lt hZh (h' % (a + b)) (Nat.mod_lt _ (by omega)) hZh'
      have hsum : h' + delta a b = h + c := by unfold delta at hPb ⊢; omega
      calc (h' % (a + b) + delta a b) % (a + b)
          = (h' + delta a b) % (a + b) := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        _ = (h + c) % (a + b) := by rw [hsum]
        _ = (h + c % (a + b)) % (a + b) := (Nat.add_mod_mod _ _ _).symm
    · have hbad := ((isP_iff a b c ha hab hbc h').mp hph').1 (by omega)
      have : h' - a = h := by omega
      rw [this, hph] at hbad; contradiction

/-- Condition `N1`: `∀ u ∈ Λ, (ρ + u + a) % (a + b) ∈ Z`. -/
def N1 (a b rho : ℕ) : Prop :=
  ∀ u, Lambda a b u → Z a b ((rho + u + a) % (a + b))

/-- Explicit cyclic-interval description of `Θ_{c+b}` (`N1`). -/
def ExplicitTheta_cb (a b rho : ℕ) : Prop :=
  if eta a b % 2 = 0 then
    ∀ j, 1 ≤ j → j ≤ eps a b → Z a b ((rho + (a + b) - j) % (a + b))
  else
    ∀ j, eps a b + 1 ≤ j → j ≤ a → Z a b ((rho + (a + b) - j) % (a + b))

/-- **F4 / Explicit Equivalence:** `N1 ↔ ExplicitTheta_cb`. -/
theorem N1_iff_explicit (a b rho : ℕ) (ha : 0 < a) (hab : a < b) :
    N1 a b rho ↔ ExplicitTheta_cb a b rho := by
  have hde := eta_mul_add_eps a b
  have heps := eps_lt_a (b := b) ha
  have hdb : delta a b + a = b := by unfold delta; omega
  have hm : (eta a b + 1) * a = eta a b * a + a := Nat.succ_mul _ _
  unfold N1 ExplicitTheta_cb Lambda
  split_ifs with heven
  · constructor
    · intro hN j hj1 hj2
      have hZ := hN ((eta a b + 1) * a + (eps a b - j)) ⟨by omega, by omega⟩
      have hEq : rho + ((eta a b + 1) * a + (eps a b - j)) + a = rho + (a + b) - j := by omega
      rwa [hEq] at hZ
    · rintro hE u ⟨h1, h2⟩
      have hZ := hE ((eta a b + 1) * a + eps a b - u) (by omega) (by omega)
      have hEq : rho + u + a = rho + (a + b) - ((eta a b + 1) * a + eps a b - u) := by omega
      rwa [hEq]
  · constructor
    · intro hN j hj1 hj2
      have hZ := hN ((eta a b + 1) * a + eps a b - j) ⟨by omega, by omega⟩
      have hEq : rho + ((eta a b + 1) * a + eps a b - j) + a = rho + (a + b) - j := by omega
      rwa [hEq] at hZ
    · rintro hE u ⟨h1, h2⟩
      have hZ := hE ((eta a b + 1) * a + eps a b - u) (by omega) (by omega)
      have hEq : rho + u + a = rho + (a + b) - ((eta a b + 1) * a + eps a b - u) := by omega
      rwa [hEq]

/-- **Theorem A2(i):** `W` is `(c + b)`-periodic iff `N1`. -/
lemma period_cb_iff_N1 (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    PurelyPeriodicP a b c ha hab hbc (c + b) ↔ N1 a b (c % (a + b)) := by
  rw [join_lemma a b c ha hab hbc (by omega)]
  have hPa : c + b - a = c + delta a b := by unfold delta; omega
  have hPb : c + b - b = c := by omega
  have hPc : c + b - c = b := by omega
  constructor
  · intro hno u hu
    have hD := Lambda_subset_D ha hab hu
    have huI := (Lambda_iff_interval ha hab).mp hu
    have hnot : isP a b c ha hab hbc (c + u) = false := by
      by_contra hnotf
      have hpt : isP a b c ha hab hbc (c + u) = true := by
        cases hv : isP a b c ha hab hbc (c + u) <;> simp_all
      have hdb : delta a b + a = b := by unfold delta; omega
      set h := u - delta a b with hh_def
      have hh : h < a := by omega
      have hph : isP a b c ha hab hbc h = true := by
        rw [L1_below a b c ha hab hbc h (by omega), F1 a b ha hab, Nat.mod_eq_of_lt (by omega)]
        exact decide_eq_true (Z_of_lt_a hab hh)
      have hbad := (hno h (c + u) (by omega) (by omega) hph hpt).1
      rw [hPa] at hbad
      exact hbad (by omega)
    by_contra hnZ
    have hpt := (L2 a b c ha hab hbc hD.1 hD.2.1).mpr ⟨hD, hnZ⟩
    rw [hnot] at hpt
    contradiction
  · intro hN h h' hh hh' hph hph'
    refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
    · -- `h' = h + (c + delta a b) ∈ [c + delta, c + b)`
      have hdb : delta a b + a = b := by unfold delta; omega
      have hh_lt : h < a := by omega
      set u := h + delta a b with hu_def
      have h'_eq : h' = c + u := by omega
      by_cases hua : a ≤ u
      · have hub : u < b := by omega
        have hL2 := (L2 a b c ha hab hbc hua hub).mp (by rwa [← h'_eq])
        have hLam : Lambda a b u := (Lambda_iff_interval ha hab).mpr ⟨by omega, hub, hL2.1.2.2⟩
        exact hL2.2 (hN u hLam)
      · have := L1_gap a b c ha hab hbc (by omega) (by omega : h' < c + a)
        rw [this] at hph'; contradiction
    · have hbad := ((isP_iff a b c ha hab hbc h').mp hph').2.2 (by omega)
      have : h' - c = h := by omega
      rw [this, hph] at hbad; contradiction
    · have hbad := ((isP_iff a b c ha hab hbc h').mp hph').2.1 (by omega)
      have : h' - b = h := by omega
      rw [this, hph] at hbad; contradiction

/-- **Theorem A2(ii)–(iv):** `Theta_cb ↔ N1` for all `0 < a < b` and all `rho`. -/
theorem Theta_cb_iff_N1 (a b rho : ℕ) (ha : 0 < a) (hab : a < b) :
    Theta_cb a b rho ↔ N1 a b rho := by
  have hde := eta_mul_add_eps a b
  have heps := eps_lt_a (b := b) ha
  have hdb : delta a b + a = b := by unfold delta; omega
  have hm : (eta a b + 1) * a = eta a b * a + a := Nat.succ_mul _ _
  constructor
  · -- (ii) `Theta_cb → N1`
    rintro ⟨hT2a, hT2b⟩ l hl
    by_contra hnZ
    have hnotZ : ¬ Z a b ((rho + l) % (a + b)) := hT2a l hl
    have hmod : ((rho + l) % (a + b) + a) % (a + b) = (rho + l + a) % (a + b) := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hLam : Lambda a b ((rho + l) % (a + b)) :=
      (Lambda_iff_double_outside ha hab (Nat.mod_lt _ (by omega))).mpr ⟨hnotZ, by rwa [hmod]⟩
    exact hT2b l (Lambda_subset_D ha hab hl) hLam
  · -- (iii) & (iv) `N1 → Theta_cb`
    intro hN
    constructor
    · -- (T2a)
      intro l hl hZ
      have h1 := F2 ha hZ
      have hmod : ((rho + l) % (a + b) + a) % (a + b) = (rho + l + a) % (a + b) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [hmod] at h1
      exact h1 (hN l hl)
    · -- (T2b)
      intro d hd hLam
      have hE := (N1_iff_explicit a b rho ha hab).mp hN
      have hn : 0 < a + b := by omega
      obtain ⟨L, hL⟩ : ∃ L, L = (rho + d) % (a + b) := ⟨_, rfl⟩
      rw [← hL] at hLam
      have hl_lt : L < a + b := by rw [hL]; exact Nat.mod_lt _ hn
      obtain ⟨hda, hdb', hnZd⟩ := hd
      -- `(ρ + (a + b) - j) % (a + b)` is pinned down by its sum with `d + j`.
      have hR : ∀ j V, j ≤ a → V < a + b →
          (V + (d + j) = L ∨ V + (d + j) = L + (a + b)) →
          (rho + (a + b) - j) % (a + b) = V := by
        intro j V hj hV hVeq
        apply add_mod_cancel (Nat.mod_lt _ hn) hV (d := d + j)
        have e1 : ((rho + (a + b) - j) % (a + b) + (d + j)) % (a + b) = L := by
          rw [Nat.mod_add_mod]
          have : rho + (a + b) - j + (d + j) = rho + d + (a + b) := by omega
          rw [this, Nat.add_mod_right, hL]
        have e2 : (V + (d + j)) % (a + b) = L := by
          rcases hVeq with h | h
          · rw [h, Nat.mod_eq_of_lt hl_lt]
          · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hl_lt]
        rw [e1, e2]
      -- With `K` even and `L < K a + d + j ≤ L + a`, the residue lies in `[b, a + b)` (`K = 0`)
      -- or in the odd block `[(K - 1) a, K a)` (`K ≥ 2`); either way it is outside `Z`.
      have hkill : ∀ j K, j ≤ a → K % 2 = 0 → L < K * a + d + j → K * a + d + j ≤ L + a →
          ¬ Z a b ((rho + (a + b) - j) % (a + b)) := by
        intro j K hj hK h1 h2
        rcases Nat.eq_zero_or_pos K with hK0 | hKpos
        · subst hK0
          rw [hR j (a + b + L - d - j) hj (by omega) (Or.inr (by omega))]
          rintro ⟨hlt, _⟩
          omega
        · have hK1 : (K - 1) * a + a = K * a := by
            rw [← Nat.add_one_mul, Nat.sub_add_cancel hKpos]
          rw [hR j (L - d - j) hj (by omega) (Or.inl (by omega))]
          rintro ⟨_, hpar⟩
          have q1 : K - 1 ≤ (L - d - j) / a := (Nat.le_div_iff_mul_le ha).mpr (by omega)
          have q2 : (L - d - j) / a < K := (Nat.div_lt_iff_lt_mul ha).mpr (by omega)
          omega
      have hdq := Nat.div_add_mod' d a
      have hs_lt : d % a < a := Nat.mod_lt d ha
      have hq_odd : (d / a) % 2 = 1 := by unfold Z at hnZd; omega
      have hq_pos : 1 ≤ d / a := (Nat.le_div_iff_mul_le ha).mpr (by omega)
      have hq_lt : d / a < eta a b + 2 :=
        (Nat.div_lt_iff_lt_mul ha).mpr (by rw [Nat.add_mul]; omega)
      unfold Lambda at hLam
      unfold ExplicitTheta_cb at hE
      split_ifs at hLam hE with heven
      · obtain ⟨hl1, hl2⟩ := hLam
        have hK : (eta a b + 1 - d / a) * a + d / a * a = (eta a b + 1) * a := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        exact hkill (max 1 (L + 1 - (eta a b + 1) * a - d % a)) (eta a b + 1 - d / a)
          (by omega) (by omega) (by omega) (by omega) (hE _ (by omega) (by omega))
      · obtain ⟨hl1, hl2⟩ := hLam
        have hK : (eta a b - d / a) * a + d / a * a = eta a b * a := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        exact hkill (max (eps a b + 1) (L + 1 - eta a b * a - d % a)) (eta a b - d / a)
          (by omega) (by omega) (by omega) (by omega) (hE _ (by omega) (by omega))

/-- **Theorem A2 (period `c + b`).** For every `1 ≤ a < b < c`, `W` is `(c + b)`-periodic iff `ρ ∈ Θ_{c+b}`. -/
theorem period_cb_iff (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    PurelyPeriodicP a b c ha hab hbc (c + b) ↔ Theta_cb a b (c % (a + b)) :=
  (period_cb_iff_N1 a b c ha hab hbc).trans (Theta_cb_iff_N1 a b (c % (a + b)) ha hab).symm

/-- Explicit cyclic-interval formula for `Θ_{c+b}`. -/
theorem Theta_cb_iff_explicit (a b rho : ℕ) (ha : 0 < a) (hab : a < b) :
    Theta_cb a b rho ↔ ExplicitTheta_cb a b rho :=
  (Theta_cb_iff_N1 a b rho ha hab).trans (N1_iff_explicit a b rho ha hab)

/-! ## Section 4: Main Theorem (Manabe Conjecture 57) and Partial Period Exclusions -/

/-- **Main Theorem (Conjecture 57 of Manabe, `arXiv:2609.05358v2`, strengthened).**
For every `1 ≤ a < b < c`, if the Sprague–Grundy sequence `G_S` is purely periodic with period
`a + b`, `c + a`, or `c + b` (not necessarily the least period, and without requiring `a ≥ 2`,
`gcd(a, b, c) = 1`, or `c ≠ a + b`), then the angle `ρ = c % (a + b)` belongs to the
corresponding admissible set `Θ_{a+b}`, `Θ_{c+a}`, or `Θ_{c+b}`. -/
theorem manabe_conjecture_57 (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (PurelyPeriodicG a b c ha hab hbc (a + b) → Theta_ab a b (c % (a + b))) ∧
    (PurelyPeriodicG a b c ha hab hbc (c + a) → Theta_ca a b (c % (a + b))) ∧
    (PurelyPeriodicG a b c ha hab hbc (c + b) → Theta_cb a b (c % (a + b))) :=
  ⟨fun h => (period_ab_iff a b c ha hab hbc).mp (purelyPeriodicP_of_G a b c ha hab hbc h),
   fun h => (period_ca_iff a b c ha hab hbc).mp (purelyPeriodicP_of_G a b c ha hab hbc h),
   fun h => (period_cb_iff a b c ha hab hbc).mp (purelyPeriodicP_of_G a b c ha hab hbc h)⟩

/-- **Partial period exclusion 1:** No pure `P`-position period `p` lies in `(c - a, c + a)`. -/
theorem no_period_in_open_interval (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {p : ℕ} (h1 : c - a < p) (h2 : p < c + a) :
    ¬ PurelyPeriodicP a b c ha hab hbc p := by
  intro hper
  by_cases hpc : p < c
  · -- Take `r = c - p ∈ [0, a)`; then `r ∈ W`, so `r + p = c ∈ W`, contradicting `L1_gap`.
    set r := c - p
    have hr : r < a := by omega
    have hpr : isP a b c ha hab hbc r = true := by
      rw [L1_below a b c ha hab hbc r (by omega), F1 a b ha hab, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_true (Z_of_lt_a hab hr)
    have hpc' : isP a b c ha hab hbc c = true := by
      have e := hper r
      rw [show r + p = c by omega] at e
      rw [e]; exact hpr
    have := L1_gap a b c ha hab hbc le_rfl (by omega)
    rw [this] at hpc'; contradiction
  · -- `c ≤ p < c + a`: `0 ∈ W`, so `p = 0 + p ∈ W`, contradicting `L1_gap`.
    have hp0 : isP a b c ha hab hbc 0 = true := by
      rw [L1_below a b c ha hab hbc 0 (by omega), F1 a b ha hab, Nat.zero_mod]
      exact decide_eq_true (Z_of_lt_a hab ha)
    have hpp : isP a b c ha hab hbc p = true := by
      simpa using (hper 0).trans hp0
    have := L1_gap a b c ha hab hbc (by omega) h2
    rw [this] at hpp; contradiction

/-- If `f` has period `g ∣ p` on `[0, M)` and period `p ≤ M` on `[0, M + p)`, then
`f y = f (y % g)` on `[0, M + p)`. -/
lemma mod_period_of_prefix {f : ℕ → Bool} {g p M : ℕ} (hg : 0 < g) (hgp : g ∣ p) (hpM : p ≤ M)
    (hpre : ∀ x, x + g < M → f (x + g) = f x)
    (hper : ∀ x, x + p < M + p → f (x + p) = f x) :
    ∀ y, y < M + p → f y = f (y % g) := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro hy
    by_cases hyg : y < g
    · rw [Nat.mod_eq_of_lt hyg]
    · by_cases hyM : y < M
      · have h1 := hpre (y - g) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at h1
        have h2 := Nat.add_mod_right (y - g) g
        rw [Nat.sub_add_cancel (by omega)] at h2
        rw [h1, ih (y - g) (by omega) (by omega), h2]
      · obtain ⟨k, hk⟩ := hgp
        have h1 := hper (y - p) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at h1
        have h2 : y % g = (y - p) % g := by
          have := Nat.add_mul_mod_self_left (y - p) g k
          rw [← hk, Nat.sub_add_cancel (by omega)] at this
          exact this
        rw [h1, ih (y - p) (by omega) (by omega), h2]

/-- Fine–Wilf periodicity lemma for a function `f : ℕ → Bool` on `[0, L)` with periods `p, q > 0`
and `L ≥ p + q - gcd(p, q)`. -/
lemma fine_wilf_prefix {f : ℕ → Bool} {p q L : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hL : p + q - Nat.gcd p q ≤ L)
    (hper_p : ∀ x, x + p < L → f (x + p) = f x)
    (hper_q : ∀ x, x + q < L → f (x + q) = f x) :
    ∀ x, x + Nat.gcd p q < L → f (x + Nat.gcd p q) = f x := by
  induction hsum : p + q using Nat.strong_induction_on generalizing p q L with
  | h s ih =>
    by_cases heq : p = q
    · subst heq
      simpa [Nat.gcd_self] using hper_p
    · by_cases hlt : p < q
      · -- Replace `(p, q)` by `(p, q - p)` on `[0, L - p)`.
        have hqp : 0 < q - p := by omega
        have hgcd : Nat.gcd p (q - p) = Nat.gcd p q := by
          have := Nat.gcd_sub_self_right (m := p) (n := q) (by omega)
          simpa [Nat.gcd_comm] using this
        have hper_qp : ∀ x, x + (q - p) < L - p → f (x + (q - p)) = f x := by
          intro x hx
          have h1 : f (x + q) = f (x + (q - p)) := by
            have : x + (q - p) + p = x + q := by omega
            rw [← this]; exact hper_p (x + (q - p)) (by omega)
          rw [← h1, hper_q x (by omega)]
        have hrec := ih (p + (q - p)) (by omega) (p := p) (q := q - p) (L := L - p)
          hp hqp (by rw [hgcd]; omega) (fun x hx => hper_p x (by omega)) hper_qp rfl
        rw [hgcd] at hrec
        have hg_le : Nat.gcd p q ≤ q - p :=
          Nat.le_of_dvd (by omega) (Nat.dvd_sub (Nat.gcd_dvd_right p q) (Nat.gcd_dvd_left p q))
        have hmod := mod_period_of_prefix (f := f) (Nat.gcd_pos_of_pos_left q hp)
          (Nat.gcd_dvd_left p q) (by omega) hrec (fun x hx => hper_p x (by omega))
        intro x hx
        rw [hmod (x + Nat.gcd p q) (by omega), hmod x (by omega), Nat.add_mod_right]
      · -- Symmetric case `q < p`
        have hlt' : q < p := by omega
        have hpq : 0 < p - q := by omega
        have hgcd : Nat.gcd (p - q) q = Nat.gcd p q :=
          Nat.gcd_sub_self_left (m := q) (n := p) (by omega)
        have hper_pq : ∀ x, x + (p - q) < L - q → f (x + (p - q)) = f x := by
          intro x hx
          have h1 : f (x + p) = f (x + (p - q)) := by
            have : x + (p - q) + q = x + p := by omega
            rw [← this]; exact hper_q (x + (p - q)) (by omega)
          rw [← h1, hper_p x (by omega)]
        have hrec := ih ((p - q) + q) (by omega) (p := p - q) (q := q) (L := L - q)
          hpq hq (by rw [hgcd]; omega) hper_pq (fun x hx => hper_q x (by omega)) rfl
        rw [hgcd] at hrec
        have hg_le : Nat.gcd p q ≤ p - q :=
          Nat.le_of_dvd (by omega) (Nat.dvd_sub (Nat.gcd_dvd_left p q) (Nat.gcd_dvd_right p q))
        have hmod := mod_period_of_prefix (f := f) (Nat.gcd_pos_of_pos_right p hq)
          (Nat.gcd_dvd_right p q) (by omega) hrec (fun x hx => hper_q x (by omega))
        intro x hx
        rw [hmod (x + Nat.gcd p q) (by omega), hmod x (by omega), Nat.add_mod_right]

/-- **Partial period exclusion 2 (Extended Lemma 54, including `a + b ∣ p`).**
If `W` has a pure period `p > 0` with `c ≥ p + (a + b) - gcd(p, a + b)`, then
`W` is `(a + b)`-periodic and `ρ ∈ Θ_{a+b}`. -/
theorem fine_wilf_period_implies_Theta_ab (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {p : ℕ} (hp : 0 < p) (hfw : p + (a + b) - Nat.gcd p (a + b) ≤ c)
    (hper : PurelyPeriodicP a b c ha hab hbc p) :
    Theta_ab a b (c % (a + b)) := by
  have hn : 0 < a + b := by omega
  set g := Nat.gcd p (a + b)
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left (a + b) hp
  have hg_dvd_p : g ∣ p := Nat.gcd_dvd_left p (a + b)
  have hg_dvd_n : g ∣ a + b := Nat.gcd_dvd_right p (a + b)
  have hp_le_c : p ≤ c := by
    have : g ≤ a + b := Nat.le_of_dvd hn hg_dvd_n
    omega
  -- `isP` on `[0, c)` has periods `p` and `a + b`, hence period `g`.
  have hper_g_prefix : ∀ x, x + g < c → isP a b c ha hab hbc (x + g) = isP a b c ha hab hbc x := by
    apply fine_wilf_prefix hp hn hfw
    · intro x _; exact hper x
    · intro x hx
      rw [L1_below a b c ha hab hbc (x + (a + b)) hx,
          L1_below a b c ha hab hbc x (by omega),
          F1 a b ha hab, F1 a b ha hab, Nat.add_mod_right]
  -- Since `g ∣ p` and `p ≤ c`, repeating a `g`-periodic block of length `p` is `g`-periodic on all `ℕ`.
  have hper_g_lt_p : ∀ r, r < p → isP a b c ha hab hbc r = isP a b c ha hab hbc (r % g) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hrp
      by_cases hrg : r < g
      · rw [Nat.mod_eq_of_lt hrg]
      · have h1 : isP a b c ha hab hbc r = isP a b c ha hab hbc (r - g) := by
          have := hper_g_prefix (r - g) (by omega)
          rwa [Nat.sub_add_cancel (by omega)] at this
        have h2 : (r - g) % g = r % g := by
          have := Nat.add_mod_right (r - g) g
          rw [Nat.sub_add_cancel (by omega)] at this
          exact this.symm
        rw [h1, ih (r - g) (by omega) (by omega), h2]
  have hper_p_mod : ∀ x, isP a b c ha hab hbc x = isP a b c ha hab hbc (x % p) := by
    intro x
    have hstep : ∀ k r, isP a b c ha hab hbc (r + k * p) = isP a b c ha hab hbc r := by
      intro k r
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
    have hdiv : x = x % p + (x / p) * p := by
      have := Nat.div_add_mod' x p; omega
    rw [hdiv, hstep, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hper_g_all : ∀ x, isP a b c ha hab hbc x = isP a b c ha hab hbc (x % g) := by
    intro x
    rw [hper_p_mod x, hper_g_lt_p (x % p) (Nat.mod_lt x hp), Nat.mod_mod_of_dvd x hg_dvd_p]
  have hper_n : PurelyPeriodicP a b c ha hab hbc (a + b) := by
    intro x
    rw [hper_g_all (x + (a + b)), hper_g_all x]
    rcases hg_dvd_n with ⟨k, hk⟩
    rw [hk, Nat.add_mul_mod_self_left]
  exact (period_ab_iff a b c ha hab hbc).mp hper_n

end ManabeSubtraction

#print axioms ManabeSubtraction.period_ab_iff
#print axioms ManabeSubtraction.period_ca_iff
#print axioms ManabeSubtraction.period_cb_iff
#print axioms ManabeSubtraction.Theta_cb_iff_explicit
#print axioms ManabeSubtraction.manabe_conjecture_57
#print axioms ManabeSubtraction.no_period_in_open_interval
#print axioms ManabeSubtraction.fine_wilf_period_implies_Theta_ab
