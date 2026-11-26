import Mathlib

/-!
# Proof of Rahid Zaman's OEIS A395348 Conjecture

This module proves Rahid Zaman's recurrence conjecture on OEIS A395348 (Nov 18, 2026)
for the two-color greedy spiral queen game on `ℤ²`:
for every `n ≥ 2`, `a (n + 4) = a n + 8 * n + 34`, where `a n` (OEIS A395348) is the
spiral label of the `n`-th Black queen and `b n` (OEIS A395349) is the spiral label of
the `n`-th Red queen.

## Main Theorems

* `isGreedyGame_pred`: the explicit closed-form sequences `predBlackLabel` and
  `predRedLabel` satisfy the exact greedy two-color spiral queen specification `IsGreedyGame`.
* `isGreedyGame_unique`: the greedy game uniquely determines `(a, b)`.
* `zaman_A395348_recurrence`: for any `(a, b)` satisfying `IsGreedyGame a b` and every
  `n ≥ 2`, `a (n + 4) = a n + 8 * n + 34`.
-/

namespace ZamanA395348

/-! ### Section 1: Standard square spiral on `ℤ²` -/

/-- Structural-recursive helper computing the ring radius `r ≥ 1` with `k < (2r + 1)^2`. -/
def spiralRingAux (k : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | fuel + 1, r => if k < (2 * r + 1) ^ 2 then r else spiralRingAux k fuel (r + 1)

/-- Ring radius of spiral label `k`: `0` for `k = 0`, and `r ≥ 1` with `(2r - 1)^2 ≤ k < (2r + 1)^2`. -/
def spiralRing (k : ℕ) : ℕ :=
  if k = 0 then 0 else spiralRingAux k k 1

/-- Coordinates on ring `r ≥ 1`, edge `e ∈ {0, 1, 2, 3}`, offset `t < 2r`. -/
def ringEdgeXY (r e t : ℕ) : ℤ × ℤ :=
  let rZ : ℤ := (r : ℤ)
  let tZ : ℤ := (t : ℤ)
  if e = 0 then (rZ, 1 - rZ + tZ)
  else if e = 1 then (rZ - 1 - tZ, rZ)
  else if e = 2 then (-rZ, rZ - 1 - tZ)
  else (1 - rZ + tZ, -rZ)

/-- Coordinates `(x, y) ∈ ℤ²` of spiral label `k ≥ 0` (OEIS A308884 / A274641). -/
def spiralXY (k : ℕ) : ℤ × ℤ :=
  if k = 0 then (0, 0)
  else
    let r : ℕ := spiralRing k
    let idx : ℕ := k - (2 * r - 1) ^ 2
    ringEdgeXY r (idx / (2 * r)) (idx % (2 * r))

/-- Two lattice cells attack each other as chess queens (same row, column, or diagonal). -/
def attacks (p q : ℤ × ℤ) : Prop :=
  p.1 = q.1 ∨ p.2 = q.2 ∨ p.1 + p.2 = q.1 + q.2 ∨ p.1 - p.2 = q.1 - q.2

instance (p q : ℤ × ℤ) : Decidable (attacks p q) := by
  unfold attacks; infer_instance

/-- Exact greedy two-color spiral queen game specification (OEIS A395348 & A395349). -/
def IsGreedyGame (a b : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    -- Black's turn `n`: `a n` is the least `k` not occupied by Black `0..n-1` and not attacked by Red `0..n-1`
    ((∀ i < n, a n ≠ a i) ∧ (∀ i < n, ¬ attacks (spiralXY (a n)) (spiralXY (b i))) ∧
      ∀ k < a n, (∃ i < n, k = a i) ∨ (∃ i < n, attacks (spiralXY k) (spiralXY (b i)))) ∧
    -- Red's turn `n`: `b n` is the least `k` not occupied by Red `0..n-1` and not attacked by Black `0..n`
    ((∀ i < n, b n ≠ b i) ∧ (∀ i ≤ n, ¬ attacks (spiralXY (b n)) (spiralXY (a i))) ∧
      ∀ k < b n, (∃ i < n, k = b i) ∨ (∃ i ≤ n, attacks (spiralXY k) (spiralXY (a i))))

/-! ### Section 2: Predicted closed-form coordinates and labels -/

/-- Predicted Black queen coordinates `B(n)` for every round `n ≥ 0`. -/
def predBlack (n : ℕ) : ℤ × ℤ :=
  if n < 4 then
    match n with
    | 0 => (0, 0)
    | 1 => (1, 1)
    | 2 => (-2, 0)
    | _ => (3, 1)
  else
    let h : ℤ := (((n - 4) / 4 : ℕ) : ℤ)
    match (n - 4) % 4 with
    | 0 => (-(2 * h + 3), 1)
    | 1 => (2 * h + 4, 0)
    | 2 => (-(2 * h + 4), 0)
    | _ => (2 * h + 5, 1)

/-- Predicted Red queen coordinates `R(n)` for every round `n ≥ 0`. -/
def predRed (n : ℕ) : ℤ × ℤ :=
  if n < 4 then
    match n with
    | 0 => (2, -1)
    | 1 => (-1, 2)
    | 2 => (-1, -2)
    | _ => (2, 3)
  else
    let h : ℤ := (((n - 4) / 4 : ℕ) : ℤ)
    match (n - 4) % 4 with
    | 0 => (2, -(2 * h + 3))
    | 1 => (-1, 2 * h + 4)
    | 2 => (-1, -(2 * h + 4))
    | _ => (2, 2 * h + 5)

/-- Predicted Black queen spiral label `a(n)` for every round `n ≥ 0`. -/
def predBlackLabel (n : ℕ) : ℕ :=
  if n < 4 then
    match n with
    | 0 => 0
    | 1 => 2
    | 2 => 18
    | _ => 28
  else
    let h := (n - 4) / 4
    match (n - 4) % 4 with
    | 0 => let r := 2 * h + 3; 4 * r * r + r - 1
    | 1 => let r := 2 * h + 4; 4 * r * r - 3 * r
    | 2 => let r := 2 * h + 4; 4 * r * r + r
    | _ => let r := 2 * h + 5; 4 * r * r - 3 * r + 1

/-- Predicted Red queen spiral label `b(n)` for every round `n ≥ 0`. -/
def predRedLabel (n : ℕ) : ℕ :=
  if n < 4 then
    match n with
    | 0 => 9
    | 1 => 15
    | 2 => 21
    | _ => 31
  else
    let h := (n - 4) / 4
    match (n - 4) % 4 with
    | 0 => let r := 2 * h + 3; 4 * r * r + 3 * r + 2
    | 1 => let r := 2 * h + 4; 4 * r * r - r + 1
    | 2 => let r := 2 * h + 4; 4 * r * r + 3 * r - 1
    | _ => let r := 2 * h + 5; 4 * r * r - r - 2

/-! ### Section 3: Spiral coordinate lemmas -/

private lemma spiralRingAux_eq {k r : ℕ} (hlo : (2 * r - 1) ^ 2 ≤ k) (hhi : k < (2 * r + 1) ^ 2) :
    ∀ (fuel r₀ : ℕ), 1 ≤ r₀ → r₀ ≤ r → r - r₀ ≤ fuel → spiralRingAux k fuel r₀ = r := by
  intro fuel
  induction fuel with
  | zero =>
    intro r₀ _ hle hdiff
    unfold spiralRingAux; omega
  | succ fuel ih =>
    intro r₀ hr₀ hle hdiff
    unfold spiralRingAux
    by_cases heq : r₀ = r
    · subst heq; rw [if_pos hhi]
    · have hlt : r₀ < r := by omega
      have hge : (2 * r₀ + 1) ^ 2 ≤ k := by
        have h1 : 2 * r₀ + 1 ≤ 2 * r - 1 := by omega
        have h2 : (2 * r₀ + 1) ^ 2 ≤ (2 * r - 1) ^ 2 := Nat.pow_le_pow_left h1 2
        omega
      rw [if_neg (by omega)]
      exact ih (r₀ + 1) (by omega) (by omega) (by omega)

private lemma spiralRing_eq {r k : ℕ} (hr : 1 ≤ r)
    (hlo : (2 * r - 1) ^ 2 ≤ k) (hhi : k < (2 * r + 1) ^ 2) :
    spiralRing k = r := by
  have hk0 : k ≠ 0 := by
    have h2r : 1 ≤ 2 * r - 1 := by omega
    have : 1 ≤ (2 * r - 1) ^ 2 := by nlinarith
    omega
  have hrk : r - 1 ≤ k := by
    have h2r : r ≤ 2 * r - 1 := by omega
    have hsq : r ≤ (2 * r - 1) ^ 2 := by nlinarith
    omega
  unfold spiralRing
  rw [if_neg hk0]
  exact spiralRingAux_eq hlo hhi k 1 le_rfl hr hrk

private lemma spiralXY_of_ring {r e t : ℕ} (hr : 1 ≤ r) (he : e < 4) (ht : t < 2 * r) :
    spiralXY ((2 * r - 1) ^ 2 + 2 * r * e + t) = ringEdgeXY r e t := by
  set k := (2 * r - 1) ^ 2 + 2 * r * e + t
  have hk0 : k ≠ 0 := by
    have h2r : 1 ≤ 2 * r - 1 := by omega
    have : 1 ≤ (2 * r - 1) ^ 2 := by nlinarith
    omega
  have hlo : (2 * r - 1) ^ 2 ≤ k := by omega
  have hhi : k < (2 * r + 1) ^ 2 := by
    have hdiff : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by
      zify [show 1 ≤ 2 * r by omega]; ring
    have h6r : 2 * r * e ≤ 6 * r := by nlinarith
    omega
  have hr_eq : spiralRing k = r := spiralRing_eq hr hlo hhi
  have hidx : k - (2 * r - 1) ^ 2 = 2 * r * e + t := by omega
  have he_eq : (2 * r * e + t) / (2 * r) = e := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht, add_zero]
  have ht_eq : (2 * r * e + t) % (2 * r) = t := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  unfold spiralXY
  simp only [hk0, ↓reduceIte, hr_eq, hidx, he_eq, ht_eq]

private lemma black_at (h j : ℕ) (hj : j < 4) :
    predBlack (4 * h + 4 + j) =
      if j = 0 then (-(2 * (h : ℤ) + 3), 1)
      else if j = 1 then (2 * (h : ℤ) + 4, 0)
      else if j = 2 then (-(2 * (h : ℤ) + 4), 0)
      else (2 * (h : ℤ) + 5, 1) := by
  unfold predBlack
  rw [if_neg (by omega)]
  have hd : (4 * h + 4 + j - 4) / 4 = h := by omega
  have hm : (4 * h + 4 + j - 4) % 4 = j := by omega
  rw [hd, hm]
  interval_cases j <;> rfl

private lemma red_at (h j : ℕ) (hj : j < 4) :
    predRed (4 * h + 4 + j) =
      if j = 0 then (2, -(2 * (h : ℤ) + 3))
      else if j = 1 then (-1, 2 * (h : ℤ) + 4)
      else if j = 2 then (-1, -(2 * (h : ℤ) + 4))
      else (2, 2 * (h : ℤ) + 5) := by
  unfold predRed
  rw [if_neg (by omega)]
  have hd : (4 * h + 4 + j - 4) / 4 = h := by omega
  have hm : (4 * h + 4 + j - 4) % 4 = j := by omega
  rw [hd, hm]
  interval_cases j <;> rfl

private lemma blackLabel_at (h j : ℕ) (hj : j < 4) :
    predBlackLabel (4 * h + 4 + j) =
      if j = 0 then let r := 2 * h + 3; 4 * r * r + r - 1
      else if j = 1 then let r := 2 * h + 4; 4 * r * r - 3 * r
      else if j = 2 then let r := 2 * h + 4; 4 * r * r + r
      else let r := 2 * h + 5; 4 * r * r - 3 * r + 1 := by
  unfold predBlackLabel
  rw [if_neg (by omega)]
  have hd : (4 * h + 4 + j - 4) / 4 = h := by omega
  have hm : (4 * h + 4 + j - 4) % 4 = j := by omega
  rw [hd, hm]
  interval_cases j <;> rfl

private lemma redLabel_at (h j : ℕ) (hj : j < 4) :
    predRedLabel (4 * h + 4 + j) =
      if j = 0 then let r := 2 * h + 3; 4 * r * r + 3 * r + 2
      else if j = 1 then let r := 2 * h + 4; 4 * r * r - r + 1
      else if j = 2 then let r := 2 * h + 4; 4 * r * r + 3 * r - 1
      else let r := 2 * h + 5; 4 * r * r - r - 2 := by
  unfold predRedLabel
  rw [if_neg (by omega)]
  have hd : (4 * h + 4 + j - 4) / 4 = h := by omega
  have hm : (4 * h + 4 + j - 4) % 4 = j := by omega
  rw [hd, hm]
  interval_cases j <;> rfl

private lemma spiralXY_predBlackLabel (n : ℕ) :
    spiralXY (predBlackLabel n) = predBlack n := by
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne, blackLabel_at h j hj, black_at h j hj]
    interval_cases j
    · simp only [↓reduceIte]
      set r := 2 * h + 3
      have hr : 3 ≤ r := by omega
      have hlabel : 4 * r * r + r - 1 = (2 * r - 1) ^ 2 + 2 * r * 2 + (r - 2) := by
        zify [show 1 ≤ 4 * r * r + r by nlinarith, show 1 ≤ 2 * r by omega, show 2 ≤ r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    · simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      set r := 2 * h + 4
      have hr : 4 ≤ r := by omega
      have hlabel : 4 * r * r - 3 * r = (2 * r - 1) ^ 2 + 2 * r * 0 + (r - 1) := by
        zify [show 3 * r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega, show 1 ≤ r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    · simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      set r := 2 * h + 4
      have hr : 4 ≤ r := by omega
      have hlabel : 4 * r * r + r = (2 * r - 1) ^ 2 + 2 * r * 2 + (r - 1) := by
        zify [show 1 ≤ 2 * r by omega, show 1 ≤ r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    · simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      set r := 2 * h + 5
      have hr : 5 ≤ r := by omega
      have hlabel : 4 * r * r - 3 * r + 1 = (2 * r - 1) ^ 2 + 2 * r * 0 + r := by
        zify [show 3 * r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)

private lemma spiralXY_predRedLabel (n : ℕ) :
    spiralXY (predRedLabel n) = predRed n := by
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne, redLabel_at h j hj, red_at h j hj]
    interval_cases j
    · simp only [↓reduceIte]
      set r := 2 * h + 3
      have hr : 3 ≤ r := by omega
      have hlabel : 4 * r * r + 3 * r + 2 = (2 * r - 1) ^ 2 + 2 * r * 3 + (r + 1) := by
        zify [show 1 ≤ 2 * r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    · simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      set r := 2 * h + 4
      have hr : 4 ≤ r := by omega
      have hlabel : 4 * r * r - r + 1 = (2 * r - 1) ^ 2 + 2 * r * 1 + r := by
        zify [show r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    · simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      set r := 2 * h + 4
      have hr : 4 ≤ r := by omega
      have hlabel : 4 * r * r + 3 * r - 1 = (2 * r - 1) ^ 2 + 2 * r * 3 + (r - 2) := by
        zify [show 1 ≤ 4 * r * r + 3 * r by nlinarith, show 1 ≤ 2 * r by omega, show 2 ≤ r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    · simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      set r := 2 * h + 5
      have hr : 5 ≤ r := by omega
      have hlabel : 4 * r * r - r - 2 = (2 * r - 1) ^ 2 + 2 * r * 1 + (r - 3) := by
        have h1 : r + 2 ≤ 4 * r * r := by nlinarith
        zify [show r ≤ 4 * r * r by omega, show 2 ≤ 4 * r * r - r by omega, show 1 ≤ 2 * r by omega, show 3 ≤ r by omega]; ring
      rw [hlabel, spiralXY_of_ring (by omega) (by omega) (by omega)]
      unfold ringEdgeXY; simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      exact Prod.ext (by dsimp only [r]; omega) (by dsimp only [r]; omega)

/-! ### Section 4: Global parity, coordinate ranges, and monotonicity -/

private lemma predBlack_props (n : ℕ) :
    (predBlack n).2 ∈ ({0, 1} : Set ℤ) ∧
    (predBlack n).1 ≠ -1 ∧ (predBlack n).1 ≠ 2 ∧
    ((predBlack n).1 + (predBlack n).2) % 2 = 0 ∧
    ((predBlack n).1 - (predBlack n).2) % 2 = 0 := by
  by_cases hn : n < 4
  · interval_cases n <;> simp [predBlack]
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne, black_at h j hj]
    interval_cases j <;> simp <;> omega

private lemma predRed_props (n : ℕ) :
    (predRed n).1 ∈ ({-1, 2} : Set ℤ) ∧
    (predRed n).2 ≠ 0 ∧ (predRed n).2 ≠ 1 ∧
    ((predRed n).1 + (predRed n).2) % 2 = 1 ∧
    ((predRed n).1 - (predRed n).2) % 2 = 1 := by
  by_cases hn : n < 4
  · interval_cases n <;> simp [predRed]
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne, red_at h j hj]
    interval_cases j <;> simp <;> omega

/-- No Black queen ever attacks any Red queen (universal parity and coordinate separation!). -/
theorem predBlack_not_attacks_predRed (i j : ℕ) :
    ¬ attacks (predBlack i) (predRed j) := by
  have hb := predBlack_props i
  have hr := predRed_props j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hr
  intro h
  rcases h with h | h | h | h
  · rcases hr.1 with h1 | h1 <;> omega
  · rcases hb.1 with h1 | h1 <;> omega
  · omega
  · omega

private lemma predBlackLabel_strictMono : StrictMono predBlackLabel := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne]
    interval_cases j
    · rw [blackLabel_at h 0 (by omega), show 4 * h + 4 + 0 + 1 = 4 * h + 4 + 1 by omega,
        blackLabel_at h 1 (by omega)]; simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      zify [show 1 ≤ 4 * (2 * h + 3) * (2 * h + 3) + (2 * h + 3) by nlinarith,
        show 3 * (2 * h + 4) ≤ 4 * (2 * h + 4) * (2 * h + 4) by nlinarith]; nlinarith
    · rw [blackLabel_at h 1 (by omega), show 4 * h + 4 + 1 + 1 = 4 * h + 4 + 2 by omega,
        blackLabel_at h 2 (by omega)]; simp only [show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
        show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      zify [show 3 * (2 * h + 4) ≤ 4 * (2 * h + 4) * (2 * h + 4) by nlinarith]; nlinarith
    · rw [blackLabel_at h 2 (by omega), show 4 * h + 4 + 2 + 1 = 4 * h + 4 + 3 by omega,
        blackLabel_at h 3 (by omega)]; simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      zify [show 3 * (2 * h + 5) ≤ 4 * (2 * h + 5) * (2 * h + 5) by nlinarith]; nlinarith
    · rw [blackLabel_at h 3 (by omega), show 4 * h + 4 + 3 + 1 = 4 * (h + 1) + 4 + 0 by omega,
        blackLabel_at (h + 1) 0 (by omega)]; simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      zify [show 3 * (2 * h + 5) ≤ 4 * (2 * h + 5) * (2 * h + 5) by nlinarith,
        show 1 ≤ 4 * (2 * (h + 1) + 3) * (2 * (h + 1) + 3) + (2 * (h + 1) + 3) by nlinarith]; nlinarith

private lemma predRedLabel_strictMono : StrictMono predRedLabel := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne]
    interval_cases j
    · rw [redLabel_at h 0 (by omega), show 4 * h + 4 + 0 + 1 = 4 * h + 4 + 1 by omega,
        redLabel_at h 1 (by omega)]; simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      zify [show 2 * h + 4 ≤ 4 * (2 * h + 4) * (2 * h + 4) by nlinarith]; nlinarith
    · rw [redLabel_at h 1 (by omega), show 4 * h + 4 + 1 + 1 = 4 * h + 4 + 2 by omega,
        redLabel_at h 2 (by omega)]; simp only [show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
        show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      zify [show 2 * h + 4 ≤ 4 * (2 * h + 4) * (2 * h + 4) by nlinarith,
        show 1 ≤ 4 * (2 * h + 4) * (2 * h + 4) + 3 * (2 * h + 4) by nlinarith]; nlinarith
    · rw [redLabel_at h 2 (by omega), show 4 * h + 4 + 2 + 1 = 4 * h + 4 + 3 by omega,
        redLabel_at h 3 (by omega)]; simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      have h1 : 2 * h + 5 + 2 ≤ 4 * (2 * h + 5) * (2 * h + 5) := by nlinarith
      zify [show 1 ≤ 4 * (2 * h + 4) * (2 * h + 4) + 3 * (2 * h + 4) by nlinarith,
        show 2 * h + 5 ≤ 4 * (2 * h + 5) * (2 * h + 5) by omega,
        show 2 ≤ 4 * (2 * h + 5) * (2 * h + 5) - (2 * h + 5) by omega]; nlinarith
    · rw [redLabel_at h 3 (by omega), show 4 * h + 4 + 3 + 1 = 4 * (h + 1) + 4 + 0 by omega,
        redLabel_at (h + 1) 0 (by omega)]; simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      have h1 : 2 * h + 5 + 2 ≤ 4 * (2 * h + 5) * (2 * h + 5) := by nlinarith
      zify [show 2 * h + 5 ≤ 4 * (2 * h + 5) * (2 * h + 5) by omega,
        show 2 ≤ 4 * (2 * h + 5) * (2 * h + 5) - (2 * h + 5) by omega]; nlinarith

/-! ### Section 5: Explicit line-set witnesses (Lemma 2.1) -/

/-- Every `x ∈ [-(2h+2), 2h+3] \ {-1, 2}` occurs as `(predBlack i).1` for some `i < 4h + 4` (`h ≥ 1`). -/
private lemma exists_black_x {h : ℕ} (hh : 1 ≤ h) {x : ℤ}
    (hlo : -(2 * (h : ℤ) + 2) ≤ x) (hhi : x ≤ 2 * (h : ℤ) + 3) (h1 : x ≠ -1) (h2 : x ≠ 2) :
    ∃ i < 4 * h + 4, (predBlack i).1 = x := by
  by_cases hbase : -2 ≤ x ∧ x ≤ 3
  · rcases (by omega : x = -2 ∨ x = 0 ∨ x = 1 ∨ x = 3) with rfl | rfl | rfl | rfl
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨3, by omega, rfl⟩
  · by_cases hpos : 4 ≤ x
    · by_cases hev : x % 2 = 0
      · refine ⟨4 * ((x - 4) / 2).toNat + 4 + 1, by omega, ?_⟩
        rw [black_at _ 1 (by omega)]; simp; omega
      · refine ⟨4 * ((x - 5) / 2).toNat + 4 + 3, by omega, ?_⟩
        rw [black_at _ 3 (by omega)]; simp; omega
    · -- `x ≤ -3`
      by_cases hev : x % 2 = 0
      · refine ⟨4 * ((-x - 4) / 2).toNat + 4 + 2, by omega, ?_⟩
        rw [black_at _ 2 (by omega)]; simp; omega
      · refine ⟨4 * ((-x - 3) / 2).toNat + 4 + 0, by omega, ?_⟩
        rw [black_at _ 0 (by omega)]; simp; omega

/-- Every `y ∈ [-(2h+2), 2h+3] \ {0, 1}` occurs as `(predRed i).2` for some `i < 4h + 4` (`h ≥ 1`). -/
private lemma exists_red_y {h : ℕ} (hh : 1 ≤ h) {y : ℤ}
    (hlo : -(2 * (h : ℤ) + 2) ≤ y) (hhi : y ≤ 2 * (h : ℤ) + 3) (h0 : y ≠ 0) (h1 : y ≠ 1) :
    ∃ i < 4 * h + 4, (predRed i).2 = y := by
  by_cases hbase : -2 ≤ y ∧ y ≤ 3
  · rcases (by omega : y = -2 ∨ y = -1 ∨ y = 2 ∨ y = 3) with rfl | rfl | rfl | rfl
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨3, by omega, rfl⟩
  · by_cases hpos : 4 ≤ y
    · by_cases hev : y % 2 = 0
      · refine ⟨4 * ((y - 4) / 2).toNat + 4 + 1, by omega, ?_⟩
        rw [red_at _ 1 (by omega)]; simp; omega
      · refine ⟨4 * ((y - 5) / 2).toNat + 4 + 3, by omega, ?_⟩
        rw [red_at _ 3 (by omega)]; simp; omega
    · -- `y ≤ -3`
      by_cases hev : y % 2 = 0
      · refine ⟨4 * ((-y - 4) / 2).toNat + 4 + 2, by omega, ?_⟩
        rw [red_at _ 2 (by omega)]; simp; omega
      · refine ⟨4 * ((-y - 3) / 2).toNat + 4 + 0, by omega, ?_⟩
        rw [red_at _ 0 (by omega)]; simp; omega

/-! ### Section 6: Verification of the greedy game (`IsGreedyGame predBlackLabel predRedLabel`) -/

/-- Decompose any label `k` on ring `r ≥ 1` into `(e, t)` with `e < 4`, `t < 2r`. -/
private lemma spiralXY_cases_ring {r k : ℕ} (hr : 1 ≤ r)
    (hlo : (2 * r - 1) ^ 2 ≤ k) (hhi : k < (2 * r + 1) ^ 2) :
    ∃ e t : ℕ, e < 4 ∧ t < 2 * r ∧ k = (2 * r - 1) ^ 2 + 2 * r * e + t ∧
      spiralXY k = ringEdgeXY r e t := by
  let idx := k - (2 * r - 1) ^ 2
  let e := idx / (2 * r)
  let t := idx % (2 * r)
  have hdiff : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by
    zify [show 1 ≤ 2 * r by omega]; ring
  have hidx_lt : idx < 8 * r := by omega
  have he : e < 4 := Nat.div_lt_of_lt_mul (by omega)
  have ht : t < 2 * r := Nat.mod_lt _ (by omega)
  have hk_eq : k = (2 * r - 1) ^ 2 + 2 * r * e + t := by
    have := Nat.div_add_mod idx (2 * r)
    dsimp only [idx, e, t] at *
    omega
  refine ⟨e, t, he, ht, hk_eq, ?_⟩
  conv_lhs => rw [hk_eq]
  exact spiralXY_of_ring hr he ht

/-- Structural-recursive binary-splitting checker over `[lo, lo + len)` (depth `d`, kernel-reducible). -/
private def allRangeAux (p : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, lo, len => if len = 0 then true else p lo
  | d + 1, lo, len =>
    if len ≤ 1 then (if len = 0 then true else p lo)
    else
      let half := len / 2
      allRangeAux p d lo half && allRangeAux p d (lo + half) (len - half)

private lemma allRangeAux_spec (p : ℕ → Bool) :
    ∀ d lo len, len ≤ 2 ^ d → allRangeAux p d lo len = true → ∀ k, lo ≤ k → k < lo + len → p k = true := by
  intro d
  induction d with
  | zero =>
    intro lo len hlen h k hlo hhi
    unfold allRangeAux at h
    have h1 : len = 1 := by simp at hlen; omega
    have h2 : k = lo := by omega
    subst h1; subst h2; simpa using h
  | succ d ih =>
    intro lo len hlen h k hlo hhi
    unfold allRangeAux at h
    by_cases hle1 : len ≤ 1
    · rw [if_pos hle1] at h
      have h1 : len = 1 := by omega
      have h2 : k = lo := by omega
      subst h1; subst h2; simpa using h
    · rw [if_neg hle1] at h
      simp only [Bool.and_eq_true] at h
      set half := len / 2
      have h2d : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; omega
      by_cases hlt : k < lo + half
      · exact ih lo half (by omega) h.1 k hlo hlt
      · exact ih (lo + half) (len - half) (by omega) h.2 k (by omega) (by omega)

private def anyLt (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => p n || anyLt p n

private lemma anyLt_spec (p : ℕ → Bool) :
    ∀ n, anyLt p n = true → ∃ i < n, p i = true := by
  intro n
  induction n with
  | zero => intro h; simp [anyLt] at h
  | succ n ih =>
    intro h
    unfold anyLt at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h2
    · exact ⟨n, by omega, h1⟩
    · obtain ⟨i, hi, hp⟩ := ih h2; exact ⟨i, by omega, hp⟩

private def checkBaseRound (n : ℕ) : Bool :=
  allRangeAux (fun k =>
    anyLt (fun i => decide (k = predBlackLabel i)) n ||
    anyLt (fun i => decide (attacks (spiralXY k) (predRed i))) n) 8 0 (predBlackLabel n) &&
  allRangeAux (fun k =>
    anyLt (fun i => decide (k = predRedLabel i)) n ||
    anyLt (fun i => decide (attacks (spiralXY k) (predBlack i))) (n + 1)) 8 0 (predRedLabel n)

private lemma checkBaseRound_0 : checkBaseRound 0 = true := by decide
private lemma checkBaseRound_1 : checkBaseRound 1 = true := by decide
private lemma checkBaseRound_2 : checkBaseRound 2 = true := by decide
private lemma checkBaseRound_3 : checkBaseRound 3 = true := by decide
private lemma checkBaseRound_4 : checkBaseRound 4 = true := by decide
private lemma checkBaseRound_5 : checkBaseRound 5 = true := by decide
private lemma checkBaseRound_6 : checkBaseRound 6 = true := by decide
private lemma checkBaseRound_7 : checkBaseRound 7 = true := by decide

/-- Decidable finite check for the base rounds `0 ≤ n ≤ 7` (16 placements, labels ≤ 93). -/
private lemma base_rounds_valid (n : ℕ) (hn : n < 8) :
    (∀ k < predBlackLabel n,
      (∃ i < n, k = predBlackLabel i) ∨
      (∃ i < n, attacks (spiralXY k) (predRed i))) ∧
    (∀ k < predRedLabel n,
      (∃ i < n, k = predRedLabel i) ∨
      (∃ i < n + 1, attacks (spiralXY k) (predBlack i))) := by
  have hb_le : predBlackLabel n ≤ 2 ^ 8 := by interval_cases n <;> decide
  have hr_le : predRedLabel n ≤ 2 ^ 8 := by interval_cases n <;> decide
  have hchk : checkBaseRound n = true := by
    interval_cases n
    · exact checkBaseRound_0
    · exact checkBaseRound_1
    · exact checkBaseRound_2
    · exact checkBaseRound_3
    · exact checkBaseRound_4
    · exact checkBaseRound_5
    · exact checkBaseRound_6
    · exact checkBaseRound_7
  unfold checkBaseRound at hchk
  simp only [Bool.and_eq_true] at hchk
  constructor
  · intro k hk
    have h1 := allRangeAux_spec _ 8 0 (predBlackLabel n) hb_le hchk.1 k (Nat.zero_le k) (by omega)
    rcases Bool.or_eq_true_iff.mp h1 with hocc | hatt
    · obtain ⟨i, hi, hp⟩ := anyLt_spec _ n hocc
      exact Or.inl ⟨i, hi, of_decide_eq_true hp⟩
    · obtain ⟨i, hi, hp⟩ := anyLt_spec _ n hatt
      exact Or.inr ⟨i, hi, of_decide_eq_true hp⟩
  · intro k hk
    have h2 := allRangeAux_spec _ 8 0 (predRedLabel n) hr_le hchk.2 k (Nat.zero_le k) (by omega)
    rcases Bool.or_eq_true_iff.mp h2 with hocc | hatt
    · obtain ⟨i, hi, hp⟩ := anyLt_spec _ n hocc
      exact Or.inl ⟨i, hi, of_decide_eq_true hp⟩
    · obtain ⟨i, hi, hp⟩ := anyLt_spec _ (n + 1) hatt
      exact Or.inr ⟨i, hi, of_decide_eq_true hp⟩

/-- Gap attack verification for all 8 turns of every block `h ≥ 1`. -/
private lemma block_gap_black {h j : ℕ} (hh : 1 ≤ h) (hj : j < 4) {k : ℕ}
    (hlo : predBlackLabel (4 * h + 4 + j - 1) < k) (hhi : k < predBlackLabel (4 * h + 4 + j)) :
    ∃ i < 4 * h + 4 + j, attacks (spiralXY k) (predRed i) := by
  interval_cases j
  · -- j = 0: prev is `4h+3` (`r = 2h+3`), target is `4h+4` (`r = 2h+3`)
    set r := 2 * h + 3
    have hr : 5 ≤ r := by omega
    have hprev : predBlackLabel (4 * h + 3) = (2 * r - 1) ^ 2 + r := by
      rw [show 4 * h + 3 = 4 * (h - 1) + 4 + 3 by omega, blackLabel_at (h - 1) 3 (by omega)]
      simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      rw [show 2 * (h - 1) + 5 = r by omega]
      zify [show 3 * r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega]; ring
    have htarg : predBlackLabel (4 * h + 4) = (2 * r - 1) ^ 2 + 2 * r * 2 + (r - 2) := by
      rw [show 4 * h + 4 = 4 * h + 4 + 0 by omega, blackLabel_at h 0 (by omega)]
      simp only [↓reduceIte]
      rw [show 2 * h + 3 = r by omega]
      zify [show 1 ≤ 4 * r * r + r by nlinarith, show 1 ≤ 2 * r by omega, show 2 ≤ r by omega]; ring
    rw [show 4 * h + 4 + 0 - 1 = 4 * h + 3 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 0 = 4 * h + 4 by omega, htarg] at hhi
    have hhi_ring : k < (2 * r + 1) ^ 2 := by
      have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
      omega
    obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
    have hy_range : 2 ≤ (spiralXY k).2 ∧ (spiralXY k).2 ≤ 2 * (h : ℤ) + 3 := by
      rw [hxy]; unfold ringEdgeXY
      interval_cases e <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;> omega
    obtain ⟨i, hi, hyi⟩ := exists_red_y hh (by omega) hy_range.2 (by omega) (by omega)
    exact ⟨i, by omega, Or.inr (Or.inl hyi.symm)⟩
  · -- j = 1: prev is `4h+4` (ring `r-1 = 2h+3`), target is `4h+5` (ring `r = 2h+4`)
    set r := 2 * h + 4
    have hr : 6 ≤ r := by omega
    have hr1_ge : 5 ≤ r - 1 := by omega
    have hprev : predBlackLabel (4 * h + 4) = (2 * (r - 1) - 1) ^ 2 + 2 * (r - 1) * 2 + (r - 3) := by
      rw [show 4 * h + 4 = 4 * h + 4 + 0 by omega, blackLabel_at h 0 (by omega)]
      simp only [↓reduceIte]
      rw [show 2 * h + 3 = r - 1 by omega]
      zify [show 1 ≤ 4 * (r - 1) * (r - 1) + (r - 1) by nlinarith,
        show 1 ≤ 2 * (r - 1) by omega, show 3 ≤ r by omega, show 1 ≤ r by omega]; ring
    have htarg : predBlackLabel (4 * h + 5) = (2 * r - 1) ^ 2 + (r - 1) := by
      rw [show 4 * h + 5 = 4 * h + 4 + 1 by omega, blackLabel_at h 1 (by omega)]
      simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r by omega]
      zify [show 3 * r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega, show 1 ≤ r by omega]; ring
    rw [show 4 * h + 4 + 1 - 1 = 4 * h + 4 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 1 = 4 * h + 5 by omega, htarg] at hhi
    have hbd : (2 * (r - 1) + 1) ^ 2 = (2 * r - 1) ^ 2 := by rw [show 2 * (r - 1) + 1 = 2 * r - 1 by omega]
    by_cases hring : k < (2 * r - 1) ^ 2
    · obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r - 1) (k := k) (by omega) (by omega) (by rw [hbd]; exact hring)
      have hcell : (spiralXY k = (-((r - 1 : ℕ) : ℤ), 0)) ∨
          (-(2 * (h : ℤ) + 3) ≤ (spiralXY k).2 ∧ (spiralXY k).2 ≤ -1) := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e
        · exfalso; omega
        · exfalso; omega
        · simp only [Nat.reduceEqDiff, ↓reduceIte]
          by_cases ht0 : t = r - 2
          · left; exact Prod.ext (by omega) (by omega)
          · right; omega
        · right; simp only [Nat.reduceEqDiff, ↓reduceIte]; omega
      rcases hcell with hspec | ⟨hy1, hy2⟩
      · refine ⟨4 * (h - 1) + 4 + 2, by omega, ?_⟩
        rw [hspec, red_at (h - 1) 2 (by omega)]
        simp only [Nat.reduceEqDiff, ↓reduceIte]
        right; right; left; dsimp [r]; omega
      · by_cases hyend : (spiralXY k).2 = -(2 * (h : ℤ) + 3)
        · refine ⟨4 * h + 4 + 0, by omega, ?_⟩
          rw [red_at h 0 (by omega)]; simp only [↓reduceIte]; right; left; omega
        · obtain ⟨i, hi, hyi⟩ := exists_red_y hh (y := (spiralXY k).2) (by omega) (by omega) (by omega) (by omega)
          exact ⟨i, by omega, Or.inr (Or.inl hyi.symm)⟩
    · have hhi_ring : k < (2 * r + 1) ^ 2 := by
        have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
        omega
      obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
      obtain ⟨hy1, hy2⟩ : -(2 * (h : ℤ) + 3) ≤ (spiralXY k).2 ∧ (spiralXY k).2 ≤ -1 := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;> omega
      by_cases hyend : (spiralXY k).2 = -(2 * (h : ℤ) + 3)
      · refine ⟨4 * h + 4 + 0, by omega, ?_⟩
        rw [red_at h 0 (by omega)]; simp only [↓reduceIte]; right; left; omega
      · obtain ⟨i, hi, hyi⟩ := exists_red_y hh (y := (spiralXY k).2) (by omega) (by omega) (by omega) (by omega)
        exact ⟨i, by omega, Or.inr (Or.inl hyi.symm)⟩
  · -- j = 2: prev is `4h+5` (ring `r = 2h+4`), target is `4h+6` (ring `r = 2h+4`)
    set r := 2 * h + 4
    have hr : 6 ≤ r := by omega
    have hprev : predBlackLabel (4 * h + 5) = (2 * r - 1) ^ 2 + (r - 1) := by
      rw [show 4 * h + 5 = 4 * h + 4 + 1 by omega, blackLabel_at h 1 (by omega)]
      simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r by omega]
      zify [show 3 * r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega, show 1 ≤ r by omega]; ring
    have htarg : predBlackLabel (4 * h + 6) = (2 * r - 1) ^ 2 + 2 * r * 2 + (r - 1) := by
      rw [show 4 * h + 6 = 4 * h + 4 + 2 by omega, blackLabel_at h 2 (by omega)]
      simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r by omega]
      zify [show 1 ≤ 2 * r by omega, show 1 ≤ r by omega]; ring
    rw [show 4 * h + 4 + 2 - 1 = 4 * h + 5 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 2 = 4 * h + 6 by omega, htarg] at hhi
    have hhi_ring : k < (2 * r + 1) ^ 2 := by
      have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
      omega
    obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
    have hcell : spiralXY k = ((r : ℤ), 1) ∨ spiralXY k = (-(r : ℤ), 1) ∨
        (2 ≤ (spiralXY k).2 ∧ (spiralXY k).2 ≤ 2 * (h : ℤ) + 4) := by
      rw [hxy]; unfold ringEdgeXY
      interval_cases e
      · simp only [↓reduceIte]
        by_cases ht1 : t = r
        · left; exact Prod.ext (by omega) (by omega)
        · right; right; omega
      · right; right; simp only [Nat.reduceEqDiff, ↓reduceIte]; omega
      · simp only [Nat.reduceEqDiff, ↓reduceIte]
        by_cases ht1 : t = r - 2
        · right; left; exact Prod.ext (by omega) (by omega)
        · right; right; omega
      · exfalso; omega
    rcases hcell with h1 | h2 | ⟨hy1, hy2⟩
    · refine ⟨4 * (h - 1) + 4 + 3, by omega, ?_⟩
      rw [h1, red_at (h - 1) 3 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
      right; right; left; dsimp [r]; omega
    · refine ⟨4 * (h - 1) + 4 + 2, by omega, ?_⟩
      rw [h2, red_at (h - 1) 2 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
      right; right; left; dsimp [r]; omega
    · by_cases hytop : (spiralXY k).2 = 2 * (h : ℤ) + 4
      · refine ⟨4 * h + 4 + 1, by omega, ?_⟩
        rw [red_at h 1 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; right; left; omega
      · obtain ⟨i, hi, hyi⟩ := exists_red_y hh (y := (spiralXY k).2) (by omega) (by omega) (by omega) (by omega)
        exact ⟨i, by omega, Or.inr (Or.inl hyi.symm)⟩
  · -- j = 3: prev is `4h+6` (ring `r-1 = 2h+4`), target is `4h+7` (ring `r = 2h+5`)
    set r := 2 * h + 5
    have hr : 7 ≤ r := by omega
    have hprev : predBlackLabel (4 * h + 6) = (2 * (r - 1) - 1) ^ 2 + 2 * (r - 1) * 2 + (r - 2) := by
      rw [show 4 * h + 6 = 4 * h + 4 + 2 by omega, blackLabel_at h 2 (by omega)]
      simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r - 1 by omega]
      zify [show 1 ≤ 2 * (r - 1) by omega, show 2 ≤ r by omega, show 1 ≤ r by omega]; ring
    have htarg : predBlackLabel (4 * h + 7) = (2 * r - 1) ^ 2 + r := by
      rw [show 4 * h + 7 = 4 * h + 4 + 3 by omega, blackLabel_at h 3 (by omega)]
      simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      rw [show 2 * h + 5 = r by omega]
      zify [show 3 * r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega]; ring
    rw [show 4 * h + 4 + 3 - 1 = 4 * h + 6 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 3 = 4 * h + 7 by omega, htarg] at hhi
    have hbd : (2 * (r - 1) + 1) ^ 2 = (2 * r - 1) ^ 2 := by rw [show 2 * (r - 1) + 1 = 2 * r - 1 by omega]
    by_cases hring : k < (2 * r - 1) ^ 2
    · obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r - 1) (k := k) (by omega) (by omega) (by rw [hbd]; exact hring)
      obtain ⟨hy1, hy2⟩ : -(2 * (h : ℤ) + 4) ≤ (spiralXY k).2 ∧ (spiralXY k).2 ≤ -1 := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;> omega
      by_cases hy4 : (spiralXY k).2 = -(2 * (h : ℤ) + 4)
      · refine ⟨4 * h + 4 + 2, by omega, ?_⟩
        rw [red_at h 2 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; right; left; omega
      · by_cases hy3 : (spiralXY k).2 = -(2 * (h : ℤ) + 3)
        · refine ⟨4 * h + 4 + 0, by omega, ?_⟩
          rw [red_at h 0 (by omega)]; simp only [↓reduceIte]; right; left; omega
        · obtain ⟨i, hi, hyi⟩ := exists_red_y hh (y := (spiralXY k).2) (by omega) (by omega) (by omega) (by omega)
          exact ⟨i, by omega, Or.inr (Or.inl hyi.symm)⟩
    · have hhi_ring : k < (2 * r + 1) ^ 2 := by
        have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
        omega
      obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
      have hcell : spiralXY k = ((r : ℤ), 0) ∨
          (-(2 * (h : ℤ) + 4) ≤ (spiralXY k).2 ∧ (spiralXY k).2 ≤ -1) := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e
        · simp only [↓reduceIte]
          by_cases ht0 : t = r - 1
          · left; exact Prod.ext (by omega) (by omega)
          · right; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      rcases hcell with hspec | ⟨hy1, hy2⟩
      · refine ⟨4 * (h - 1) + 4 + 3, by omega, ?_⟩
        rw [hspec, red_at (h - 1) 3 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        right; right; left; dsimp [r]; omega
      · by_cases hy4 : (spiralXY k).2 = -(2 * (h : ℤ) + 4)
        · refine ⟨4 * h + 4 + 2, by omega, ?_⟩
          rw [red_at h 2 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; right; left; omega
        · by_cases hy3 : (spiralXY k).2 = -(2 * (h : ℤ) + 3)
          · refine ⟨4 * h + 4 + 0, by omega, ?_⟩
            rw [red_at h 0 (by omega)]; simp only [↓reduceIte]; right; left; omega
          · obtain ⟨i, hi, hyi⟩ := exists_red_y hh (y := (spiralXY k).2) (by omega) (by omega) (by omega) (by omega)
            exact ⟨i, by omega, Or.inr (Or.inl hyi.symm)⟩

private lemma block_gap_red {h j : ℕ} (hh : 1 ≤ h) (hj : j < 4) {k : ℕ}
    (hlo : predRedLabel (4 * h + 4 + j - 1) < k) (hhi : k < predRedLabel (4 * h + 4 + j)) :
    ∃ i ≤ 4 * h + 4 + j, attacks (spiralXY k) (predBlack i) := by
  interval_cases j
  · -- j = 0: prev is `4h+3` (ring `r = 2h+3`), target is `4h+4` (ring `r = 2h+3`)
    set r := 2 * h + 3
    have hr : 5 ≤ r := by omega
    have hprev : predRedLabel (4 * h + 3) = (2 * r - 1) ^ 2 + 2 * r * 1 + (r - 3) := by
      rw [show 4 * h + 3 = 4 * (h - 1) + 4 + 3 by omega, redLabel_at (h - 1) 3 (by omega)]
      simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      rw [show 2 * (h - 1) + 5 = r by omega]
      have h1 : r + 2 ≤ 4 * r * r := by nlinarith
      zify [show r ≤ 4 * r * r by omega, show 2 ≤ 4 * r * r - r by omega, show 1 ≤ 2 * r by omega, show 3 ≤ r by omega]; ring
    have htarg : predRedLabel (4 * h + 4) = (2 * r - 1) ^ 2 + 2 * r * 3 + (r + 1) := by
      rw [show 4 * h + 4 = 4 * h + 4 + 0 by omega, redLabel_at h 0 (by omega)]
      simp only [↓reduceIte]
      rw [show 2 * h + 3 = r by omega]
      zify [show 1 ≤ 2 * r by omega]; ring
    rw [show 4 * h + 4 + 0 - 1 = 4 * h + 3 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 0 = 4 * h + 4 by omega, htarg] at hhi
    have hhi_ring : k < (2 * r + 1) ^ 2 := by
      have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
      omega
    obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
    have hcell : spiralXY k = (-1, (r : ℤ)) ∨ spiralXY k = (-1, -(r : ℤ)) ∨
        (-(2 * (h : ℤ) + 3) ≤ (spiralXY k).1 ∧ (spiralXY k).1 ≤ 1 ∧ (spiralXY k).1 ≠ -1) := by
      rw [hxy]; unfold ringEdgeXY
      interval_cases e
      · exfalso; omega
      · simp only [Nat.reduceEqDiff, ↓reduceIte]
        by_cases ht1 : t = r
        · left; exact Prod.ext (by omega) (by omega)
        · right; right; omega
      · right; right; simp only [Nat.reduceEqDiff, ↓reduceIte]; omega
      · simp only [Nat.reduceEqDiff, ↓reduceIte]
        by_cases ht1 : t = r - 2
        · right; left; exact Prod.ext (by omega) (by omega)
        · right; right; omega
    rcases hcell with h1 | h2 | ⟨hx1, hx2, hx3⟩
    · refine ⟨4 * (h - 1) + 4 + 1, by omega, ?_⟩
      rw [h1, black_at (h - 1) 1 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
      right; right; left; dsimp [r]; omega
    · refine ⟨4 * (h - 1) + 4 + 3, by omega, ?_⟩
      rw [h2, black_at (h - 1) 3 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
      right; right; right; dsimp [r]; omega
    · by_cases hxe : (spiralXY k).1 = -(2 * (h : ℤ) + 3)
      · refine ⟨4 * h + 4 + 0, by omega, ?_⟩
        rw [black_at h 0 (by omega)]; simp only [↓reduceIte]; left; omega
      · obtain ⟨i, hi, hxi⟩ := exists_black_x hh (by omega) (by omega) hx3 (by omega)
        exact ⟨i, by omega, Or.inl hxi.symm⟩
  · -- j = 1: prev is `4h+4` (ring `r-1 = 2h+3`), target is `4h+5` (ring `r = 2h+4`)
    set r := 2 * h + 4
    have hr : 6 ≤ r := by omega
    have hprev : predRedLabel (4 * h + 4) = (2 * (r - 1) - 1) ^ 2 + 2 * (r - 1) * 3 + r := by
      rw [show 4 * h + 4 = 4 * h + 4 + 0 by omega, redLabel_at h 0 (by omega)]
      simp only [↓reduceIte]
      rw [show 2 * h + 3 = r - 1 by omega]
      zify [show 1 ≤ 2 * (r - 1) by omega, show 1 ≤ r by omega]; ring
    have htarg : predRedLabel (4 * h + 5) = (2 * r - 1) ^ 2 + 2 * r * 1 + r := by
      rw [show 4 * h + 5 = 4 * h + 4 + 1 by omega, redLabel_at h 1 (by omega)]
      simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r by omega]
      zify [show r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega]; ring
    rw [show 4 * h + 4 + 1 - 1 = 4 * h + 4 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 1 = 4 * h + 5 by omega, htarg] at hhi
    have hbd : (2 * (r - 1) + 1) ^ 2 = (2 * r - 1) ^ 2 := by rw [show 2 * (r - 1) + 1 = 2 * r - 1 by omega]
    by_cases hring : k < (2 * r - 1) ^ 2
    · obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r - 1) (k := k) (by omega) (by omega) (by rw [hbd]; exact hring)
      obtain ⟨hx1, hx2⟩ : 3 ≤ (spiralXY k).1 ∧ (spiralXY k).1 ≤ 2 * (h : ℤ) + 3 := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;> omega
      obtain ⟨i, hi, hxi⟩ := exists_black_x hh (by omega) hx2 (by omega) (by omega)
      exact ⟨i, by omega, Or.inl hxi.symm⟩
    · have hhi_ring : k < (2 * r + 1) ^ 2 := by
        have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
        omega
      obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
      have hcell : spiralXY k = (2, (r : ℤ)) ∨
          (0 ≤ (spiralXY k).1 ∧ (spiralXY k).1 ≤ 2 * (h : ℤ) + 4 ∧ (spiralXY k).1 ≠ 2) := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e
        · right; simp only [↓reduceIte]; omega
        · simp only [Nat.reduceEqDiff, ↓reduceIte]
          by_cases ht2 : t = r - 3
          · left; exact Prod.ext (by omega) (by omega)
          · right; omega
        · exfalso; omega
        · exfalso; omega
      rcases hcell with hspec | ⟨hx1, hx2, hx3⟩
      · refine ⟨4 * (h - 1) + 4 + 2, by omega, ?_⟩
        rw [hspec, black_at (h - 1) 2 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        right; right; right; dsimp [r]; omega
      · by_cases hx4 : (spiralXY k).1 = 2 * (h : ℤ) + 4
        · refine ⟨4 * h + 4 + 1, by omega, ?_⟩
          rw [black_at h 1 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; left; omega
        · obtain ⟨i, hi, hxi⟩ := exists_black_x hh (by omega) (by omega) (by omega) hx3
          exact ⟨i, by omega, Or.inl hxi.symm⟩
  · -- j = 2: prev is `4h+5` (ring `r = 2h+4`), target is `4h+6` (ring `r = 2h+4`)
    set r := 2 * h + 4
    have hr : 6 ≤ r := by omega
    have hprev : predRedLabel (4 * h + 5) = (2 * r - 1) ^ 2 + 2 * r * 1 + r := by
      rw [show 4 * h + 5 = 4 * h + 4 + 1 by omega, redLabel_at h 1 (by omega)]
      simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r by omega]
      zify [show r ≤ 4 * r * r by nlinarith, show 1 ≤ 2 * r by omega]; ring
    have htarg : predRedLabel (4 * h + 6) = (2 * r - 1) ^ 2 + 2 * r * 3 + (r - 2) := by
      rw [show 4 * h + 6 = 4 * h + 4 + 2 by omega, redLabel_at h 2 (by omega)]
      simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r by omega]
      zify [show 1 ≤ 4 * r * r + 3 * r by nlinarith, show 1 ≤ 2 * r by omega, show 2 ≤ r by omega]; ring
    rw [show 4 * h + 4 + 2 - 1 = 4 * h + 5 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 2 = 4 * h + 6 by omega, htarg] at hhi
    have hhi_ring : k < (2 * r + 1) ^ 2 := by
      have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
      omega
    obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
    obtain ⟨hx1, hx2⟩ : -(2 * (h : ℤ) + 4) ≤ (spiralXY k).1 ∧ (spiralXY k).1 ≤ -2 := by
      rw [hxy]; unfold ringEdgeXY
      interval_cases e <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;> omega
    by_cases hx4 : (spiralXY k).1 = -(2 * (h : ℤ) + 4)
    · refine ⟨4 * h + 4 + 2, by omega, ?_⟩
      rw [black_at h 2 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; left; omega
    · by_cases hx3 : (spiralXY k).1 = -(2 * (h : ℤ) + 3)
      · refine ⟨4 * h + 4 + 0, by omega, ?_⟩
        rw [black_at h 0 (by omega)]; simp only [↓reduceIte]; left; omega
      · obtain ⟨i, hi, hxi⟩ := exists_black_x hh (x := (spiralXY k).1) (by omega) (by omega) (by omega) (by omega)
        exact ⟨i, by omega, Or.inl hxi.symm⟩
  · -- j = 3: prev is `4h+6` (ring `r-1 = 2h+4`), target is `4h+7` (ring `r = 2h+5`)
    set r := 2 * h + 5
    have hr : 7 ≤ r := by omega
    have hr1_ge : 6 ≤ r - 1 := by omega
    have hprev : predRedLabel (4 * h + 6) = (2 * (r - 1) - 1) ^ 2 + 2 * (r - 1) * 3 + (r - 3) := by
      rw [show 4 * h + 6 = 4 * h + 4 + 2 by omega, redLabel_at h 2 (by omega)]
      simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      rw [show 2 * h + 4 = r - 1 by omega]
      zify [show 1 ≤ 4 * (r - 1) * (r - 1) + 3 * (r - 1) by nlinarith,
        show 1 ≤ 2 * (r - 1) by omega, show 3 ≤ r by omega, show 1 ≤ r by omega]; ring
    have htarg : predRedLabel (4 * h + 7) = (2 * r - 1) ^ 2 + 2 * r * 1 + (r - 3) := by
      rw [show 4 * h + 7 = 4 * h + 4 + 3 by omega, redLabel_at h 3 (by omega)]
      simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
      rw [show 2 * h + 5 = r by omega]
      have h1 : r + 2 ≤ 4 * r * r := by nlinarith
      zify [show r ≤ 4 * r * r by omega, show 2 ≤ 4 * r * r - r by omega, show 1 ≤ 2 * r by omega, show 3 ≤ r by omega]; ring
    rw [show 4 * h + 4 + 3 - 1 = 4 * h + 6 by omega, hprev] at hlo
    rw [show 4 * h + 4 + 3 = 4 * h + 7 by omega, htarg] at hhi
    have hbd : (2 * (r - 1) + 1) ^ 2 = (2 * r - 1) ^ 2 := by rw [show 2 * (r - 1) + 1 = 2 * r - 1 by omega]
    by_cases hring : k < (2 * r - 1) ^ 2
    · obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r - 1) (k := k) (by omega) (by omega) (by rw [hbd]; exact hring)
      have hcell : spiralXY k = (2, -((r - 1 : ℕ) : ℤ)) ∨
          (0 ≤ (spiralXY k).1 ∧ (spiralXY k).1 ≤ 2 * (h : ℤ) + 4 ∧ (spiralXY k).1 ≠ 2) := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · simp only [Nat.reduceEqDiff, ↓reduceIte]
          by_cases ht2 : t = r
          · left; exact Prod.ext (by omega) (by omega)
          · right; omega
      rcases hcell with hspec | ⟨hx1, hx2, hx3⟩
      · refine ⟨4 * (h - 1) + 4 + 2, by omega, ?_⟩
        rw [hspec, black_at (h - 1) 2 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        right; right; left; dsimp [r]; omega
      · by_cases hx4 : (spiralXY k).1 = 2 * (h : ℤ) + 4
        · refine ⟨4 * h + 4 + 1, by omega, ?_⟩
          rw [black_at h 1 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; left; omega
        · obtain ⟨i, hi, hxi⟩ := exists_black_x hh (by omega) (by omega) (by omega) hx3
          exact ⟨i, by omega, Or.inl hxi.symm⟩
    · have hhi_ring : k < (2 * r + 1) ^ 2 := by
        have : (2 * r + 1) ^ 2 = (2 * r - 1) ^ 2 + 8 * r := by zify [show 1 ≤ 2 * r by omega]; ring
        omega
      obtain ⟨e, t, he, ht, hk_eq, hxy⟩ := spiralXY_cases_ring (r := r) (by omega) (by omega) hhi_ring
      obtain ⟨hx1, hx2⟩ : 3 ≤ (spiralXY k).1 ∧ (spiralXY k).1 ≤ 2 * (h : ℤ) + 5 := by
        rw [hxy]; unfold ringEdgeXY
        interval_cases e <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;> omega
      by_cases hx5 : (spiralXY k).1 = 2 * (h : ℤ) + 5
      · refine ⟨4 * h + 4 + 3, by omega, ?_⟩
        rw [black_at h 3 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; left; omega
      · by_cases hx4 : (spiralXY k).1 = 2 * (h : ℤ) + 4
        · refine ⟨4 * h + 4 + 1, by omega, ?_⟩
          rw [black_at h 1 (by omega)]; simp only [Nat.reduceEqDiff, ↓reduceIte]; left; omega
        · obtain ⟨i, hi, hxi⟩ := exists_black_x hh (x := (spiralXY k).1) (by omega) (by omega) (by omega) (by omega)
          exact ⟨i, by omega, Or.inl hxi.symm⟩

/-- **Theorem 1 (Game Satisfaction):** `predBlackLabel` and `predRedLabel` satisfy the exact
greedy two-color spiral queen game specification for every `n ≥ 0`. -/
theorem isGreedyGame_pred : IsGreedyGame predBlackLabel predRedLabel := by
  intro n
  induction n with
  | zero =>
    have hb0 := (base_rounds_valid 0 (by omega)).1
    have hr0 := (base_rounds_valid 0 (by omega)).2
    refine ⟨⟨fun i hi => by omega, fun i hi => by omega, fun k hk => ?_⟩,
            ⟨fun i hi => by omega, fun i hi => ?_, fun k hk => ?_⟩⟩
    · rcases hb0 k hk with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
      · exact Or.inl ⟨i, hi, heq⟩
      · exact Or.inr ⟨i, hi, by rw [spiralXY_predRedLabel]; exact hatt⟩
    · rw [spiralXY_predRedLabel, spiralXY_predBlackLabel]
      exact fun h => predBlack_not_attacks_predRed i 0 (by
        unfold attacks at h ⊢; rcases h with h | h | h | h <;> omega)
    · rcases hr0 k hk with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
      · exact Or.inl ⟨i, hi, heq⟩
      · exact Or.inr ⟨i, by omega, by rw [spiralXY_predBlackLabel]; exact hatt⟩
  | succ m ih =>
    constructor
    · refine ⟨fun i hi => ne_of_gt (predBlackLabel_strictMono hi), fun i _ => ?_, fun k hk => ?_⟩
      · rw [spiralXY_predBlackLabel, spiralXY_predRedLabel]
        exact predBlack_not_attacks_predRed (m + 1) i
      · by_cases hlt : k < predBlackLabel m
        · rcases ih.1.2.2 k hlt with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
          · exact Or.inl ⟨i, by omega, heq⟩
          · exact Or.inr ⟨i, by omega, hatt⟩
        · by_cases heq : k = predBlackLabel m
          · exact Or.inl ⟨m, by omega, heq⟩
          · by_cases hbase : m + 1 < 8
            · rcases (base_rounds_valid (m + 1) hbase).1 k hk with ⟨i, hi, hki⟩ | ⟨i, hi, hatt⟩
              · exact Or.inl ⟨i, hi, hki⟩
              · exact Or.inr ⟨i, hi, by rw [spiralXY_predRedLabel]; exact hatt⟩
            · set h := (m + 1 - 4) / 4
              set j := (m + 1 - 4) % 4
              have hh : 1 ≤ h := by omega
              have hj : j < 4 := by omega
              have hidx : 4 * h + 4 + j = m + 1 := by omega
              have hprev_idx : 4 * h + 4 + j - 1 = m := by omega
              obtain ⟨i, hi, hatt⟩ := block_gap_black hh hj (hprev_idx.symm ▸ (by omega)) (hidx.symm ▸ hk)
              exact Or.inr ⟨i, by omega, by rw [spiralXY_predRedLabel]; exact hatt⟩
    · refine ⟨fun i hi => ne_of_gt (predRedLabel_strictMono hi), fun i _ => ?_, fun k hk => ?_⟩
      · rw [spiralXY_predRedLabel, spiralXY_predBlackLabel]
        exact fun h => predBlack_not_attacks_predRed i (m + 1) (by
          unfold attacks at h ⊢; rcases h with h | h | h | h <;> omega)
      · by_cases hlt : k < predRedLabel m
        · rcases ih.2.2.2 k hlt with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
          · exact Or.inl ⟨i, by omega, heq⟩
          · exact Or.inr ⟨i, by omega, hatt⟩
        · by_cases heq : k = predRedLabel m
          · exact Or.inl ⟨m, by omega, heq⟩
          · by_cases hbase : m + 1 < 8
            · rcases (base_rounds_valid (m + 1) hbase).2 k hk with ⟨i, hi, hki⟩ | ⟨i, hi, hatt⟩
              · exact Or.inl ⟨i, hi, hki⟩
              · exact Or.inr ⟨i, by omega, by rw [spiralXY_predBlackLabel]; exact hatt⟩
            · set h := (m + 1 - 4) / 4
              set j := (m + 1 - 4) % 4
              have hh : 1 ≤ h := by omega
              have hj : j < 4 := by omega
              have hidx : 4 * h + 4 + j = m + 1 := by omega
              have hprev_idx : 4 * h + 4 + j - 1 = m := by omega
              obtain ⟨i, hi, hatt⟩ := block_gap_red hh hj (hprev_idx.symm ▸ (by omega)) (hidx.symm ▸ hk)
              exact Or.inr ⟨i, by omega, by rw [spiralXY_predBlackLabel]; exact hatt⟩

/-- Uniqueness of the greedy two-color spiral queen game sequences. -/
theorem isGreedyGame_unique {a₁ b₁ a₂ b₂ : ℕ → ℕ}
    (h₁ : IsGreedyGame a₁ b₁) (h₂ : IsGreedyGame a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  suffices h : ∀ n, a₁ n = a₂ n ∧ b₁ n = b₂ n by
    exact ⟨funext (fun n => (h n).1), funext (fun n => (h n).2)⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have ha : a₁ n = a₂ n := by
      rcases lt_trichotomy (a₁ n) (a₂ n) with hlt | heq | hgt
      · rcases (h₂ n).1.2.2 (a₁ n) hlt with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
        · rw [← (ih i hi).1] at heq; exact ((h₁ n).1.1 i hi heq).elim
        · rw [← (ih i hi).2] at hatt; exact ((h₁ n).1.2.1 i hi hatt).elim
      · exact heq
      · rcases (h₁ n).1.2.2 (a₂ n) hgt with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
        · rw [(ih i hi).1] at heq; exact ((h₂ n).1.1 i hi heq).elim
        · rw [(ih i hi).2] at hatt; exact ((h₂ n).1.2.1 i hi hatt).elim
    have hb : b₁ n = b₂ n := by
      rcases lt_trichotomy (b₁ n) (b₂ n) with hlt | heq | hgt
      · rcases (h₂ n).2.2.2 (b₁ n) hlt with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
        · rw [← (ih i hi).2] at heq; exact ((h₁ n).2.1 i hi heq).elim
        · have hia : a₂ i = a₁ i := by
            rcases Nat.lt_or_eq_of_le hi with hlti | rfl
            · exact (ih i hlti).1.symm
            · exact ha.symm
          rw [hia] at hatt; exact ((h₁ n).2.2.1 i hi hatt).elim
      · exact heq
      · rcases (h₁ n).2.2.2 (b₂ n) hgt with ⟨i, hi, heq⟩ | ⟨i, hi, hatt⟩
        · rw [(ih i hi).2] at heq; exact ((h₂ n).2.1 i hi heq).elim
        · have hia : a₁ i = a₂ i := by
            rcases Nat.lt_or_eq_of_le hi with hlti | rfl
            · exact (ih i hlti).1
            · exact ha
          rw [hia] at hatt; exact ((h₂ n).2.2.1 i hi hatt).elim
    exact ⟨ha, hb⟩

/-! ### Section 7: Rahid Zaman's Recurrence (OEIS A395348) -/

/-- Closed-form recurrence for `predBlackLabel`. -/
theorem predBlackLabel_recurrence {n : ℕ} (hn : 2 ≤ n) :
    predBlackLabel (n + 4) = predBlackLabel n + 8 * n + 34 := by
  by_cases hlt : n < 4
  · interval_cases n <;> decide
  · set h := (n - 4) / 4
    set j := (n - 4) % 4
    have hj : j < 4 := Nat.mod_lt _ (by omega)
    have hne : n = 4 * h + 4 + j := by omega
    rw [hne, show 4 * h + 4 + j + 4 = 4 * (h + 1) + 4 + j by omega,
      blackLabel_at (h + 1) j hj, blackLabel_at h j hj]
    interval_cases j <;> simp only [Nat.reduceEqDiff, ↓reduceIte] <;>
      (zify [show 1 ≤ 4 * (2 * h + 3) * (2 * h + 3) + (2 * h + 3) by nlinarith,
             show 1 ≤ 4 * (2 * (h + 1) + 3) * (2 * (h + 1) + 3) + (2 * (h + 1) + 3) by nlinarith,
             show 3 * (2 * h + 4) ≤ 4 * (2 * h + 4) * (2 * h + 4) by nlinarith,
             show 3 * (2 * (h + 1) + 4) ≤ 4 * (2 * (h + 1) + 4) * (2 * (h + 1) + 4) by nlinarith,
             show 3 * (2 * h + 5) ≤ 4 * (2 * h + 5) * (2 * h + 5) by nlinarith,
             show 3 * (2 * (h + 1) + 5) ≤ 4 * (2 * (h + 1) + 5) * (2 * (h + 1) + 5) by nlinarith];
       ring)

/-- **Main Theorem (Rahid Zaman's OEIS A395348 Conjecture):**
For any sequences `(a, b)` generated by the two-color greedy spiral queen game,
`a (n + 4) = a n + 8 * n + 34` for every integer `n ≥ 2`. -/
theorem zaman_A395348_recurrence {a b : ℕ → ℕ} (h : IsGreedyGame a b) {n : ℕ} (hn : 2 ≤ n) :
    a (n + 4) = a n + 8 * n + 34 := by
  have heq := (isGreedyGame_unique h isGreedyGame_pred).1
  rw [heq]
  exact predBlackLabel_recurrence hn

end ZamanA395348
