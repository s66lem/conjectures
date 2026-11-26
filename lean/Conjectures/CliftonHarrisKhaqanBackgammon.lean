import Mathlib

/-!
# Resolution of Clifton–Harris–Khaqan Question 5.2 (Backgammon Parking Enumeration)

Reference: A. Clifton, P. E. Harris, M. Khaqan,
"Parking functions inspired by board games", arXiv:2611.29890v1 (23 Nov 2026), Section 5.

Under the backgammon parking scheme on `n` spots (`Fin n`), cars `0, 1, ..., n - 1` arrive
in order with preference list `a : Fin n → Fin n`. If spot `a c` is free, car `c` parks there;
otherwise car `c` displaces the current occupant `j` to the leftmost unoccupied spot.

We formally prove:
1. **Lemma A (`polyOfOutcome_cons1`):** For every `n : ℕ` and every outcome `σ : Fin n → Fin n`,
   `P_{1 ⊕ σ}(y) = Φ(P_σ(y))`, where `P_π(y) = ∑_{a ∈ O_B⁻¹(π)} y^{L(a)}`, `L(a)` is the longest
   distinct prefix length of `a`, and `Φ(y^j) = y + y^2 + ... + y^(j+1)`.
2. **Lemma B (`polyOfOutcome_delta`):** For the decreasing outcome `δ_n(p) = n - 1 - p` (`n ≥ 2`),
   `P_{δ_n}(y) = y * P_{δ_{n-1}}(y) + P_{1 ⊕ δ_{n-2}}(y)`.
3. **Base generating function (`polyOfOutcome_delta_eq`):** With `m(x) = ∑ M_n x^n` (Motzkin series)
   and `p(x) = x + x^2 m(x)`, `[y^j] P_{δ_n}(y) = [x^n] p(x)^j` for every `n, j ∈ ℕ`.
4. **Main Theorem (`clifton_harris_khaqan_Q52`):** For all integers `n ≥ k ≥ 1`,
   `|O_B⁻¹(1 2 ... k n (n-1) ... (k+1))| = ∑_{i=0}^{k-1} B(k - 1, i) * [x^(n - k)] m(x)^(k + 1 - i)`,
   where `B(r, i)` is Catalan's triangle.
-/

namespace CliftonHarrisKhaqanBackgammon

open Finset Polynomial PowerSeries

/-! ### Section 1: The backgammon parking process -/

/-- State of `n` parking spots: `none` if empty, `some c` if occupied by car `c`. -/
abbrev SpotState (n : ℕ) := Fin n → Option (Fin n)

/-- Empty parking lot of size `n`. -/
def emptyState (n : ℕ) : SpotState n := fun _ => none

/-- Leftmost unoccupied spot (`none` if every spot is occupied). -/
def leftmostFree {n : ℕ} (s : SpotState n) : Option (Fin n) :=
  (List.finRange n).find? fun p => (s p).isNone

private lemma leftmostFree_eq_none_iff {n : ℕ} {s : SpotState n} :
    leftmostFree s = none ↔ ∀ p : Fin n, s p ≠ none := by
  unfold leftmostFree
  rw [List.find?_eq_none]
  constructor
  · intro h p hp
    have := h p (List.mem_finRange p)
    simp [hp] at this
  · intro h p _
    cases hp : s p with
    | none => exact absurd hp (h p)
    | some _ => simp

private lemma leftmostFree_spec {n : ℕ} {s : SpotState n} {q : Fin n}
    (h : leftmostFree s = some q) : s q = none := by
  unfold leftmostFree at h
  have hspec := List.find?_some h
  simpa [Option.isNone_iff_eq_none] using hspec

private lemma leftmostFree_min {n : ℕ} {s : SpotState n} {q p : Fin n}
    (h : leftmostFree s = some q) (hp : p < q) : s p ≠ none := by
  unfold leftmostFree at h
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨_, as, bs, heq, hbefore⟩ := h
  have hnodup : (List.finRange n).Pairwise (· < ·) := List.pairwise_lt_finRange n
  rw [heq, List.pairwise_append] at hnodup
  have hmem : p ∈ as ++ q :: bs := heq ▸ List.mem_finRange p
  rw [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hpa | rfl | hpb
  · have hfalse := hbefore p hpa
    intro hnone; simp [hnone] at hfalse
  · exact absurd hp (lt_irrefl p)
  · have hqp : q < p := (List.pairwise_cons.mp hnodup.2.1).1 p hpb
    exact absurd (lt_trans hp hqp) (lt_irrefl p)

private lemma leftmostFree_eq_some_iff {n : ℕ} {s : SpotState n} {q : Fin n} :
    leftmostFree s = some q ↔ s q = none ∧ ∀ p : Fin n, p < q → s p ≠ none := by
  constructor
  · intro h
    exact ⟨leftmostFree_spec h, fun p hp => leftmostFree_min h hp⟩
  · rintro ⟨hq, hmin⟩
    cases hf : leftmostFree s with
    | none => exact absurd hq (leftmostFree_eq_none_iff.mp hf q)
    | some r =>
      have hr : s r = none := leftmostFree_spec hf
      have hqr : r = q := by
        rcases lt_trichotomy r q with hlt | heq | hgt
        · exact absurd hr (hmin r hlt)
        · exact heq
        · exact absurd hq (leftmostFree_min hf hgt)
      rw [hqr]

/-- One step of the backgammon parking scheme: car `c` arrives preferring spot `pref`.
If `pref` is empty, `c` parks there; otherwise `c` takes `pref` and the displaced occupant
moves to the leftmost empty spot (`leftmostFree`). -/
def backgammonStep {n : ℕ} (s : SpotState n) (c pref : Fin n) : SpotState n :=
  match s pref with
  | none => Function.update s pref (some c)
  | some j =>
    let s₁ := Function.update s pref (some c)
    match leftmostFree s₁ with
    | none => s₁
    | some q => Function.update s₁ q (some j)

/-- Run the first `t` cars (`0, ..., t - 1`) of preference list `a : Fin n → Fin n`. -/
def backgammonRun {n : ℕ} (a : Fin n → Fin n) : (t : ℕ) → t ≤ n → SpotState n
  | 0, _ => emptyState n
  | t + 1, ht => backgammonStep (backgammonRun a t (by omega)) ⟨t, ht⟩ (a ⟨t, ht⟩)

/-- Final spot occupancy after all `n` cars have parked. -/
def backgammonFinal {n : ℕ} (a : Fin n → Fin n) : SpotState n :=
  backgammonRun a n le_rfl

/-- Preference list `a` realizes outcome permutation `π : Fin n → Fin n` (car `π p` in spot `p`). -/
def outcomeMatches {n : ℕ} (a : Fin n → Fin n) (π : Fin n → Fin n) : Prop :=
  ∀ p : Fin n, backgammonFinal a p = some (π p)

instance instDecidableOutcomeMatches {n : ℕ} (a π : Fin n → Fin n) :
    Decidable (outcomeMatches a π) := by
  unfold outcomeMatches; infer_instance

/-- Finite set `O_B⁻¹(π)` of all preference lists in `(Fin n → Fin n)` with outcome `π`. -/
def outcomeSet {n : ℕ} (π : Fin n → Fin n) : Finset (Fin n → Fin n) :=
  Finset.univ.filter fun a => outcomeMatches a π

/-! ### Section 2: Structural invariants (F1) and (F2) -/

private def occCount {n : ℕ} (s : SpotState n) : ℕ :=
  (Finset.univ.filter fun p : Fin n => s p ≠ none).card

/-- (F1) Monotonicity: once a spot is occupied, it remains occupied after any step. -/
private lemma backgammonStep_isSome_of_isSome {n : ℕ} (s : SpotState n) (c pref p : Fin n)
    (hp : s p ≠ none) : backgammonStep s c pref p ≠ none := by
  unfold backgammonStep
  cases hsp : s pref with
  | none =>
    by_cases hpa : p = pref
    · subst hpa; simp
    · simp [Function.update_of_ne hpa, hp]
  | some j =>
    dsimp only
    cases hfind : leftmostFree (Function.update s pref (some c)) with
    | none =>
      dsimp only
      by_cases hpa : p = pref
      · subst hpa; simp
      · simp [Function.update_of_ne hpa, hp]
    | some q =>
      dsimp only
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Function.update_of_ne hpq]
        by_cases hpa : p = pref
        · subst hpa; simp
        · simp [Function.update_of_ne hpa, hp]

/-- Monotonicity across any prefix of steps. -/
private lemma backgammonRun_isSome_mono {n : ℕ} (a : Fin n → Fin n) {t₁ t₂ : ℕ}
    (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ n) (p : Fin n) (hp : backgammonRun a t₁ (by omega) p ≠ none) :
    backgammonRun a t₂ h2 p ≠ none := by
  induction t₂ with
  | zero =>
    have : t₁ = 0 := by omega
    subst this; exact hp
  | succ t ih =>
    by_cases h : t₁ ≤ t
    · exact backgammonStep_isSome_of_isSome _ _ _ p (ih h (by omega) hp)
    · have : t₁ = t + 1 := by omega
      subst this; exact hp

/-- Occupancy count increases by 1 at each step whenever `occCount s < n`. -/
private lemma occCount_backgammonStep {n : ℕ} (s : SpotState n) (c pref : Fin n)
    (hlt : occCount s < n) : occCount (backgammonStep s c pref) = occCount s + 1 := by
  unfold backgammonStep
  cases hsp : s pref with
  | none =>
    unfold occCount
    have hset : (Finset.univ.filter fun p : Fin n => Function.update s pref (some c) p ≠ none) =
        insert pref (Finset.univ.filter fun p : Fin n => s p ≠ none) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases h : p = pref
      · subst h; simp
      · simp [h]
    rw [hset, Finset.card_insert_of_notMem]
    simp [hsp]
  | some j =>
    dsimp only
    have hex : ∃ q : Fin n, Function.update s pref (some c) q = none := by
      have hcard : (Finset.univ.filter fun p : Fin n => s p ≠ none).card < Fintype.card (Fin n) := by
        simpa [occCount] using hlt
      obtain ⟨q, hq⟩ : ∃ q : Fin n, s q = none := by
        by_contra hall
        push Not at hall
        have : (Finset.univ.filter fun p : Fin n => s p ≠ none) = Finset.univ := by
          ext p; simp [hall p]
        rw [this, Finset.card_univ] at hcard
        exact lt_irrefl _ hcard
      have hne : q ≠ pref := by intro heq; subst heq; rw [hq] at hsp; cases hsp
      exact ⟨q, by rw [Function.update_of_ne hne, hq]⟩
    cases hfind : leftmostFree (Function.update s pref (some c)) with
    | none =>
      exfalso
      obtain ⟨q, hq⟩ := hex
      exact (leftmostFree_eq_none_iff.mp hfind q) hq
    | some q =>
      have hq_none : Function.update s pref (some c) q = none := leftmostFree_spec hfind
      have hq_ne : q ≠ pref := by intro heq; subst heq; simp at hq_none
      have hsq : s q = none := by rwa [Function.update_of_ne hq_ne] at hq_none
      unfold occCount
      have hset : (Finset.univ.filter fun p : Fin n =>
            Function.update (Function.update s pref (some c)) q (some j) p ≠ none) =
          insert q (Finset.univ.filter fun p : Fin n => s p ≠ none) := by
        ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hpq : p = q
        · subst hpq; simp
        · rw [Function.update_of_ne hpq]
          by_cases hpa : p = pref
          · subst hpa; simp [hsp, hpq]
          · simp [Function.update_of_ne hpa, hpq]
      rw [hset, Finset.card_insert_of_notMem]
      simp [hsq]

private lemma occCount_backgammonRun {n : ℕ} (a : Fin n → Fin n) :
    ∀ (t : ℕ) (ht : t ≤ n), occCount (backgammonRun a t ht) = t := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [backgammonRun, emptyState, occCount]
  | succ t ih =>
    intro ht
    rw [backgammonRun, occCount_backgammonStep]
    · rw [ih (by omega)]
    · rw [ih (by omega)]; omega

/-- If `s p = some d` and `p` is never chosen by `pref` (and `p` is already occupied), then `s p` stays `some d`. -/
private lemma backgammonStep_preserve_of_ne {n : ℕ} (s : SpotState n) (c pref p d : Fin n)
    (hsp : s p = some d) (hne : p ≠ pref) :
    backgammonStep s c pref p = some d := by
  unfold backgammonStep
  cases hpref : s pref with
  | none =>
    dsimp only
    rw [Function.update_of_ne hne, hsp]
  | some j =>
    dsimp only
    cases hfind : leftmostFree (Function.update s pref (some c)) with
    | none =>
      dsimp only
      rw [Function.update_of_ne hne, hsp]
    | some q =>
      dsimp only
      have hq_none : Function.update s pref (some c) q = none := leftmostFree_spec hfind
      have hpq : p ≠ q := by
        intro heq; subst heq
        rw [Function.update_of_ne hne, hsp] at hq_none
        cases hq_none
      rw [Function.update_of_ne hpq, Function.update_of_ne hne, hsp]

/-- Every car parked at step `< t` is `< t`. -/
private lemma backgammonStep_car_lt {n : ℕ} (s : SpotState n) (c pref : Fin n) {B : ℕ}
    (hc : c.val < B) (hs : ∀ p d, s p = some d → d.val < B) :
    ∀ p d, backgammonStep s c pref p = some d → d.val < B := by
  intro p d hpd
  unfold backgammonStep at hpd
  cases hpref : s pref with
  | none =>
    rw [hpref] at hpd; dsimp only at hpd
    by_cases h : p = pref
    · subst h; simp at hpd; subst hpd; exact hc
    · rw [Function.update_of_ne h] at hpd; exact hs p d hpd
  | some j =>
    rw [hpref] at hpd; dsimp only at hpd
    have hj : j.val < B := hs pref j hpref
    cases hfind : leftmostFree (Function.update s pref (some c)) with
    | none =>
      rw [hfind] at hpd; dsimp only at hpd
      by_cases h : p = pref
      · subst h; simp at hpd; subst hpd; exact hc
      · rw [Function.update_of_ne h] at hpd; exact hs p d hpd
    | some q =>
      rw [hfind] at hpd; dsimp only at hpd
      by_cases hpq : p = q
      · subst hpq; simp at hpd; subst hpd; exact hj
      · rw [Function.update_of_ne hpq] at hpd
        by_cases h : p = pref
        · subst h; simp at hpd; subst hpd; exact hc
        · rw [Function.update_of_ne h] at hpd; exact hs p d hpd

/-- If a spot `p` holds a car `d ≠ car0` at step `t`, it can never hold `car0` later
if every later car arriving has index `> car0`. -/
private lemma backgammonStep_ne_zero_of_ne_zero {n : ℕ} (hn : 0 < n) (s : SpotState n) (c pref p : Fin n)
    (hc : c.val ≠ 0) (hp_occ : s p ≠ none) (hp_ne : s p ≠ some ⟨0, hn⟩) :
    backgammonStep s c pref p ≠ some ⟨0, hn⟩ := by
  unfold backgammonStep
  cases hpref : s pref with
  | none =>
    dsimp only
    by_cases h : p = pref
    · subst h; simp [Fin.ext_iff, hc]
    · rw [Function.update_of_ne h]; exact hp_ne
  | some j =>
    dsimp only
    cases hfind : leftmostFree (Function.update s pref (some c)) with
    | none =>
      dsimp only
      by_cases h : p = pref
      · subst h; simp [Fin.ext_iff, hc]
      · rw [Function.update_of_ne h]; exact hp_ne
    | some q =>
      dsimp only
      have hq_none : Function.update s pref (some c) q = none := leftmostFree_spec hfind
      have hpq : p ≠ q := by
        intro heq; subst heq
        by_cases hpa : p = pref
        · subst hpa; simp at hq_none
        · rw [Function.update_of_ne hpa] at hq_none; exact hp_occ hq_none
      rw [Function.update_of_ne hpq]
      by_cases h : p = pref
      · subst h; simp [Fin.ext_iff, hc]
      · rw [Function.update_of_ne h]; exact hp_ne

private lemma backgammonRun_ne_zero_mono {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n)
    {t₁ t₂ : ℕ} (h1 : 1 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ n) (p : Fin n)
    (hp_occ : backgammonRun a t₁ (by omega) p ≠ none)
    (hp_ne : backgammonRun a t₁ (by omega) p ≠ some ⟨0, hn⟩) :
    backgammonRun a t₂ h2 p ≠ some ⟨0, hn⟩ := by
  induction t₂ with
  | zero => omega
  | succ t ih =>
    by_cases h : t₁ ≤ t
    · have hocc : backgammonRun a t (by omega) p ≠ none :=
        backgammonRun_isSome_mono a h (by omega) p hp_occ
      have hne : backgammonRun a t (by omega) p ≠ some ⟨0, hn⟩ := ih h (by omega) hp_occ hp_ne
      exact backgammonStep_ne_zero_of_ne_zero hn _ ⟨t, h2⟩ _ p (by simp; omega) hocc hne
    · have : t₁ = t + 1 := by omega
      subst this; exact hp_ne

/-! ### Section 3: Longest distinct prefix length `L(a)` and polynomial `P_π(y)` -/

/-- Predicate: the first `t` entries of `a : Fin n → Fin n` are pairwise distinct. -/
def isDistinctPrefix {n : ℕ} (a : Fin n → Fin n) (t : ℕ) : Prop :=
  ∀ i j : Fin n, i.val < t → j.val < t → a i = a j → i = j

instance instDecidableIsDistinctPrefix {n : ℕ} (a : Fin n → Fin n) (t : ℕ) :
    Decidable (isDistinctPrefix a t) := by
  unfold isDistinctPrefix; infer_instance

/-- Length `L(a)` of the longest prefix of pairwise distinct entries of `a : Fin n → Fin n`. -/
def distinctPrefixLen {n : ℕ} (a : Fin n → Fin n) : ℕ :=
  ((Finset.range (n + 1)).filter (isDistinctPrefix a)).max'
    ⟨0, by simp [isDistinctPrefix]⟩

private lemma distinctPrefixLen_le {n : ℕ} (a : Fin n → Fin n) :
    distinctPrefixLen a ≤ n := by
  have hmem := Finset.max'_mem ((Finset.range (n + 1)).filter (isDistinctPrefix a))
    ⟨0, by simp [isDistinctPrefix]⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hmem
  unfold distinctPrefixLen
  omega

private lemma isDistinctPrefix_distinctPrefixLen {n : ℕ} (a : Fin n → Fin n) :
    isDistinctPrefix a (distinctPrefixLen a) := by
  have hmem := Finset.max'_mem ((Finset.range (n + 1)).filter (isDistinctPrefix a))
    ⟨0, by simp [isDistinctPrefix]⟩
  exact (Finset.mem_filter.mp hmem).2

private lemma le_distinctPrefixLen_iff {n : ℕ} (a : Fin n → Fin n) {t : ℕ} (ht : t ≤ n) :
    t ≤ distinctPrefixLen a ↔ isDistinctPrefix a t := by
  constructor
  · intro hle i j hi hj hij
    exact isDistinctPrefix_distinctPrefixLen a i j (by omega) (by omega) hij
  · intro hdist
    exact Finset.le_max' _ t (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hdist⟩)

/-- Generating polynomial `P_π(y) = ∑_{a ∈ O_B⁻¹(π)} y^{L(a)}` in `ℚ[X]`. -/
noncomputable def polyOfOutcome {n : ℕ} (π : Fin n → Fin n) : Polynomial ℚ :=
  ∑ a ∈ outcomeSet π, Polynomial.X ^ distinctPrefixLen a

/-- Linear operator `Φ : ℚ[X] →ₗ[ℚ] ℚ[X]` defined by `Φ(y^j) = ∑_{r=1}^{j+1} y^r`. -/
noncomputable def phiOp (P : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ range (P.natDegree + 1),
    Polynomial.C (P.coeff j) * ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1)

private lemma phiOp_X_pow (j : ℕ) :
    phiOp (Polynomial.X ^ j) = ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1) := by
  unfold phiOp
  rw [Polynomial.natDegree_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Polynomial.coeff_X_pow, hbj]
  · intro hj; simp at hj

private lemma phiOp_eq_sum_support {s : Finset ℕ} (P : Polynomial ℚ)
    (hs : ∀ j, P.coeff j ≠ 0 → j ∈ s) :
    phiOp P = ∑ j ∈ s, Polynomial.C (P.coeff j) * ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1) := by
  unfold phiOp
  have h1 : ∑ j ∈ range (P.natDegree + 1),
      Polynomial.C (P.coeff j) * ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1) =
      ∑ j ∈ range (P.natDegree + 1) ∪ s,
        Polynomial.C (P.coeff j) * ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1) := by
    refine Finset.sum_subset Finset.subset_union_left (fun j _ hj => ?_)
    have hgt : P.natDegree < j := by simp only [Finset.mem_range] at hj; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, map_zero, zero_mul]
  have h2 : ∑ j ∈ s,
      Polynomial.C (P.coeff j) * ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1) =
      ∑ j ∈ range (P.natDegree + 1) ∪ s,
        Polynomial.C (P.coeff j) * ∑ r ∈ range (j + 1), Polynomial.X ^ (r + 1) := by
    refine Finset.sum_subset Finset.subset_union_right (fun j _ hj => ?_)
    have hc0 : P.coeff j = 0 := by by_contra hne; exact hj (hs j hne)
    rw [hc0, map_zero, zero_mul]
  exact h1.trans h2.symm

private lemma phiOp_add (P Q : Polynomial ℚ) : phiOp (P + Q) = phiOp P + phiOp Q := by
  set M := max P.natDegree Q.natDegree + 1
  have hPQ : ∀ j, (P + Q).coeff j ≠ 0 → j ∈ range M := by
    intro j hj
    simp only [Finset.mem_range]
    by_contra hge
    have h1 : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : Q.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.coeff_add, h1, h2, add_zero] at hj
    exact hj rfl
  have hP : ∀ j, P.coeff j ≠ 0 → j ∈ range M := fun j hj =>
    Finset.mem_range.mpr (by have := Polynomial.le_natDegree_of_ne_zero hj; omega)
  have hQ : ∀ j, Q.coeff j ≠ 0 → j ∈ range M := fun j hj =>
    Finset.mem_range.mpr (by have := Polynomial.le_natDegree_of_ne_zero hj; omega)
  rw [phiOp_eq_sum_support (P + Q) hPQ, phiOp_eq_sum_support P hP, phiOp_eq_sum_support Q hQ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.coeff_add, map_add, add_mul]

private lemma phiOp_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) :
    phiOp (∑ i ∈ s, f i) = ∑ i ∈ s, phiOp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [phiOp]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, phiOp_add, ih, Finset.sum_insert ha]

private lemma phiOp_C_mul (c : ℚ) (P : Polynomial ℚ) :
    phiOp (Polynomial.C c * P) = Polynomial.C c * phiOp P := by
  set M := P.natDegree + 1
  have hcP : ∀ j, (Polynomial.C c * P).coeff j ≠ 0 → j ∈ range M := by
    intro j hj
    rw [Polynomial.coeff_C_mul] at hj
    have hP0 : P.coeff j ≠ 0 := right_ne_zero_of_mul hj
    exact Finset.mem_range.mpr (by have := Polynomial.le_natDegree_of_ne_zero hP0; omega)
  rw [phiOp_eq_sum_support (Polynomial.C c * P) hcP, phiOp, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.coeff_C_mul, map_mul, mul_assoc]

/-! ### Section 4: Lemma A — General car-1 reduction `P_{1 ⊕ σ} = Φ(P_σ)` -/

/-- Outcome `1 ⊕ σ : Fin (n + 1) → Fin (n + 1)` placing car `0` in spot `0` and `σ p + 1` in spot `p + 1`. -/
def cons1 {n : ℕ} (σ : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun p => (σ p).succ)

/-- Lift a state `s : SpotState n` to `SpotState (n + 1)` with `s0` in spot `0` and cars shifted by `+1`. -/
private def liftState {n : ℕ} (s0 : Option (Fin (n + 1))) (s : SpotState n) : SpotState (n + 1) :=
  Fin.cases s0 (fun p => (s p).map Fin.succ)

/-- When spot `0` is occupied (`s0 ≠ none`), one step of car `c.succ` with preference `pref.succ`
on `liftState s0 s` equals `liftState s0 (backgammonStep s c pref)`. -/
private lemma backgammonStep_liftState {n : ℕ} (s0 : Option (Fin (n + 1))) (hs0 : s0 ≠ none)
    (s : SpotState n) (c pref : Fin n) :
    backgammonStep (liftState s0 s) c.succ pref.succ = liftState s0 (backgammonStep s c pref) := by
  unfold backgammonStep
  have hpref : liftState s0 s pref.succ = (s pref).map Fin.succ := rfl
  rw [hpref]
  cases hsp : s pref with
  | none =>
    simp only [Option.map_none]
    funext p
    refine Fin.cases ?_ (fun q => ?_) p
    · simp [liftState, Function.update_of_ne (Fin.succ_ne_zero pref).symm]
    · by_cases hqp : q = pref
      · subst hqp; simp [liftState]
      · simp [liftState, Function.update_of_ne hqp, Function.update_of_ne (Fin.succ_injective n |>.ne hqp)]
  | some j =>
    simp only [Option.map_some]
    have hupd : Function.update (liftState s0 s) pref.succ (some c.succ) =
        liftState s0 (Function.update s pref (some c)) := by
      funext p
      refine Fin.cases ?_ (fun q => ?_) p
      · simp [liftState, Function.update_of_ne (Fin.succ_ne_zero pref).symm]
      · by_cases hqp : q = pref
        · subst hqp; simp [liftState]
        · simp [liftState, Function.update_of_ne hqp, Function.update_of_ne (Fin.succ_injective n |>.ne hqp)]
    rw [hupd]
    have hfind_eq : leftmostFree (liftState s0 (Function.update s pref (some c))) =
        (leftmostFree (Function.update s pref (some c))).map Fin.succ := by
      cases hinner : leftmostFree (Function.update s pref (some c)) with
      | none =>
        rw [Option.map_none, leftmostFree_eq_none_iff]
        intro p
        refine Fin.cases hs0 (fun q => ?_) p
        have hq := leftmostFree_eq_none_iff.mp hinner q
        simp only [liftState, Fin.cases_succ, ne_eq, Option.map_eq_none_iff]
        exact hq
      | some q =>
        rw [Option.map_some, leftmostFree_eq_some_iff]
        refine ⟨?_, ?_⟩
        · simp only [liftState, Fin.cases_succ, Option.map_eq_none_iff]
          exact leftmostFree_spec hinner
        · intro p hp
          refine Fin.cases (fun _ => hs0) (fun r hr => ?_) p hp
          have hr_lt : r < q := Fin.succ_lt_succ_iff.mp hr
          simp only [liftState, Fin.cases_succ, ne_eq, Option.map_eq_none_iff]
          exact leftmostFree_min hinner hr_lt
    rw [hfind_eq]
    cases leftmostFree (Function.update s pref (some c)) with
    | none =>
      rfl
    | some q =>
      simp only [Option.map_some]
      funext p
      refine Fin.cases ?_ (fun r => ?_) p
      · simp [liftState, Function.update_of_ne (Fin.succ_ne_zero q).symm]
      · by_cases hrq : r = q
        · subst hrq; simp [liftState]
        · simp [liftState, Function.update_of_ne hrq, Function.update_of_ne (Fin.succ_injective n |>.ne hrq)]

/-- Running cars `1..n` from `liftState (some 0) (backgammonRun a' t)` produces `liftState (some 0) (backgammonRun a' n)`. -/
private lemma backgammonRun_liftState_from {n : ℕ} (a : Fin (n + 1) → Fin (n + 1))
    (a' : Fin n → Fin n) (ha : ∀ i : Fin n, a i.succ = (a' i).succ)
    (t₀ : ℕ) (ht₀ : t₀ ≤ n)
    (hinit : backgammonRun a (t₀ + 1) (by omega) =
      liftState (some 0) (backgammonRun a' t₀ ht₀)) :
    ∀ (t : ℕ) (ht : t ≤ n), t₀ ≤ t →
      backgammonRun a (t + 1) (by omega) = liftState (some 0) (backgammonRun a' t ht) := by
  intro t
  induction t with
  | zero =>
    intro ht hle
    have : t₀ = 0 := by omega
    subst this; exact hinit
  | succ t ih =>
    intro ht hle
    by_cases h : t₀ ≤ t
    · rw [backgammonRun, ih (by omega) h]
      have ha_t : a ⟨t + 1, by omega⟩ = (a' ⟨t, by omega⟩).succ := ha ⟨t, by omega⟩
      have hc_t : (⟨t + 1, by omega⟩ : Fin (n + 1)) = (⟨t, by omega⟩ : Fin n).succ := rfl
      rw [ha_t, hc_t, backgammonStep_liftState (some 0) (by simp)]
      rfl
    · have : t₀ = t + 1 := by omega
      subst this; exact hinit

/-- Case 1 forward map: prepend `0` to `(a' i).succ`. -/
private def prependZero {n : ℕ} (a' : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun i => (a' i).succ)

private lemma outcomeMatches_prependZero {n : ℕ} {a' σ : Fin n → Fin n} :
    outcomeMatches (prependZero a') (cons1 σ) ↔ outcomeMatches a' σ := by
  have hrun : backgammonFinal (prependZero a') = liftState (some 0) (backgammonFinal a') := by
    apply backgammonRun_liftState_from (prependZero a') a' (fun _ => rfl) 0 (Nat.zero_le n)
    · funext p
      refine Fin.cases ?_ (fun q => ?_) p
      · simp [backgammonRun, backgammonStep, emptyState, prependZero, liftState]
      · simp [backgammonRun, backgammonStep, emptyState, prependZero, liftState]
    · exact Nat.zero_le n
  constructor
  · intro h p
    have hp := h p.succ
    rw [hrun] at hp
    simp only [liftState, cons1, Fin.cases_succ] at hp
    cases hfp : backgammonFinal a' p with
    | none => rw [hfp] at hp; simp at hp
    | some c =>
      rw [hfp] at hp; simp only [Option.map_some, Option.some.injEq, Fin.succ_inj] at hp
      rw [hp]
  · intro h p
    rw [hrun]
    refine Fin.cases ?_ (fun q => ?_) p
    · rfl
    · simp only [liftState, cons1, Fin.cases_succ, h q, Option.map_some]

private lemma distinctPrefixLen_prependZero {n : ℕ} (a' : Fin n → Fin n) :
    distinctPrefixLen (prependZero a') = distinctPrefixLen a' + 1 := by
  have hle1 : distinctPrefixLen (prependZero a') ≤ n + 1 := distinctPrefixLen_le _
  have hle2 : distinctPrefixLen a' ≤ n := distinctPrefixLen_le _
  apply le_antisymm
  · have hpos : 1 ≤ distinctPrefixLen (prependZero a') := by
      rw [le_distinctPrefixLen_iff _ (by omega)]
      intro i j hi hj _
      exact Fin.ext (by omega)
    have hsub : distinctPrefixLen (prependZero a') - 1 ≤ distinctPrefixLen a' := by
      rw [le_distinctPrefixLen_iff _ (by omega)]
      intro i j hi hj hij
      have hdist := isDistinctPrefix_distinctPrefixLen (prependZero a')
      have heq := hdist i.succ j.succ (by simp; omega) (by simp; omega)
        (by simp [prependZero, hij])
      exact Fin.succ_inj.mp heq
    omega
  · rw [le_distinctPrefixLen_iff _ (by omega)]
    intro i j hi hj hij
    refine Fin.cases ?_ (fun i' => ?_) i hi hij
    · intro _ hij0
      refine Fin.cases (fun _ _ => rfl) (fun j' _ h0 => ?_) j hj hij0
      simp only [prependZero, Fin.cases_zero, Fin.cases_succ] at h0
      exact absurd h0 (Fin.succ_ne_zero _).symm
    · intro hi' hij'
      refine Fin.cases (fun _ h0 => ?_) (fun j' hj' hij'' => ?_) j hj hij'
      · simp [prependZero] at h0
      · simp only [prependZero, Fin.cases_succ, Fin.succ_inj] at hij''
        have := isDistinctPrefix_distinctPrefixLen a' i' j' (by simp at hi'; omega)
          (by simp at hj'; omega) hij''
        rw [this]

/-- Before any bump occurs, distinct choices `a 0, ..., a (t-1)` simply park car `i` at spot `a i`. -/
private lemma backgammonRun_of_distinct {n : ℕ} (a : Fin n → Fin n) :
    ∀ (t : ℕ) (ht : t ≤ n), isDistinctPrefix a t →
      ∀ p : Fin n, backgammonRun a t ht p =
        if h : ∃ i : Fin n, i.val < t ∧ a i = p then some h.choose else none := by
  intro t
  induction t with
  | zero =>
    intro _ _ p
    simp [backgammonRun, emptyState]
  | succ t ih =>
    intro ht hdist p
    have hdist' : isDistinctPrefix a t := fun i j hi hj hij => hdist i j (by omega) (by omega) hij
    have hprev := ih (by omega) hdist'
    have hfree : backgammonRun a t (by omega) (a ⟨t, ht⟩) = none := by
      rw [hprev]
      rw [dif_neg]
      rintro ⟨i, hi, hai⟩
      have := hdist i ⟨t, ht⟩ (by omega) (by simp) hai
      have : i.val = t := congrArg Fin.val this
      omega
    rw [backgammonRun, backgammonStep, hfree]
    dsimp only
    by_cases hp : p = a ⟨t, ht⟩
    · subst hp
      simp only [Function.update_self]
      have hex : ∃ i : Fin n, i.val < t + 1 ∧ a i = a ⟨t, ht⟩ := ⟨⟨t, ht⟩, by simp, rfl⟩
      rw [dif_pos hex]
      congr 1
      have hspec := hex.choose_spec
      exact (hdist hex.choose ⟨t, ht⟩ hspec.1 (by simp) hspec.2).symm
    · rw [Function.update_of_ne hp, hprev]
      split_ifs with h1 h2 h2
      · congr 1
        exact hdist h1.choose h2.choose (by have := h1.choose_spec.1; omega)
          h2.choose_spec.1 (h1.choose_spec.2.trans h2.choose_spec.2.symm)
      · exfalso; obtain ⟨i, hi, hai⟩ := h1; exact h2 ⟨i, by omega, hai⟩
      · exfalso; obtain ⟨i, hi, hai⟩ := h2
        by_cases hit : i.val = t
        · have : i = ⟨t, ht⟩ := Fin.ext hit
          subst this; exact hp hai.symm
        · exact h1 ⟨i, by omega, hai⟩
      · rfl

/-- Case 2 forward map: given `a' ∈ O_B⁻¹(σ)` and `r < L(a')` (0-indexed `r : Fin n`),
prepend `(a' r).succ` to `(a' i).succ`. -/
private def prependAt {n : ℕ} (a' : Fin n → Fin n) (r : Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases (a' r).succ (fun i => (a' i).succ)

private lemma outcomeMatches_prependAt {n : ℕ} {a' σ : Fin n → Fin n} (r : Fin n)
    (hr : r.val < distinctPrefixLen a') :
    outcomeMatches (prependAt a' r) (cons1 σ) ↔ outcomeMatches a' σ := by
  have hdist_r : isDistinctPrefix a' (r.val + 1) :=
    (le_distinctPrefixLen_iff a' (by omega)).mp (by omega)
  have hdist_a : isDistinctPrefix (prependAt a' r) (r.val + 1) := by
    intro i j hi hj hij
    refine Fin.cases ?_ (fun i' => ?_) i hi hij
    · intro _
      refine Fin.cases (fun _ _ => rfl) (fun j' hj' h0 => ?_) j hj
      simp only [prependAt, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj] at h0
      have heq := hdist_r r j' (by omega) (by simp at hj'; omega) h0
      have : r.val = j'.val := congrArg Fin.val heq
      simp at hj'; omega
    · intro hi'
      refine Fin.cases (fun _ h0 => ?_) (fun j' hj' hij' => ?_) j hj
      · simp only [prependAt, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj] at h0
        have heq := hdist_r i' r (by simp at hi'; omega) (by omega) h0
        have : i'.val = r.val := congrArg Fin.val heq
        simp at hi'; omega
      · simp only [prependAt, Fin.cases_succ, Fin.succ_inj] at hij'
        have := hdist_r i' j' (by simp at hi'; omega) (by simp at hj'; omega) hij'
        rw [this]
  -- At step `r + 1` (just before car `r + 1`), cars `0..r` are parked at `a 0, ..., a r` (all > 0), spot 0 is empty!
  have hbefore := backgammonRun_of_distinct (prependAt a' r) (r.val + 1) (by omega) hdist_a
  -- At step `r + 2`, car `r + 1` chooses `a (r + 1) = (a' r).succ = a 0`, bumping car `0` to spot `0`!
  have ha_bump : prependAt a' r ⟨r.val + 1, by omega⟩ = (a' r).succ := rfl
  have hcar0_at : backgammonRun (prependAt a' r) (r.val + 1) (by omega) (a' r).succ = some 0 := by
    rw [hbefore]
    have hex : ∃ i : Fin (n + 1), i.val < r.val + 1 ∧ prependAt a' r i = (a' r).succ :=
      ⟨0, by simp, rfl⟩
    rw [dif_pos hex]
    congr 1
    exact hdist_a hex.choose 0 hex.choose_spec.1 (by simp) hex.choose_spec.2
  have hspot0_free : backgammonRun (prependAt a' r) (r.val + 1) (by omega) 0 = none := by
    rw [hbefore, dif_neg]
    rintro ⟨i, _, hi⟩
    refine Fin.cases (fun h => ?_) (fun i' h => ?_) i hi
    · exact Fin.succ_ne_zero _ h
    · exact Fin.succ_ne_zero _ h
  have hafter : backgammonRun (prependAt a' r) (r.val + 2) (by omega) =
      liftState (some 0) (backgammonRun a' (r.val + 1) (by omega)) := by
    rw [backgammonRun, ha_bump, backgammonStep, hcar0_at]
    dsimp only
    have hfind0 : leftmostFree
        (Function.update (backgammonRun (prependAt a' r) (r.val + 1) (by omega))
          (a' r).succ (some ⟨r.val + 1, by omega⟩)) = some 0 := by
      rw [leftmostFree_eq_some_iff]
      refine ⟨?_, fun p hp => by exfalso; exact Fin.not_lt_zero p hp⟩
      rw [Function.update_of_ne (Fin.succ_ne_zero _).symm, hspot0_free]
    rw [hfind0]
    dsimp only
    have hrun' := backgammonRun_of_distinct a' (r.val + 1) (by omega) hdist_r
    funext p
    refine Fin.cases ?_ (fun q => ?_) p
    · simp [liftState]
    · rw [Function.update_of_ne (Fin.succ_ne_zero q)]
      simp only [liftState, Fin.cases_succ, hrun']
      by_cases hqr : q = a' r
      · subst hqr
        simp only [Function.update_self]
        have hex : ∃ i : Fin n, i.val < r.val + 1 ∧ a' i = a' r := ⟨r, by omega, rfl⟩
        rw [dif_pos hex]
        simp only [Option.map_some, Option.some.injEq]
        have heq : hex.choose = r := hdist_r hex.choose r hex.choose_spec.1 (by omega) hex.choose_spec.2
        rw [heq]; rfl
      · rw [Function.update_of_ne ((Fin.succ_injective n).ne hqr), hbefore]
        split_ifs with h1 h2 h2
        · simp only [Option.map_some, Option.some.injEq]
          cases h1c : h1.choose using Fin.cases with
          | zero =>
            have hai := h1.choose_spec.2
            rw [h1c] at hai
            simp only [prependAt, Fin.cases_zero, Fin.succ_inj] at hai
            exact absurd hai.symm hqr
          | succ i' =>
            have hi := h1.choose_spec.1; have hai := h1.choose_spec.2
            rw [h1c] at hi hai
            simp only [prependAt, Fin.cases_succ, Fin.succ_inj] at hai
            have heq := hdist_r i' h2.choose (by simp at hi; omega) h2.choose_spec.1
              (hai.trans h2.choose_spec.2.symm)
            rw [heq]
        · exfalso
          cases h1c : h1.choose using Fin.cases with
          | zero =>
            have hai := h1.choose_spec.2
            rw [h1c] at hai
            simp only [prependAt, Fin.cases_zero, Fin.succ_inj] at hai
            exact hqr hai.symm
          | succ i' =>
            have hi := h1.choose_spec.1; have hai := h1.choose_spec.2
            rw [h1c] at hi hai
            simp only [Fin.val_succ, prependAt, Fin.cases_succ, Fin.succ_inj] at hi hai
            exact h2 ⟨i', by omega, hai⟩
        · exfalso
          obtain ⟨i', hi', hai'⟩ := h2
          have hi'_ne : i'.val ≠ r.val := by
            intro heq; exact hqr (by rw [← hai', show i' = r from Fin.ext heq])
          exact h1 ⟨i'.succ, by simp; omega, by simp [prependAt, hai']⟩
        · rfl
  have hrun : backgammonFinal (prependAt a' r) = liftState (some 0) (backgammonFinal a') :=
    backgammonRun_liftState_from (prependAt a' r) a' (fun _ => rfl) (r.val + 1) (by omega) hafter
      n le_rfl (by omega)
  constructor
  · intro h p
    have hp := h p.succ
    rw [hrun] at hp
    simp only [liftState, cons1, Fin.cases_succ] at hp
    cases hfp : backgammonFinal a' p with
    | none => rw [hfp] at hp; simp at hp
    | some c =>
      rw [hfp] at hp; simp only [Option.map_some, Option.some.injEq, Fin.succ_inj] at hp
      rw [hp]
  · intro h p
    rw [hrun]
    refine Fin.cases ?_ (fun q => ?_) p
    · rfl
    · simp only [liftState, cons1, Fin.cases_succ, h q, Option.map_some]

private lemma distinctPrefixLen_prependAt {n : ℕ} (a' : Fin n → Fin n) (r : Fin n)
    (hr : r.val < distinctPrefixLen a') :
    distinctPrefixLen (prependAt a' r) = r.val + 1 := by
  have hdist_r : isDistinctPrefix a' (r.val + 1) :=
    (le_distinctPrefixLen_iff a' (by omega)).mp (by omega)
  apply le_antisymm
  · by_contra hgt
    have hdist := isDistinctPrefix_distinctPrefixLen (prependAt a' r)
    have heq := hdist 0 r.succ (by simp; omega) (by simp; omega) rfl
    exact Fin.succ_ne_zero r heq.symm
  · rw [le_distinctPrefixLen_iff _ (by omega)]
    intro i j hi hj hij
    refine Fin.cases ?_ (fun i' => ?_) i hi hij
    · intro _
      refine Fin.cases (fun _ _ => rfl) (fun j' hj' h0 => ?_) j hj
      simp only [prependAt, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj] at h0
      have heq := hdist_r r j' (by omega) (by simp at hj'; omega) h0
      have : r.val = j'.val := congrArg Fin.val heq
      simp at hj'; omega
    · intro hi'
      refine Fin.cases (fun _ h0 => ?_) (fun j' hj' hij' => ?_) j hj
      · simp only [prependAt, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj] at h0
        have heq := hdist_r i' r (by simp at hi'; omega) (by omega) h0
        have : i'.val = r.val := congrArg Fin.val heq
        simp at hi'; omega
      · simp only [prependAt, Fin.cases_succ, Fin.succ_inj] at hij'
        have := hdist_r i' j' (by simp at hi'; omega) (by simp at hj'; omega) hij'
        rw [this]

/-- Converse decomposition for any `a ∈ O_B⁻¹(1 ⊕ σ)`: either `a = prependZero a'` or `a = prependAt a' r`. -/
private lemma mem_outcomeSet_cons1_cases {n : ℕ} {σ : Fin n → Fin n} {a : Fin (n + 1) → Fin (n + 1)}
    (ha : outcomeMatches a (cons1 σ)) :
    (a 0 = 0 ∧ ∃ a' : Fin n → Fin n, a = prependZero a' ∧ outcomeMatches a' σ) ∨
    (a 0 ≠ 0 ∧ ∃ a' : Fin n → Fin n, ∃ r : Fin n,
      r.val < distinctPrefixLen a' ∧ a = prependAt a' r ∧ outcomeMatches a' σ) := by
  -- First show no car `i ≥ 1` ever prefers spot `0`!
  have hno0 : ∀ i : Fin n, a i.succ ≠ 0 := by
    intro i hi
    -- After step `i.val + 2`, spot `0` holds car `i.succ ≠ 0`, so by monotonicity it can NEVER hold car `0`!
    have hocc_i : backgammonRun a (i.val + 2) (by omega) 0 = some i.succ := by
      rw [backgammonRun, show a ⟨i.val + 1, by omega⟩ = 0 from hi]
      unfold backgammonStep
      cases h0 : backgammonRun a (i.val + 1) (by omega) 0 with
      | none => simp; ext; rfl
      | some j =>
        dsimp only
        cases hfind : leftmostFree
            (Function.update (backgammonRun a (i.val + 1) (by omega)) 0 (some ⟨i.val + 1, by omega⟩)) with
        | none => simp; ext; rfl
        | some q =>
          dsimp only
          have hq_none := leftmostFree_spec hfind
          have hq0 : q ≠ 0 := by intro h; subst h; simp at hq_none
          rw [Function.update_of_ne hq0.symm, Function.update_self]; rfl
    have hfinal := backgammonRun_ne_zero_mono (Nat.succ_pos n) a (t₁ := i.val + 2) (t₂ := n + 1)
      (by omega) (by omega) le_rfl 0 (by rw [hocc_i]; simp)
      (by rw [hocc_i]; intro h; injection h with h; exact Fin.succ_ne_zero i h)
    exact hfinal (ha 0)
  -- Define `a' : Fin n → Fin n` by shifting `a i.succ` down by `1`.
  let a' : Fin n → Fin n := fun i => ⟨(a i.succ).val - 1, by
    have := (a i.succ).isLt
    have hne := Fin.val_ne_of_ne (hno0 i)
    simp only [Fin.val_zero] at hne
    omega⟩
  have ha'_eq : ∀ i : Fin n, a i.succ = (a' i).succ := by
    intro i
    ext
    dsimp only [a', Fin.val_succ]
    have hne := Fin.val_ne_of_ne (hno0 i)
    simp only [Fin.val_zero] at hne
    omega
  by_cases ha0 : a 0 = 0
  · left
    have hEq : a = prependZero a' := by
      funext i
      refine Fin.cases ha0 (fun i' => ha'_eq i') i
    refine ⟨ha0, a', hEq, ?_⟩
    rw [hEq] at ha
    exact (outcomeMatches_prependZero.mp ha)
  · right
    have h0_at_1 : backgammonRun a 1 (by omega) 0 = none := by
      simp [backgammonRun, backgammonStep, emptyState, Function.update_of_ne (Ne.symm ha0)]
    have h0_at_end : backgammonRun a (n + 1) le_rfl 0 = some 0 := ha 0
    have hex_t : ∃ s ∈ Finset.Icc 1 n, ∃ h : s + 1 ≤ n + 1, backgammonRun a (s + 1) h 0 ≠ none := by
      by_cases h1 : 1 ≤ n
      · refine ⟨n, Finset.mem_Icc.mpr ⟨h1, le_rfl⟩, le_rfl, by rw [h0_at_end]; simp⟩
      · have hn0 : n = 0 := by omega
        subst hn0
        exact absurd (Fin.eq_zero (a 0)) ha0
    let S_t := (Finset.Icc 1 n).filter fun s =>
      ∃ h : s + 1 ≤ n + 1, backgammonRun a (s + 1) h 0 ≠ none
    have hne_set : S_t.Nonempty := by
      obtain ⟨s, hs, hle, hne⟩ := hex_t
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hle, hne⟩⟩
    let t := S_t.min' hne_set
    have ht_mem : t ∈ S_t := Finset.min'_mem S_t hne_set
    have ht_Icc : 1 ≤ t ∧ t ≤ n := Finset.mem_Icc.mp (Finset.mem_filter.mp ht_mem).1
    have ht_occ : backgammonRun a (t + 1) (by omega) 0 ≠ none := (Finset.mem_filter.mp ht_mem).2.2
    have ht_free : backgammonRun a t (by omega) 0 = none := by
      by_cases ht1 : t = 1
      · rw [show backgammonRun a t (by omega) 0 = backgammonRun a 1 (by omega) 0 by congr 1]
        exact h0_at_1
      · by_contra hne
        have hmem_prev : t - 1 ∈ S_t := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, by
            simpa [show t - 1 + 1 = t by omega] using hne⟩
        have hlt : t ≤ t - 1 := Finset.min'_le S_t (t - 1) hmem_prev
        omega
    have hdist_t : isDistinctPrefix a t := by
      have hno_bump : ∀ s : ℕ, (hs : s < t) →
          backgammonRun a s (by omega) (a ⟨s, by omega⟩) = none := by
        intro s hs
        by_contra hne
        have hs0_free : backgammonRun a s (by omega) 0 = none := by
          by_contra hocc
          have := backgammonRun_isSome_mono a (by omega : s ≤ t) (by omega) 0 hocc
          exact this ht_free
        have hs0_occ : backgammonRun a (s + 1) (by omega) 0 ≠ none := by
          rw [backgammonRun, backgammonStep]
          cases hcur : backgammonRun a s (by omega) (a ⟨s, by omega⟩) with
          | none => exact absurd hcur hne
          | some j =>
            dsimp only
            have hne0 : a ⟨s, by omega⟩ ≠ 0 := by
              cases s with
              | zero => exact ha0
              | succ s' => exact hno0 ⟨s', by omega⟩
            have hfind0 : leftmostFree
                (Function.update (backgammonRun a s (by omega)) (a ⟨s, by omega⟩)
                  (some ⟨s, by omega⟩)) = some 0 := by
              rw [leftmostFree_eq_some_iff]
              exact ⟨by rw [Function.update_of_ne hne0.symm, hs0_free],
                fun p hp => absurd hp (Fin.not_lt_zero p)⟩
            rw [hfind0]
            simp
        have h1 : backgammonRun a t (by omega) 0 ≠ none :=
          backgammonRun_isSome_mono a (by omega : s + 1 ≤ t) (by omega) 0 hs0_occ
        exact h1 ht_free
      have hind : ∀ k : ℕ, k ≤ t → isDistinctPrefix a k := by
        intro k
        induction k with
        | zero => intro _ i j hi; omega
        | succ k ihk =>
          intro hkt
          have hprev := ihk (by omega)
          have hstate := backgammonRun_of_distinct a k (by omega) hprev
          have hfree_k := hno_bump k (by omega)
          intro i j hi hj hij
          by_cases hik : i.val < k
          · by_cases hjk : j.val < k
            · exact hprev i j hik hjk hij
            · have hjeq : j = ⟨k, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hjeq] at hij
              rw [hstate] at hfree_k
              have hex : ∃ m : Fin (n + 1), m.val < k ∧ a m = a ⟨k, by omega⟩ := ⟨i, hik, hij⟩
              rw [dif_pos hex] at hfree_k
              cases hfree_k
          · have hieq : i = ⟨k, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hieq] at hij
            by_cases hjk : j.val < k
            · rw [hstate] at hfree_k
              have hex : ∃ m : Fin (n + 1), m.val < k ∧ a m = a ⟨k, by omega⟩ := ⟨j, hjk, hij.symm⟩
              rw [dif_pos hex] at hfree_k
              cases hfree_k
            · exact Fin.ext (by omega)
      exact hind t le_rfl
    have hst := backgammonRun_of_distinct a t (by omega) hdist_t
    have hat_occ : backgammonRun a t (by omega) (a ⟨t, by omega⟩) = some 0 := by
      have hat_ne0 : a ⟨t, by omega⟩ ≠ 0 := by
        rw [show (⟨t, by omega⟩ : Fin (n + 1)) = (⟨t - 1, by omega⟩ : Fin n).succ from
          Fin.ext (by simp; omega)]
        exact hno0 _
      cases hcur : backgammonRun a t (by omega) (a ⟨t, by omega⟩) with
      | none =>
        exfalso
        have : backgammonRun a (t + 1) (by omega) 0 = none := by
          rw [backgammonRun, backgammonStep, hcur]
          dsimp only
          rw [Function.update_of_ne hat_ne0.symm, ht_free]
        exact ht_occ this
      | some j =>
        have hfind0 : leftmostFree
            (Function.update (backgammonRun a t (by omega)) (a ⟨t, by omega⟩)
              (some ⟨t, by omega⟩)) = some 0 := by
          rw [leftmostFree_eq_some_iff]
          exact ⟨by rw [Function.update_of_ne hat_ne0.symm, ht_free],
            fun p hp => absurd hp (Fin.not_lt_zero p)⟩
        have hspot0 : backgammonRun a (t + 1) (by omega) 0 = some j := by
          rw [backgammonRun, backgammonStep, hcur]
          dsimp only
          rw [hfind0]
          dsimp only
          rw [Function.update_self]
        by_cases hj0 : j = 0
        · subst hj0; rfl
        · exfalso
          have := backgammonRun_ne_zero_mono (Nat.succ_pos n) a (t₁ := t + 1) (t₂ := n + 1)
            (by omega) (by omega) le_rfl 0 (by rw [hspot0]; simp) (by rw [hspot0]; simp [hj0])
          exact this (ha 0)
    have hat_eq_a0 : a ⟨t, by omega⟩ = a 0 := by
      rw [hst] at hat_occ
      split_ifs at hat_occ with hex
      · simp only [Option.some.injEq] at hat_occ
        have hspec := hex.choose_spec
        rw [hat_occ] at hspec
        exact hspec.2.symm
    let r : Fin n := ⟨t - 1, by omega⟩
    have ha0_eq : a 0 = (a' r).succ := by
      rw [← hat_eq_a0, show (⟨t, by omega⟩ : Fin (n + 1)) = r.succ from Fin.ext (by simp [r]; omega)]
      exact ha'_eq r
    have hEq : a = prependAt a' r := by
      funext i
      refine Fin.cases ha0_eq (fun i' => ha'_eq i') i
    have hr_lt : r.val < distinctPrefixLen a' := by
      have : r.val + 1 ≤ distinctPrefixLen a' := by
        rw [le_distinctPrefixLen_iff a' (by omega)]
        intro i j hi hj hij
        by_cases hi_r : i.val < r.val
        · by_cases hj_r : j.val < r.val
          · have heq := hdist_t i.succ j.succ (by simp [r] at hi_r ⊢; omega)
              (by simp [r] at hj_r ⊢; omega) (by rw [ha'_eq, ha'_eq, hij])
            exact Fin.succ_inj.mp heq
          · have hj_eq : j = r := Fin.ext (by simp [r] at hj_r hj ⊢; omega)
            subst hj_eq
            have heq := hdist_t i.succ 0 (by simp [r] at hi_r ⊢; omega) (by simp only [Fin.val_zero]; omega)
              (by rw [ha'_eq, ha0_eq, hij])
            exact absurd heq (Fin.succ_ne_zero i)
        · have hi_eq : i = r := Fin.ext (by simp [r] at hi_r hi ⊢; omega)
          subst hi_eq
          by_cases hj_r : j.val < r.val
          · have heq := hdist_t 0 j.succ (by simp only [Fin.val_zero]; omega) (by simp [r] at hj_r ⊢; omega)
              (by rw [ha0_eq, ha'_eq, hij])
            exact absurd heq.symm (Fin.succ_ne_zero j)
          · exact Fin.ext (by simp [r] at hj_r hj ⊢; omega)
      omega
    refine ⟨ha0, a', r, hr_lt, hEq, ?_⟩
    rw [hEq] at ha
    exact (outcomeMatches_prependAt r hr_lt).mp ha

/-- **Lemma A (General car-1 reduction):** For every `n : ℕ` and every `σ : Fin n → Fin n`,
`P_{1 ⊕ σ}(y) = Φ(P_σ(y))`. -/
theorem polyOfOutcome_cons1 {n : ℕ} (σ : Fin n → Fin n) :
    polyOfOutcome (cons1 σ) = phiOp (polyOfOutcome σ) := by
  unfold polyOfOutcome
  rw [phiOp_sum]
  simp_rw [phiOp_X_pow]
  -- Split `outcomeSet (cons1 σ)` into `{a | a 0 = 0}` and `{a | a 0 ≠ 0}`:
  rw [← Finset.sum_filter_add_sum_filter_not (outcomeSet (cons1 σ)) (fun a => a 0 = 0)]
  -- Case 1 (`a 0 = 0`): bijection `a' ↦ prependZero a'` gives `∑_{a' ∈ outcomeSet σ} X^(L(a') + 1)`.
  have h1 : ∑ a ∈ (outcomeSet (cons1 σ)).filter (fun a => a 0 = 0),
      (Polynomial.X : Polynomial ℚ) ^ distinctPrefixLen a =
      ∑ a' ∈ outcomeSet σ, (Polynomial.X : Polynomial ℚ) ^ (distinctPrefixLen a' + 1) := by
    symm
    refine Finset.sum_nbij prependZero ?_ ?_ ?_ ?_
    · intro a' ha'
      simp only [outcomeSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
      exact ⟨outcomeMatches_prependZero.mpr ha', rfl⟩
    · intro a₁ _ a₂ _ hEq
      funext i
      have := congrFun hEq i.succ
      simp only [prependZero, Fin.cases_succ, Fin.succ_inj] at this
      exact this
    · intro a ha
      simp only [outcomeSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases mem_outcomeSet_cons1_cases ha.1 with ⟨_, a', heq, ha'⟩ | ⟨hne, _⟩
      · exact ⟨a', Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩), heq.symm⟩
      · exact absurd ha.2 hne
    · intro a' _
      rw [distinctPrefixLen_prependZero]
  -- Case 2 (`a 0 ≠ 0`): bijection `⟨a', r⟩ ↦ prependAt a' r` gives `∑_{a'} ∑_{r < L(a')} X^(r + 1)`.
  have h2 : ∑ a ∈ (outcomeSet (cons1 σ)).filter (fun a => ¬ a 0 = 0),
      (Polynomial.X : Polynomial ℚ) ^ distinctPrefixLen a =
      ∑ a' ∈ outcomeSet σ, ∑ r ∈ range (distinctPrefixLen a'), (Polynomial.X : Polynomial ℚ) ^ (r + 1) := by
    have hrw : ∑ a' ∈ outcomeSet σ, ∑ r ∈ range (distinctPrefixLen a'), (Polynomial.X : Polynomial ℚ) ^ (r + 1) =
        ∑ a' ∈ outcomeSet σ,
          ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < distinctPrefixLen a'),
            (Polynomial.X : Polynomial ℚ) ^ (r.val + 1) := by
      refine Finset.sum_congr rfl fun a' _ => ?_
      symm
      refine Finset.sum_nbij Fin.val ?_ ?_ ?_ ?_
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        exact Finset.mem_range.mpr hr
      · intro r₁ _ r₂ _ hval
        exact Fin.ext hval
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_range] at hm
        have hlt : m < n := lt_of_lt_of_le hm (distinctPrefixLen_le a')
        refine ⟨⟨m, hlt⟩, ?_, rfl⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hm
      · intro _ _; rfl
    rw [hrw]
    symm
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij (fun x => prependAt x.1 x.2) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, outcomeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨(outcomeMatches_prependAt x.2 hx.2).mpr hx.1, Fin.succ_ne_zero _⟩
    · intro x₁ hx₁ x₂ hx₂ hEq
      simp only [Finset.mem_coe, Finset.mem_sigma, outcomeSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx₁ hx₂
      have h1 : x₁.1 = x₂.1 := by
        funext i
        have := congrFun hEq i.succ
        simp only [prependAt, Fin.cases_succ, Fin.succ_inj] at this
        exact this
      cases x₁ with
      | mk a₁ r₁ =>
        cases x₂ with
        | mk a₂ r₂ =>
          dsimp only at h1 hx₁ hx₂ hEq
          subst h1
          have h0 := congrFun hEq 0
          simp only [prependAt, Fin.cases_zero, Fin.succ_inj] at h0
          have hdist := isDistinctPrefix_distinctPrefixLen a₁
          have hr : r₁ = r₂ := hdist r₁ r₂ hx₁.2 hx₂.2 h0
          subst hr; rfl
    · intro a ha
      simp only [outcomeSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases mem_outcomeSet_cons1_cases ha.1 with ⟨h0, _⟩ | ⟨_, a', r, hr_lt, heq, ha'⟩
      · exact absurd h0 ha.2
      · refine ⟨⟨a', r⟩, ?_, heq.symm⟩
        simp only [Finset.mem_coe, Finset.mem_sigma, outcomeSet, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨ha', hr_lt⟩
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [distinctPrefixLen_prependAt x.1 x.2 hx.2]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_range_succ, add_comm]

/-! ### Section 5: Lemma B — Decreasing outcome `δ_n` -/

/-- Decreasing outcome permutation `δ_n(p) = n - 1 - p` on `Fin n`. -/
def delta (n : ℕ) : Fin n → Fin n :=
  fun p => ⟨n - 1 - p.val, by omega⟩

theorem polyOfOutcome_delta_zero : polyOfOutcome (delta 0) = 1 := by
  unfold polyOfOutcome
  have hset : outcomeSet (delta 0) = {Fin.elim0} := by
    ext a
    simp only [outcomeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; funext p; exact Fin.elim0 p
    · intro _ p; exact Fin.elim0 p
  rw [hset, Finset.sum_singleton]
  have h0 : distinctPrefixLen (Fin.elim0 : Fin 0 → Fin 0) = 0 :=
    Nat.eq_zero_of_le_zero (distinctPrefixLen_le _)
  rw [h0, pow_zero]

theorem polyOfOutcome_delta_one : polyOfOutcome (delta 1) = Polynomial.X := by
  unfold polyOfOutcome
  have hset : outcomeSet (delta 1) = {fun _ => 0} := by
    ext a
    simp only [outcomeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; funext p; exact Fin.eq_zero (a p)
    · intro ha; subst ha
      intro p
      have hp : p = 0 := Fin.eq_zero p
      subst hp
      simp [backgammonFinal, backgammonRun, backgammonStep, emptyState, delta]
  rw [hset, Finset.sum_singleton]
  have h1 : distinctPrefixLen (fun _ : Fin 1 => (0 : Fin 1)) = 1 := by
    apply le_antisymm (distinctPrefixLen_le _)
    rw [le_distinctPrefixLen_iff _ le_rfl]
    intro i j _ _ _
    exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm
  rw [h1, pow_one]

/-- Lift a state `s : SpotState m` to `SpotState (m + 1)` with `sLast` in `Fin.last m` and cars shifted by `+1`. -/
private def liftLastState {m : ℕ} (sLast : Option (Fin (m + 1))) (s : SpotState m) : SpotState (m + 1) :=
  Fin.lastCases sLast (fun p => (s p).map Fin.succ)

private lemma backgammonStep_liftLastState {m : ℕ} (sLast : Option (Fin (m + 1))) (hsLast : sLast ≠ none)
    (s : SpotState m) (c pref : Fin m) :
    backgammonStep (liftLastState sLast s) c.succ pref.castSucc =
      liftLastState sLast (backgammonStep s c pref) := by
  unfold backgammonStep
  have hpref : liftLastState sLast s pref.castSucc = (s pref).map Fin.succ := by
    simp [liftLastState]
  rw [hpref]
  cases hsp : s pref with
  | none =>
    simp only [Option.map_none]
    funext p
    refine Fin.lastCases ?_ (fun q => ?_) p
    · simp [liftLastState, Function.update_of_ne (Fin.castSucc_ne_last pref).symm]
    · by_cases hqp : q = pref
      · subst hqp; simp [liftLastState]
      · simp [liftLastState, Function.update_of_ne hqp,
          Function.update_of_ne (Fin.castSucc_injective m |>.ne hqp)]
  | some j =>
    simp only [Option.map_some]
    have hupd : Function.update (liftLastState sLast s) pref.castSucc (some c.succ) =
        liftLastState sLast (Function.update s pref (some c)) := by
      funext p
      refine Fin.lastCases ?_ (fun q => ?_) p
      · simp [liftLastState, Function.update_of_ne (Fin.castSucc_ne_last pref).symm]
      · by_cases hqp : q = pref
        · subst hqp; simp [liftLastState]
        · simp [liftLastState, Function.update_of_ne hqp,
            Function.update_of_ne (Fin.castSucc_injective m |>.ne hqp)]
    rw [hupd]
    have hfind_eq : leftmostFree (liftLastState sLast (Function.update s pref (some c))) =
        (leftmostFree (Function.update s pref (some c))).map Fin.castSucc := by
      cases hinner : leftmostFree (Function.update s pref (some c)) with
      | none =>
        rw [Option.map_none, leftmostFree_eq_none_iff]
        intro p
        refine Fin.lastCases (by simp [liftLastState, hsLast]) (fun q => ?_) p
        have hq := leftmostFree_eq_none_iff.mp hinner q
        simp only [liftLastState, Fin.lastCases_castSucc, ne_eq, Option.map_eq_none_iff]
        exact hq
      | some q =>
        rw [Option.map_some, leftmostFree_eq_some_iff]
        refine ⟨?_, ?_⟩
        · simp only [liftLastState, Fin.lastCases_castSucc, Option.map_eq_none_iff]
          exact leftmostFree_spec hinner
        · intro p hp
          refine Fin.lastCases (fun hlt => by exact absurd hlt (not_lt.mpr (Fin.le_last _)))
            (fun r hr => ?_) p hp
          have hr_lt : r < q := Fin.castSucc_lt_castSucc_iff.mp hr
          simp only [liftLastState, Fin.lastCases_castSucc, ne_eq, Option.map_eq_none_iff]
          exact leftmostFree_min hinner hr_lt
    rw [hfind_eq]
    cases leftmostFree (Function.update s pref (some c)) with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      funext p
      refine Fin.lastCases ?_ (fun r => ?_) p
      · simp [liftLastState, Function.update_of_ne (Fin.castSucc_ne_last q).symm]
      · by_cases hrq : r = q
        · subst hrq; simp [liftLastState]
        · simp [liftLastState, Function.update_of_ne hrq,
            Function.update_of_ne (Fin.castSucc_injective m |>.ne hrq)]

private lemma backgammonRun_liftLastState_from {m : ℕ} (a : Fin (m + 1) → Fin (m + 1))
    (a' : Fin m → Fin m) (ha : ∀ i : Fin m, a i.succ = (a' i).castSucc)
    (hinit : backgammonRun a 1 (by omega) = liftLastState (some 0) (emptyState m)) :
    ∀ (t : ℕ) (ht : t ≤ m),
      backgammonRun a (t + 1) (by omega) = liftLastState (some 0) (backgammonRun a' t ht) := by
  intro t
  induction t with
  | zero => intro _; exact hinit
  | succ t ih =>
    intro ht
    rw [backgammonRun, ih (by omega)]
    have ha_t : a ⟨t + 1, by omega⟩ = (a' ⟨t, by omega⟩).castSucc := ha ⟨t, by omega⟩
    have hc_t : (⟨t + 1, by omega⟩ : Fin (m + 1)) = (⟨t, by omega⟩ : Fin m).succ := rfl
    rw [ha_t, hc_t, backgammonStep_liftLastState (some 0) (by simp)]
    rfl

/-- Lemma B, Case 1 forward map: prepend `Fin.last m` to `(a' i).castSucc`. -/
private def prependLast {m : ℕ} (a' : Fin m → Fin m) : Fin (m + 1) → Fin (m + 1) :=
  Fin.cases (Fin.last m) (fun i => (a' i).castSucc)

private lemma outcomeMatches_prependLast {m : ℕ} {a' : Fin m → Fin m} :
    outcomeMatches (prependLast a') (delta (m + 1)) ↔ outcomeMatches a' (delta m) := by
  have hrun : backgammonFinal (prependLast a') = liftLastState (some 0) (backgammonFinal a') := by
    apply backgammonRun_liftLastState_from (prependLast a') a' (fun _ => rfl)
    · funext p
      refine Fin.lastCases ?_ (fun q => ?_) p
      · simp [backgammonRun, backgammonStep, emptyState, prependLast, liftLastState]
      · simp [backgammonRun, backgammonStep, emptyState, prependLast, liftLastState]
  constructor
  · intro h p
    have hp := h p.castSucc
    rw [hrun] at hp
    simp only [liftLastState, Fin.lastCases_castSucc] at hp
    cases hfp : backgammonFinal a' p with
    | none => rw [hfp] at hp; simp at hp
    | some c =>
      rw [hfp] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      have hval : c.val + 1 = m - p.val := by
        have := congrArg Fin.val hp
        simpa [delta] using this
      have hc : c = delta m p := Fin.ext (by dsimp [delta]; omega)
      rw [hc]
  · intro h p
    rw [hrun]
    refine Fin.lastCases ?_ (fun q => ?_) p
    · simp only [liftLastState, Fin.lastCases_last, delta]
      congr 1; ext; simp
    · simp only [liftLastState, Fin.lastCases_castSucc, h q, Option.map_some]
      congr 1; ext; simp [delta]; omega

private lemma distinctPrefixLen_prependLast {m : ℕ} (a' : Fin m → Fin m) :
    distinctPrefixLen (prependLast a') = distinctPrefixLen a' + 1 := by
  have hle1 : distinctPrefixLen (prependLast a') ≤ m + 1 := distinctPrefixLen_le _
  have hle2 : distinctPrefixLen a' ≤ m := distinctPrefixLen_le _
  apply le_antisymm
  · have hpos : 1 ≤ distinctPrefixLen (prependLast a') := by
      rw [le_distinctPrefixLen_iff _ (by omega)]
      intro i j hi hj _
      exact Fin.ext (by omega)
    have hsub : distinctPrefixLen (prependLast a') - 1 ≤ distinctPrefixLen a' := by
      rw [le_distinctPrefixLen_iff _ (by omega)]
      intro i j hi hj hij
      have hdist := isDistinctPrefix_distinctPrefixLen (prependLast a')
      have heq := hdist i.succ j.succ (by simp; omega) (by simp; omega)
        (by simp [prependLast, hij])
      exact Fin.succ_inj.mp heq
    omega
  · rw [le_distinctPrefixLen_iff _ (by omega)]
    intro i j hi hj hij
    refine Fin.cases ?_ (fun i' => ?_) i hi hij
    · intro _
      refine Fin.cases (fun _ _ => rfl) (fun j' _ h0 => ?_) j hj
      exact absurd h0.symm (Fin.castSucc_ne_last (a' j'))
    · intro hi'
      refine Fin.cases (fun _ h0 => ?_) (fun j' hj' hij' => ?_) j hj
      · exact absurd h0 (Fin.castSucc_ne_last (a' i'))
      · simp only [prependLast, Fin.cases_succ] at hij'
        have heq := Fin.castSucc_injective m hij'
        have := isDistinctPrefix_distinctPrefixLen a' i' j' (by simp at hi'; omega)
          (by simp at hj'; omega) heq
        rw [this]

/-- Embed a state `s : SpotState m` into `SpotState (m + 1)` with `Fin.last m` empty and cars cast by `Fin.castSucc`. -/
private def embedInitState {m : ℕ} (s : SpotState m) : SpotState (m + 1) :=
  Fin.lastCases none (fun p => (s p).map Fin.castSucc)

private lemma backgammonStep_embedInitState {m : ℕ} (s : SpotState m) (hs : occCount s < m)
    (c pref : Fin m) :
    backgammonStep (embedInitState s) c.castSucc pref.castSucc =
      embedInitState (backgammonStep s c pref) := by
  unfold backgammonStep
  have hpref : embedInitState s pref.castSucc = (s pref).map Fin.castSucc := by
    simp [embedInitState]
  rw [hpref]
  cases hsp : s pref with
  | none =>
    simp only [Option.map_none]
    funext p
    refine Fin.lastCases ?_ (fun q => ?_) p
    · simp [embedInitState, Function.update_of_ne (Fin.castSucc_ne_last pref).symm]
    · by_cases hqp : q = pref
      · subst hqp; simp [embedInitState]
      · simp [embedInitState, Function.update_of_ne hqp,
          Function.update_of_ne (Fin.castSucc_injective m |>.ne hqp)]
  | some j =>
    simp only [Option.map_some]
    have hupd : Function.update (embedInitState s) pref.castSucc (some c.castSucc) =
        embedInitState (Function.update s pref (some c)) := by
      funext p
      refine Fin.lastCases ?_ (fun q => ?_) p
      · simp [embedInitState, Function.update_of_ne (Fin.castSucc_ne_last pref).symm]
      · by_cases hqp : q = pref
        · subst hqp; simp [embedInitState]
        · simp [embedInitState, Function.update_of_ne hqp,
            Function.update_of_ne (Fin.castSucc_injective m |>.ne hqp)]
    rw [hupd]
    -- Since `occCount s < m`, there is an empty spot in `Fin m` for `Function.update s pref (some c)`.
    have hex : ∃ q : Fin m, Function.update s pref (some c) q = none := by
      have hcard : (Finset.univ.filter fun p : Fin m => s p ≠ none).card < Fintype.card (Fin m) := by
        simpa [occCount] using hs
      obtain ⟨q, hq⟩ : ∃ q : Fin m, s q = none := by
        by_contra hall
        push Not at hall
        have : (Finset.univ.filter fun p : Fin m => s p ≠ none) = Finset.univ := by
          ext p; simp [hall p]
        rw [this, Finset.card_univ] at hcard
        exact lt_irrefl _ hcard
      have hne : q ≠ pref := by intro heq; subst heq; rw [hq] at hsp; cases hsp
      exact ⟨q, by rw [Function.update_of_ne hne, hq]⟩
    cases hinner : leftmostFree (Function.update s pref (some c)) with
    | none =>
      exfalso
      obtain ⟨q, hq⟩ := hex
      exact (leftmostFree_eq_none_iff.mp hinner q) hq
    | some q =>
      have hfind_eq : leftmostFree (embedInitState (Function.update s pref (some c))) = some q.castSucc := by
        rw [leftmostFree_eq_some_iff]
        refine ⟨?_, ?_⟩
        · simp only [embedInitState, Fin.lastCases_castSucc, Option.map_eq_none_iff]
          exact leftmostFree_spec hinner
        · intro p hp
          refine Fin.lastCases (fun hlt => by exact absurd hlt (not_lt.mpr (Fin.le_last _)))
            (fun r hr => ?_) p hp
          have hr_lt : r < q := Fin.castSucc_lt_castSucc_iff.mp hr
          simp only [embedInitState, Fin.lastCases_castSucc, ne_eq, Option.map_eq_none_iff]
          exact leftmostFree_min hinner hr_lt
      rw [hfind_eq]
      funext p
      refine Fin.lastCases ?_ (fun r => ?_) p
      · simp [embedInitState, Function.update_of_ne (Fin.castSucc_ne_last q).symm]
      · by_cases hrq : r = q
        · subst hrq; simp [embedInitState]
        · simp [embedInitState, Function.update_of_ne hrq,
            Function.update_of_ne (Fin.castSucc_injective m |>.ne hrq)]

/-- Lemma B, Case 2 forward map: append `0` to `(a'' i).castSucc`. -/
private def appendZero {n : ℕ} (a'' : Fin (n + 1) → Fin (n + 1)) : Fin (n + 2) → Fin (n + 2) :=
  Fin.snoc (fun i => (a'' i).castSucc) 0

private lemma backgammonRun_appendZero {n : ℕ} (a'' : Fin (n + 1) → Fin (n + 1)) :
    ∀ (t : ℕ) (ht : t ≤ n + 1),
      backgammonRun (appendZero a'') t (by omega) = embedInitState (backgammonRun a'' t ht) := by
  intro t
  induction t with
  | zero =>
    intro _
    funext p
    refine Fin.lastCases ?_ (fun q => ?_) p
    · simp [backgammonRun, emptyState, embedInitState]
    · simp [backgammonRun, emptyState, embedInitState]
  | succ t ih =>
    intro ht
    rw [backgammonRun, ih (by omega)]
    have ha_t : appendZero a'' ⟨t, by omega⟩ = (a'' ⟨t, by omega⟩).castSucc := by
      have : (⟨t, by omega⟩ : Fin (n + 2)) = (⟨t, by omega⟩ : Fin (n + 1)).castSucc := rfl
      rw [this, appendZero, Fin.snoc_castSucc]
    have hc_t : (⟨t, by omega⟩ : Fin (n + 2)) = (⟨t, by omega⟩ : Fin (n + 1)).castSucc := rfl
    rw [ha_t, hc_t, backgammonStep_embedInitState _ (by rw [occCount_backgammonRun]; omega)]
    rfl

private lemma outcomeMatches_appendZero {n : ℕ} {a'' : Fin (n + 1) → Fin (n + 1)} :
    outcomeMatches (appendZero a'') (delta (n + 2)) ↔ outcomeMatches a'' (cons1 (delta n)) := by
  have hprev : backgammonRun (appendZero a'') (n + 1) (by omega) =
      embedInitState (backgammonFinal a'') :=
    backgammonRun_appendZero a'' (n + 1) le_rfl
  constructor
  · intro h p
    -- Every spot in `Fin (n + 1)` is occupied in `backgammonFinal a''` (since `occCount = n + 1`).
    have hall : ∀ q : Fin (n + 1), backgammonFinal a'' q ≠ none := by
      have hcard : (Finset.univ.filter fun q : Fin (n + 1) => backgammonFinal a'' q ≠ none).card =
          Fintype.card (Fin (n + 1)) := by
        unfold backgammonFinal
        simpa [occCount] using occCount_backgammonRun a'' (n + 1) le_rfl
      have heq := Finset.eq_univ_of_card _ hcard
      intro q
      have hmem : q ∈ Finset.univ.filter (fun q : Fin (n + 1) => backgammonFinal a'' q ≠ none) := by
        rw [heq]; exact Finset.mem_univ q
      exact (Finset.mem_filter.mp hmem).2
    -- Obtain the car `c0` at spot `0` of `backgammonFinal a''`.
    obtain ⟨c0, hc0⟩ : ∃ c0 : Fin (n + 1), backgammonFinal a'' 0 = some c0 :=
      Option.ne_none_iff_exists'.mp (hall 0)
    have hstep_last : backgammonFinal (appendZero a'') =
        Function.update
          (Function.update (embedInitState (backgammonFinal a'')) 0 (some (Fin.last (n + 1))))
          (Fin.last (n + 1)) (some c0.castSucc) := by
      have hpref0 : appendZero a'' (Fin.last (n + 1)) = 0 := by simp [appendZero]
      have h0_eq : embedInitState (backgammonFinal a'') 0 = some c0.castSucc := by
        have h0c : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
        rw [h0c, embedInitState, Fin.lastCases_castSucc, hc0, Option.map_some]
      have hfind : leftmostFree
            (Function.update (embedInitState (backgammonFinal a'')) 0 (some (Fin.last (n + 1)))) =
          some (Fin.last (n + 1)) := by
        rw [leftmostFree_eq_some_iff]
        have hlast_ne0 : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
          intro h; have := congrArg Fin.val h; simp at this
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne hlast_ne0]
          simp [embedInitState]
        · intro q hq
          refine Fin.lastCases (fun hlt => absurd hlt (lt_irrefl _)) (fun r _ => ?_) q hq
          by_cases hr0 : r = 0
          · subst hr0; simp
          · rw [Function.update_of_ne (by intro heq; exact hr0 (Fin.castSucc_injective _ heq))]
            simp [embedInitState, hall r]
      rw [backgammonFinal, backgammonRun, hprev]
      change backgammonStep (embedInitState (backgammonFinal a'')) (Fin.last (n + 1))
        (appendZero a'' (Fin.last (n + 1))) = _
      rw [hpref0]
      unfold backgammonStep
      rw [h0_eq]
      dsimp only
      rw [hfind]
    refine Fin.cases ?_ (fun q => ?_) p
    · have hlast := h (Fin.last (n + 1))
      rw [hstep_last, Function.update_self] at hlast
      simp only [Option.some.injEq] at hlast
      have hc0_val : c0.val = 0 := by
        have := congrArg Fin.val hlast
        simpa [delta] using this
      have hc0_zero : c0 = 0 := Fin.ext hc0_val
      rw [hc0, hc0_zero]; rfl
    · have hq := h q.succ.castSucc
      rw [hstep_last, Function.update_of_ne (Fin.castSucc_ne_last _),
        Function.update_of_ne (by intro heq; exact Fin.succ_ne_zero q (Fin.castSucc_injective _ heq))] at hq
      simp only [embedInitState, Fin.lastCases_castSucc] at hq
      cases hfq : backgammonFinal a'' q.succ with
      | none => rw [hfq] at hq; simp at hq
      | some d =>
        rw [hfq] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        have hd_val : d.val = n - q.val := by
          have := congrArg Fin.val hq
          simpa [delta] using this
        have hd : d = cons1 (delta n) q.succ := Fin.ext (by simp [cons1, delta]; omega)
        rw [hd]
  · intro h p
    have h0_eq : embedInitState (backgammonFinal a'') 0 = some 0 := by
      have h0c : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
      rw [h0c, embedInitState, Fin.lastCases_castSucc, h 0]
      rfl
    have hfind : leftmostFree
          (Function.update (embedInitState (backgammonFinal a'')) 0 (some (Fin.last (n + 1)))) =
        some (Fin.last (n + 1)) := by
      rw [leftmostFree_eq_some_iff]
      have hlast_ne0 : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
        intro h; have := congrArg Fin.val h; simp at this
      refine ⟨?_, ?_⟩
      · rw [Function.update_of_ne hlast_ne0]
        simp [embedInitState]
      · intro q hq
        refine Fin.lastCases (fun hlt => absurd hlt (lt_irrefl _)) (fun r _ => ?_) q hq
        by_cases hr0 : r = 0
        · subst hr0; simp
        · rw [Function.update_of_ne (by intro heq; exact hr0 (Fin.castSucc_injective _ heq))]
          simp [embedInitState, h r]
    have hstep_last : backgammonFinal (appendZero a'') =
        Function.update
          (Function.update (embedInitState (backgammonFinal a'')) 0 (some (Fin.last (n + 1))))
          (Fin.last (n + 1)) (some 0) := by
      rw [backgammonFinal, backgammonRun, hprev]
      change backgammonStep (embedInitState (backgammonFinal a'')) (Fin.last (n + 1))
        (appendZero a'' (Fin.last (n + 1))) = _
      rw [show appendZero a'' (Fin.last (n + 1)) = 0 by simp [appendZero]]
      unfold backgammonStep
      rw [h0_eq]
      dsimp only
      rw [hfind]
    rw [hstep_last]
    refine Fin.lastCases ?_ (fun q => ?_) p
    · rw [Function.update_self]
      congr 1; ext; simp [delta]
    · rw [Function.update_of_ne (Fin.castSucc_ne_last q)]
      refine Fin.cases ?_ (fun r => ?_) q
      · rw [show (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) from rfl, Function.update_self]
        rfl
      · rw [Function.update_of_ne (by intro heq; exact Fin.succ_ne_zero r (Fin.castSucc_injective _ heq))]
        simp only [embedInitState, Fin.lastCases_castSucc, h r.succ, Option.map_some]
        congr 1; ext; simp [cons1, delta]; omega

private lemma distinctPrefixLen_appendZero {n : ℕ} (a'' : Fin (n + 1) → Fin (n + 1)) :
    distinctPrefixLen (appendZero a'') = distinctPrefixLen a'' := by
  have hle_a'' : distinctPrefixLen a'' ≤ n + 1 := distinctPrefixLen_le _
  have hle_app : distinctPrefixLen (appendZero a'') ≤ n + 1 := by
    by_contra hgt
    have hge : n + 2 ≤ distinctPrefixLen (appendZero a'') := by omega
    have hdist := (le_distinctPrefixLen_iff (appendZero a'') le_rfl).mp hge
    have hinj : Function.Injective a'' := by
      intro i j hij
      have := hdist i.castSucc j.castSucc (by omega) (by omega)
        (by simp [appendZero, hij])
      exact Fin.castSucc_injective _ this
    obtain ⟨i, hi⟩ := Finite.injective_iff_surjective.mp hinj 0
    have heq := hdist i.castSucc (Fin.last (n + 1)) (by omega) (by omega)
      (by simp [appendZero, hi])
    exact Fin.castSucc_ne_last i heq
  apply le_antisymm
  · rw [le_distinctPrefixLen_iff a'' hle_app]
    intro i j hi hj hij
    have hdist := isDistinctPrefix_distinctPrefixLen (appendZero a'')
    have heq := hdist i.castSucc j.castSucc hi hj (by simp [appendZero, hij])
    exact Fin.castSucc_injective _ heq
  · rw [le_distinctPrefixLen_iff (appendZero a'') (by omega)]
    intro i j hi hj hij
    have hi' : i.val < n + 1 := by omega
    have hj' : j.val < n + 1 := by omega
    let i' : Fin (n + 1) := ⟨i.val, hi'⟩
    let j' : Fin (n + 1) := ⟨j.val, hj'⟩
    have hi_eq : i = i'.castSucc := Fin.ext rfl
    have hj_eq : j = j'.castSucc := Fin.ext rfl
    rw [hi_eq, hj_eq] at hij ⊢
    simp only [appendZero, Fin.snoc_castSucc] at hij
    have heq := isDistinctPrefix_distinctPrefixLen a'' i' j' hi hj (Fin.castSucc_injective _ hij)
    rw [heq]

/-- Converse decomposition for Lemma B: any `a ∈ O_B⁻¹(δ_{n+2})` is either `prependLast a'` or `appendZero a''`. -/
private lemma mem_outcomeSet_delta_cases {n : ℕ} {a : Fin (n + 2) → Fin (n + 2)}
    (ha : outcomeMatches a (delta (n + 2))) :
    (a 0 = Fin.last (n + 1) ∧ ∃ a' : Fin (n + 1) → Fin (n + 1),
      a = prependLast a' ∧ outcomeMatches a' (delta (n + 1))) ∨
    (a 0 ≠ Fin.last (n + 1) ∧ ∃ a'' : Fin (n + 1) → Fin (n + 1),
      a = appendZero a'' ∧ outcomeMatches a'' (cons1 (delta n))) := by
  have hlast_final : backgammonFinal a (Fin.last (n + 1)) = some 0 := by
    have := ha (Fin.last (n + 1))
    convert this using 2
    ext; simp [delta]
  -- No car `i ≥ 1` ever prefers `Fin.last (n + 1)`.
  have hno_last : ∀ i : Fin (n + 1), a i.succ ≠ Fin.last (n + 1) := by
    intro i hi
    have hocc_i : backgammonRun a (i.val + 2) (by omega) (Fin.last (n + 1)) = some i.succ := by
      rw [backgammonRun, show a ⟨i.val + 1, by omega⟩ = Fin.last (n + 1) from hi]
      unfold backgammonStep
      cases h0 : backgammonRun a (i.val + 1) (by omega) (Fin.last (n + 1)) with
      | none => simp; ext; rfl
      | some j =>
        dsimp only
        cases hfind : leftmostFree
            (Function.update (backgammonRun a (i.val + 1) (by omega)) (Fin.last (n + 1))
              (some ⟨i.val + 1, by omega⟩)) with
        | none => simp; ext; rfl
        | some q =>
          dsimp only
          have hq_none := leftmostFree_spec hfind
          have hq_ne : q ≠ Fin.last (n + 1) := by intro h; subst h; simp at hq_none
          rw [Function.update_of_ne hq_ne.symm, Function.update_self]; rfl
    have hfinal := backgammonRun_ne_zero_mono (Nat.succ_pos (n + 1)) a (t₁ := i.val + 2) (t₂ := n + 2)
      (by omega) (by omega) le_rfl (Fin.last (n + 1)) (by rw [hocc_i]; simp)
      (by rw [hocc_i]; intro h; injection h with h; exact Fin.succ_ne_zero i h)
    exact hfinal hlast_final
  by_cases ha0 : a 0 = Fin.last (n + 1)
  · left
    let a' : Fin (n + 1) → Fin (n + 1) := fun i =>
      ⟨(a i.succ).val, by have := (a i.succ).isLt; have := Fin.val_ne_of_ne (hno_last i); simp at this; omega⟩
    have hEq : a = prependLast a' := by
      funext i
      refine Fin.cases ha0 (fun i' => Fin.ext rfl) i
    refine ⟨ha0, a', hEq, ?_⟩
    rw [hEq] at ha
    exact outcomeMatches_prependLast.mp ha
  · right
    -- Every `i : Fin (n + 2)` satisfies `a i ≠ Fin.last (n + 1)`.
    have hall_ne_last : ∀ i : Fin (n + 2), a i ≠ Fin.last (n + 1) := by
      intro i
      refine Fin.cases ha0 hno_last i
    -- Spot `Fin.last (n + 1)` stays `none` through step `n + 1`!
    have hlast_free : ∀ (t : ℕ) (ht : t ≤ n + 1),
        backgammonRun a t (by omega) (Fin.last (n + 1)) = none := by
      intro t
      induction t with
      | zero => intro _; simp [backgammonRun, emptyState]
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hat_ne : a ⟨t, by omega⟩ ≠ Fin.last (n + 1) := hall_ne_last ⟨t, by omega⟩
        rw [backgammonRun]
        unfold backgammonStep
        cases hcur : backgammonRun a t (by omega) (a ⟨t, by omega⟩) with
        | none =>
          dsimp only
          rw [Function.update_of_ne hat_ne.symm, hprev]
        | some j =>
          dsimp only
          -- Since `occCount (backgammonRun a t) = t ≤ n`, there is an empty spot `< Fin.last (n + 1)`!
          have hex_lt : ∃ q : Fin (n + 2), q < Fin.last (n + 1) ∧
              Function.update (backgammonRun a t (by omega)) (a ⟨t, by omega⟩)
                (some ⟨t, by omega⟩) q = none := by
            by_contra hall_occ
            push Not at hall_occ
            have hsub : (Finset.univ.erase (Fin.last (n + 1))) ⊆
                Finset.univ.filter (fun p : Fin (n + 2) => backgammonRun a t (by omega) p ≠ none) := by
              intro p hp
              rw [Finset.mem_erase] at hp
              have hplt : p < Fin.last (n + 1) := lt_of_le_of_ne (Fin.le_last p) hp.1
              have hp1 := hall_occ p hplt
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ p, ?_⟩
              by_cases hpa : p = a ⟨t, by omega⟩
              · rw [hpa, hcur]; simp
              · rwa [Function.update_of_ne hpa] at hp1
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
            have hocc := occCount_backgammonRun a t (by omega)
            unfold occCount at hocc
            omega
          cases hfind : leftmostFree
              (Function.update (backgammonRun a t (by omega)) (a ⟨t, by omega⟩)
                (some ⟨t, by omega⟩)) with
          | none =>
            dsimp only
            rw [Function.update_of_ne hat_ne.symm, hprev]
          | some q =>
            dsimp only
            obtain ⟨q₀, hq₀_lt, hq₀_none⟩ := hex_lt
            have hq_le : q ≤ q₀ := by
              by_contra hgt
              exact leftmostFree_min hfind (not_le.mp hgt) hq₀_none
            have hq_ne : q ≠ Fin.last (n + 1) := ne_of_lt (lt_of_le_of_lt hq_le hq₀_lt)
            rw [Function.update_of_ne hq_ne.symm, Function.update_of_ne hat_ne.symm, hprev]
    -- At step `n + 1`, spot `Fin.last (n + 1)` is `none`, and every other spot is occupied by a car `< n + 1`.
    have hcar_lt : ∀ (t : ℕ) (ht : t ≤ n + 2) (p d : Fin (n + 2)),
        backgammonRun a t ht p = some d → d.val < t := by
      intro t
      induction t with
      | zero => intro _ p d h; simp [backgammonRun, emptyState] at h
      | succ t ih =>
        intro ht
        exact backgammonStep_car_lt _ ⟨t, ht⟩ _ (by simp)
          (fun p d h => Nat.lt_succ_of_lt (ih (by omega) p d h))
    have hfree_n1 := hlast_free (n + 1) le_rfl
    have hall_occ_n1 : ∀ p : Fin (n + 2), p ≠ Fin.last (n + 1) →
        backgammonRun a (n + 1) (by omega) p ≠ none := by
      have hsub : (Finset.univ.filter fun p : Fin (n + 2) => backgammonRun a (n + 1) (by omega) p ≠ none) ⊆
          Finset.univ.erase (Fin.last (n + 1)) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ p⟩
        intro heq; subst heq; exact hp.2 hfree_n1
      have hcard_eq : (Finset.univ.filter fun p : Fin (n + 2) => backgammonRun a (n + 1) (by omega) p ≠ none).card =
          (Finset.univ.erase (Fin.last (n + 1))).card := by
        have h1 : (Finset.univ.filter fun p : Fin (n + 2) => backgammonRun a (n + 1) (by omega) p ≠ none).card = n + 1 :=
          occCount_backgammonRun a (n + 1) (by omega)
        rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
      intro p hp
      have hmem : p ∈ Finset.univ.filter (fun p : Fin (n + 2) => backgammonRun a (n + 1) (by omega) p ≠ none) := by
        rw [heq]; exact Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩
      exact (Finset.mem_filter.mp hmem).2
    -- Therefore car `Fin.last (n + 1)` MUST choose spot `0`!
    have halast_zero : a (Fin.last (n + 1)) = 0 := by
      set pref := a (Fin.last (n + 1))
      have hpref_ne : pref ≠ Fin.last (n + 1) := hall_ne_last (Fin.last (n + 1))
      obtain ⟨j, hj⟩ : ∃ j : Fin (n + 2), backgammonRun a (n + 1) (by omega) pref = some j :=
        Option.ne_none_iff_exists'.mp (hall_occ_n1 pref hpref_ne)
      have hfind_last : leftmostFree
            (Function.update (backgammonRun a (n + 1) (by omega)) pref (some (Fin.last (n + 1)))) =
          some (Fin.last (n + 1)) := by
        rw [leftmostFree_eq_some_iff]
        refine ⟨by rw [Function.update_of_ne hpref_ne.symm, hfree_n1], ?_⟩
        intro q hq
        have hq_ne : q ≠ Fin.last (n + 1) := ne_of_lt hq
        by_cases hqp : q = pref
        · subst hqp; simp
        · rw [Function.update_of_ne hqp]; exact hall_occ_n1 q hq_ne
      have hfinal_eq : backgammonFinal a =
          Function.update
            (Function.update (backgammonRun a (n + 1) (by omega)) pref (some (Fin.last (n + 1))))
            (Fin.last (n + 1)) (some j) := by
        rw [backgammonFinal, backgammonRun]
        change backgammonStep (backgammonRun a (n + 1) (by omega)) (Fin.last (n + 1)) pref = _
        unfold backgammonStep
        rw [hj]; dsimp only; rw [hfind_last]
      have h0_final : backgammonFinal a 0 = some (Fin.last (n + 1)) := by
        have := ha 0
        convert this using 2; ext; simp [delta]
      have h0_ne_last : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        intro h; have := congrArg Fin.val h; simp at this
      by_contra hne0
      rw [hfinal_eq, Function.update_of_ne h0_ne_last,
        Function.update_of_ne (Ne.symm hne0)] at h0_final
      have hlt := hcar_lt (n + 1) (by omega) 0 (Fin.last (n + 1)) h0_final
      simp at hlt
    let a'' : Fin (n + 1) → Fin (n + 1) := fun i =>
      ⟨(a i.castSucc).val, by
        have := (a i.castSucc).isLt
        have := Fin.val_ne_of_ne (hall_ne_last i.castSucc)
        simp at this; omega⟩
    have hEq : a = appendZero a'' := by
      funext i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · simp [appendZero, halast_zero]
      · simp [appendZero, a'']
    refine ⟨ha0, a'', hEq, ?_⟩
    rw [hEq] at ha
    exact outcomeMatches_appendZero.mp ha

/-- **Lemma B (Decreasing outcome recurrence):** For every `n : ℕ`,
`P_{δ_{n+2}}(y) = y * P_{δ_{n+1}}(y) + P_{1 ⊕ δ_n}(y)`. -/
theorem polyOfOutcome_delta (n : ℕ) :
    polyOfOutcome (delta (n + 2)) =
      Polynomial.X * polyOfOutcome (delta (n + 1)) + polyOfOutcome (cons1 (delta n)) := by
  unfold polyOfOutcome
  rw [← Finset.sum_filter_add_sum_filter_not (outcomeSet (delta (n + 2)))
    (fun a => a 0 = Fin.last (n + 1))]
  have h1 : ∑ a ∈ (outcomeSet (delta (n + 2))).filter (fun a => a 0 = Fin.last (n + 1)),
      (Polynomial.X : Polynomial ℚ) ^ distinctPrefixLen a =
      Polynomial.X * ∑ a' ∈ outcomeSet (delta (n + 1)), (Polynomial.X : Polynomial ℚ) ^ distinctPrefixLen a' := by
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij prependLast ?_ ?_ ?_ ?_
    · intro a' ha'
      simp only [outcomeSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
      exact ⟨outcomeMatches_prependLast.mpr ha', rfl⟩
    · intro a₁ _ a₂ _ hEq
      funext i
      have := congrFun hEq i.succ
      simp only [prependLast, Fin.cases_succ] at this
      exact Fin.castSucc_injective _ this
    · intro a ha
      simp only [outcomeSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases mem_outcomeSet_delta_cases ha.1 with ⟨_, a', heq, ha'⟩ | ⟨hne, _⟩
      · exact ⟨a', Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩), heq.symm⟩
      · exact absurd ha.2 hne
    · intro a' _
      rw [distinctPrefixLen_prependLast, pow_succ']
  have h2 : ∑ a ∈ (outcomeSet (delta (n + 2))).filter (fun a => ¬ a 0 = Fin.last (n + 1)),
      (Polynomial.X : Polynomial ℚ) ^ distinctPrefixLen a =
      ∑ a'' ∈ outcomeSet (cons1 (delta n)), (Polynomial.X : Polynomial ℚ) ^ distinctPrefixLen a'' := by
    symm
    refine Finset.sum_nbij appendZero ?_ ?_ ?_ ?_
    · intro a'' ha''
      simp only [outcomeSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha'' ⊢
      exact ⟨outcomeMatches_appendZero.mpr ha'', Fin.castSucc_ne_last (a'' 0)⟩
    · intro a₁ _ a₂ _ hEq
      funext i
      have := congrFun hEq i.castSucc
      simp only [appendZero, Fin.snoc_castSucc] at this
      exact Fin.castSucc_injective _ this
    · intro a ha
      simp only [outcomeSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases mem_outcomeSet_delta_cases ha.1 with ⟨h0, _⟩ | ⟨_, a'', heq, ha''⟩
      · exact absurd h0 ha.2
      · exact ⟨a'', Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha''⟩), heq.symm⟩
    · intro a'' _
      rw [distinctPrefixLen_appendZero]
  rw [h1, h2]

/-! ### Section 6: Motzkin generating function, Catalan's triangle, and Main Theorem (Question 5.2) -/

/-- Motzkin numbers `M_n` (OEIS A001006): `M_0 = 1, M_1 = 1, M_{n+2} = M_{n+1} + ∑_{i=0}^n M_i M_{n-i}`. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => motzkin (n + 1) + ∑ i : Fin (n + 1), motzkin i.val * motzkin (n - i.val)
termination_by n => n
decreasing_by all_goals omega

private lemma motzkin_succ_succ (n : ℕ) :
    motzkin (n + 2) = motzkin (n + 1) + ∑ i ∈ range (n + 1), motzkin i * motzkin (n - i) := by
  rw [motzkin]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => motzkin i * motzkin (n - i)) (n + 1)]

/-- Formal Motzkin generating function `m(x) = ∑_{n ≥ 0} M_n x^n ∈ ℚ[[x]]`. -/
noncomputable def motzkinSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (motzkin n : ℚ)

/-- Auxiliary series `p(x) = x + x^2 m(x) ∈ ℚ[[x]]`. -/
noncomputable def pSeries : PowerSeries ℚ :=
  PowerSeries.X + PowerSeries.X ^ 2 * motzkinSeries

private lemma coeff_motzkinSeries (n : ℕ) :
    PowerSeries.coeff n motzkinSeries = (motzkin n : ℚ) :=
  PowerSeries.coeff_mk n _

private lemma coeff_X_mul_succ (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_succ_X_mul]

private lemma motzkinSeries_eq :
    motzkinSeries = 1 + PowerSeries.X * motzkinSeries + PowerSeries.X ^ 2 * motzkinSeries ^ 2 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [map_add, map_add, coeff_motzkinSeries, PowerSeries.coeff_one, if_pos rfl,
      PowerSeries.coeff_zero_X_mul, sq, mul_assoc, PowerSeries.coeff_zero_X_mul, add_zero, add_zero]
    simp [motzkin]
  | succ n =>
    cases n with
    | zero =>
      rw [map_add, map_add, coeff_motzkinSeries, PowerSeries.coeff_one, if_neg (by omega), zero_add,
        coeff_X_mul_succ, coeff_motzkinSeries, sq, mul_assoc, coeff_X_mul_succ,
        PowerSeries.coeff_zero_X_mul, add_zero]
      simp [motzkin]
    | succ n =>
      rw [map_add, map_add, coeff_motzkinSeries, PowerSeries.coeff_one, if_neg (by omega), zero_add]
      rw [coeff_X_mul_succ, coeff_motzkinSeries]
      rw [sq, mul_assoc, coeff_X_mul_succ, coeff_X_mul_succ]
      rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i motzkinSeries * PowerSeries.coeff j motzkinSeries) n]
      simp_rw [coeff_motzkinSeries]
      rw [motzkin_succ_succ]
      simp [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]

private lemma one_sub_pSeries_mul_motzkin :
    (1 - pSeries) * motzkinSeries = 1 := by
  have h := motzkinSeries_eq
  unfold pSeries
  linear_combination h

private lemma pSeries_mul_motzkin :
    pSeries * motzkinSeries = motzkinSeries - 1 := by
  have h := one_sub_pSeries_mul_motzkin
  linear_combination -h

private lemma coeff_zero_pSeries : PowerSeries.coeff 0 pSeries = 0 := by
  simp [pSeries]

private lemma coeff_one_pSeries : PowerSeries.coeff 1 pSeries = 1 := by
  rw [pSeries, map_add, PowerSeries.coeff_X, if_pos rfl, sq, mul_assoc, coeff_X_mul_succ,
    PowerSeries.coeff_zero_X_mul, add_zero]

private lemma coeff_pSeries_pow_eq_zero_of_lt :
    ∀ {j n : ℕ}, n < j → PowerSeries.coeff n (pSeries ^ j) = 0 := by
  intro j
  induction j with
  | zero => intro n hn; omega
  | succ j ih =>
    intro n hn
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a pSeries * PowerSeries.coeff b (pSeries ^ j)) n]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_range] at ha
    cases a with
    | zero => rw [coeff_zero_pSeries, zero_mul]
    | succ k =>
      have hlt : n - (k + 1) < j := by omega
      rw [ih hlt, mul_zero]

private lemma coeff_pSeries_pow_mul_eq_zero_of_lt {j n : ℕ} (f : PowerSeries ℚ) (h : n < j) :
    PowerSeries.coeff n (pSeries ^ j * f) = 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (pSeries ^ j) * PowerSeries.coeff b f) n]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [coeff_pSeries_pow_eq_zero_of_lt (by omega : a < j), zero_mul]

private lemma motzkinSeries_eq_geom_sum_add (M : ℕ) :
    motzkinSeries = (∑ i ∈ range M, pSeries ^ i) + pSeries ^ M * motzkinSeries := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, add_assoc]
    have hstep : pSeries ^ M + pSeries ^ (M + 1) * motzkinSeries = pSeries ^ M * motzkinSeries := by
      have hm := pSeries_mul_motzkin
      calc
        pSeries ^ M + pSeries ^ (M + 1) * motzkinSeries
            = pSeries ^ M * (1 + pSeries * motzkinSeries) := by rw [pow_succ]; ring
        _ = pSeries ^ M * motzkinSeries := by rw [hm, add_sub_cancel]
    rw [hstep, ← ih]

private lemma coeff_phiOp_zero (P : Polynomial ℚ) : (phiOp P).coeff 0 = 0 := by
  unfold phiOp
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
  have : ∑ r ∈ range (j + 1), (Polynomial.X ^ (r + 1) : Polynomial ℚ).coeff 0 = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    simp [Polynomial.coeff_X_pow]
  rw [this, mul_zero]

private lemma coeff_phiOp_succ (P : Polynomial ℚ) (r N : ℕ) (hN : P.natDegree ≤ N) :
    (phiOp P).coeff (r + 1) = ∑ k ∈ range (N + 1), if r ≤ k then P.coeff k else 0 := by
  rw [phiOp_eq_sum_support (s := range (N + 1)) P (fun j hj => Finset.mem_range.mpr
    (by have := Polynomial.le_natDegree_of_ne_zero hj; omega))]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
  by_cases hrk : r ≤ k
  · rw [if_pos hrk]
    rw [Finset.sum_eq_single r]
    · simp [Polynomial.coeff_X_pow]
    · intro b _ hbr
      rw [Polynomial.coeff_X_pow, if_neg (by omega)]
    · intro hr; exact absurd (Finset.mem_range.mpr (by omega)) hr
  · rw [if_neg hrk]
    have : ∑ b ∈ range (k + 1), (Polynomial.X ^ (b + 1) : Polynomial ℚ).coeff (r + 1) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [Finset.mem_range] at hb
      rw [Polynomial.coeff_X_pow, if_neg (by omega)]
    rw [this, mul_zero]

private lemma natDegree_polyOfOutcome_le {n : ℕ} (π : Fin n → Fin n) :
    (polyOfOutcome π).natDegree ≤ n := by
  unfold polyOfOutcome
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le n, fun a _ => ?_⟩
  dsimp only [Function.comp_apply]
  rw [Polynomial.natDegree_X_pow]
  exact distinctPrefixLen_le a

/-- **Proposition 2 (Base bivariate generating function):**
For every `n, j : ℕ`, `[y^j] P_{δ_n}(y) = [x^n] p(x)^j`. -/
theorem polyOfOutcome_delta_coeff :
    ∀ (n j : ℕ), (polyOfOutcome (delta n)).coeff j = PowerSeries.coeff n (pSeries ^ j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro j
    match n with
    | 0 =>
      rw [polyOfOutcome_delta_zero, Polynomial.coeff_one]
      cases j with
      | zero => simp
      | succ j =>
        rw [if_neg (Nat.succ_ne_zero j), coeff_pSeries_pow_eq_zero_of_lt (Nat.succ_pos j)]
    | 1 =>
      rw [polyOfOutcome_delta_one, Polynomial.coeff_X]
      cases j with
      | zero => simp
      | succ j =>
        cases j with
        | zero => simp [coeff_one_pSeries]
        | succ j =>
          rw [if_neg (by omega), coeff_pSeries_pow_eq_zero_of_lt (by omega)]
    | n + 2 =>
      rw [polyOfOutcome_delta, polyOfOutcome_cons1, Polynomial.coeff_add]
      cases j with
      | zero =>
        rw [Polynomial.coeff_X_mul_zero, coeff_phiOp_zero, add_zero, pow_zero, PowerSeries.coeff_one,
          if_neg (by omega)]
      | succ r =>
        rw [Polynomial.coeff_X_mul, coeff_phiOp_succ _ r n (natDegree_polyOfOutcome_le _)]
        rw [ih (n + 1) (by omega) r]
        have hsum : (∑ k ∈ range (n + 1), if r ≤ k then (polyOfOutcome (delta n)).coeff k else 0) =
            PowerSeries.coeff n (pSeries ^ r * motzkinSeries) := by
          have hgeom := congrArg (fun f => pSeries ^ r * f) (motzkinSeries_eq_geom_sum_add (n + 1))
          rw [mul_add, Finset.mul_sum, ← mul_assoc, ← pow_add] at hgeom
          have hcoeff := congrArg (PowerSeries.coeff n) hgeom
          rw [map_add, map_sum, coeff_pSeries_pow_mul_eq_zero_of_lt _ (by omega : n < r + (n + 1)),
            add_zero] at hcoeff
          rw [hcoeff]
          symm
          have hsplit : ∑ i ∈ range (n + 1), PowerSeries.coeff n (pSeries ^ r * pSeries ^ i) =
              ∑ i ∈ range (n + 1), PowerSeries.coeff n (pSeries ^ (r + i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← pow_add]
          rw [hsplit]
          -- Reindex `k = r + i` (terms with `r + i > n` vanish since `coeff n (p^k) = 0`).
          by_cases hrn : r ≤ n
          · have h1 : ∑ i ∈ range (n + 1), PowerSeries.coeff n (pSeries ^ (r + i)) =
                ∑ i ∈ range (n + 1 - r), PowerSeries.coeff n (pSeries ^ (r + i)) := by
              symm
              refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hni => ?_
              rw [Finset.mem_range] at hi hni
              exact coeff_pSeries_pow_eq_zero_of_lt (by omega)
            rw [h1]
            have h2 : ∑ k ∈ range (n + 1), (if r ≤ k then (polyOfOutcome (delta n)).coeff k else 0) =
                ∑ k ∈ (range (n + 1)).filter (fun k => r ≤ k), (polyOfOutcome (delta n)).coeff k := by
              rw [Finset.sum_filter]
            rw [h2]
            refine Finset.sum_nbij (fun i => r + i) ?_ ?_ ?_ ?_
            · intro i hi
              rw [Finset.mem_range] at hi
              rw [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, by omega⟩
            · intro i₁ _ i₂ _ hEq; dsimp only at hEq; omega
            · intro k hk
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
              exact ⟨k - r, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
            · intro i _; exact (ih n (by omega) (r + i)).symm
          · have h1 : ∑ i ∈ range (n + 1), PowerSeries.coeff n (pSeries ^ (r + i)) = 0 :=
              Finset.sum_eq_zero fun i _ => coeff_pSeries_pow_eq_zero_of_lt (by omega)
            have h2 : ∑ k ∈ range (n + 1), (if r ≤ k then (polyOfOutcome (delta n)).coeff k else 0) = 0 :=
              Finset.sum_eq_zero fun k hk => by rw [Finset.mem_range] at hk; rw [if_neg (by omega)]
            rw [h1, h2]
        rw [hsum]
        have hstep : pSeries ^ (r + 1) =
            PowerSeries.X * pSeries ^ r + PowerSeries.X ^ 2 * (pSeries ^ r * motzkinSeries) := by
          rw [pow_succ, pSeries]; ring
        rw [hstep, map_add, coeff_X_mul_succ, sq, mul_assoc,
          coeff_X_mul_succ, coeff_X_mul_succ]

/-- Catalan's triangle `B(r, i)` (`0 ≤ i ≤ r`, OEIS A009766), defined recursively by
`B(0, 0) = 1` and `B(r + 1, i) = ∑_{t = 0}^{min(i, r)} B(r, t)`. -/
def catalanTri : ℕ → ℕ → ℕ
  | 0, i => if i = 0 then 1 else 0
  | r + 1, i => if i ≤ r + 1 then ∑ t ∈ range (min i r + 1), catalanTri r t else 0

/-- Closed-form verification of Catalan's triangle:
`(r + 1) * B(r, i) = (r + 1 - i) * C(r + i, i)` for all `i ≤ r`. -/
theorem catalanTri_closed_form :
    ∀ (r i : ℕ), i ≤ r → (r + 1) * catalanTri r i = (r + 1 - i) * (r + i).choose i := by
  intro r
  induction r with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp [catalanTri]
  | succ r ih =>
    intro i hi
    induction i with
    | zero =>
      have h0 : catalanTri (r + 1) 0 = 1 := by
        simp only [catalanTri, Nat.zero_le, ↓reduceIte, Nat.zero_min]
        have hbase : ∀ m, catalanTri m 0 = 1 := by
          intro m
          induction m with
          | zero => rfl
          | succ m ihm => simp [catalanTri, ihm]
        exact hbase r
      rw [h0]; simp
    | succ i ihi =>
      by_cases hir : i + 1 ≤ r
      · have hrec : catalanTri (r + 1) (i + 1) = catalanTri (r + 1) i + catalanTri r (i + 1) := by
          simp only [catalanTri, hi, show i ≤ r + 1 by omega, ↓reduceIte]
          rw [show min (i + 1) r = i + 1 by omega, show min i r = i by omega, Finset.sum_range_succ]
        have h1 := ihi (by omega)
        have h2 := ih (i + 1) hir
        have hpascal : (r + 1 + (i + 1)).choose (i + 1) =
            (r + 1 + i).choose i + (r + 1 + i).choose (i + 1) := by
          rw [show r + 1 + (i + 1) = (r + 1 + i) + 1 by omega, Nat.choose_succ_succ]
        have hcho : (r + 1 + i).choose (i + 1) * (i + 1) = (r + 1) * (r + i + 1).choose i := by
          have := Nat.choose_succ_right_eq (r + 1 + i) i
          have hsub : r + 1 + i - i = r + 1 := by omega
          rw [hsub] at this
          rw [show r + i + 1 = r + 1 + i by omega]
          linarith
        have hcho2 : (r + 1) * ((r + 1 + i).choose i * (r + 1 - i)) =
            (r + 1) * (r + 1 - i) * (r + 1 + i).choose i := by ring
        -- Multiply target by `(r + 1)` and simplify via `Nat.choose_succ_right_eq`!
        have hmul : (r + 1) * ((r + 2) * catalanTri (r + 1) (i + 1)) =
            (r + 1) * ((r + 2 - (i + 1)) * (r + 1 + (i + 1)).choose (i + 1)) := by
          rw [hrec, mul_add, mul_add]
          rw [show (r + 1) * ((r + 2) * catalanTri (r + 1) i) =
              (r + 1) * ((r + 1 + 1) * catalanTri (r + 1) i) by rfl, h1]
          rw [show (r + 1) * ((r + 2) * catalanTri r (i + 1)) =
              (r + 2) * ((r + 1) * catalanTri r (i + 1)) by ring, h2]
          rw [hpascal]
          have hkey : (r + 1 + i).choose i * (r + 1) = (r + 1 + i).choose (i + 1) * (i + 1) := by
            have := Nat.choose_succ_right_eq (r + 1 + i) i
            have hsub : r + 1 + i - i = r + 1 := by omega
            rw [hsub] at this; linarith
          have h1s : r + 1 + 1 - i = (r + 1 - i) + 1 := by omega
          have h2s : r + 1 - (i + 1) = r - i := by omega
          have h3s : r + 2 - (i + 1) = r + 1 - i := by omega
          have h4s : r + (i + 1) = r + 1 + i := by omega
          rw [h1s, h2s, h3s, h4s]
          have hr_eq : r + 1 - i = (r - i) + 1 := by omega
          rw [hr_eq]
          have hadd : (r + 1) = (r - i) + (i + 1) := by omega
          calc
            (r + 1) * (((r - i) + 1 + 1) * (r + 1 + i).choose i) +
                (r + 2) * ((r - i) * (r + 1 + i).choose (i + 1))
                = ((r - i) + 1) * ((r + 1) * (r + 1 + i).choose i) +
                  (r + 1) * (r + 1 + i).choose i +
                  (r + 2) * (r - i) * (r + 1 + i).choose (i + 1) := by ring
            _ = ((r - i) + 1) * ((r + 1) * (r + 1 + i).choose i) +
                  ((r + 1 + i).choose (i + 1) * (i + 1)) +
                  (r + 2) * (r - i) * (r + 1 + i).choose (i + 1) := by
                  rw [mul_comm (r + 1) ((r + 1 + i).choose i), hkey]
            _ = (r + 1) * (((r - i) + 1) * ((r + 1 + i).choose i + (r + 1 + i).choose (i + 1))) := by
                  have : (r + 1) * ((r - i) + 1) = (i + 1) + (r + 2) * (r - i) := by
                    nlinarith [hadd]
                  nlinarith
        exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos r) hmul
      · -- Boundary case `i + 1 = r + 1`, so `i = r`!
        have hir_eq : i = r := by omega
        subst i
        have heq_diag : catalanTri (r + 1) (r + 1) = catalanTri (r + 1) r := by
          simp only [catalanTri, le_refl, show r ≤ r + 1 by omega, ↓reduceIte]
          rw [show min (r + 1) r = r by omega, show min r r = r by omega]
        rw [heq_diag]
        have h1 := ihi (by omega)
        rw [show (r + 1 + 1 - r) = 2 by omega] at h1
        rw [show (r + 2 - (r + 1)) = 1 by omega, one_mul]
        rw [show (r + 1 + 1) = r + 2 by omega] at h1
        rw [h1]
        have hsym := Nat.choose_succ_succ (r + 1 + r) r
        have hhalf : (r + 1 + r).choose (r + 1) = (r + 1 + r).choose r := by
          rw [← Nat.choose_symm (by omega : r ≤ r + 1 + r)]
          congr 1; omega
        rw [show r + 1 + (r + 1) = (r + 1 + r) + 1 by omega, hsym, hhalf]
        ring

/-- Evaluation of iterated `Φ^k(y^j)` at `y = 1`: `c(0, j) = 1`, `c(k + 1, j) = ∑_{r=0}^j c(k, r + 1)`. -/
def cCoeff : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, j => ∑ r ∈ range (j + 1), cCoeff k (r + 1)

private lemma phiOp_iter_add (k : ℕ) (P Q : Polynomial ℚ) :
    phiOp^[k] (P + Q) = phiOp^[k] P + phiOp^[k] Q := by
  induction k generalizing P Q with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      phiOp_add, ih]

private lemma phiOp_iter_sum {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → Polynomial ℚ) :
    phiOp^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, phiOp^[k] (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [phiOp]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, phiOp_iter_add, ih, Finset.sum_insert ha]

private lemma phiOp_iter_C_mul (k : ℕ) (c : ℚ) (P : Polynomial ℚ) :
    phiOp^[k] (Polynomial.C c * P) = Polynomial.C c * phiOp^[k] P := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, phiOp_C_mul, ih]

private lemma eval_one_phiOp_iter_X_pow (k j : ℕ) :
    (phiOp^[k] (Polynomial.X ^ j)).eval 1 = (cCoeff k j : ℚ) := by
  induction k generalizing j with
  | zero => simp [cCoeff]
  | succ k ih =>
    rw [Function.iterate_succ_apply, phiOp_X_pow, phiOp_iter_sum, Polynomial.eval_finsetSum]
    simp_rw [ih, cCoeff, Nat.cast_sum]

private lemma eval_one_phiOp_iter (k N : ℕ) (P : Polynomial ℚ) (hN : P.natDegree ≤ N) :
    (phiOp^[k] P).eval 1 = ∑ j ∈ range (N + 1), P.coeff j * (cCoeff k j : ℚ) := by
  have hP : P = ∑ j ∈ range (N + 1), Polynomial.C (P.coeff j) * Polynomial.X ^ j := by
    conv_lhs => rw [Polynomial.as_sum_range' P (N + 1) (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
  conv_lhs => rw [hP]
  rw [phiOp_iter_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phiOp_iter_C_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_one_phiOp_iter_X_pow]

/-- Target power series `G_k(p(x))` expressed directly in powers of `motzkinSeries`. -/
noncomputable def targetSeries : ℕ → PowerSeries ℚ
  | 0 => motzkinSeries
  | k + 1 => ∑ i ∈ range (k + 1), (catalanTri k i : ℚ) • motzkinSeries ^ (k + 2 - i)

private lemma targetSeries_zero_coeff_eq (r : ℕ) :
    PowerSeries.coeff 0 (targetSeries (r + 1)) = ∑ i ∈ range (r + 1), (catalanTri r i : ℚ) := by
  simp only [targetSeries, map_sum, PowerSeries.coeff_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm0 : PowerSeries.coeff 0 (motzkinSeries ^ (r + 2 - i)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_motzkinSeries]
    simp [motzkin]
  rw [hm0, mul_one]

/-- Algebraic step for Lemma C:
`p(x) * targetSeries (k + 1) = m(x) * (targetSeries k - C (coeff 0 (targetSeries k)))`. -/
private lemma pSeries_mul_targetSeries_succ (k : ℕ) :
    pSeries * targetSeries (k + 1) =
      motzkinSeries * (targetSeries k - PowerSeries.C (PowerSeries.coeff 0 (targetSeries k))) := by
  cases k with
  | zero =>
    have h0 : PowerSeries.coeff 0 (targetSeries 0) = 1 := by
      rw [targetSeries, coeff_motzkinSeries]; simp [motzkin]
    rw [h0, map_one]
    have ht1 : targetSeries 1 = motzkinSeries ^ 2 := by
      simp [targetSeries, catalanTri]
    rw [ht1, targetSeries]
    have hm := pSeries_mul_motzkin
    linear_combination motzkinSeries * hm
  | succ r =>
    rw [targetSeries_zero_coeff_eq r]
    have hsub : targetSeries (r + 1) - PowerSeries.C (∑ i ∈ range (r + 1), (catalanTri r i : ℚ)) =
        (motzkinSeries - 1) *
          ∑ i ∈ range (r + 1), (catalanTri r i : ℚ) • ∑ s ∈ range (r + 2 - i), motzkinSeries ^ s := by
      simp only [targetSeries, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hC : PowerSeries.C (catalanTri r i : ℚ) = (catalanTri r i : ℚ) • (1 : PowerSeries ℚ) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [hC, ← smul_sub, Algebra.mul_smul_comm]
      congr 1
      simpa using (geom_sum_mul (motzkinSeries : PowerSeries ℚ) (r + 2 - i)).symm.trans (mul_comm _ _)
    have hswap : ∑ i ∈ range (r + 1), (catalanTri r i : ℚ) • ∑ s ∈ range (r + 2 - i), motzkinSeries ^ s =
        ∑ j ∈ range (r + 2), (catalanTri (r + 1) j : ℚ) • motzkinSeries ^ (r + 1 - j) := by
      simp_rw [Finset.smul_sum]
      have hpad : ∀ i ∈ range (r + 1),
          ∑ s ∈ range (r + 2 - i), (catalanTri r i : ℚ) • motzkinSeries ^ s =
          ∑ s ∈ range (r + 2),
            if i + s ≤ r + 1 then (catalanTri r i : ℚ) • motzkinSeries ^ s else 0 := by
        intro i hi
        rw [Finset.mem_range] at hi
        symm
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext s; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
      symm
      refine Finset.sum_nbij (fun j => r + 1 - j) ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
      · intro j₁ hj₁ j₂ hj₂ hEq
        simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
        dsimp only at hEq
        omega
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_range] at hs
        exact ⟨r + 1 - s, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
      · intro j hj
        rw [Finset.mem_range] at hj
        simp only [catalanTri, show j ≤ r + 1 by omega, ↓reduceIte, Nat.cast_sum, Finset.sum_smul]
        symm
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hsub, hswap]
    have hm := pSeries_mul_motzkin
    rw [← hm]
    have hrhs : motzkinSeries * (pSeries * motzkinSeries *
          ∑ j ∈ range (r + 2), (catalanTri (r + 1) j : ℚ) • motzkinSeries ^ (r + 1 - j)) =
        pSeries * ∑ j ∈ range (r + 2),
          (catalanTri (r + 1) j : ℚ) • (motzkinSeries ^ 2 * motzkinSeries ^ (r + 1 - j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.mul_smul_comm, Algebra.mul_smul_comm, Algebra.mul_smul_comm]
      congr 1; ring
    rw [hrhs]
    simp only [targetSeries]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [← pow_add, show 2 + (r + 1 - j) = r + 3 - j by omega]

/-- If `coeff d (pSeries * h) = 0` for all `d ≤ M + 1`, then `coeff n h = 0` for all `n ≤ M`. -/
private lemma coeff_eq_zero_of_pSeries_mul_eq_zero {h : PowerSeries ℚ} {M : ℕ}
    (hzero : ∀ d ≤ M + 1, PowerSeries.coeff d (pSeries * h) = 0) :
    ∀ n ≤ M, PowerSeries.coeff n h = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hd := hzero (n + 1) (by omega)
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i pSeries * PowerSeries.coeff j h) (n + 1)] at hd
    rw [Finset.sum_range_succ', coeff_zero_pSeries, zero_mul, add_zero] at hd
    rw [Finset.sum_range_succ', coeff_one_pSeries, one_mul] at hd
    have htail : ∑ k ∈ range n, PowerSeries.coeff (k + 2) pSeries * PowerSeries.coeff (n + 1 - (k + 2)) h = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [ih (n + 1 - (k + 2)) (by omega) (by omega), mul_zero]
    rw [htail, zero_add] at hd
    simpa using hd

/-- **Lemma C (Catalan-triangle expansion):**
For every `k, N : ℕ`,
`[x^N] targetSeries k = ∑_{j=0}^N c(k, j) * [x^N] p(x)^j`. -/
theorem coeff_targetSeries_eq :
    ∀ (k N : ℕ), PowerSeries.coeff N (targetSeries k) =
      ∑ j ∈ range (N + 1), (cCoeff k j : ℚ) * PowerSeries.coeff N (pSeries ^ j) := by
  intro k
  induction k with
  | zero =>
    intro N
    simp only [targetSeries, cCoeff, Nat.cast_one, one_mul]
    have hgeom := congrArg (PowerSeries.coeff N) (motzkinSeries_eq_geom_sum_add (N + 1))
    rw [map_add, map_sum, coeff_pSeries_pow_mul_eq_zero_of_lt _ (by omega), add_zero] at hgeom
    exact hgeom
  | succ k ih =>
    intro N
    let S : ℕ → ℕ → PowerSeries ℚ := fun m M =>
      ∑ j ∈ range (M + 1), (cCoeff m j : ℚ) • pSeries ^ j
    let K : ℚ := ∑ r ∈ range (N + 1), (cCoeff k (r + 1) : ℚ)
    have hfin : pSeries * S (k + 1) N =
        motzkinSeries * (S k (N + 1) - PowerSeries.C (cCoeff k 0 : ℚ)) -
          K • (pSeries ^ (N + 2) * motzkinSeries) := by
      have h1sub : (1 - pSeries) * (pSeries * S (k + 1) N) =
          (S k (N + 1) - PowerSeries.C (cCoeff k 0 : ℚ)) - K • pSeries ^ (N + 2) := by
        have hS1 : pSeries * S (k + 1) N =
            ∑ r ∈ range (N + 1), (cCoeff k (r + 1) : ℚ) •
              (pSeries ^ (r + 1) * ∑ t ∈ range (N + 1 - r), pSeries ^ t) := by
          simp only [S, cCoeff, Nat.cast_sum, Finset.sum_smul, Finset.mul_sum]
          have hpad : ∀ j ∈ range (N + 1),
              ∑ r ∈ range (j + 1), pSeries * ((cCoeff k (r + 1) : ℚ) • pSeries ^ j) =
              ∑ r ∈ range (N + 1),
                if r ≤ j then (cCoeff k (r + 1) : ℚ) • pSeries ^ (j + 1) else 0 := by
            intro j hj
            rw [Finset.mem_range] at hj
            symm
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun r _ => ?_
            · ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega
            · rw [Algebra.mul_smul_comm, pow_succ']
          rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.mem_range] at hr
          rw [← Finset.sum_filter, Finset.smul_sum]
          symm
          refine Finset.sum_nbij (fun t => r + t) ?_ ?_ ?_ ?_
          · intro t ht; rw [Finset.mem_range] at ht
            rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, by omega⟩
          · intro t₁ _ t₂ _ hEq; dsimp only at hEq; omega
          · intro j hj
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
            exact ⟨j - r, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
          · intro t _
            rw [← pow_add, show r + 1 + t = r + t + 1 by omega]
        rw [hS1, Finset.mul_sum]
        have hterm : ∀ r ∈ range (N + 1),
            (1 - pSeries) * ((cCoeff k (r + 1) : ℚ) •
              (pSeries ^ (r + 1) * ∑ t ∈ range (N + 1 - r), pSeries ^ t)) =
            (cCoeff k (r + 1) : ℚ) • pSeries ^ (r + 1) -
              (cCoeff k (r + 1) : ℚ) • pSeries ^ (N + 2) := by
          intro r hr
          rw [Finset.mem_range] at hr
          rw [Algebra.mul_smul_comm, ← smul_sub]
          congr 1
          have hgeom := geom_sum_mul pSeries (N + 1 - r)
          calc
            (1 - pSeries) * (pSeries ^ (r + 1) * ∑ t ∈ range (N + 1 - r), pSeries ^ t)
                = pSeries ^ (r + 1) * ((1 - pSeries) * ∑ t ∈ range (N + 1 - r), pSeries ^ t) := by ring
            _ = pSeries ^ (r + 1) * (1 - pSeries ^ (N + 1 - r)) := by
                congr 1; linear_combination -hgeom
            _ = pSeries ^ (r + 1) - pSeries ^ (N + 2) := by
                rw [mul_sub, mul_one, ← pow_add, show r + 1 + (N + 1 - r) = N + 2 by omega]
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_smul]
        congr 1
        simp only [S]
        conv_rhs => rw [Finset.sum_range_succ', pow_zero]
        have hC : PowerSeries.C (cCoeff k 0 : ℚ) = (cCoeff k 0 : ℚ) • (1 : PowerSeries ℚ) := by
          rw [Algebra.smul_def, mul_one]; rfl
        rw [hC, add_sub_cancel_right]
      have hmul := congrArg (fun f => motzkinSeries * f) h1sub
      have hm1 : motzkinSeries * (1 - pSeries) = 1 := by
        rw [mul_comm, one_sub_pSeries_mul_motzkin]
      rw [← mul_assoc, hm1, one_mul, mul_sub, Algebra.mul_smul_comm,
        mul_comm motzkinSeries (pSeries ^ (N + 2))] at hmul
      exact hmul
    have h0_eq : PowerSeries.coeff 0 (targetSeries k) = (cCoeff k 0 : ℚ) := by
      rw [ih 0]; simp
    have hdiff : pSeries * (targetSeries (k + 1) - S (k + 1) N) =
        motzkinSeries * (targetSeries k - S k (N + 1)) + K • (pSeries ^ (N + 2) * motzkinSeries) := by
      have h1 := pSeries_mul_targetSeries_succ k
      rw [h0_eq] at h1
      linear_combination h1 - hfin
    have hzero : ∀ d ≤ N + 1, PowerSeries.coeff d (pSeries * (targetSeries (k + 1) - S (k + 1) N)) = 0 := by
      intro d hd
      rw [hdiff, map_add, PowerSeries.coeff_smul, smul_eq_mul,
        coeff_pSeries_pow_mul_eq_zero_of_lt _ (by omega), mul_zero, add_zero]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a motzkinSeries * PowerSeries.coeff b (targetSeries k - S k (N + 1))) d]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [Finset.mem_range] at ha
      have hx2 : PowerSeries.coeff (d - a) (targetSeries k - S k (N + 1)) = 0 := by
        rw [map_sub, ih (d - a)]
        simp only [S, map_sum, PowerSeries.coeff_smul, smul_eq_mul]
        have htrunc : ∑ j ∈ range (N + 2), (cCoeff k j : ℚ) * PowerSeries.coeff (d - a) (pSeries ^ j) =
            ∑ j ∈ range ((d - a) + 1), (cCoeff k j : ℚ) * PowerSeries.coeff (d - a) (pSeries ^ j) := by
          symm
          refine Finset.sum_subset (Finset.range_mono (by omega)) fun j hj hnj => ?_
          rw [Finset.mem_range] at hj hnj
          rw [coeff_pSeries_pow_eq_zero_of_lt (by omega), mul_zero]
        rw [htrunc, sub_self]
      rw [hx2, mul_zero]
    have hN := coeff_eq_zero_of_pSeries_mul_eq_zero hzero N le_rfl
    rw [map_sub, sub_eq_zero] at hN
    rw [hN]
    simp only [S, map_sum, PowerSeries.coeff_smul, smul_eq_mul]

/-- The permutation `π_{n, k} = 1 2 ... k n (n - 1) ... (k + 1)` on `Fin n` (0-indexed). -/
def targetPerm (n k : ℕ) (_hkn : k ≤ n) : Fin n → Fin n :=
  fun p => if h : p.val < k then p else ⟨n + k - 1 - p.val, by have := p.isLt; omega⟩

private lemma targetPerm_zero (n : ℕ) : targetPerm n 0 (Nat.zero_le n) = delta n := by
  funext p
  simp [targetPerm, delta]

private lemma targetPerm_succ (m k : ℕ) :
    targetPerm (m + (k + 1)) (k + 1) (by omega) =
      cons1 (targetPerm (m + k) k (by omega)) := by
  funext p
  refine Fin.cases ?_ (fun q => ?_) p
  · simp [targetPerm, cons1]
  · simp only [targetPerm, cons1, Fin.cases_succ, Fin.val_succ]
    by_cases hqk : q.val < k
    · rw [dif_pos (by omega), dif_pos hqk]
    · rw [dif_neg (by omega), dif_neg hqk]
      ext
      have hqlt : q.val < m + k := q.isLt
      simp only [Fin.val_succ, Nat.add_eq] at hqlt ⊢
      omega

private lemma polyOfOutcome_targetPerm_add (m k : ℕ) :
    polyOfOutcome (targetPerm (m + k) k (by omega)) =
      phiOp^[k] (polyOfOutcome (delta m)) := by
  induction k with
  | zero =>
    simp [targetPerm_zero]
  | succ k ih =>
    rw [targetPerm_succ, polyOfOutcome_cons1, ih, Function.iterate_succ_apply']

/-- **Main Theorem (Resolution of Clifton–Harris–Khaqan Question 5.2, arXiv:2611.29890v1):**
For all integers `n ≥ k ≥ 1`,
`|O_B⁻¹(1 2 ... k n (n - 1) ... (k + 1))| = ∑_{i=0}^{k-1} B(k - 1, i) * [x^(n - k)] m(x)^(k + 1 - i)`,
where `B(r, i)` is Catalan's triangle and `m(x)` is the Motzkin generating function. -/
theorem clifton_harris_khaqan_Q52 {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((outcomeSet (targetPerm n k hkn)).card : ℚ) =
      ∑ i ∈ range k, (catalanTri (k - 1) i : ℚ) *
        PowerSeries.coeff (n - k) (motzkinSeries ^ (k + 1 - i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  have hcard : ((outcomeSet (targetPerm (m + k) k hkn)).card : ℚ) =
      (polyOfOutcome (targetPerm (m + k) k hkn)).eval 1 := by
    unfold polyOfOutcome
    rw [Polynomial.eval_finsetSum]
    simp
  rw [hcard, polyOfOutcome_targetPerm_add m k,
    eval_one_phiOp_iter k m _ (natDegree_polyOfOutcome_le _)]
  have hsum : ∑ j ∈ range (m + 1), (polyOfOutcome (delta m)).coeff j * (cCoeff k j : ℚ) =
      PowerSeries.coeff m (targetSeries k) := by
    rw [coeff_targetSeries_eq k m]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [polyOfOutcome_delta_coeff m j, mul_comm]
  rw [hsum]
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  simp only [targetSeries, map_sum, PowerSeries.coeff_smul, smul_eq_mul,
    Nat.add_sub_cancel]

/-- `r`-fold convolution of Motzkin numbers: `M^{(r)}_N = [x^N] m(x)^r` in `ℕ`. -/
def motzkinConv : ℕ → ℕ → ℕ
  | 0, N => if N = 0 then 1 else 0
  | r + 1, N => ∑ i ∈ range (N + 1), motzkin i * motzkinConv r (N - i)

private lemma coeff_motzkinSeries_pow (r N : ℕ) :
    PowerSeries.coeff N (motzkinSeries ^ r) = (motzkinConv r N : ℚ) := by
  induction r generalizing N with
  | zero =>
    simp [motzkinConv, PowerSeries.coeff_one]
  | succ r ih =>
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i motzkinSeries * PowerSeries.coeff j (motzkinSeries ^ r)) N]
    simp_rw [coeff_motzkinSeries, ih]
    simp [motzkinConv, Nat.cast_sum, Nat.cast_mul]

/-- Pure `ℕ`-valued corollary of `clifton_harris_khaqan_Q52`:
`|O_B⁻¹(1 2 ... k n (n - 1) ... (k + 1))| = ∑_{i=0}^{k-1} B(k - 1, i) * M^{(k + 1 - i)}_{n - k}`. -/
theorem clifton_harris_khaqan_Q52_nat {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (outcomeSet (targetPerm n k hkn)).card =
      ∑ i ∈ range k, catalanTri (k - 1) i * motzkinConv (k + 1 - i) (n - k) := by
  have hq := clifton_harris_khaqan_Q52 hk hkn
  simp_rw [coeff_motzkinSeries_pow] at hq
  exact_mod_cast hq

end CliftonHarrisKhaqanBackgammon
