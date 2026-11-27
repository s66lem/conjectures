import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Disproof of Runbo Li's Twin-Practical Conjecture 1.1 (`NNTDM` 32(3), 2026)

This file formalizes the refutation of Conjecture 1.1 of Runbo Li,
*On a conjecture involving twin practical numbers*, Notes on Number Theory and Discrete Mathematics
32(3) (2026), 544–555 (DOI `10.7546/nntdm.2026.32.3.544-555`):

> **Conjecture 1.1.** For any positive integer `C`, there are infinitely many practical numbers `q`
> such that `q^C` and `q^C + 2` are also practical numbers.

We prove:
1. `not_practical_pow30_add_two`: for every positive integer `q`, `q^30 + 2` is not practical.
2. `not_practical_pow_mul30_add_two`: for every `C` divisible by `30` and every `q ≥ 1`,
   `q^C + 2` is not practical.
3. `li_conjecture_1_1_empty_of_dvd_thirty` & `li_conjecture_1_1_false`: for every `C` with
   `30 ∣ C`, the set `{q | IsPractical q ∧ IsPractical (q^C) ∧ IsPractical (q^C + 2)}` is empty,
   refuting Conjecture 1.1 at `C = 30` (and infinitely many exponents `C = 30t`).
4. `local_obstruction_iff_dvd_thirty`: for any `C ≥ 1`, the local small-divisor obstruction
   `∀ q, 2 ∣ q → ¬ 4 ∣ q^C + 2 ∧ ¬ 9 ∣ q^C + 2 ∧ ¬ 5 ∣ q^C + 2 ∧ ¬ 7 ∣ q^C + 2 ∧ ¬ 11 ∣ q^C + 2 ∧ ¬ 13 ∣ q^C + 2`
   holds if and only if `30 ∣ C`, proving `C = 30` is the exact minimal modulus of this obstruction.
5. `small_exponents_witnesses`: explicit positive examples for `C ∈ {1, 2, 3, 4, 5, 6}` where
   `q`, `q^C`, and `q^C + 2` are all practical.
-/

namespace LiTwinPractical

/-- A positive integer `n` is *practical* if every integer `m` with `1 ≤ m ≤ n` can be written
as a sum of distinct positive divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 1 ≤ m → m ≤ n → ∃ S ⊆ n.divisors, S.sum id = m

/-! ### Elementary residue obstructions for `q^30 + 2` -/

private lemma pow_mod_periodic {q m k : ℕ} (hper : q ^ k % m = 1) (C : ℕ) :
    q ^ C % m = q ^ (C % k) % m := by
  conv_lhs => rw [← Nat.div_add_mod C k]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hper, one_pow, ← Nat.mul_mod, one_mul]

private lemma not_dvd_four_of_even (q : ℕ) (hq : 2 ∣ q) : ¬ 4 ∣ q ^ 30 + 2 := by
  rcases hq with ⟨k, rfl⟩
  have h1 : (2 * k) ^ 30 = 4 * (2 ^ 28 * k ^ 30) := by ring
  rw [h1]
  omega

private lemma pow30_mod (q m : ℕ) :
    q ^ 30 % m = (((q % m) ^ 2 % m) ^ 3 % m) ^ 5 % m := by
  have h : q ^ 30 = ((q ^ 2) ^ 3) ^ 5 := by ring
  rw [h]
  rw [Nat.pow_mod ((q ^ 2) ^ 3) 5 m]
  rw [Nat.pow_mod (q ^ 2) 3 m]
  rw [Nat.pow_mod q 2 m]

private lemma not_dvd_nine (q : ℕ) : ¬ 9 ∣ q ^ 30 + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow30_mod]
  have h := Nat.mod_lt q (by decide : 0 < 9)
  interval_cases (q % 9) <;> norm_num

private lemma not_dvd_five (q : ℕ) : ¬ 5 ∣ q ^ 30 + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow30_mod]
  have h := Nat.mod_lt q (by decide : 0 < 5)
  interval_cases (q % 5) <;> norm_num

private lemma not_dvd_seven (q : ℕ) : ¬ 7 ∣ q ^ 30 + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow30_mod]
  have h := Nat.mod_lt q (by decide : 0 < 7)
  interval_cases (q % 7) <;> norm_num

private lemma not_dvd_eleven (q : ℕ) : ¬ 11 ∣ q ^ 30 + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow30_mod]
  have h := Nat.mod_lt q (by decide : 0 < 11)
  interval_cases (q % 11) <;> norm_num

private lemma not_dvd_thirteen (q : ℕ) : ¬ 13 ∣ q ^ 30 + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow30_mod]
  have h := Nat.mod_lt q (by decide : 0 < 13)
  interval_cases (q % 13) <;> norm_num

private lemma odd_pow30_add_two_not_practical {n : ℕ} (hn3 : 3 ≤ n) (hodd : ¬ 2 ∣ n) :
    ¬ IsPractical n := by
  rintro ⟨_, hrep⟩
  obtain ⟨S, hSsub, hSsum⟩ := hrep 2 (by omega) (by omega)
  have hSsub1 : S ⊆ ({1} : Finset ℕ) := by
    intro d hd
    have hdiv : d ∣ n := Nat.dvd_of_mem_divisors (hSsub hd)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (hSsub hd)
    have hdle : d ≤ 2 := by
      have h1 := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
      rw [hSsum] at h1
      exact h1
    have hdne2 : d ≠ 2 := fun h2 => hodd (h2 ▸ hdiv)
    simp only [Finset.mem_singleton]
    omega
  have hle : S.sum id ≤ ({1} : Finset ℕ).sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub1 (fun _ _ _ => Nat.zero_le _)
  rw [hSsum] at hle
  simp only [Finset.sum_singleton, id] at hle
  omega

private lemma even_obstructed_not_practical {n : ℕ} (hn13 : 13 ≤ n)
    (h4 : ¬ 4 ∣ n) (h9 : ¬ 9 ∣ n) (h5 : ¬ 5 ∣ n) (h7 : ¬ 7 ∣ n) (h11 : ¬ 11 ∣ n) (h13 : ¬ 13 ∣ n) :
    ¬ IsPractical n := by
  rintro ⟨_, hrep⟩
  obtain ⟨S, hSsub, hSsum⟩ := hrep 13 (by omega) hn13
  have hSsub6 : S ⊆ ({1, 2, 3, 6} : Finset ℕ) := by
    intro d hd
    have hdiv : d ∣ n := Nat.dvd_of_mem_divisors (hSsub hd)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (hSsub hd)
    have hdle : d ≤ 13 := by
      have h1 := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
      rw [hSsum] at h1
      exact h1
    have hdne : d ≠ 4 ∧ d ≠ 5 ∧ d ≠ 7 ∧ d ≠ 8 ∧ d ≠ 9 ∧ d ≠ 10 ∧ d ≠ 11 ∧ d ≠ 12 ∧ d ≠ 13 := by
      refine ⟨fun h => h4 (h ▸ hdiv), fun h => h5 (h ▸ hdiv), fun h => h7 (h ▸ hdiv),
        fun h => h4 (dvd_trans (by decide : 4 ∣ 8) (h ▸ hdiv)),
        fun h => h9 (h ▸ hdiv),
        fun h => h5 (dvd_trans (by decide : 5 ∣ 10) (h ▸ hdiv)),
        fun h => h11 (h ▸ hdiv),
        fun h => h4 (dvd_trans (by decide : 4 ∣ 12) (h ▸ hdiv)),
        fun h => h13 (h ▸ hdiv)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases d <;> simp_all
  have hle : S.sum id ≤ ({1, 2, 3, 6} : Finset ℕ).sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub6 (fun _ _ _ => Nat.zero_le _)
  have hsum6 : ({1, 2, 3, 6} : Finset ℕ).sum id = 12 := by decide
  rw [hSsum, hsum6] at hle
  omega

/-- **Theorem 1:** For every positive integer `q`, `q ^ 30 + 2` is not a practical number. -/
theorem not_practical_pow30_add_two (q : ℕ) (hq : 0 < q) : ¬ IsPractical (q ^ 30 + 2) := by
  by_cases h2 : 2 ∣ q
  · have hq2 : 2 ≤ q := Nat.le_of_dvd hq h2
    have hn13 : 13 ≤ q ^ 30 + 2 := by
      have hpow : 2 ^ 30 ≤ q ^ 30 := Nat.pow_le_pow_left hq2 30
      omega
    exact even_obstructed_not_practical hn13
      (not_dvd_four_of_even q h2) (not_dvd_nine q) (not_dvd_five q)
      (not_dvd_seven q) (not_dvd_eleven q) (not_dvd_thirteen q)
  · have hodd : ¬ 2 ∣ q ^ 30 + 2 := by
      intro hdvd
      have hdvd' : 2 ∣ q ^ 30 := by
        have := (Nat.dvd_add_left (dvd_refl 2)).mp hdvd
        exact this
      exact h2 (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd')
    have hn3 : 3 ≤ q ^ 30 + 2 := by
      have hpow : 1 ≤ q ^ 30 := Nat.one_le_pow 30 q hq
      omega
    exact odd_pow30_add_two_not_practical hn3 hodd

/-- **Theorem 2:** For every natural number `C` divisible by `30` and every positive integer `q`,
`q ^ C + 2` is not a practical number. -/
theorem not_practical_pow_mul30_add_two (C q : ℕ) (hC : 30 ∣ C) (hq : 0 < q) :
    ¬ IsPractical (q ^ C + 2) := by
  rcases hC with ⟨t, rfl⟩
  cases t with
  | zero =>
    simp only [mul_zero, pow_zero]
    exact odd_pow30_add_two_not_practical (by omega) (by decide)
  | succ t =>
    rw [mul_comm, pow_mul]
    exact not_practical_pow30_add_two (q ^ (t + 1)) (Nat.pow_pos hq)

/-- For every `C` divisible by `30`, there are NO practical numbers `q` such that `q^C` and
`q^C + 2` are both practical. -/
theorem li_conjecture_1_1_empty_of_dvd_thirty (C : ℕ) (hC : 30 ∣ C) :
    {q : ℕ | IsPractical q ∧ IsPractical (q ^ C) ∧ IsPractical (q ^ C + 2)} = ∅ := by
  ext q
  constructor
  · rintro ⟨hq, _, hq2⟩
    exact not_practical_pow_mul30_add_two C q hC hq.1 hq2
  · intro h
    exact False.elim h

/-- **Main Disproof (Refutation of Runbo Li Conjecture 1.1, NNTDM 32(3), 2026):**
It is false that for every positive integer `C`, there are infinitely many practical numbers `q`
with both `q ^ C` and `q ^ C + 2` practical. -/
theorem li_conjecture_1_1_false :
    ¬ ∀ C : ℕ, 0 < C →
      Set.Infinite {q : ℕ | IsPractical q ∧ IsPractical (q ^ C) ∧ IsPractical (q ^ C + 2)} := by
  intro h
  have h30 := h 30 (by decide)
  rw [li_conjecture_1_1_empty_of_dvd_thirty 30 (dvd_refl 30)] at h30
  exact h30 Set.finite_empty

/-! ### Exact characterization of the small-divisor obstruction (`30 ∣ C`) -/

/-- **Theorem 3 (Sharpness of `C = 30`):** For every positive integer `C`, the elementary
small-divisor obstruction (`4, 9, 5, 7, 11, 13` never divide `q^C + 2` for even `q`) holds
if and only if `30 ∣ C`. -/
theorem local_obstruction_iff_dvd_thirty (C : ℕ) (hC : 0 < C) :
    (∀ q : ℕ, 2 ∣ q →
      ¬ 4 ∣ q ^ C + 2 ∧ ¬ 9 ∣ q ^ C + 2 ∧ ¬ 5 ∣ q ^ C + 2 ∧
      ¬ 7 ∣ q ^ C + 2 ∧ ¬ 11 ∣ q ^ C + 2 ∧ ¬ 13 ∣ q ^ C + 2) ↔ 30 ∣ C := by
  constructor
  · intro hall
    -- Step 1: 2 ∣ C (using mod 5 on q = 8 or q = 2)
    have h2 : 2 ∣ C := by
      by_contra hodd
      have hmod4 : C % 4 = 1 ∨ C % 4 = 3 := by omega
      rcases hmod4 with h1 | h3
      · have h5 := (hall 8 (by decide)).2.2.1
        apply h5
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 8) (m := 5) (k := 4) (by decide) C, h1]
        decide
      · have h5 := (hall 2 (by decide)).2.2.1
        apply h5
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 2) (m := 5) (k := 4) (by decide) C, h3]
        decide
    -- Step 2: 3 ∣ C (using mod 9 on q = 4 or q = 2)
    have h3 : 3 ∣ C := by
      by_contra hnd3
      have hmod6 : C % 6 = 2 ∨ C % 6 = 4 := by omega
      rcases hmod6 with h2' | h4'
      · have h9 := (hall 4 (by decide)).2.1
        apply h9
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 4) (m := 9) (k := 6) (by decide) C, h2']
        decide
      · have h9 := (hall 2 (by decide)).2.1
        apply h9
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 2) (m := 9) (k := 6) (by decide) C, h4']
        decide
    -- Step 3: 5 ∣ C (using mod 11 on q = 8, 16, 2, 4)
    have h5 : 5 ∣ C := by
      by_contra hnd5
      have hmod10 : C % 10 = 2 ∨ C % 10 = 4 ∨ C % 10 = 6 ∨ C % 10 = 8 := by omega
      rcases hmod10 with h2' | h4' | h6' | h8'
      · have h11 := (hall 8 (by decide)).2.2.2.2.1
        apply h11
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 8) (m := 11) (k := 10) (by norm_num) C, h2']
        norm_num
      · have h11 := (hall 16 (by decide)).2.2.2.2.1
        apply h11
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 16) (m := 11) (k := 10) (by norm_num) C, h4']
        norm_num
      · have h11 := (hall 2 (by decide)).2.2.2.2.1
        apply h11
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 2) (m := 11) (k := 10) (by norm_num) C, h6']
        norm_num
      · have h11 := (hall 4 (by decide)).2.2.2.2.1
        apply h11
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
          pow_mod_periodic (q := 4) (m := 11) (k := 10) (by norm_num) C, h8']
        norm_num
    omega
  · rintro ⟨t, rfl⟩ q hq
    have ht : 0 < t := by omega
    have hqt : 2 ∣ q ^ t := dvd_pow hq (by omega)
    rw [mul_comm, pow_mul]
    exact ⟨not_dvd_four_of_even (q ^ t) hqt, not_dvd_nine (q ^ t), not_dvd_five (q ^ t),
      not_dvd_seven (q ^ t), not_dvd_eleven (q ^ t), not_dvd_thirteen (q ^ t)⟩

/-! ### Positive contrast: explicit practical triples `(q, q^C, q^C + 2)` for `C ∈ {1, 2, 3, 4, 5, 6}` -/

/-- Decidable greedy subset-sum check over a descending list of divisors. -/
private def greedyRep : List ℕ → ℕ → Option (List ℕ)
  | _, 0 => some []
  | [], _ + 1 => none
  | d :: ds, m =>
    if d ≤ m then
      match greedyRep ds (m - d) with
      | some xs => some (d :: xs)
      | none => greedyRep ds m
    else
      greedyRep ds m

private lemma greedyRep_sound :
    ∀ (ds : List ℕ) (m : ℕ) (xs : List ℕ),
      greedyRep ds m = some xs → xs.Sublist ds ∧ xs.sum = m
  | [], 0, xs, h => by
    simp only [greedyRep, Option.some.injEq] at h
    subst h; exact ⟨List.Sublist.slnil, rfl⟩
  | [], _ + 1, _, h => by simp [greedyRep] at h
  | d :: ds, 0, xs, h => by
    simp only [greedyRep, Option.some.injEq] at h
    subst h; exact ⟨List.nil_sublist _, rfl⟩
  | d :: ds, m + 1, xs, h => by
    dsimp only [greedyRep] at h
    split_ifs at h with hle
    · cases hrec : greedyRep ds (m + 1 - d) with
      | some ys =>
        rw [hrec] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hsub, hsum⟩ := greedyRep_sound ds (m + 1 - d) ys hrec
        exact ⟨List.Sublist.cons_cons d hsub, by simp only [List.sum_cons]; omega⟩
      | none =>
        rw [hrec] at h
        obtain ⟨hsub, hsum⟩ := greedyRep_sound ds (m + 1) xs h
        exact ⟨List.Sublist.cons d hsub, hsum⟩
    · obtain ⟨hsub, hsum⟩ := greedyRep_sound ds (m + 1) xs h
      exact ⟨List.Sublist.cons d hsub, hsum⟩

private def checkGreedyAll (ds : List ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => (greedyRep ds (k + 1)).isSome && checkGreedyAll ds k

private lemma checkGreedyAll_spec (ds : List ℕ) :
    ∀ (N : ℕ), checkGreedyAll ds N = true →
      ∀ m, 1 ≤ m → m ≤ N → ∃ xs : List ℕ, xs.Sublist ds ∧ xs.sum = m
  | 0, _, m, h1, h2 => by omega
  | N + 1, h, m, h1, h2 => by
    simp only [checkGreedyAll, Bool.and_eq_true] at h
    by_cases hm : m = N + 1
    · subst hm
      cases hg : greedyRep ds (N + 1) with
      | none => rw [hg] at h; simp at h
      | some xs => exact ⟨xs, greedyRep_sound ds (N + 1) xs hg⟩
    · exact checkGreedyAll_spec ds N h.2 m h1 (by omega)

private lemma isPractical_of_greedy (n : ℕ) (hn : 0 < n) (ds : List ℕ)
    (hnodup : ds.Nodup) (hdiv : ∀ d ∈ ds, d ∣ n)
    (hcheck : checkGreedyAll ds n = true) : IsPractical n := by
  refine ⟨hn, fun m h1 h2 => ?_⟩
  obtain ⟨xs, hsub, hsum⟩ := checkGreedyAll_spec ds n hcheck m h1 h2
  have hxsnodup : xs.Nodup := hnodup.sublist hsub
  refine ⟨xs.toFinset, ?_, ?_⟩
  · intro d hd
    rw [List.mem_toFinset] at hd
    exact Nat.mem_divisors.mpr ⟨hdiv d (hsub.subset hd), by omega⟩
  · rw [List.sum_toFinset _ hxsnodup]
    simpa using hsum

/-- Multiplicative closure: if `a` is practical, `1 < k ≤ a`, and `gcd(a, k) = 1`, then
`a * k` is practical. -/
private lemma isPractical_mul_coprime {a k : ℕ} (ha : IsPractical a) (hk1 : 1 < k) (hka : k ≤ a)
    (hcop : Nat.Coprime a k) : IsPractical (a * k) := by
  refine ⟨Nat.mul_pos ha.1 (by omega), fun m hm1 hmak => ?_⟩
  set q := m / k
  set r := m % k
  have hqr : k * q + r = m := Nat.div_add_mod m k
  have hqa : q ≤ a := Nat.div_le_of_le_mul (by linarith)
  have hra : r ≤ a := by
    have := Nat.mod_lt m (by omega : 0 < k)
    omega
  have hexQ : ∃ S₁ ⊆ a.divisors, S₁.sum id = q := by
    by_cases hq0 : q = 0
    · exact ⟨∅, Finset.empty_subset _, by simp [hq0]⟩
    · exact ha.2 q (Nat.pos_of_ne_zero hq0) hqa
  have hexR : ∃ S₂ ⊆ a.divisors, S₂.sum id = r := by
    by_cases hr0 : r = 0
    · exact ⟨∅, Finset.empty_subset _, by simp [hr0]⟩
    · exact ha.2 r (Nat.pos_of_ne_zero hr0) hra
  obtain ⟨S₁, hS₁sub, hS₁sum⟩ := hexQ
  obtain ⟨S₂, hS₂sub, hS₂sum⟩ := hexR
  let T₁ := S₁.image (k * ·)
  have hdisj : Disjoint T₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [Finset.mem_image] at hx₁
    rcases hx₁ with ⟨d₁, _, rfl⟩
    have hd₂ : k * d₁ ∣ a := Nat.dvd_of_mem_divisors (hS₂sub hx₂)
    have hka' : k ∣ a := dvd_trans (dvd_mul_right k d₁) hd₂
    have hk1' : k ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hka' (dvd_refl k)
    have := Nat.le_of_dvd (by omega) hk1'
    omega
  refine ⟨T₁ ∪ S₂, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx₁ | hx₂
    · rw [Finset.mem_image] at hx₁
      rcases hx₁ with ⟨d₁, hd₁, rfl⟩
      have hd1div : d₁ ∣ a := Nat.dvd_of_mem_divisors (hS₁sub hd₁)
      exact Nat.mem_divisors.mpr ⟨by rw [mul_comm a k]; exact mul_dvd_mul_left k hd1div,
        Nat.ne_of_gt (Nat.mul_pos ha.1 (by omega))⟩
    · have hd2div : x ∣ a := Nat.dvd_of_mem_divisors (hS₂sub hx₂)
      exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_left hd2div k,
        Nat.ne_of_gt (Nat.mul_pos ha.1 (by omega))⟩
  · rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ hxy => mul_left_cancel₀ (by omega) hxy)]
    have hmulsum : S₁.sum (fun x => id (k * x)) = k * S₁.sum id := by
      rw [Finset.mul_sum]; rfl
    rw [hmulsum, hS₁sum, hS₂sum, hqr]

/-- Doubling preserves practicality: if `a` is practical, then `2 * a` is practical. -/
private lemma isPractical_two_mul {a : ℕ} (ha : IsPractical a) : IsPractical (2 * a) := by
  refine ⟨by have := ha.1; omega, fun m hm1 hm2a => ?_⟩
  by_cases hma : m ≤ a
  · obtain ⟨S, hSsub, hSsum⟩ := ha.2 m hm1 hma
    refine ⟨S, fun d hd => ?_, hSsum⟩
    exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right (Nat.dvd_of_mem_divisors (hSsub hd)) 2,
      by have := ha.1; omega⟩
  · by_cases hm2 : m = 2 * a
    · subst hm2
      exact ⟨{2 * a}, by simp [Nat.mem_divisors, ha.1.ne'], by simp⟩
    · -- Write m = (m - a) + a? Instead represent m - 2^0? Simpler: m > a so 1 ≤ m - a < a;
      -- actually split parity of m: if m = 2*k, use image (2 * ·); if m = 2*k + 1, use insert 1 (image (2 * ·))!
      by_cases hev : m % 2 = 0
      · have hk1 : 1 ≤ m / 2 := by omega
        have hka : m / 2 ≤ a := by omega
        obtain ⟨S, hSsub, hSsum⟩ := ha.2 (m / 2) hk1 hka
        refine ⟨S.image (2 * ·), ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_image] at hx
          rcases hx with ⟨d, hd, rfl⟩
          exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_left 2 (Nat.dvd_of_mem_divisors (hSsub hd)),
            by have := ha.1; omega⟩
        · have h2s : S.sum (fun x => id (2 * x)) = 2 * S.sum id := by
            rw [Finset.mul_sum]; rfl
          rw [Finset.sum_image (fun x _ y _ hxy => by omega), h2s, hSsum]
          omega
      · have hk1 : 1 ≤ m / 2 := by omega
        have hka : m / 2 ≤ a := by omega
        obtain ⟨S, hSsub, hSsum⟩ := ha.2 (m / 2) hk1 hka
        have hnot1 : (1 : ℕ) ∉ S.image (2 * ·) := by
          intro h1
          rw [Finset.mem_image] at h1
          rcases h1 with ⟨d, _, hd⟩
          omega
        refine ⟨insert 1 (S.image (2 * ·)), ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx'
          · exact Nat.mem_divisors.mpr ⟨one_dvd _, by have := ha.1; omega⟩
          · rw [Finset.mem_image] at hx'
            rcases hx' with ⟨d, hd, rfl⟩
            exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_left 2 (Nat.dvd_of_mem_divisors (hSsub hd)),
              by have := ha.1; omega⟩
        · have h2s : S.sum (fun x => id (2 * x)) = 2 * S.sum id := by
            rw [Finset.mul_sum]; rfl
          rw [Finset.sum_insert hnot1, Finset.sum_image (fun x _ y _ hxy => by omega), h2s, hSsum]
          dsimp only [id]
          omega

private lemma isPractical_pow_two : ∀ k : ℕ, IsPractical (2 ^ k)
  | 0 => ⟨by decide, fun m h1 h2 => ⟨{1}, by simp, by simp; omega⟩⟩
  | k + 1 => by
    rw [pow_succ']
    exact isPractical_two_mul (isPractical_pow_two k)

private lemma isPractical_6 : IsPractical 6 :=
  isPractical_of_greedy 6 (by decide) [6, 3, 2, 1] (by decide) (by decide) (by decide)

private lemma isPractical_18 : IsPractical 18 :=
  isPractical_of_greedy 18 (by decide) [18, 9, 6, 3, 2, 1] (by decide) (by decide) (by decide)

private lemma isPractical_54 : IsPractical 54 :=
  isPractical_of_greedy 54 (by decide) [54, 27, 18, 9, 6, 3, 2, 1] (by decide) (by decide) (by decide)

private lemma isPractical_66 : IsPractical 66 :=
  isPractical_of_greedy 66 (by decide) [66, 33, 22, 11, 6, 3, 2, 1] (by decide) (by decide) (by decide)

private lemma isPractical_1026 : IsPractical 1026 := by
  have h : (1026 : ℕ) = 54 * 19 := by norm_num
  rw [h]
  exact isPractical_mul_coprime isPractical_54 (by decide) (by decide) (by decide)

/-- **Theorem 4 (Positive witnesses for small exponents):** For each `C ∈ {1, 2, 3, 4, 5, 6}`,
there exists an explicit practical number `q` such that `q^C` and `q^C + 2` are both practical. -/
theorem small_exponents_witnesses :
    (IsPractical 2 ∧ IsPractical (2 ^ 1) ∧ IsPractical (2 ^ 1 + 2)) ∧
    (IsPractical 2 ∧ IsPractical (2 ^ 2) ∧ IsPractical (2 ^ 2 + 2)) ∧
    (IsPractical 4 ∧ IsPractical (4 ^ 3) ∧ IsPractical (4 ^ 3 + 2)) ∧
    (IsPractical 2 ∧ IsPractical (2 ^ 4) ∧ IsPractical (2 ^ 4 + 2)) ∧
    (IsPractical 4 ∧ IsPractical (4 ^ 5) ∧ IsPractical (4 ^ 5 + 2)) ∧
    (IsPractical 2 ∧ IsPractical (2 ^ 6) ∧ IsPractical (2 ^ 6 + 2)) := by
  refine ⟨⟨isPractical_pow_two 1, isPractical_pow_two 1, isPractical_pow_two 2⟩,
    ⟨isPractical_pow_two 1, isPractical_pow_two 2, isPractical_6⟩,
    ⟨isPractical_pow_two 2, isPractical_pow_two 6, isPractical_66⟩,
    ⟨isPractical_pow_two 1, isPractical_pow_two 4, isPractical_18⟩,
    ⟨isPractical_pow_two 2, isPractical_pow_two 10, isPractical_1026⟩,
    ⟨isPractical_pow_two 1, isPractical_pow_two 6, isPractical_66⟩⟩

end LiTwinPractical
