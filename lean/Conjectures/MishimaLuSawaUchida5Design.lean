import Mathlib

/-!
# Odd-Size Antipodal Rational 5-Designs for the Chebyshev Measure
(Mishima, Lu, Sawa, Uchida, arXiv:2503.21151v4 / Res. Number Theory 12 (2026), No. 39, Problem 8.3)

This file resolves **Problem 8.3** and completes the classification of odd-size antipodal rational
5-designs for the Chebyshev measure `(1 - t^2)^(-1/2) dt / π` on `(-1, 1)`:

> **Problem 8.3.** *Find an antipodal $5$-design with $37$ rational points, as the smallest open case.*

An `n`-point antipodal rational 5-design for the Chebyshev measure is a finite set `X : Finset ℚ`
of cardinality `n` contained in `(-1, 1)` such that `-X = X` and for every `k ∈ {0, 1, 2, 3, 4, 5}`:
`∑ x ∈ X, x ^ k = n * chebMoment k`, where `chebMoment` takes values `1, 0, 1/2, 0, 3/8, 0`.

We prove from first principles:
1. **Resolution of Problem 8.3 (`mishima_problem_8_3_37_design`):** An explicit 37-point antipodal
   rational 5-design with denominator `240` exists.
2. **Existence for every odd `n = 2N + 1 ≥ 35` (`exists_odd_5design_of_ge_17`):** Using explicit
   base designs for `N = 17, 18, 19` and disjoint 6-point rational blocks `Y_t = {±a_t, ±b_t, ±c_t}`
   whose positive values lie in three pairwise disjoint intervals `(0, 2/14)`, `(11/14, 12/14)`,
   `(12/14, 13/14)` and are each strictly monotone for `t ≥ 20`.
3. **Self-contained 2-adic non-existence for all `N ≤ 16` (`not_exists_odd_5design_of_le_16`):**
   Reproves Theorem 8.1 of Mishima–Lu–Sawa–Uchida from scratch via 2-adic valuation analysis.
4. **Complete odd-size spectrum (`mishima_odd_5design_iff`):** For every `N : ℕ`, an antipodal
   rational 5-design of size `2 * N + 1` exists if and only if `17 ≤ N` (equivalently `35 ≤ 2*N+1`).
-/

namespace MishimaLuSawaUchida5Design

/-- Moments `∫_{-1}^1 t^k (1 - t^2)^(-1/2) dt / π` for `k = 0, 1, 2, 3, 4, 5`. -/
def chebMoment : Fin 6 → ℚ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1 / 2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 3 / 8
  | ⟨5, _⟩ => 0

/-- An `n`-point antipodal rational 5-design for the Chebyshev measure on `(-1, 1)`. -/
def IsAntipodalRat5Design (X : Finset ℚ) (n : ℕ) : Prop :=
  X.card = n ∧
  (∀ x ∈ X, -1 < x ∧ x < 1) ∧
  (∀ x ∈ X, -x ∈ X) ∧
  (∀ k : Fin 6, ∑ x ∈ X, x ^ k.val = (n : ℚ) * chebMoment k)

/-- Build the `(2 * S.card + 1)`-point antipodal set `{0} ∪ S ∪ (-S)` from a positive set `S`. -/
def mkOddDesign (S : Finset ℚ) : Finset ℚ :=
  insert (0 : ℚ) (S ∪ S.image Neg.neg)

private lemma mkOddDesign_spec (S : Finset ℚ)
    (hpos : ∀ x ∈ S, 0 < x ∧ x < 1)
    (h2 : ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4)
    (h4 : ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16) :
    IsAntipodalRat5Design (mkOddDesign S) (2 * S.card + 1) := by
  have h0S : (0 : ℚ) ∉ S := fun h => lt_irrefl 0 (hpos 0 h).1
  have h0neg : (0 : ℚ) ∉ S.image Neg.neg := by
    rw [Finset.mem_image]
    rintro ⟨x, hx, hneg⟩
    have := (hpos x hx).1
    linarith
  have hdisj : Disjoint S (S.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro x hx hmem
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨y, hy, rfl⟩
    have hx0 := (hpos (-y) hx).1
    have hy0 := (hpos y hy).1
    linarith
  have h0U : (0 : ℚ) ∉ S ∪ S.image Neg.neg := by
    simp [Finset.mem_union, h0S, h0neg]
  have hneg_card : (S.image Neg.neg).card = S.card :=
    Finset.card_image_of_injective S neg_injective
  have hcard : (mkOddDesign S).card = 2 * S.card + 1 := by
    unfold mkOddDesign
    rw [Finset.card_insert_of_notMem h0U, Finset.card_union_of_disjoint hdisj, hneg_card]
    omega
  refine ⟨hcard, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mkOddDesign, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with rfl | hx | ⟨y, hy, rfl⟩
    · constructor <;> norm_num
    · have := hpos x hx; constructor <;> linarith
    · have := hpos y hy; constructor <;> linarith
  · intro x hx
    simp only [mkOddDesign, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx ⊢
    rcases hx with rfl | hx | ⟨y, hy, rfl⟩
    · left; ring
    · right; right; exact ⟨x, hx, rfl⟩
    · right; left; simpa using hy
  · intro k
    have hsum_neg : ∀ m : ℕ, ∑ x ∈ S.image Neg.neg, x ^ m = (-1 : ℚ) ^ m * ∑ x ∈ S, x ^ m := by
      intro m
      rw [Finset.sum_image (fun a _ b _ h => neg_injective h), Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [neg_eq_neg_one_mul, mul_pow]
    have hsum_all : ∀ m : ℕ, 1 ≤ m →
        ∑ x ∈ mkOddDesign S, x ^ m = (1 + (-1 : ℚ) ^ m) * ∑ x ∈ S, x ^ m := by
      intro m hm
      unfold mkOddDesign
      rw [Finset.sum_insert h0U, Finset.sum_union hdisj, zero_pow (by omega), zero_add, hsum_neg]
      ring
    fin_cases k
    · -- k = 0
      simp only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hcard, chebMoment]
    · -- k = 1
      change ∑ x ∈ mkOddDesign S, x ^ 1 = _
      rw [hsum_all 1 (by omega)]
      simp only [chebMoment]; ring
    · -- k = 2
      change ∑ x ∈ mkOddDesign S, x ^ 2 = _
      rw [hsum_all 2 (by omega), h2]
      simp only [chebMoment]; push_cast; ring
    · -- k = 3
      change ∑ x ∈ mkOddDesign S, x ^ 3 = _
      rw [hsum_all 3 (by omega)]
      simp only [chebMoment]; ring
    · -- k = 4
      change ∑ x ∈ mkOddDesign S, x ^ 4 = _
      rw [hsum_all 4 (by omega), h4]
      simp only [chebMoment]; push_cast; ring
    · -- k = 5
      change ∑ x ∈ mkOddDesign S, x ^ 5 = _
      rw [hsum_all 5 (by omega)]
      simp only [chebMoment]; ring

/-! ### 1. Explicit Base Designs for `N = 17, 18, 19` (including Problem 8.3: `n = 37`) -/

/-- Linear-time Boolean check that a list of natural numbers is strictly increasing. -/
private def isStrictlyInc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && isStrictlyInc (b :: t)

private lemma pairwise_lt_of_isStrictlyInc : ∀ l : List ℕ, isStrictlyInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
      simp only [isStrictlyInc, Bool.and_eq_true, decide_eq_true_eq] at h
      have htail : (b :: t).Pairwise (· < ·) := pairwise_lt_of_isStrictlyInc (b :: t) h.2
      refine List.Pairwise.cons ?_ htail
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact h.1
      · exact lt_trans h.1 ((List.pairwise_cons.mp htail).1 x hxt)

private lemma nodup_of_isStrictlyInc {l : List ℕ} (h : isStrictlyInc l = true) : l.Nodup :=
  (pairwise_lt_of_isStrictlyInc l h).imp (fun hlt => ne_of_lt hlt)

private lemma list_sum_div_pow (D : ℚ) (k : ℕ) (xs : List ℕ) :
    (xs.map (fun a : ℕ => ((a : ℚ) / D) ^ k)).sum =
      ((xs.map (fun a : ℕ => (a ^ k : ℕ))).sum : ℚ) / D ^ k := by
  induction xs with
  | nil => simp
  | cons a tl ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        Nat.cast_add, Nat.cast_pow, div_pow, add_div, ih]

/-- Helper: verify an explicit strictly increasing integer numerator list `nums` with denominator `D`
yields a valid odd-size antipodal rational 5-design of size `2 * nums.length + 1`. -/
private def checkBase (D : ℕ) (nums : List ℕ) : Bool :=
  0 < D &&
  isStrictlyInc nums &&
  nums.all (fun a => 0 < a && a < D) &&
  (4 * (nums.map (fun a => a ^ 2)).sum == (2 * nums.length + 1) * D ^ 2) &&
  (16 * (nums.map (fun a => a ^ 4)).sum == 3 * (2 * nums.length + 1) * D ^ 4)

private lemma design_of_checkBase (D : ℕ) (nums : List ℕ)
    (hchk : checkBase D nums = true) :
    let S : Finset ℚ := (nums.map (fun a : ℕ => (a : ℚ) / (D : ℚ))).toFinset
    S.card = nums.length ∧
    (∀ x ∈ S, 0 < x ∧ x < 1) ∧
    ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
    ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16 := by
  simp only [checkBase, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hD, hinc⟩, hbounds⟩, hsum2⟩, hsum4⟩
  have hnodup : nums.Nodup := nodup_of_isStrictlyInc hinc
  have hD_pos : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr hD
  have hD_ne : (D : ℚ) ≠ 0 := hD_pos.ne'
  have hinj : Function.Injective (fun a : ℕ => (a : ℚ) / (D : ℚ)) := by
    intro a b hab
    have hq : (a : ℚ) = (b : ℚ) := by
      have := congrArg (· * (D : ℚ)) hab
      simpa [div_mul_cancel₀ _ hD_ne] using this
    exact Nat.cast_injective hq
  have hnodup_map : (nums.map (fun a : ℕ => (a : ℚ) / (D : ℚ))).Nodup :=
    hnodup.map hinj
  set L : List ℚ := nums.map (fun a : ℕ => (a : ℚ) / (D : ℚ))
  set S : Finset ℚ := L.toFinset
  have hcard : S.card = nums.length := by
    rw [List.toFinset_card_of_nodup hnodup_map, List.length_map]
  refine ⟨hcard, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    rcases hx with ⟨a, ha, rfl⟩
    have hb := hbounds a ha
    have ha0 : (0 : ℚ) < (a : ℚ) := Nat.cast_pos.mpr hb.1
    have haD : (a : ℚ) < (D : ℚ) := Nat.cast_lt.mpr hb.2
    exact ⟨div_pos ha0 hD_pos, (div_lt_one hD_pos).mpr haD⟩
  · have hsum_list : ∑ x ∈ S, x ^ 2 = (L.map (fun x => x ^ 2)).sum := by
      rw [List.sum_toFinset _ hnodup_map]
    rw [hsum_list, hcard]
    have hpow2 : (L.map (fun x => x ^ 2)).sum =
        ((nums.map (fun a : ℕ => (a ^ 2 : ℕ))).sum : ℚ) / (D : ℚ) ^ 2 := by
      dsimp [L]
      rw [List.map_map]
      exact list_sum_div_pow (D : ℚ) 2 nums
    rw [hpow2]
    have hq2 : (4 : ℚ) * ((nums.map (fun a : ℕ => (a ^ 2 : ℕ))).sum : ℚ) =
        (2 * (nums.length : ℚ) + 1) * (D : ℚ) ^ 2 := by
      exact_mod_cast hsum2
    field_simp [hD_ne]
    linarith
  · have hsum_list : ∑ x ∈ S, x ^ 4 = (L.map (fun x => x ^ 4)).sum := by
      rw [List.sum_toFinset _ hnodup_map]
    rw [hsum_list, hcard]
    have hpow4 : (L.map (fun x => x ^ 4)).sum =
        ((nums.map (fun a : ℕ => (a ^ 4 : ℕ))).sum : ℚ) / (D : ℚ) ^ 4 := by
      dsimp [L]
      rw [List.map_map]
      exact list_sum_div_pow (D : ℚ) 4 nums
    rw [hpow4]
    have hq4 : (16 : ℚ) * ((nums.map (fun a : ℕ => (a ^ 4 : ℕ))).sum : ℚ) =
        3 * (2 * (nums.length : ℚ) + 1) * (D : ℚ) ^ 4 := by
      exact_mod_cast hsum4
    field_simp [hD_ne]
    linarith

/-- Base design for `N = 17` (`n = 35`, denominator `1092`). -/
def base17Nums : List ℕ :=
  [55, 87, 171, 305, 533, 575, 733, 753, 765, 881, 905, 966, 981, 985, 1083, 1085, 1089]

/-- Base design for `N = 18` (`n = 37`, denominator `240`) — resolves **Problem 8.3**. -/
def base18Nums : List ℕ :=
  [15, 57, 61, 69, 93, 129, 141, 147, 151, 183, 199, 209, 211, 215, 234, 235, 238, 239]

/-- Base design for `N = 19` (`n = 39`, denominator `420`). -/
def base19Nums : List ℕ :=
  [47, 93, 108, 113, 129, 153, 161, 305, 309, 343, 353, 357, 365, 366, 369, 395, 405, 408, 413]

private lemma checkBase17 : checkBase 1092 base17Nums = true := by decide
private lemma checkBase18 : checkBase 240 base18Nums = true := by decide
private lemma checkBase19 : checkBase 420 base19Nums = true := by decide

/-- **Resolution of Mishima–Lu–Sawa–Uchida Problem 8.3 (arXiv:2503.21151v4):**
There exists a 37-point antipodal rational 5-design for the Chebyshev measure
(explicitly given over denominator 240 by `base18Nums`). -/
theorem mishima_problem_8_3_37_design :
    ∃ X : Finset ℚ, IsAntipodalRat5Design X 37 := by
  have h := design_of_checkBase 240 base18Nums checkBase18
  set S : Finset ℚ := (base18Nums.map (fun a : ℕ => (a : ℚ) / (240 : ℚ))).toFinset
  have hlen : base18Nums.length = 18 := rfl
  have hS : S.card = 18 := h.1.trans hlen
  refine ⟨mkOddDesign S, ?_⟩
  have hd := mkOddDesign_spec S h.2.1 h.2.2.1 h.2.2.2
  rwa [hS] at hd

/-! ### 2. Disjoint 6-Point Rational Blocks `Y_t` and Existence for Every `N ≥ 17` -/

/-- Three positive rational points of the 6-point block at parameter `t : ℕ` (`t ≥ 20`):
- `blockA t = (2t² - 22t - 13) / (14(t² + t + 1)) ∈ (0, 2/14)`, strictly increasing;
- `blockC t = (11t² + 26t + 2) / (14(t² + t + 1)) ∈ (11/14, 12/14)`, strictly decreasing;
- `blockB t = (13t² + 4t - 11) / (14(t² + t + 1)) ∈ (12/14, 13/14)`, strictly increasing. -/
def blockDen (t : ℕ) : ℚ := 14 * ((t : ℚ) ^ 2 + (t : ℚ) + 1)
def blockA (t : ℕ) : ℚ := (2 * (t : ℚ) ^ 2 - 22 * (t : ℚ) - 13) / blockDen t
def blockB (t : ℕ) : ℚ := (13 * (t : ℚ) ^ 2 + 4 * (t : ℚ) - 11) / blockDen t
def blockC (t : ℕ) : ℚ := (11 * (t : ℚ) ^ 2 + 26 * (t : ℚ) + 2) / blockDen t

private lemma blockDen_pos (t : ℕ) : 0 < blockDen t := by
  unfold blockDen; positivity

private lemma block_moments (t : ℕ) :
    (blockA t) ^ 2 + (blockB t) ^ 2 + (blockC t) ^ 2 = 3 / 2 ∧
    (blockA t) ^ 4 + (blockB t) ^ 4 + (blockC t) ^ 4 = 9 / 8 := by
  have hd : blockDen t ≠ 0 := (blockDen_pos t).ne'
  unfold blockDen at hd
  unfold blockA blockB blockC blockDen
  constructor <;> field_simp [hd] <;> ring

private lemma block_intervals (t : ℕ) (ht : 20 ≤ t) :
    0 < blockA t ∧ blockA t < 2 / 14 ∧
    11 / 14 < blockC t ∧ blockC t < 12 / 14 ∧
    12 / 14 < blockB t ∧ blockB t < 13 / 14 := by
  have htq : (20 : ℚ) ≤ (t : ℚ) := Nat.cast_le.mpr ht
  have hd : 0 < blockDen t := blockDen_pos t
  unfold blockDen at hd
  unfold blockA blockB blockC blockDen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (by nlinarith) hd
  · rw [div_lt_div_iff₀ hd (by norm_num : (0 : ℚ) < 14)]; nlinarith
  · rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 14) hd]; nlinarith
  · rw [div_lt_div_iff₀ hd (by norm_num : (0 : ℚ) < 14)]; nlinarith
  · rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 14) hd]; nlinarith
  · rw [div_lt_div_iff₀ hd (by norm_num : (0 : ℚ) < 14)]; nlinarith

private lemma blockA_strictMono {t₁ t₂ : ℕ} (h1 : 20 ≤ t₁) (hlt : t₁ < t₂) :
    blockA t₁ < blockA t₂ := by
  have h1q : (20 : ℚ) ≤ (t₁ : ℚ) := Nat.cast_le.mpr h1
  have hltq : (t₁ : ℚ) < (t₂ : ℚ) := Nat.cast_lt.mpr hlt
  have hd1 := blockDen_pos t₁
  have hd2 := blockDen_pos t₂
  unfold blockDen at hd1 hd2
  unfold blockA blockDen
  rw [div_lt_div_iff₀ hd1 hd2]
  have hdiff :
      (2 * (t₂ : ℚ) ^ 2 - 22 * t₂ - 13) * (14 * (t₁ ^ 2 + t₁ + 1)) -
      (2 * (t₁ : ℚ) ^ 2 - 22 * t₁ - 13) * (14 * (t₂ ^ 2 + t₂ + 1)) =
      14 * ((t₂ : ℚ) - t₁) * (24 * t₁ * t₂ + 15 * (t₁ + t₂) - 9) := by ring
  have hf1 : 0 < (t₂ : ℚ) - t₁ := by linarith
  have hf2 : 0 < 24 * (t₁ : ℚ) * t₂ + 15 * (t₁ + t₂) - 9 := by nlinarith
  have hpos : 0 < 14 * ((t₂ : ℚ) - t₁) * (24 * t₁ * t₂ + 15 * (t₁ + t₂) - 9) :=
    mul_pos (mul_pos (by norm_num) hf1) hf2
  linarith

private lemma blockB_strictMono {t₁ t₂ : ℕ} (h1 : 20 ≤ t₁) (hlt : t₁ < t₂) :
    blockB t₁ < blockB t₂ := by
  have h1q : (20 : ℚ) ≤ (t₁ : ℚ) := Nat.cast_le.mpr h1
  have hltq : (t₁ : ℚ) < (t₂ : ℚ) := Nat.cast_lt.mpr hlt
  have hd1 := blockDen_pos t₁
  have hd2 := blockDen_pos t₂
  unfold blockDen at hd1 hd2
  unfold blockB blockDen
  rw [div_lt_div_iff₀ hd1 hd2]
  have hdiff :
      (13 * (t₂ : ℚ) ^ 2 + 4 * t₂ - 11) * (14 * (t₁ ^ 2 + t₁ + 1)) -
      (13 * (t₁ : ℚ) ^ 2 + 4 * t₁ - 11) * (14 * (t₂ ^ 2 + t₂ + 1)) =
      14 * ((t₂ : ℚ) - t₁) * (9 * t₁ * t₂ + 24 * (t₁ + t₂) + 15) := by ring
  have hf1 : 0 < (t₂ : ℚ) - t₁ := by linarith
  have hf2 : 0 < 9 * (t₁ : ℚ) * t₂ + 24 * (t₁ + t₂) + 15 := by nlinarith
  have hpos : 0 < 14 * ((t₂ : ℚ) - t₁) * (9 * t₁ * t₂ + 24 * (t₁ + t₂) + 15) :=
    mul_pos (mul_pos (by norm_num) hf1) hf2
  linarith

private lemma blockC_strictAnti {t₁ t₂ : ℕ} (h1 : 20 ≤ t₁) (hlt : t₁ < t₂) :
    blockC t₂ < blockC t₁ := by
  have h1q : (20 : ℚ) ≤ (t₁ : ℚ) := Nat.cast_le.mpr h1
  have hltq : (t₁ : ℚ) < (t₂ : ℚ) := Nat.cast_lt.mpr hlt
  have hd1 := blockDen_pos t₁
  have hd2 := blockDen_pos t₂
  unfold blockDen at hd1 hd2
  unfold blockC blockDen
  rw [div_lt_div_iff₀ hd2 hd1]
  have hdiff :
      (11 * (t₁ : ℚ) ^ 2 + 26 * t₁ + 2) * (14 * (t₂ ^ 2 + t₂ + 1)) -
      (11 * (t₂ : ℚ) ^ 2 + 26 * t₂ + 2) * (14 * (t₁ ^ 2 + t₁ + 1)) =
      14 * ((t₂ : ℚ) - t₁) * (15 * t₁ * t₂ - 9 * (t₁ + t₂) - 24) := by ring
  have hf1 : 0 < (t₂ : ℚ) - t₁ := by linarith
  have hf2 : 0 < 15 * (t₁ : ℚ) * t₂ - 9 * (t₁ + t₂) - 24 := by nlinarith
  have hpos : 0 < 14 * ((t₂ : ℚ) - t₁) * (15 * t₁ * t₂ - 9 * (t₁ + t₂) - 24) :=
    mul_pos (mul_pos (by norm_num) hf1) hf2
  linarith

/-- For any finite set `F : Finset ℚ`, there exists `t ≥ 20` whose 3-point positive block
`{blockA t, blockB t, blockC t}` is disjoint from `F`. -/
private lemma exists_fresh_block (F : Finset ℚ) :
    ∃ t : ℕ, 20 ≤ t ∧ blockA t ∉ F ∧ blockB t ∉ F ∧ blockC t ∉ F := by
  set W : Finset ℕ := Finset.Ico 20 (20 + 3 * F.card + 1)
  set BA := W.filter (fun t => blockA t ∈ F)
  set BB := W.filter (fun t => blockB t ∈ F)
  set BC := W.filter (fun t => blockC t ∈ F)
  have hBA : BA.card ≤ F.card := by
    refine Finset.card_le_card_of_injOn blockA
      (fun t ht => (Finset.mem_filter.mp ht).2) ?_
    intro t₁ h₁ t₂ h₂ heq
    have ht1 : 20 ≤ t₁ := (Finset.mem_Ico.mp (Finset.mem_filter.mp h₁).1).1
    have ht2 : 20 ≤ t₂ := (Finset.mem_Ico.mp (Finset.mem_filter.mp h₂).1).1
    rcases lt_trichotomy t₁ t₂ with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (blockA_strictMono ht1 hlt))
    · rfl
    · exact absurd heq.symm (ne_of_lt (blockA_strictMono ht2 hgt))
  have hBB : BB.card ≤ F.card := by
    refine Finset.card_le_card_of_injOn blockB
      (fun t ht => (Finset.mem_filter.mp ht).2) ?_
    intro t₁ h₁ t₂ h₂ heq
    have ht1 : 20 ≤ t₁ := (Finset.mem_Ico.mp (Finset.mem_filter.mp h₁).1).1
    have ht2 : 20 ≤ t₂ := (Finset.mem_Ico.mp (Finset.mem_filter.mp h₂).1).1
    rcases lt_trichotomy t₁ t₂ with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (blockB_strictMono ht1 hlt))
    · rfl
    · exact absurd heq.symm (ne_of_lt (blockB_strictMono ht2 hgt))
  have hBC : BC.card ≤ F.card := by
    refine Finset.card_le_card_of_injOn blockC
      (fun t ht => (Finset.mem_filter.mp ht).2) ?_
    intro t₁ h₁ t₂ h₂ heq
    have ht1 : 20 ≤ t₁ := (Finset.mem_Ico.mp (Finset.mem_filter.mp h₁).1).1
    have ht2 : 20 ≤ t₂ := (Finset.mem_Ico.mp (Finset.mem_filter.mp h₂).1).1
    rcases lt_trichotomy t₁ t₂ with hlt | rfl | hgt
    · exact absurd heq (ne_of_gt (blockC_strictAnti ht1 hlt))
    · rfl
    · exact absurd heq.symm (ne_of_gt (blockC_strictAnti ht2 hgt))
  have hunion : (BA ∪ BB ∪ BC).card < W.card := by
    have h1 : (BA ∪ BB ∪ BC).card ≤ (BA ∪ BB).card + BC.card := Finset.card_union_le _ _
    have h2 : (BA ∪ BB).card ≤ BA.card + BB.card := Finset.card_union_le _ _
    have hW : W.card = 3 * F.card + 1 := by simp [W]; omega
    omega
  have hne : (W \ (BA ∪ BB ∪ BC)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : W ⊆ BA ∪ BB ∪ BC := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle := Finset.card_le_card hsub
    omega
  rcases hne with ⟨t, ht⟩
  rw [Finset.mem_sdiff] at ht
  refine ⟨t, (Finset.mem_Ico.mp ht.1).1, ?_, ?_, ?_⟩
  · intro h; exact ht.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨ht.1, h⟩)))
  · intro h; exact ht.2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨ht.1, h⟩)))
  · intro h; exact ht.2 (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨ht.1, h⟩))

/-- Extending any positive `N`-element witness by a fresh 3-element block gives an `(N + 3)`-element witness. -/
private lemma extend_by_three (S : Finset ℚ)
    (hpos : ∀ x ∈ S, 0 < x ∧ x < 1)
    (h2 : ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4)
    (h4 : ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16) :
    ∃ S' : Finset ℚ,
      S'.card = S.card + 3 ∧
      (∀ x ∈ S', 0 < x ∧ x < 1) ∧
      ∑ x ∈ S', x ^ 2 = (2 * (S'.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S', x ^ 4 = 3 * (2 * (S'.card : ℚ) + 1) / 16 := by
  rcases exists_fresh_block S with ⟨t, ht, haS, hbS, hcS⟩
  have hint := block_intervals t ht
  have hab : blockA t ≠ blockB t := by linarith
  have hac : blockA t ≠ blockC t := by linarith
  have hbc : blockB t ≠ blockC t := by linarith
  have hmom := block_moments t
  set S' : Finset ℚ := insert (blockA t) (insert (blockB t) (insert (blockC t) S))
  have ha_not : blockA t ∉ insert (blockB t) (insert (blockC t) S) := by
    simp [hab, hac, haS]
  have hb_not : blockB t ∉ insert (blockC t) S := by
    simp [hbc, hbS]
  have hcard : S'.card = S.card + 3 := by
    simp only [S', Finset.card_insert_of_notMem ha_not, Finset.card_insert_of_notMem hb_not,
      Finset.card_insert_of_notMem hcS]
  refine ⟨S', hcard, ?_, ?_, ?_⟩
  · intro x hx
    simp only [S', Finset.mem_insert] at hx
    rcases hx with rfl | rfl | rfl | hxS
    · exact ⟨hint.1, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact hpos x hxS
  · simp only [S', Finset.sum_insert ha_not, Finset.sum_insert hb_not, Finset.sum_insert hcS]
    rw [h2, hcard]
    push_cast
    linarith [hmom.1]
  · simp only [S', Finset.sum_insert ha_not, Finset.sum_insert hb_not, Finset.sum_insert hcS]
    rw [h4, hcard]
    push_cast
    linarith [hmom.2]

private lemma exists_pos_set_add_3k (N₀ : ℕ)
    (hbase : ∃ S : Finset ℚ,
      S.card = N₀ ∧
      (∀ x ∈ S, 0 < x ∧ x < 1) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16) :
    ∀ k : ℕ, ∃ S : Finset ℚ,
      S.card = N₀ + 3 * k ∧
      (∀ x ∈ S, 0 < x ∧ x < 1) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16 := by
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
      rcases ih with ⟨S, hcard, hpos, h2, h4⟩
      rcases extend_by_three S hpos h2 h4 with ⟨S', hcard', hpos', h2', h4'⟩
      refine ⟨S', ?_, hpos', h2', h4'⟩
      omega

/-- **Existence Theorem:** For every `N ≥ 17`, there exists a `(2N + 1)`-point antipodal
rational 5-design for the Chebyshev measure. -/
theorem exists_odd_5design_of_ge_17 (N : ℕ) (hN : 17 ≤ N) :
    ∃ X : Finset ℚ, IsAntipodalRat5Design X (2 * N + 1) := by
  have h17 : ∃ S : Finset ℚ, S.card = 17 ∧ (∀ x ∈ S, 0 < x ∧ x < 1) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16 := by
    have h := design_of_checkBase 1092 base17Nums checkBase17
    exact ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have h18 : ∃ S : Finset ℚ, S.card = 18 ∧ (∀ x ∈ S, 0 < x ∧ x < 1) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16 := by
    have h := design_of_checkBase 240 base18Nums checkBase18
    exact ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have h19 : ∃ S : Finset ℚ, S.card = 19 ∧ (∀ x ∈ S, 0 < x ∧ x < 1) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16 := by
    have h := design_of_checkBase 420 base19Nums checkBase19
    exact ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have hpos_ex : ∃ S : Finset ℚ, S.card = N ∧ (∀ x ∈ S, 0 < x ∧ x < 1) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (S.card : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (S.card : ℚ) + 1) / 16 := by
    have hmod : (N - 17) % 3 = 0 ∨ (N - 17) % 3 = 1 ∨ (N - 17) % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · rcases exists_pos_set_add_3k 17 h17 ((N - 17) / 3) with ⟨S, hc, hp, hs2, hs4⟩
      exact ⟨S, by omega, hp, hs2, hs4⟩
    · rcases exists_pos_set_add_3k 18 h18 ((N - 18) / 3) with ⟨S, hc, hp, hs2, hs4⟩
      exact ⟨S, by omega, hp, hs2, hs4⟩
    · rcases exists_pos_set_add_3k 19 h19 ((N - 19) / 3) with ⟨S, hc, hp, hs2, hs4⟩
      exact ⟨S, by omega, hp, hs2, hs4⟩
  rcases hpos_ex with ⟨S, hcard, hpos, h2, h4⟩
  refine ⟨mkOddDesign S, ?_⟩
  have hd := mkOddDesign_spec S hpos h2 h4
  rwa [hcard] at hd

/-! ### 3. Self-Contained 2-Adic Proof of Non-Existence for `N ≤ 16` (Theorem 8.1) -/

/-- Any `(2N + 1)`-point antipodal rational 5-design splits into `{0} ∪ S ∪ (-S)` with `S.card = N`. -/
private lemma extract_pos_half (X : Finset ℚ) (N : ℕ)
    (hD : IsAntipodalRat5Design X (2 * N + 1)) :
    ∃ S : Finset ℚ,
      S.card = N ∧
      (∀ x ∈ S, 0 < x) ∧
      ∑ x ∈ S, x ^ 2 = (2 * (N : ℚ) + 1) / 4 ∧
      ∑ x ∈ S, x ^ 4 = 3 * (2 * (N : ℚ) + 1) / 16 := by
  rcases hD with ⟨hcard, _, hanti, hmom⟩
  set S : Finset ℚ := X.filter (fun x => 0 < x)
  set Sneg : Finset ℚ := X.filter (fun x => x < 0)
  have hSneg_eq : Sneg = S.image Neg.neg := by
    ext x
    simp only [S, Sneg, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hxX, hxlt⟩
      exact ⟨-x, ⟨hanti x hxX, neg_pos.mpr hxlt⟩, neg_neg x⟩
    · rintro ⟨y, ⟨hyX, hypos⟩, rfl⟩
      exact ⟨hanti y hyX, neg_lt_zero.mpr hypos⟩
  have hSneg_card : Sneg.card = S.card := by
    rw [hSneg_eq, Finset.card_image_of_injective _ neg_injective]
  have hdisj : Disjoint S Sneg := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    linarith
  have h0_mem : (0 : ℚ) ∈ X := by
    by_contra h0
    have hX : X = S ∪ Sneg := by
      ext x
      simp only [S, Sneg, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        rcases lt_trichotomy x 0 with hlt | rfl | hgt
        · exact Or.inr ⟨hx, hlt⟩
        · exact absurd hx h0
        · exact Or.inl ⟨hx, hgt⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have : X.card = 2 * S.card := by
      rw [hX, Finset.card_union_of_disjoint hdisj, hSneg_card]; omega
    omega
  have h0_notU : (0 : ℚ) ∉ S ∪ Sneg := by
    simp [S, Sneg]
  have hX_eq : X = insert (0 : ℚ) (S ∪ Sneg) := by
    ext x
    simp only [S, Sneg, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with hlt | rfl | hgt
      · exact Or.inr (Or.inr ⟨hx, hlt⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hx, hgt⟩)
    · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
      · exact h0_mem
      · exact hx
      · exact hx
  have hScard : S.card = N := by
    have : X.card = 2 * S.card + 1 := by
      rw [hX_eq, Finset.card_insert_of_notMem h0_notU, Finset.card_union_of_disjoint hdisj, hSneg_card]
      omega
    omega
  have hsum_even : ∀ m : ℕ, 1 ≤ m → Even m →
      ∑ x ∈ X, x ^ m = 2 * ∑ x ∈ S, x ^ m := by
    intro m hm hev
    rw [hX_eq, Finset.sum_insert h0_notU, Finset.sum_union hdisj, zero_pow (by omega), zero_add,
      hSneg_eq, Finset.sum_image (fun a _ b _ h => neg_injective h)]
    have hneg : ∀ x : ℚ, (-x) ^ m = x ^ m := fun x => hev.neg_pow x
    simp_rw [hneg]
    ring
  have hm2 := hmom ⟨2, by omega⟩
  have hm4 := hmom ⟨4, by omega⟩
  rw [hsum_even 2 (by omega) ⟨1, rfl⟩] at hm2
  rw [hsum_even 4 (by omega) ⟨2, rfl⟩] at hm4
  simp only [chebMoment] at hm2 hm4
  refine ⟨S, hScard, fun x hx => (Finset.mem_filter.mp hx).2, ?_, ?_⟩
  · push_cast at hm2; linarith
  · push_cast at hm4; linarith

/-- Clear denominators of a finite set of rationals with minimal 2-adic valuation. -/
private lemma common_denom_int (S : Finset ℚ) :
    ∃ (D : ℕ) (y : ℚ → ℤ), 0 < D ∧
      (∀ x ∈ S, (y x : ℚ) = (D : ℚ) * x) ∧
      (Even D → ∃ x ∈ S, ¬ Even (y x)) := by
  -- Start with the product of denominators `D₀ = ∏ x ∈ S, x.den > 0`.
  let D₀ : ℕ := ∏ x ∈ S, x.den
  have hD₀ : 0 < D₀ := Finset.prod_pos fun x _ => x.pos
  have hint₀ : ∀ x ∈ S, ∃ z : ℤ, (z : ℚ) = (D₀ : ℚ) * x := by
    intro x hx
    have hdvd : x.den ∣ D₀ := Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hx
    rcases hdvd with ⟨k, hk⟩
    refine ⟨x.num * (k : ℤ), ?_⟩
    have hx_eq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    have hden_ne : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.pos.ne'
    have hD_eq : (D₀ : ℚ) = (x.den : ℚ) * (k : ℚ) := by exact_mod_cast hk
    conv_rhs => rw [hx_eq, hD_eq]
    field_simp [hden_ne]
    push_cast; ring
  classical
  let y₀ : ℚ → ℤ := fun x => if hx : x ∈ S then (hint₀ x hx).choose else 0
  have hy₀ : ∀ x ∈ S, (y₀ x : ℚ) = (D₀ : ℚ) * x := fun x hx => by
    simp only [y₀, hx, ↓reduceDIte]
    exact (hint₀ x hx).choose_spec
  -- Factor out powers of 2 as long as `D` and every `y x` (`x ∈ S`) are all even.
  have hreduce : ∀ (D : ℕ) (y : ℚ → ℤ), 0 < D → (∀ x ∈ S, (y x : ℚ) = (D : ℚ) * x) →
      ∃ (D' : ℕ) (y' : ℚ → ℤ), 0 < D' ∧
        (∀ x ∈ S, (y' x : ℚ) = (D' : ℚ) * x) ∧
        (Even D' → ∃ x ∈ S, ¬ Even (y' x)) := by
    intro D
    induction D using Nat.strongRecOn with
    | ind D ih =>
      intro y hD hy
      by_cases hcond : Even D ∧ ∀ x ∈ S, Even (y x)
      · rcases hcond with ⟨hDe, hye⟩
        have hD2_lt : D / 2 < D := Nat.div_lt_self hD (by omega)
        have hD2_pos : 0 < D / 2 := by
          rcases hDe with ⟨m, hm⟩; omega
        have hD_eq : (D : ℚ) = 2 * ((D / 2 : ℕ) : ℚ) := by
          rcases hDe with ⟨m, hm⟩
          have : D / 2 = m := by omega
          rw [this, hm]; push_cast; ring
        refine ih (D / 2) hD2_lt (fun x => y x / 2) hD2_pos ?_
        intro x hx
        rcases hye x hx with ⟨c, hc⟩
        have hy_eq : y x / 2 = c := by omega
        have hy_q : ((y x / 2 : ℤ) : ℚ) * 2 = (y x : ℚ) := by
          rw [hy_eq, hc]; push_cast; ring
        have hmul := hy x hx
        rw [hD_eq] at hmul
        linarith
      · refine ⟨D, y, hD, hy, ?_⟩
        intro hDe
        by_contra hall
        push Not at hall
        exact hcond ⟨hDe, hall⟩
  exact hreduce D₀ y₀ hD₀ hy₀

/-- **Non-existence Theorem (self-contained proof of Theorem 8.1 of arXiv:2503.21151v4):**
For every `N ≤ 16`, there is no `(2N + 1)`-point antipodal rational 5-design for the
Chebyshev measure. -/
theorem not_exists_odd_5design_of_le_16 (N : ℕ) (hN : N ≤ 16) :
    ¬ ∃ X : Finset ℚ, IsAntipodalRat5Design X (2 * N + 1) := by
  rintro ⟨X, hDes⟩
  rcases extract_pos_half X N hDes with ⟨S, hScard, _, h2, h4⟩
  rcases common_denom_int S with ⟨D, y, hDpos, hy, hmin⟩
  set M : ℤ := 2 * (N : ℤ) + 1
  -- Integer equations: `4 * ∑ y² = M * D²` and `16 * ∑ y⁴ = 3 * M * D⁴`.
  have hZ2 : 4 * ∑ x ∈ S, (y x) ^ 2 = M * (D : ℤ) ^ 2 := by
    have hq : (4 : ℚ) * ∑ x ∈ S, (y x : ℚ) ^ 2 = (M : ℚ) * (D : ℚ) ^ 2 := by
      have hrew : ∑ x ∈ S, (y x : ℚ) ^ 2 = (D : ℚ) ^ 2 * ∑ x ∈ S, x ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hy x hx, mul_pow]
      rw [hrew, h2]
      dsimp [M]; push_cast; ring
    exact_mod_cast hq
  have hZ4 : 16 * ∑ x ∈ S, (y x) ^ 4 = 3 * M * (D : ℤ) ^ 4 := by
    have hq : (16 : ℚ) * ∑ x ∈ S, (y x : ℚ) ^ 4 = 3 * (M : ℚ) * (D : ℚ) ^ 4 := by
      have hrew : ∑ x ∈ S, (y x : ℚ) ^ 4 = (D : ℚ) ^ 4 * ∑ x ∈ S, x ^ 4 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hy x hx, mul_pow]
      rw [hrew, h4]
      dsimp [M]; push_cast; ring
    exact_mod_cast hq
  -- Case 1: `D` odd (`e = 0`): `4 ∣ M * D²`, impossible since `M` and `D` are odd.
  by_cases hDe : Even D
  · -- `D` is even: write `D = 2 * D₁`.
    rcases hmin hDe with ⟨x₀, hx₀S, hx₀odd⟩
    -- Count odd elements `r = (S.filter (fun x => ¬ Even (y x))).card`.
    classical
    set Sodd : Finset ℚ := S.filter (fun x => ¬ Even (y x))
    set Seven : Finset ℚ := S.filter (fun x => Even (y x))
    have hodd_pos : 1 ≤ Sodd.card :=
      Finset.one_le_card.mpr ⟨x₀, Finset.mem_filter.mpr ⟨hx₀S, hx₀odd⟩⟩
    have hSodd_le : Sodd.card ≤ N := by
      rw [← hScard]; exact Finset.card_filter_le _ _
    -- Mod 16, `y⁴ ≡ 1 (mod 16)` if `y` is odd and `0 (mod 16)` if `y` is even.
    have hy4_mod16 : ∀ z : ℤ, z ^ 4 % 16 = if Even z then 0 else 1 := by
      intro z
      by_cases hz : Even z
      · rcases hz with ⟨k, rfl⟩
        have : (k + k) ^ 4 = 16 * k ^ 4 := by ring
        rw [if_pos ⟨k, rfl⟩, this]; omega
      · have hodd : z % 2 = 1 := by
          by_contra h
          apply hz; exact ⟨z / 2, by omega⟩
        set q := z / 2
        have hze : z = 2 * q + 1 := by omega
        rw [if_neg hz, hze]
        have hexp : (2 * q + 1) ^ 4 = 16 * (q ^ 4 + 2 * q ^ 3 + q ^ 2) + 8 * (q * (q + 1)) + 1 := by ring
        have hpar : 2 ∣ q * (q + 1) := by
          rcases Int.even_or_odd q with ⟨t, ht⟩ | ⟨t, ht⟩
          · exact ⟨t * (q + 1), by rw [ht]; ring⟩
          · exact ⟨q * (t + 1), by rw [ht]; ring⟩
        rcases hpar with ⟨u, hu⟩
        have hexp2 : (2 * q + 1) ^ 4 = 16 * (q ^ 4 + 2 * q ^ 3 + q ^ 2 + u) + 1 := by
          rw [hexp, hu]; ring
        rw [hexp2]; omega
    have hsum4_mod16 : (∑ x ∈ S, (y x) ^ 4) % 16 = (Sodd.card : ℤ) % 16 := by
      have hsplit : ∑ x ∈ S, (y x) ^ 4 =
          (∑ x ∈ Sodd, (y x) ^ 4) + (∑ x ∈ Seven, (y x) ^ 4) := by
        rw [add_comm]
        exact (Finset.sum_filter_add_sum_filter_not S (fun x => Even (y x)) _).symm
      rw [hsplit]
      have h1 : ∀ (T : Finset ℚ) (f : ℚ → ℤ) (c : ℤ),
          (∀ x ∈ T, f x % 16 = c % 16) → (∑ x ∈ T, f x) % 16 = (T.card * c) % 16 := by
        intro T f c hmod
        induction T using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
            have ha' := hmod a (Finset.mem_insert_self a s)
            have hs' := ih (fun x hx => hmod x (Finset.mem_insert_of_mem hx))
            push_cast
            have hmul : ((s.card : ℤ) + 1) * c = c + (s.card : ℤ) * c := by ring
            rw [hmul]
            omega
      have hodd_sum : (∑ x ∈ Sodd, (y x) ^ 4) % 16 = ((Sodd.card : ℤ) * 1) % 16 :=
        h1 Sodd (fun x => (y x) ^ 4) 1 (fun x hx => by
          rw [hy4_mod16, if_neg (Finset.mem_filter.mp hx).2]; rfl)
      have heven_sum : (∑ x ∈ Seven, (y x) ^ 4) % 16 = ((Seven.card : ℤ) * 0) % 16 :=
        h1 Seven (fun x => (y x) ^ 4) 0 (fun x hx => by
          rw [hy4_mod16, if_pos (Finset.mem_filter.mp hx).2]; rfl)
      omega
    rcases hDe with ⟨D₁, hD₁⟩
    by_cases hD₁e : Even D₁
    · -- Case 3 (`e ≥ 2`, so `4 ∣ D`): write `D = 4 * D₂`.
      rcases hD₁e with ⟨D₂, hD₂⟩
      have hD4 : (D : ℤ) = 4 * (D₂ : ℤ) := by omega
      have hsum4_eq : ∑ x ∈ S, (y x) ^ 4 = 48 * M * (D₂ : ℤ) ^ 4 := by
        rw [hD4] at hZ4
        linarith
      have hdiv16 : (Sodd.card : ℤ) % 16 = 0 := by
        have h16 : 48 * M * (D₂ : ℤ) ^ 4 = 16 * (3 * M * (D₂ : ℤ) ^ 4) := by ring
        rw [← hsum4_mod16, hsum4_eq, h16]; omega
      -- Since `1 ≤ Sodd.card ≤ N ≤ 16` and `16 ∣ Sodd.card`, we MUST have `Sodd.card = 16` and `N = 16`!
      have hSodd16 : Sodd.card = 16 := by omega
      have hN16 : N = 16 := by omega
      have hAllOdd : ∀ x ∈ S, ¬ Even (y x) := by
        have heq_set : Sodd = S := Finset.eq_of_subset_of_card_le
          (Finset.filter_subset _ _) (by omega)
        intro x hx
        rw [← heq_set] at hx
        exact (Finset.mem_filter.mp hx).2
      -- Every `y x` is odd, so `(y x)^2 = 1 + 8 * t x` and `(y x)^4 = 1 + 16 * t x + 64 * (t x)^2`.
      have hsq_form : ∀ x ∈ S, ∃ t : ℤ, (y x) ^ 2 = 1 + 8 * t := by
        intro x hx
        have hne := hAllOdd x hx
        have hm2 : y x % 2 = 1 := by
          by_contra h; apply hne; exact ⟨y x / 2, by omega⟩
        set q := y x / 2
        have hye : y x = 2 * q + 1 := by omega
        have hpar : 2 ∣ q * (q + 1) := by
          rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
          · exact ⟨u * (q + 1), by rw [hu]; ring⟩
          · exact ⟨q * (u + 1), by rw [hu]; ring⟩
        rcases hpar with ⟨t, ht⟩
        exact ⟨t, by rw [hye]; linarith [show (2 * q + 1) ^ 2 = 1 + 4 * (q * (q + 1)) by ring]⟩
      let t : ℚ → ℤ := fun x => if hx : x ∈ S then (hsq_form x hx).choose else 0
      have ht_eq : ∀ x ∈ S, (y x) ^ 2 = 1 + 8 * t x := fun x hx => by
        simp only [t, hx, ↓reduceDIte]; exact (hsq_form x hx).choose_spec
      set T1 : ℤ := ∑ x ∈ S, t x
      set T2 : ℤ := ∑ x ∈ S, (t x) ^ 2
      have hsum2_T : ∑ x ∈ S, (y x) ^ 2 = 16 + 8 * T1 := by
        calc ∑ x ∈ S, (y x) ^ 2
            = ∑ x ∈ S, (1 + 8 * t x) := Finset.sum_congr rfl fun x hx => ht_eq x hx
          _ = (∑ _x ∈ S, (1 : ℤ)) + 8 * ∑ x ∈ S, t x := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = 16 + 8 * T1 := by simp [hScard, hN16, T1]
      have hsum4_T : ∑ x ∈ S, (y x) ^ 4 = 16 + 16 * T1 + 64 * T2 := by
        calc ∑ x ∈ S, (y x) ^ 4
            = ∑ x ∈ S, (1 + 16 * t x + 64 * (t x) ^ 2) := Finset.sum_congr rfl fun x hx => by
              have h1 := ht_eq x hx
              calc (y x) ^ 4 = ((y x) ^ 2) ^ 2 := by ring
                _ = (1 + 8 * t x) ^ 2 := by rw [h1]
                _ = 1 + 16 * t x + 64 * (t x) ^ 2 := by ring
          _ = (∑ _x ∈ S, (1 : ℤ)) + 16 * (∑ x ∈ S, t x) + 64 * ∑ x ∈ S, (t x) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = 16 + 16 * T1 + 64 * T2 := by simp [hScard, hN16, T1, T2]
      have hsum2_D2 : 16 + 8 * T1 = 4 * M * (D₂ : ℤ) ^ 2 := by
        rw [hD4, hsum2_T] at hZ2; linarith
      have hsum4_D2 : 16 + 16 * T1 + 64 * T2 = 48 * M * (D₂ : ℤ) ^ 4 := by
        rw [← hsum4_T]; exact hsum4_eq
      -- Subcase `e = 2` (`D₂` odd) vs `e ≥ 3` (`D₂` even).
      by_cases hD₂e : Even D₂
      · -- `e ≥ 3`: `2 ∣ D₂`, so `16 ∣ 16 + 8 * T1` (forces `T1` even) and `256 ∣ 16 + 16*T1 + 64*T2`
        -- (forces `1 + T1 + 4 * T2 ≡ 0 (mod 16)`, so `T1` odd). Contradiction!
        rcases hD₂e with ⟨D₃, hD₃⟩
        have hD2_even : (D₂ : ℤ) = 2 * (D₃ : ℤ) := by omega
        rw [hD2_even] at hsum2_D2 hsum4_D2
        have h16_dvd : (16 : ℤ) ∣ 16 + 8 * T1 := ⟨M * (D₃ : ℤ) ^ 2, by linarith⟩
        have h256_dvd : (256 : ℤ) ∣ 16 + 16 * T1 + 64 * T2 := ⟨3 * M * (D₃ : ℤ) ^ 4, by linarith⟩
        rcases h16_dvd with ⟨a, ha⟩
        rcases h256_dvd with ⟨b, hb⟩
        omega
      · -- `e = 2`: `D₂` is odd, so `4 * M * D₂² ≡ 4 (mod 8)`, contradicting `16 + 8 * T1 ≡ 0 (mod 8)`!
        have hD2_odd : (D₂ : ℤ) % 2 = 1 := by
          by_contra h; apply hD₂e; exact ⟨D₂ / 2, by omega⟩
        set q := (D₂ : ℤ) / 2
        have hD2_eq : (D₂ : ℤ) = 2 * q + 1 := by omega
        have hM_eq : M = 33 := by dsimp [M]; omega
        rw [hD2_eq, hM_eq] at hsum2_D2
        have hexp : 4 * 33 * (2 * q + 1) ^ 2 = 8 * (66 * q ^ 2 + 66 * q + 16) + 4 := by ring
        rw [hexp] at hsum2_D2
        omega
    · -- Case 2 (`e = 1`, `D = 2 * D₁` with `D₁` odd):
      -- `∑ y² = M * D₁²` and `∑ y⁴ = 3 * M * D₁⁴`.
      have hD2 : (D : ℤ) = 2 * (D₁ : ℤ) := by omega
      have hsum2_eq : ∑ x ∈ S, (y x) ^ 2 = M * (D₁ : ℤ) ^ 2 := by
        rw [hD2] at hZ2; linarith
      have hsum4_eq : ∑ x ∈ S, (y x) ^ 4 = 3 * M * (D₁ : ℤ) ^ 4 := by
        rw [hD2] at hZ4; linarith
      -- Mod 8: `D₁² ≡ 1`, `D₁⁴ ≡ 1`, so `r ≡ 3 * M (mod 8)` from `hsum4_mod16`
      -- and `r + 4 * j ≡ M (mod 8)` from `hsum2_eq`, giving `2 * M + 4 * j ≡ 0 (mod 8)`, impossible for odd `M`!
      have hD1_odd : (D₁ : ℤ) % 2 = 1 := by
        by_contra h; apply hD₁e; exact ⟨D₁ / 2, by omega⟩
      have hD1_sq : ((D₁ : ℤ) ^ 2) % 8 = 1 := by
        set q := (D₁ : ℤ) / 2
        have hq : (D₁ : ℤ) = 2 * q + 1 := by omega
        have hpar : 2 ∣ q * (q + 1) := by
          rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
          · exact ⟨u * (q + 1), by rw [hu]; ring⟩
          · exact ⟨q * (u + 1), by rw [hu]; ring⟩
        rcases hpar with ⟨t, ht⟩
        rw [hq]; have : (2 * q + 1) ^ 2 = 8 * t + 1 := by linarith [show (2 * q + 1) ^ 2 = 1 + 4 * (q * (q + 1)) by ring]
        rw [this]; omega
      have hD1_4 : ((D₁ : ℤ) ^ 4) % 8 = 1 := by
        have : (D₁ : ℤ) ^ 4 = ((D₁ : ℤ) ^ 2) * ((D₁ : ℤ) ^ 2) := by ring
        rw [this, Int.mul_emod, hD1_sq]; decide
      have hr_mod8 : (Sodd.card : ℤ) % 8 = (3 * M) % 8 := by
        have h16 := hsum4_mod16
        rw [hsum4_eq] at h16
        have hmod8 : (3 * M * (D₁ : ℤ) ^ 4) % 8 = (3 * M) % 8 := by
          rw [Int.mul_emod, hD1_4, mul_one, Int.emod_emod]
        omega
      -- Evaluate `(∑ x ∈ S, (y x)^2) % 8` via `Sodd` (each `≡ 1 mod 8`), `S2mod4` (`≡ 4 mod 8`), `S0mod4` (`≡ 0 mod 8`).
      have hsq_mod8 : ∀ z : ℤ, (z ^ 2) % 8 = if ¬ Even z then 1 else if z % 4 = 2 then 4 else 0 := by
        intro z
        by_cases hz : Even z
        · rw [if_neg (not_not.mpr hz)]
          rcases hz with ⟨k, rfl⟩
          by_cases hk : k % 2 = 1
          · have h24 : (k + k) % 4 = 2 := by omega
            rw [if_pos h24]
            set q := k / 2
            have hke : k = 2 * q + 1 := by omega
            rw [hke]; have : (2 * q + 1 + (2 * q + 1)) ^ 2 = 8 * (2 * q ^ 2 + 2 * q) + 4 := by ring
            rw [this]; omega
          · have h04 : (k + k) % 4 ≠ 2 := by omega
            rw [if_neg h04]
            set q := k / 2
            have hke : k = 2 * q := by omega
            rw [hke]; have : (2 * q + 2 * q) ^ 2 = 8 * (2 * q ^ 2) := by ring
            rw [this]; omega
        · rw [if_pos hz]
          have hodd : z % 2 = 1 := by by_contra h; apply hz; exact ⟨z / 2, by omega⟩
          set q := z / 2
          have hze : z = 2 * q + 1 := by omega
          have hpar : 2 ∣ q * (q + 1) := by
            rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
            · exact ⟨u * (q + 1), by rw [hu]; ring⟩
            · exact ⟨q * (u + 1), by rw [hu]; ring⟩
          rcases hpar with ⟨t, ht⟩
          rw [hze]; have : (2 * q + 1) ^ 2 = 8 * t + 1 := by linarith [show (2 * q + 1) ^ 2 = 1 + 4 * (q * (q + 1)) by ring]
          rw [this]; omega
      set S2 : Finset ℚ := Seven.filter (fun x => y x % 4 = 2)
      set S0 : Finset ℚ := Seven.filter (fun x => ¬ (y x % 4 = 2))
      have hsum_mod8 : ∀ (T : Finset ℚ) (f : ℚ → ℤ) (c : ℤ),
          (∀ x ∈ T, f x % 8 = c % 8) → (∑ x ∈ T, f x) % 8 = (T.card * c) % 8 := by
        intro T f c hmod
        induction T using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
            have ha' := hmod a (Finset.mem_insert_self a s)
            have hs' := ih (fun x hx => hmod x (Finset.mem_insert_of_mem hx))
            push_cast
            have hmul : ((s.card : ℤ) + 1) * c = c + (s.card : ℤ) * c := by ring
            rw [hmul]; omega
      have hsplit1 : ∑ x ∈ S, (y x) ^ 2 = (∑ x ∈ Sodd, (y x) ^ 2) + (∑ x ∈ Seven, (y x) ^ 2) := by
        rw [add_comm]
        exact (Finset.sum_filter_add_sum_filter_not S (fun x => Even (y x)) _).symm
      have hsplit2 : ∑ x ∈ Seven, (y x) ^ 2 = (∑ x ∈ S2, (y x) ^ 2) + (∑ x ∈ S0, (y x) ^ 2) :=
        (Finset.sum_filter_add_sum_filter_not Seven (fun x => y x % 4 = 2) _).symm
      have hm_odd : (∑ x ∈ Sodd, (y x) ^ 2) % 8 = ((Sodd.card : ℤ) * 1) % 8 :=
        hsum_mod8 Sodd (fun x => (y x) ^ 2) 1 (fun x hx => by
          rw [hsq_mod8, if_pos (Finset.mem_filter.mp hx).2]; rfl)
      have hm_2 : (∑ x ∈ S2, (y x) ^ 2) % 8 = ((S2.card : ℤ) * 4) % 8 :=
        hsum_mod8 S2 (fun x => (y x) ^ 2) 4 (fun x hx => by
          have hmem := Finset.mem_filter.mp hx
          have hev := (Finset.mem_filter.mp hmem.1).2
          rw [hsq_mod8, if_neg (not_not.mpr hev), if_pos hmem.2]; rfl)
      have hm_0 : (∑ x ∈ S0, (y x) ^ 2) % 8 = ((S0.card : ℤ) * 0) % 8 :=
        hsum_mod8 S0 (fun x => (y x) ^ 2) 0 (fun x hx => by
          have hmem := Finset.mem_filter.mp hx
          have hev := (Finset.mem_filter.mp hmem.1).2
          rw [hsq_mod8, if_neg (not_not.mpr hev), if_neg hmem.2]; rfl)
      have hrhs_mod8 : (M * (D₁ : ℤ) ^ 2) % 8 = M % 8 := by
        rw [Int.mul_emod, hD1_sq, mul_one, Int.emod_emod]
      have hcomb : ((Sodd.card : ℤ) + 4 * (S2.card : ℤ)) % 8 = M % 8 := by
        have h1 : (∑ x ∈ S, (y x) ^ 2) % 8 = M % 8 := by rw [hsum2_eq, hrhs_mod8]
        rw [hsplit1, hsplit2] at h1
        omega
      -- `r ≡ 3M (mod 8)` and `r + 4j ≡ M (mod 8)` imply `2M + 4j ≡ 0 (mod 8)`, contradicting `M = 2N + 1`!
      dsimp [M] at hr_mod8 hcomb
      omega
  · -- `e = 0` (`D` odd): `M * D²` is odd, contradicting `4 * ∑ y² = M * D²`.
    have hDodd : (D : ℤ) % 2 = 1 := by
      by_contra h; apply hDe; exact ⟨D / 2, by omega⟩
    have hModd : M % 2 = 1 := by dsimp [M]; omega
    have hprod_odd : (M * (D : ℤ) ^ 2) % 2 = 1 := by
      have hD2 : ((D : ℤ) * (D : ℤ)) % 2 = 1 := by
        rw [Int.mul_emod, hDodd]; decide
      have : M * (D : ℤ) ^ 2 = M * ((D : ℤ) * (D : ℤ)) := by ring
      rw [this, Int.mul_emod, hModd, hD2]; decide
    omega

/-! ### 4. Complete Spectrum of Odd-Size Antipodal Rational 5-Designs -/

/-- **Main Classification Theorem (Mishima–Lu–Sawa–Uchida, arXiv:2503.21151v4, §8):**
For every `N : ℕ`, an antipodal rational 5-design for the Chebyshev measure with `2 * N + 1`
points exists **if and only if** `17 ≤ N` (equivalently, `35 ≤ 2 * N + 1`).
In particular, `N = 18` (`37` points) exists, resolving Problem 8.3. -/
theorem mishima_odd_5design_iff (N : ℕ) :
    (∃ X : Finset ℚ, IsAntipodalRat5Design X (2 * N + 1)) ↔ 17 ≤ N := by
  constructor
  · intro h
    by_contra hlt
    exact not_exists_odd_5design_of_le_16 N (by omega) h
  · exact exists_odd_5design_of_ge_17 N

end MishimaLuSawaUchida5Design
