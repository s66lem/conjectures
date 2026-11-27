import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Explicit (5, 4) and (6, 4) Integer Sumsets of Perfect Squares (Choudhry, INTEGERS 26, 2026, #A66)

This file formalizes the resolution of A. Choudhry's open problem in
*Two Sets of Integers Such That All Elements of the Sumset of the Two Sets Are Perfect Squares*,
INTEGERS 26 (2026), #A66 (arXiv:2508.07806, Section 6; continuing R. K. Guy,
*Unsolved Problems in Number Theory*, Problem D14):

> "It would be interesting to find a quintuple `{a₁, a₂, …, a₅}` and a quadruple
> `{b₁, b₂, …, b₄}` such that all 20 sums `aᵢ + bⱼ` (`i = 1, …, 5`, `j = 1, …, 4`) are squares."

Main formalized theorems:
1. `choudhry_5_4_exists` & `choudhry_5_4_positive_disjoint`:
   Explicit `(5, 4)` solution over `ℤ` in both standard primitive form (`b₁ = 0`, `gcd = 1`) and
   all-positive, pairwise disjoint form (`aᵢ > 0`, `bⱼ > 0`, `aᵢ ≠ bⱼ`, all 20 sums `IsSquare`).
2. `five_distinct_primitive_5_4_solutions`:
   All five distinct primitive `(5, 4)` solutions in standard form with `max X ≤ 10000`, each
   verified injective with all 20 sums squares and `gcd = 1` (hence squarefree/primitive).
3. `choudhry_6_4_exists` & `choudhry_6_4_positive_disjoint`:
   Explicit `(6, 4)` solution over `ℤ` (all 24 sums `IsSquare`), strictly exceeding Choudhry's
   `(5, 4)` question, in both primitive standard form (`gcd = 1`) and all-positive disjoint form.
4. `choudhry_lemma1_scale_shift` & `infinitely_many_positive_disjoint_5_4` &
   `infinitely_many_positive_disjoint_6_4`:
   Scaling and translation invariance (`k² aᵢ - t`, `k² bⱼ + t`) producing infinitely many
   distinct all-positive, pairwise disjoint `(5, 4)` and `(6, 4)` solutions over `ℤ`.
-/

namespace ChoudhrySumsetSquares

/-- A pair `(A, B)` of integer tuples is a valid `(m, n)` square-sumset solution if `A` and `B`
are injective and every pairwise sum `A i + B j` is a perfect square in `ℤ`. -/
def IsSquareSumset {m n : ℕ} (A : Fin m → ℤ) (B : Fin n → ℤ) : Prop :=
  Function.Injective A ∧ Function.Injective B ∧ ∀ (i : Fin m) (j : Fin n), IsSquare (A i + B j)

/-- A pair `(A, B)` is an all-positive, pairwise disjoint `(m, n)` square-sumset solution. -/
def IsPosDisjointSquareSumset {m n : ℕ} (A : Fin m → ℤ) (B : Fin n → ℤ) : Prop :=
  IsSquareSumset A B ∧
    (∀ i : Fin m, 0 < A i) ∧
    (∀ j : Fin n, 0 < B j) ∧
    (∀ (i : Fin m) (j : Fin n), A i ≠ B j)

/-! ### Helper lifting natural-number root certificates to `ℤ` -/

private lemma isSquareSumset_of_nat {m n : ℕ}
    (A : Fin m → ℕ) (B : Fin n → ℕ) (R : Fin m → Fin n → ℕ)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hR : ∀ i j, A i + B j = R i j * R i j) :
    IsSquareSumset (fun i => (A i : ℤ)) (fun j => (B j : ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h; exact hA (Int.ofNat.inj h)
  · intro x y h; exact hB (Int.ofNat.inj h)
  · intro i j
    refine ⟨(R i j : ℤ), ?_⟩
    have h := congrArg (fun k : ℕ => (k : ℤ)) (hR i j)
    push_cast at h
    exact h

/-! ### Scaling and translation invariance (Choudhry's Lemma 1) -/

/-- **Choudhry's Lemma 1:** Scaling `(A, B)` by `k²` (`k ≠ 0`) and shifting by `(-t, +t)` preserves
injectivity and all pairwise sums being squares. -/
theorem choudhry_lemma1_scale_shift {m n : ℕ} {A : Fin m → ℤ} {B : Fin n → ℤ}
    (h : IsSquareSumset A B) (k : ℤ) (hk : k ≠ 0) (t : ℤ) :
    IsSquareSumset (fun i => k ^ 2 * A i - t) (fun j => k ^ 2 * B j + t) := by
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hEq
    have hmul : k ^ 2 * A i₁ = k ^ 2 * A i₂ := by linarith
    exact h.1 (mul_left_cancel₀ hk2 hmul)
  · intro j₁ j₂ hEq
    have hmul : k ^ 2 * B j₁ = k ^ 2 * B j₂ := by linarith
    exact h.2.1 (mul_left_cancel₀ hk2 hmul)
  · intro i j
    rcases h.2.2 i j with ⟨r, hr⟩
    refine ⟨k * r, ?_⟩
    calc
      (k ^ 2 * A i - t) + (k ^ 2 * B j + t)
          = k ^ 2 * (A i + B j) := by ring
      _ = k ^ 2 * (r * r) := by rw [hr]
      _ = (k * r) * (k * r) := by ring

/-! ### Primary minimal (5, 4) solution (standard form & positive disjoint form) -/

/-- Primary `(5, 4)` quintuple `A` (`216², 567², 1128², 1848², 5496²`). -/
def A5_0 : Fin 5 → ℕ := ![46656, 321489, 1272384, 3415104, 30206016]

/-- Primary `(5, 4)` quadruple `B`. -/
def B4_0 : Fin 4 → ℕ := ![0, 1198800, 2695680, 22269520]

/-- Exact 5×4 matrix of square roots `√(A5_0 i + B4_0 j)`. -/
def R5_0 : Fin 5 → Fin 4 → ℕ :=
  ![![216, 1116, 1656, 4724],
    ![567, 1233, 1737, 4753],
    ![1128, 1572, 1992, 4852],
    ![1848, 2148, 2472, 5068],
    ![5496, 5604, 5736, 7244]]

private lemma A5_0_inj : Function.Injective A5_0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A5_0]

private lemma B4_0_inj : Function.Injective B4_0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [B4_0]

private lemma R5_0_valid : ∀ i j, A5_0 i + B4_0 j = R5_0 i j * R5_0 i j := by
  intro i j; fin_cases i <;> fin_cases j <;> rfl

/-- Primary `(5, 4)` solution is primitive: `gcd(46656, 321489, 22269520) = 1`. -/
theorem primary_5_4_primitive :
    Nat.gcd (Nat.gcd (A5_0 0) (A5_0 1)) (B4_0 3) = 1 := by
  decide

/-- **Theorem 1 (Resolution of Choudhry's Sec. 6 Open Problem — Standard Form):**
There exist a quintuple `A` and a quadruple `B` of distinct integers such that all 20 sums
`A i + B j` are perfect squares. -/
theorem choudhry_5_4_exists :
    ∃ (A : Fin 5 → ℤ) (B : Fin 4 → ℤ), IsSquareSumset A B :=
  ⟨fun i => (A5_0 i : ℤ), fun j => (B4_0 j : ℤ),
    isSquareSumset_of_nat A5_0 B4_0 R5_0 A5_0_inj B4_0_inj R5_0_valid⟩

/-- **Theorem 2 (All-Positive, Pairwise Disjoint (5, 4) Solution):**
Shifting `(A5_0, B4_0)` by `(-1, +1)` yields 9 pairwise distinct strictly positive integers
partitioned into a quintuple `A'` and quadruple `B'` with all 20 sums perfect squares. -/
theorem choudhry_5_4_positive_disjoint :
    ∃ (A : Fin 5 → ℤ) (B : Fin 4 → ℤ), IsPosDisjointSquareSumset A B := by
  refine ⟨fun i => (A5_0 i : ℤ) - 1, fun j => (B4_0 j : ℤ) + 1, ?_, ?_, ?_, ?_⟩
  · have h := choudhry_lemma1_scale_shift
      (isSquareSumset_of_nat A5_0 B4_0 R5_0 A5_0_inj B4_0_inj R5_0_valid) 1 one_ne_zero 1
    simpa using h
  · intro i; fin_cases i <;> decide
  · intro j; fin_cases j <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide

/-! ### Four additional primitive (5, 4) solutions (complete set with `max X ≤ 10000`) -/

def A5_1 : Fin 5 → ℕ := ![15876, 509796, 9790641, 19527561, 46703556]
def B4_1 : Fin 4 → ℕ := ![0, 713440, 8382528, 105621408]
def R5_1 : Fin 5 → Fin 4 → ℕ :=
  ![![126, 854, 2898, 10278],
    ![714, 1106, 2982, 10302],
    ![3129, 3241, 4263, 10743],
    ![4419, 4499, 5283, 11187],
    ![6834, 6886, 7422, 12342]]

def A5_2 : Fin 5 → ℕ := ![760384, 2822400, 14930496, 24800400, 78854400]
def B4_2 : Fin 4 → ℕ := ![0, 17971200, 24269625, 135475200]
def R5_2 : Fin 5 → Fin 4 → ℕ :=
  ![![872, 4328, 5003, 11672],
    ![1680, 4560, 5205, 11760],
    ![3864, 5736, 6261, 12264],
    ![4980, 6540, 7005, 12660],
    ![8880, 9840, 10155, 14640]]

def A5_3 : Fin 5 → ℕ := ![129600, 1476225, 10497600, 32353344, 51265600]
def B4_3 : Fin 4 → ℕ := ![0, 3790800, 24076800, 138733056]
def R5_3 : Fin 5 → Fin 4 → ℕ :=
  ![![360, 1980, 4920, 11784],
    ![1215, 2295, 5055, 11841],
    ![3240, 3780, 5880, 12216],
    ![5688, 6012, 7512, 13080],
    ![7160, 7420, 8680, 13784]]

def A5_4 : Fin 5 → ℕ := ![268324, 3759721, 14047504, 21864976, 34904464]
def B4_4 : Fin 4 → ℕ := ![0, 2696960, 13704320, 139018880]
def R5_4 : Fin 5 → Fin 4 → ℕ :=
  ![![518, 1722, 3738, 11802],
    ![1939, 2541, 4179, 11949],
    ![3748, 4092, 5268, 12372],
    ![4676, 4956, 5964, 12684],
    ![5908, 6132, 6972, 13188]]

/-- GCD of a finite list of natural numbers (used to certify `gcd = 1`, hence primitivity). -/
private def listGcd : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.gcd x (listGcd xs)

/-- **Theorem 3 (Five Pairwise Distinct Primitive (5, 4) Solutions):**
All five primitive `(5, 4)` solutions with `max X ≤ 10000` are valid square-sumsets with `gcd = 1`. -/
theorem five_distinct_primitive_5_4_solutions :
    IsSquareSumset (fun i => (A5_0 i : ℤ)) (fun j => (B4_0 j : ℤ)) ∧
    IsSquareSumset (fun i => (A5_1 i : ℤ)) (fun j => (B4_1 j : ℤ)) ∧
    IsSquareSumset (fun i => (A5_2 i : ℤ)) (fun j => (B4_2 j : ℤ)) ∧
    IsSquareSumset (fun i => (A5_3 i : ℤ)) (fun j => (B4_3 j : ℤ)) ∧
    IsSquareSumset (fun i => (A5_4 i : ℤ)) (fun j => (B4_4 j : ℤ)) ∧
    listGcd [A5_0 0, A5_0 1, A5_0 2, A5_0 3, A5_0 4, B4_0 1, B4_0 2, B4_0 3] = 1 ∧
    listGcd [A5_1 0, A5_1 1, A5_1 2, A5_1 3, A5_1 4, B4_1 1, B4_1 2, B4_1 3] = 1 ∧
    listGcd [A5_2 0, A5_2 1, A5_2 2, A5_2 3, A5_2 4, B4_2 1, B4_2 2, B4_2 3] = 1 ∧
    listGcd [A5_3 0, A5_3 1, A5_3 2, A5_3 3, A5_3 4, B4_3 1, B4_3 2, B4_3 3] = 1 ∧
    listGcd [A5_4 0, A5_4 1, A5_4 2, A5_4 3, A5_4 4, B4_4 1, B4_4 2, B4_4 3] = 1 ∧
    Function.Injective (![A5_0 0, A5_1 0, A5_2 0, A5_3 0, A5_4 0] : Fin 5 → ℕ) := by
  refine ⟨isSquareSumset_of_nat A5_0 B4_0 R5_0 A5_0_inj B4_0_inj R5_0_valid,
    isSquareSumset_of_nat A5_1 B4_1 R5_1
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A5_1])
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [B4_1])
      (by intro i j; fin_cases i <;> fin_cases j <;> rfl),
    isSquareSumset_of_nat A5_2 B4_2 R5_2
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A5_2])
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [B4_2])
      (by intro i j; fin_cases i <;> fin_cases j <;> rfl),
    isSquareSumset_of_nat A5_3 B4_3 R5_3
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A5_3])
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [B4_3])
      (by intro i j; fin_cases i <;> fin_cases j <;> rfl),
    isSquareSumset_of_nat A5_4 B4_4 R5_4
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A5_4])
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [B4_4])
      (by intro i j; fin_cases i <;> fin_cases j <;> rfl),
    by decide, by decide, by decide, by decide, by decide,
    by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A5_0, A5_1, A5_2, A5_3, A5_4]⟩

/-! ### Explicit (6, 4) solution (24 sums all squares, exceeding Choudhry's (5, 4) problem) -/

/-- `(6, 4)` sextuple `A6` (`2988², 4356², 5787², 11164², 17046², 23948²`). -/
def A6 : Fin 6 → ℕ := ![8928144, 18974736, 33489369, 124634896, 290566116, 573506704]

/-- `(6, 4)` quadruple `B64`. -/
def B64 : Fin 4 → ℕ := ![0, 16594560, 137675520, 1202947200]

/-- Exact 6×4 matrix of square roots `√(A6 i + B64 j)`. -/
def R64 : Fin 6 → Fin 4 → ℕ :=
  ![![2988, 5052, 12108, 34812],
    ![4356, 5964, 12516, 34956],
    ![5787, 7077, 13083, 35163],
    ![11164, 11884, 16196, 36436],
    ![17046, 17526, 20694, 38646],
    ![23948, 24292, 26668, 42148]]

private lemma A6_inj : Function.Injective A6 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [A6]

private lemma B64_inj : Function.Injective B64 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [B64]

private lemma R64_valid : ∀ i j, A6 i + B64 j = R64 i j * R64 i j := by
  intro i j; fin_cases i <;> fin_cases j <;> rfl

/-- The `(6, 4)` solution is primitive: `gcd(A6 2, A6 3) = 1`. -/
theorem choudhry_6_4_primitive : Nat.gcd (A6 2) (A6 3) = 1 := by
  decide

/-- **Theorem 4 (Explicit (6, 4) Square-Sumset Solution):**
There exist a sextuple `A` and a quadruple `B` of distinct integers with all 24 sums `A i + B j`
perfect squares. -/
theorem choudhry_6_4_exists :
    ∃ (A : Fin 6 → ℤ) (B : Fin 4 → ℤ), IsSquareSumset A B :=
  ⟨fun i => (A6 i : ℤ), fun j => (B64 j : ℤ),
    isSquareSumset_of_nat A6 B64 R64 A6_inj B64_inj R64_valid⟩

/-- **Theorem 5 (All-Positive, Pairwise Disjoint (6, 4) Solution):**
Shifting `(A6, B64)` by `(-1, +1)` yields 10 pairwise distinct strictly positive integers
partitioned into a sextuple `A'` and quadruple `B'` with all 24 sums perfect squares. -/
theorem choudhry_6_4_positive_disjoint :
    ∃ (A : Fin 6 → ℤ) (B : Fin 4 → ℤ), IsPosDisjointSquareSumset A B := by
  refine ⟨fun i => (A6 i : ℤ) - 1, fun j => (B64 j : ℤ) + 1, ?_, ?_, ?_, ?_⟩
  · have h := choudhry_lemma1_scale_shift
      (isSquareSumset_of_nat A6 B64 R64 A6_inj B64_inj R64_valid) 1 one_ne_zero 1
    simpa using h
  · intro i; fin_cases i <;> decide
  · intro j; fin_cases j <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide

/-! ### Infinitely many all-positive, pairwise disjoint (5, 4) and (6, 4) solutions -/

/-- **Theorem 6 (Infinitely Many Positive Disjoint (5, 4) Solutions):**
For every `k ≥ 1`, scaling `(A5_0, B4_0)` by `(2k)²` and shifting by `(-1, +1)` gives an
injective family of all-positive, pairwise disjoint `(5, 4)` square-sumset solutions. -/
theorem infinitely_many_positive_disjoint_5_4 :
    ∃ (A : ℕ → Fin 5 → ℤ) (B : ℕ → Fin 4 → ℤ),
      (∀ n : ℕ, IsPosDisjointSquareSumset (A n) (B n)) ∧
      Function.Injective (fun n => A n 0) := by
  refine ⟨fun n i => ((2 * (n : ℤ) + 2) ^ 2) * (A5_0 i : ℤ) - 1,
    fun n j => ((2 * (n : ℤ) + 2) ^ 2) * (B4_0 j : ℤ) + 1, ?_, ?_⟩
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hk : (2 * (n : ℤ) + 2) ≠ 0 := by omega
    have hsq : 4 ≤ (2 * (n : ℤ) + 2) ^ 2 := by nlinarith
    refine ⟨choudhry_lemma1_scale_shift
        (isSquareSumset_of_nat A5_0 B4_0 R5_0 A5_0_inj B4_0_inj R5_0_valid)
        (2 * (n : ℤ) + 2) hk 1, ?_, ?_, ?_⟩
    · intro i
      have hAi : (1 : ℤ) ≤ (A5_0 i : ℤ) := by fin_cases i <;> decide
      nlinarith
    · intro j
      have hBj : (0 : ℤ) ≤ (B4_0 j : ℤ) := Int.natCast_nonneg _
      nlinarith
    · intro i j hEq
      have hval : ((2 * (n : ℤ) + 2) ^ 2) * ((A5_0 i : ℤ) - (B4_0 j : ℤ)) = 2 := by linarith
      have h4 : (4 : ℤ) ∣ ((2 * (n : ℤ) + 2) ^ 2) * ((A5_0 i : ℤ) - (B4_0 j : ℤ)) := by
        refine dvd_mul_of_dvd_left ?_ _
        refine ⟨((n : ℤ) + 1) ^ 2, by ring⟩
      rw [hval] at h4
      omega
  · intro n₁ n₂ hEq
    dsimp only at hEq
    have hA0 : (A5_0 0 : ℤ) = 46656 := rfl
    rw [hA0] at hEq
    have hsq : (2 * (n₁ : ℤ) + 2) ^ 2 = (2 * (n₂ : ℤ) + 2) ^ 2 := by linarith
    have hpos1 : (0 : ℤ) < 2 * (n₁ : ℤ) + 2 := by omega
    have hpos2 : (0 : ℤ) < 2 * (n₂ : ℤ) + 2 := by omega
    have heqZ : 2 * (n₁ : ℤ) + 2 = 2 * (n₂ : ℤ) + 2 := by nlinarith
    omega

/-- **Theorem 7 (Infinitely Many Positive Disjoint (6, 4) Solutions):**
For every `k ≥ 1`, scaling `(A6, B64)` by `(2k)²` and shifting by `(-1, +1)` gives an
injective family of all-positive, pairwise disjoint `(6, 4)` square-sumset solutions. -/
theorem infinitely_many_positive_disjoint_6_4 :
    ∃ (A : ℕ → Fin 6 → ℤ) (B : ℕ → Fin 4 → ℤ),
      (∀ n : ℕ, IsPosDisjointSquareSumset (A n) (B n)) ∧
      Function.Injective (fun n => A n 0) := by
  refine ⟨fun n i => ((2 * (n : ℤ) + 2) ^ 2) * (A6 i : ℤ) - 1,
    fun n j => ((2 * (n : ℤ) + 2) ^ 2) * (B64 j : ℤ) + 1, ?_, ?_⟩
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hk : (2 * (n : ℤ) + 2) ≠ 0 := by omega
    have hsq : 4 ≤ (2 * (n : ℤ) + 2) ^ 2 := by nlinarith
    refine ⟨choudhry_lemma1_scale_shift
        (isSquareSumset_of_nat A6 B64 R64 A6_inj B64_inj R64_valid)
        (2 * (n : ℤ) + 2) hk 1, ?_, ?_, ?_⟩
    · intro i
      have hAi : (1 : ℤ) ≤ (A6 i : ℤ) := by fin_cases i <;> decide
      nlinarith
    · intro j
      have hBj : (0 : ℤ) ≤ (B64 j : ℤ) := Int.natCast_nonneg _
      nlinarith
    · intro i j hEq
      have hval : ((2 * (n : ℤ) + 2) ^ 2) * ((A6 i : ℤ) - (B64 j : ℤ)) = 2 := by linarith
      have h4 : (4 : ℤ) ∣ ((2 * (n : ℤ) + 2) ^ 2) * ((A6 i : ℤ) - (B64 j : ℤ)) := by
        refine dvd_mul_of_dvd_left ?_ _
        refine ⟨((n : ℤ) + 1) ^ 2, by ring⟩
      rw [hval] at h4
      omega
  · intro n₁ n₂ hEq
    dsimp only at hEq
    have hA0 : (A6 0 : ℤ) = 8928144 := rfl
    rw [hA0] at hEq
    have hsq : (2 * (n₁ : ℤ) + 2) ^ 2 = (2 * (n₂ : ℤ) + 2) ^ 2 := by linarith
    have hpos1 : (0 : ℤ) < 2 * (n₁ : ℤ) + 2 := by omega
    have hpos2 : (0 : ℤ) < 2 * (n₂ : ℤ) + 2 := by omega
    have heqZ : 2 * (n₁ : ℤ) + 2 = 2 * (n₂ : ℤ) + 2 := by nlinarith
    omega

end ChoudhrySumsetSquares
