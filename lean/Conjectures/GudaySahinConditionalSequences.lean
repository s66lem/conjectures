import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Resolution of Güday–Şahin Conditional-Sequence Conjectures (INTEGERS 26, 2026, #A5)

This file formalizes the refutation and exact correction of Conjectures 1 and 2 of
E. Güday and M. Şahin, *Linear Recurrence Relations Satisfied by the General Conditional
Sequences*, INTEGERS 26 (2026), #A5 (pp. 15–18).

For positive integers `r, m` with `m > r`, a general conditional sequence `{q_n}` satisfies
`q_n = ∑_{j=1}^m a_{n mod r, j} q_{n-j}` for `n ≥ m`.

Main formalized results:
1. **Conjecture 2 exact correction and threshold (`m ≤ 5` vs `m ≥ 6`):**
   - `conj2_exact_corrected_formula`: for ALL `m, d : ℕ` with `3 ∣ d`,
     `2 * cardA m d = 2 * cardW m d - cardDistinctRes m d`,
     where `cardDistinctRes m d` counts compositions `(d₁, d₂, d₃) ∈ [0, m]³` of `d` whose
     residues modulo 3 are pairwise distinct.
   - `conj2_holds_le_five`: Conjecture 2 holds for ALL `m ≤ 5` and `3 ∣ d`.
   - `conj2_fails_all_ge_six`: Conjecture 2 fails at `d = 9` for EVERY `m ≥ 6`.
   - `conj2_counterexample_6_9`: at the minimal case `m = 6, d = 9`,
     `cardW 6 9 = 37`, `cardWStar 6 9 = 30`, `cardA 6 9 = 25 ≠ 22 = 37 - 30 / 2`.
2. **Exact `r ≤ 3` vs `r ≥ 4` support characterization:**
   - `paperCond_iff_bijective_of_le_three`: for `r ∈ {1, 2, 3}` and `r ∣ ∑ d_i`, Güday–Şahin's
     residue condition in Conjecture 1 is equivalent to `σ_d(i) = (i - d_i) mod r` being bijective.
   - `nonbijective_family_ge_four`: for EVERY `r ≥ 4`, the tuple `(0, r - 1, 0, 1, 0, ..., 0)`
     has sum `r` and satisfies Conjecture 1's residue condition, yet `σ_d` is not bijective.
3. **Unconditional refutation of Conjecture 1 over `ℝ` (`r = 4, m = 5`):**
   - `guday_sahin_conjecture_1_false_real`: for `r = 4, m = 5`, NO sign assignment
     `s : (Fin 4 → Fin 6) → ℝ` with values in `{-1, 1}` makes the conjectured decimated
     recurrence `q_n = ∑_{k=1}^5 A_{4k} q_{n - 4k}` hold eventually for all real coefficient
     arrays `a` and initial values `init` (under either the `a_{i,0} = 1` or `a_{i,0} = -1`
     convention). Proved via an explicit integer instance whose 5×5 monodromy matrix `M`
     satisfies an exact degree-5 polynomial with `c₁ = 13596 ≡ 0 (mod 3)`, invertible
     decimated companion matrix (`det K = c₅ = 74844 ≠ 0`), nonsingular Krylov matrix
     `det (W 0) ≠ 0`, and a modulo-3 obstruction forcing `A_4 ≡ ±1 (mod 3) ≠ 0`.
-/

namespace GudaySahinConditionalSequences

open scoped BigOperators Matrix

/-! ### Part 1: Conjecture 2 — Exact Corrected Formula, `m ≤ 5` Validity, and `m ≥ 6` Disproof -/

/-- The finite box `[0, m]³` of ordered triples of natural numbers in `{0, …, m}`. -/
def tripleBox (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (m + 1) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))

/-- Predicate for compositions of `d` into 3 parts in `[0, m]`. -/
def isComp3 (d : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 + t.2.1 + t.2.2 = d

/-- Predicate `D` from Güday–Şahin Conjecture 2 (p. 18):
if `d₁ ≡ i (mod 3)`, then `d₂ ≢ i + 1 (mod 3)` and `d₃ ≢ i + 2 (mod 3)`. -/
def inD (t : ℕ × ℕ × ℕ) : Prop :=
  t.2.1 % 3 ≠ (t.1 + 1) % 3 ∧ t.2.2 % 3 ≠ (t.1 + 2) % 3

/-- Pairwise distinct parts (defining `w*_{3,m}(d)`). -/
def distinctParts (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- Pairwise distinct residues modulo 3. -/
def distinctRes (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 % 3 ≠ t.2.1 % 3 ∧ t.1 % 3 ≠ t.2.2 % 3 ∧ t.2.1 % 3 ≠ t.2.2 % 3

/-- All three parts have the same residue modulo 3. -/
def equalRes (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 % 3 = t.2.1 % 3 ∧ t.1 % 3 = t.2.2 % 3

instance (d : ℕ) : DecidablePred (isComp3 d) := fun t => inferInstanceAs (Decidable (t.1 + t.2.1 + t.2.2 = d))
instance : DecidablePred inD := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred distinctParts := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance : DecidablePred distinctRes := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance : DecidablePred equalRes := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `w_{3,m}(d)`: number of ordered partitions of `d` into 3 parts in `[0, m]`. -/
def cardW (m d : ℕ) : ℕ :=
  ((tripleBox m).filter (isComp3 d)).card

/-- `w*_{3,m}(d)`: number of ordered partitions of `d` into 3 pairwise distinct parts in `[0, m]`. -/
def cardWStar (m d : ℕ) : ℕ :=
  ((tripleBox m).filter (fun t => isComp3 d t ∧ distinctParts t)).card

/-- `|𝒜_d|`: number of triples in `[0, m]³` of sum `d` satisfying Conjecture 2's condition `D`. -/
def cardA (m d : ℕ) : ℕ :=
  ((tripleBox m).filter (fun t => isComp3 d t ∧ inD t)).card

/-- Number of ordered partitions of `d` into 3 parts in `[0, m]` with pairwise distinct residues mod 3. -/
def cardDistinctRes (m d : ℕ) : ℕ :=
  ((tripleBox m).filter (fun t => isComp3 d t ∧ distinctRes t)).card

private lemma res3_dichotomy {t : ℕ × ℕ × ℕ} (hsum : (t.1 + t.2.1 + t.2.2) % 3 = 0) :
    equalRes t ∨ distinctRes t := by
  unfold equalRes distinctRes
  omega

private lemma inD_of_equalRes {t : ℕ × ℕ × ℕ} (heq : equalRes t) : inD t := by
  unfold equalRes at heq
  unfold inD
  omega

private lemma swap_inD_iff_not_inD {t : ℕ × ℕ × ℕ} (hdist : distinctRes t) :
    inD (t.1, t.2.2, t.2.1) ↔ ¬ inD t := by
  unfold distinctRes at hdist
  unfold inD
  dsimp only
  omega

/-- **Exact Corrected Formula for Conjecture 2 (all `m, d` with `3 ∣ d`):**
`2 * |𝒜_d| = 2 * w_{3,m}(d) - cardDistinctRes m d`. -/
theorem conj2_exact_corrected_formula (m d : ℕ) (hd : d % 3 = 0) :
    2 * cardA m d = 2 * cardW m d - cardDistinctRes m d := by
  set T := (tripleBox m).filter (isComp3 d)
  set Teq := T.filter equalRes
  set Tdist := T.filter distinctRes
  set TdistIn := Tdist.filter inD
  set TdistOut := Tdist.filter (fun t => ¬ inD t)
  have hdisj : Disjoint Teq Tdist := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    have h1 := (Finset.mem_filter.mp ht1).2
    have h2 := (Finset.mem_filter.mp ht2).2
    exact h2.1 h1.1
  have hunion : T = Teq ∪ Tdist := by
    ext t
    simp only [Teq, Tdist, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ht
      have hsum : (t.1 + t.2.1 + t.2.2) % 3 = 0 := by
        have hcomp : t.1 + t.2.1 + t.2.2 = d := (Finset.mem_filter.mp ht).2
        omega
      rcases res3_dichotomy hsum with heq | hdist
      · exact Or.inl ⟨ht, heq⟩
      · exact Or.inr ⟨ht, hdist⟩
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  have hTcard : T.card = Teq.card + Tdist.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hAset : (tripleBox m).filter (fun t => isComp3 d t ∧ inD t) = Teq ∪ TdistIn := by
    ext t
    simp only [Teq, TdistIn, Tdist, T, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hbox, hcomp, hin⟩
      have hsum : (t.1 + t.2.1 + t.2.2) % 3 = 0 := by
        unfold isComp3 at hcomp; omega
      rcases res3_dichotomy hsum with heq | hdist
      · exact Or.inl ⟨⟨hbox, hcomp⟩, heq⟩
      · exact Or.inr ⟨⟨⟨hbox, hcomp⟩, hdist⟩, hin⟩
    · rintro (⟨⟨hbox, hcomp⟩, heq⟩ | ⟨⟨⟨hbox, hcomp⟩, _⟩, hin⟩)
      · exact ⟨hbox, hcomp, inD_of_equalRes heq⟩
      · exact ⟨hbox, hcomp, hin⟩
  have hdisjA : Disjoint Teq TdistIn :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisj
  have hAcard : cardA m d = Teq.card + TdistIn.card := by
    unfold cardA
    rw [hAset, Finset.card_union_of_disjoint hdisjA]
  have hdisjIO : Disjoint TdistIn TdistOut := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    exact (Finset.mem_filter.mp ht2).2 (Finset.mem_filter.mp ht1).2
  have hunionIO : Tdist = TdistIn ∪ TdistOut := by
    ext t
    simp only [TdistIn, TdistOut, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ht
      by_cases h : inD t
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  have hTdist_split : Tdist.card = TdistIn.card + TdistOut.card := by
    rw [hunionIO, Finset.card_union_of_disjoint hdisjIO]
  have hbij : TdistIn.card = TdistOut.card := by
    refine Finset.card_bij (fun t _ => (t.1, t.2.2, t.2.1)) ?_ ?_ ?_
    · intro t ht
      simp only [TdistIn, TdistOut, Tdist, T, tripleBox, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at ht ⊢
      rcases ht with ⟨⟨⟨⟨h1, h2, h3⟩, hcomp⟩, hdist⟩, hin⟩
      refine ⟨⟨⟨⟨h1, h3, h2⟩, ?_⟩, ?_⟩, ?_⟩
      · unfold isComp3 at hcomp ⊢; dsimp only; omega
      · unfold distinctRes at hdist ⊢; exact ⟨hdist.2.1, hdist.1, Ne.symm hdist.2.2⟩
      · exact fun h => ((swap_inD_iff_not_inD hdist).mp h) hin
    · intro t₁ _ t₂ _ hEq
      rcases t₁ with ⟨a₁, b₁, c₁⟩
      rcases t₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hEq ⊢
      exact ⟨hEq.1, hEq.2.2, hEq.2.1⟩
    · intro u hu
      refine ⟨(u.1, u.2.2, u.2.1), ?_, by rcases u with ⟨a, b, c⟩; rfl⟩
      simp only [TdistIn, TdistOut, Tdist, T, tripleBox, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hu ⊢
      rcases hu with ⟨⟨⟨⟨h1, h2, h3⟩, hcomp⟩, hdist⟩, hnot⟩
      refine ⟨⟨⟨⟨h1, h3, h2⟩, ?_⟩, ?_⟩, ?_⟩
      · unfold isComp3 at hcomp ⊢; dsimp only; omega
      · unfold distinctRes at hdist ⊢; exact ⟨hdist.2.1, hdist.1, Ne.symm hdist.2.2⟩
      · exact (swap_inD_iff_not_inD hdist).mpr hnot
  have hWcard : cardW m d = T.card := rfl
  have hDcard : cardDistinctRes m d = Tdist.card := by
    unfold cardDistinctRes
    simp only [Tdist, T, Finset.filter_filter]
  omega

/-- Conjecture 2 holds for ALL `m ≤ 5` and `3 ∣ d`. -/
theorem conj2_holds_le_five (m d : ℕ) (hm : m ≤ 5) (hd : d % 3 = 0) :
    2 * cardA m d = 2 * cardW m d - cardWStar m d := by
  rw [conj2_exact_corrected_formula m d hd]
  suffices hEq : cardDistinctRes m d = cardWStar m d by rw [hEq]
  unfold cardDistinctRes cardWStar
  congr 1
  ext t
  simp only [tripleBox, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hbox, hcomp, hdist⟩
    refine ⟨hbox, hcomp, ?_⟩
    unfold distinctRes at hdist
    unfold distinctParts
    exact ⟨fun h => hdist.1 (by rw [h]), fun h => hdist.2.1 (by rw [h]),
      fun h => hdist.2.2 (by rw [h])⟩
  · rintro ⟨⟨h1, h2, h3⟩, hcomp, hparts⟩
    refine ⟨⟨h1, h2, h3⟩, hcomp, ?_⟩
    have hsum : (t.1 + t.2.1 + t.2.2) % 3 = 0 := by
      unfold isComp3 at hcomp; omega
    rcases res3_dichotomy hsum with heq | hdist
    · unfold equalRes at heq
      unfold distinctParts at hparts
      omega
    · exact hdist

/-- **Disproof of Conjecture 2 for every `m ≥ 6`:** at `d = 9`, the 6 permutations of `(0, 3, 6)`
have pairwise distinct parts yet equal residues mod 3, so `w*_{3,m}(9) > cardDistinctRes m 9`. -/
theorem conj2_fails_all_ge_six (m : ℕ) (hm : 6 ≤ m) :
    2 * cardA m 9 ≠ 2 * cardW m 9 - cardWStar m 9 := by
  have hcorr := conj2_exact_corrected_formula m 9 (by decide)
  set Sdist := (tripleBox m).filter (fun t => isComp3 9 t ∧ distinctRes t)
  set Sstar := (tripleBox m).filter (fun t => isComp3 9 t ∧ distinctParts t)
  have hsub : Sdist ⊂ Sstar := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [Sdist, Sstar, Finset.mem_filter] at ht ⊢
      rcases ht with ⟨hbox, hcomp, hdist⟩
      refine ⟨hbox, hcomp, ?_⟩
      unfold distinctRes at hdist
      unfold distinctParts
      exact ⟨fun h => hdist.1 (by rw [h]), fun h => hdist.2.1 (by rw [h]),
        fun h => hdist.2.2 (by rw [h])⟩
    · intro hEq
      have hmem : (0, 3, 6) ∈ Sstar := by
        refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · unfold tripleBox
          rw [Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range,
            Finset.mem_range]
          dsimp only
          omega
        · unfold isComp3; decide
        · unfold distinctParts; decide
      rw [← hEq] at hmem
      have hdist0 := (Finset.mem_filter.mp hmem).2.2
      unfold distinctRes at hdist0
      exact hdist0.1 (by decide)
  have hlt : cardDistinctRes m 9 < cardWStar m 9 := Finset.card_lt_card hsub
  have hle : cardWStar m 9 ≤ cardW m 9 := by
    unfold cardWStar cardW
    refine Finset.card_le_card ?_
    intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  omega

/-- Minimal concrete counterexample to Conjecture 2 (`m = 6, d = 9`):
`w_{3,6}(9) = 37`, `w*_{3,6}(9) = 30`, and `|𝒜_9| = 25 ≠ 22 = 37 - 30 / 2`. -/
theorem conj2_counterexample_6_9 :
    cardW 6 9 = 37 ∧ cardWStar 6 9 = 30 ∧ cardA 6 9 = 25 ∧
      2 * cardA 6 9 ≠ 2 * cardW 6 9 - cardWStar 6 9 := by
  decide

/-! ### Part 2: Exact `r ≤ 3` vs `r ≥ 4` Support Characterization -/

/-- The paper's residue condition from Conjecture 1 (p. 16):
if `d₀ ≡ i (mod r)`, then `d_k ≢ k + i (mod r)` for all `1 ≤ k ≤ r - 1`. -/
def PaperCond (r : ℕ) (d : Fin r → ℕ) : Prop :=
  ∀ k : Fin r, k.val ≠ 0 → d k % r ≠ (k.val + d ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩) % r

instance (r : ℕ) (d : Fin r → ℕ) : Decidable (PaperCond r d) :=
  inferInstanceAs (Decidable (∀ k : Fin r, k.val ≠ 0 → d k % r ≠ (k.val + d ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩) % r))

/-- The index shift map `σ_d(i) = (i - d_i) mod r` on `ZMod r`. -/
def sigmaMap (r : ℕ) (d : Fin r → ℕ) (i : Fin r) : ZMod r :=
  (i.val : ZMod r) - (d i : ZMod r)

private lemma sigmaMap_eq_iff {r : ℕ} (d : Fin r → ℕ) (i j : Fin r) :
    sigmaMap r d i = sigmaMap r d j ↔ (i.val + d j) % r = (j.val + d i) % r := by
  unfold sigmaMap
  rw [sub_eq_sub_iff_add_eq_add, ← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']

/-- For `r ∈ {1, 2, 3}` and `r ∣ ∑ d_i`, Güday–Şahin's condition in Conjecture 1 is
equivalent to `σ_d` being bijective on `Fin r → ZMod r`. -/
theorem paperCond_iff_bijective_of_le_three {r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (d : Fin r → ℕ) (hsum : (∑ i : Fin r, d i) % r = 0) :
    PaperCond r d ↔ Function.Bijective (sigmaMap r d) := by
  have hbij_inj : Function.Bijective (sigmaMap r d) ↔ Function.Injective (sigmaMap r d) := by
    have : NeZero r := ⟨by omega⟩
    have hcard : Fintype.card (Fin r) = Fintype.card (ZMod r) := by
      rw [Fintype.card_fin, ZMod.card]
    exact (Fintype.bijective_iff_injective_and_card (sigmaMap r d)).trans
      ⟨fun h => h.1, fun h => ⟨h, hcard⟩⟩
  rw [hbij_inj]
  have h01 : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases h01 with rfl | rfl | rfl
  · constructor
    · intro _ i j _
      exact Subsingleton.elim i j
    · intro _ k hk
      exact False.elim (hk (by omega))
  · constructor
    · intro hpc i j hij
      rw [sigmaMap_eq_iff] at hij
      have hp1 : d 1 % 2 ≠ (1 + d 0) % 2 := hpc 1 (by decide)
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        have h' : d 1 % 2 = (1 + d 0) % 2 := by simpa using hij
        exact hp1 h'
      · exfalso
        have h' : (1 + d 0) % 2 = d 1 % 2 := by simpa using hij
        exact hp1 h'.symm
      · rfl
    · intro hinj k hk hEq
      have hk1 : k = 1 := by omega
      subst hk1
      have hsig : sigmaMap 2 d 0 = sigmaMap 2 d 1 := by
        rw [sigmaMap_eq_iff]
        simpa [Nat.zero_add] using hEq
      exact absurd (hinj hsig) (by decide)
  · have hsum3 : (d 0 + d 1 + d 2) % 3 = 0 := by
      simpa [Fin.sum_univ_three, add_assoc] using hsum
    constructor
    · intro hpc i j hij
      rw [sigmaMap_eq_iff] at hij
      have hp1 : d 1 % 3 ≠ (1 + d 0) % 3 := hpc 1 (by decide)
      have hp2 : d 2 % 3 ≠ (2 + d 0) % 3 := hpc 2 (by decide)
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        have h' : d 1 % 3 = (1 + d 0) % 3 := by simpa using hij
        exact hp1 h'
      · exfalso
        have h' : d 2 % 3 = (2 + d 0) % 3 := by simpa using hij
        exact hp2 h'
      · exfalso
        have h' : (1 + d 0) % 3 = d 1 % 3 := by simpa using hij
        exact hp1 h'.symm
      · rfl
      · exfalso
        have h' : (1 + d 2) % 3 = (2 + d 1) % 3 := by simpa using hij
        omega
      · exfalso
        have h' : (2 + d 0) % 3 = d 2 % 3 := by simpa using hij
        exact hp2 h'.symm
      · exfalso
        have h' : (2 + d 1) % 3 = (1 + d 2) % 3 := by simpa using hij
        omega
      · rfl
    · intro hinj k hk hEq
      have h12 : k = 1 ∨ k = 2 := by omega
      rcases h12 with rfl | rfl
      · have hsig : sigmaMap 3 d 0 = sigmaMap 3 d 1 := by
          rw [sigmaMap_eq_iff]; simpa using hEq
        exact absurd (hinj hsig) (by decide)
      · have hsig : sigmaMap 3 d 0 = sigmaMap 3 d 2 := by
          rw [sigmaMap_eq_iff]; simpa using hEq
        exact absurd (hinj hsig) (by decide)

/-- Explicit witness tuple `(0, r - 1, 0, 1, 0, …, 0)` for any `r ≥ 4`. -/
def badTuple (r : ℕ) (i : Fin r) : ℕ :=
  if i.val = 1 then r - 1 else if i.val = 3 then 1 else 0

/-- **Infinite Non-Bijective Family (`r ≥ 4`):** for every `r ≥ 4`, `badTuple r` has sum `r`
and satisfies Conjecture 1's residue condition, yet `σ_d` maps indices `1`, `2`, `3` all to `2`
and is therefore not bijective. -/
theorem nonbijective_family_ge_four (r : ℕ) (hr : 4 ≤ r) :
    (∑ i : Fin r, badTuple r i) = r ∧
      PaperCond r (badTuple r) ∧
      ¬ Function.Bijective (sigmaMap r (badTuple r)) := by
  let i1 : Fin r := ⟨1, by omega⟩
  let i2 : Fin r := ⟨2, by omega⟩
  let i3 : Fin r := ⟨3, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · have hsum : (∑ i : Fin r, badTuple r i) = badTuple r i1 + badTuple r i3 := by
      have hsub : ({i1, i3} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair (by intro h; have := congrArg Fin.val h; simp [i1, i3] at this)]
      · intro x _ hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have h1 : x.val ≠ 1 := fun h => hx.1 (Fin.ext h)
        have h3 : x.val ≠ 3 := fun h => hx.2 (Fin.ext h)
        simp [badTuple, h1, h3]
    rw [hsum]
    simp [badTuple, i1, i3]
    omega
  · intro k hk
    have h0 : badTuple r ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩ = 0 := by simp [badTuple]
    rw [h0, Nat.add_zero]
    by_cases hk1 : k.val = 1
    · simp only [badTuple, hk1, ↓reduceIte]
      have hmod1 : (r - 1) % r = r - 1 := Nat.mod_eq_of_lt (by omega)
      have hmod2 : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
      omega
    · by_cases hk3 : k.val = 3
      · unfold badTuple
        rw [hk3]
        simp only [show (3 : ℕ) ≠ 1 by decide, ↓reduceIte]
        have hmod1 : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
        have hmod3 : 3 % r = 3 := Nat.mod_eq_of_lt (by omega)
        omega
      · simp only [badTuple, hk1, hk3, ↓reduceIte, Nat.zero_mod]
        have hmodk : k.val % r = k.val := Nat.mod_eq_of_lt k.isLt
        omega
  · intro hbij
    have hcol : sigmaMap r (badTuple r) i2 = sigmaMap r (badTuple r) i3 := by
      unfold sigmaMap
      have hb2 : badTuple r i2 = 0 := by simp [badTuple, i2]
      have hb3 : badTuple r i3 = 1 := by simp [badTuple, i3]
      rw [hb2, hb3]
      simp [i2, i3]
      ring
    have heq := hbij.1 hcol
    have := congrArg Fin.val heq
    simp [i2, i3] at this

/-! ### Part 3: Unconditional Refutation of Conjecture 1 over `ℝ` (`r = 4, m = 5`) -/

/-- The general conditional sequence of Equation (1) for `r = 4, m = 5` over any ring `R`. -/
def condSeq {R : Type*} [CommRing R] (a : Fin 4 → Fin 5 → R) (init : Fin 5 → R) : ℕ → R
  | 0 => init 0
  | 1 => init 1
  | 2 => init 2
  | 3 => init 3
  | 4 => init 4
  | n + 5 =>
      let i : Fin 4 := ⟨(n + 5) % 4, Nat.mod_lt _ (by decide)⟩
      a i 0 * condSeq a init (n + 4) +
      a i 1 * condSeq a init (n + 3) +
      a i 2 * condSeq a init (n + 2) +
      a i 3 * condSeq a init (n + 1) +
      a i 4 * condSeq a init n

/-- Index factor `a_{i, j}` extended at `j = 0` by `c0` (`c0 = 1` or `c0 = -1`). -/
def factorAt {R : Type*} (c0 : R) (a : Fin 4 → Fin 5 → R) (i : Fin 4) (j : Fin 6) : R :=
  match j with
  | ⟨0, _⟩ => c0
  | ⟨k + 1, hk⟩ => a i ⟨k, by omega⟩

/-- The set of tuples `t : Fin 4 → Fin 6` of sum `d` satisfying Conjecture 1's residue condition. -/
def conjTuples4 (d : ℕ) : Finset (Fin 4 → Fin 6) :=
  Finset.univ.filter fun t =>
    (∑ i : Fin 4, (t i).val) = d ∧ PaperCond 4 (fun i => (t i).val)

/-- Conjectured decimated coefficient `A_d` of Conjecture 1 (p. 16) for a sign assignment `s`
and `j = 0` convention `c0` (`1` or `-1`). -/
def conjCoeff {R : Type*} [CommRing R] (c0 : R) (s : (Fin 4 → Fin 6) → R)
    (a : Fin 4 → Fin 5 → R) (d : ℕ) : R :=
  ∑ t ∈ conjTuples4 d, s t * ∏ i : Fin 4, factorAt c0 a i (t i)

/-- Concrete integer counterexample array `A` for `r = 4, m = 5`:
`a_{1,3} = a_{3,1} = 1`, while every other `a_{i,j}` (`j ≥ 1`) is a nonzero multiple of 3. -/
def instA : Fin 4 → Fin 5 → ℤ
  | 0, 0 => 18 | 0, 1 => 33 | 0, 2 => 15 | 0, 3 => 30 | 0, 4 => 12
  | 1, 0 => 6  | 1, 1 => 21 | 1, 2 => 1  | 1, 3 => 18 | 1, 4 => 33
  | 2, 0 => 27 | 2, 1 => 9  | 2, 2 => 24 | 2, 3 => 6  | 2, 4 => 21
  | 3, 0 => 1  | 3, 1 => 30 | 3, 2 => 12 | 3, 3 => 27 | 3, 4 => 9

/-- Concrete initial values `q_0, …, q_4 = 2, -1, 5, 3, 7`. -/
def instInit : Fin 5 → ℤ
  | 0 => 2 | 1 => -1 | 2 => 5 | 3 => 3 | 4 => 7

/-- Integer conditional sequence `q_n` for the concrete instance. -/
def instQ : ℕ → ℤ := condSeq instA instInit

private lemma condSeq_map_intCast (a : Fin 4 → Fin 5 → ℤ) (init : Fin 5 → ℤ) :
    ∀ n : ℕ, condSeq (fun i j => (a i j : ℝ)) (fun j => (init j : ℝ)) n =
      ((condSeq a init n : ℤ) : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | m + 5 =>
      simp only [condSeq, ih (m + 4) (by omega), ih (m + 3) (by omega),
        ih (m + 2) (by omega), ih (m + 1) (by omega), ih m (by omega)]
      push_cast
      rfl

/-- State vector `v_k = (q_{4k+4}, q_{4k+3}, q_{4k+2}, q_{4k+1}, q_{4k})`. -/
def stateVec (k : ℕ) : Fin 5 → ℤ :=
  fun j => instQ (4 * k + 4 - j.val)

/-- One-step companion matrix for residue `i ∈ Fin 4`. -/
def compMat (i : Fin 4) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun r c =>
    if r = 0 then instA i c
    else if r.val = c.val + 1 then 1
    else 0

/-- 4-step monodromy matrix `M = C_0 C_3 C_2 C_1` advancing `stateVec k` to `stateVec (k + 1)`. -/
def monoMat : Matrix (Fin 5) (Fin 5) ℤ :=
  compMat 0 * (compMat 3 * (compMat 2 * compMat 1))

private lemma instQ_step_eq (n : ℕ) :
    instQ (n + 5) =
      let i : Fin 4 := ⟨(n + 5) % 4, Nat.mod_lt _ (by decide)⟩
      instA i 0 * instQ (n + 4) +
      instA i 1 * instQ (n + 3) +
      instA i 2 * instQ (n + 2) +
      instA i 3 * instQ (n + 1) +
      instA i 4 * instQ n := rfl

private lemma compMat_mulVec_window (m : ℕ) (i : Fin 4) (hi : (m + 5) % 4 = i.val) :
    (compMat i).mulVec (fun j : Fin 5 => instQ (m + 4 - j.val)) =
      fun j : Fin 5 => instQ (m + 5 - j.val) := by
  ext r
  fin_cases r
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, compMat, Matrix.of_apply,
      Fin.val_zero, Nat.sub_zero]
    rw [instQ_step_eq m]
    have hidx : (⟨(m + 5) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = i := Fin.ext hi
    rw [hidx]
    rfl
  · simp [Matrix.mulVec, dotProduct, compMat]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, compMat]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, compMat]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, compMat]

private lemma stateVec_succ (k : ℕ) : stateVec (k + 1) = monoMat.mulVec (stateVec k) := by
  have h1 := compMat_mulVec_window (4 * k) 1 (by omega)
  have h2 := compMat_mulVec_window (4 * k + 1) 2 (by omega)
  have h3 := compMat_mulVec_window (4 * k + 2) 3 (by omega)
  have h4 := compMat_mulVec_window (4 * k + 3) 0 (by omega)
  have hgoal : (fun j : Fin 5 => instQ (4 * k + 3 + 5 - j.val)) = stateVec (k + 1) := by
    ext j; unfold stateVec; congr 1
  rw [← hgoal, ← h4, ← h3, ← h2, ← h1]
  simp only [monoMat, Matrix.mulVec_mulVec]
  rfl

private lemma stateVec_add (k t : ℕ) : stateVec (k + t) = (monoMat ^ t).mulVec (stateVec k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← Nat.add_assoc, stateVec_succ, ih, pow_succ', Matrix.mulVec_mulVec]

/-- Explicit 5×5 integer literal equal to `monoMat`. -/
private def monoMatLit : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![12297, 42294, 2400, 35847, 63756],
    ![363, 1248, 72, 1047, 1881],
    ![171, 591, 33, 507, 891],
    ![6, 21, 1, 18, 33],
    ![1, 0, 0, 0, 0]]

private lemma monoMat_eq_lit : monoMat = monoMatLit := by
  decide

/-- Exact degree-5 polynomial annihilating `monoMat`:
`M^5 = 13596 M^4 + 68961 M^3 + 83853 M^2 - 562923 M + 74844 I`. -/
private lemma monoMat_poly :
    monoMat ^ 5 =
      (13596 : ℤ) • monoMat ^ 4 +
      (68961 : ℤ) • monoMat ^ 3 +
      (83853 : ℤ) • monoMat ^ 2 +
      (-562923 : ℤ) • monoMat +
      (74844 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  rw [monoMat_eq_lit]
  decide

/-- True decimated recurrence coefficients `c₁, …, c₅` for the concrete `r = 4, m = 5` instance. -/
def trueC : Fin 5 → ℤ
  | 0 => 13596
  | 1 => 68961
  | 2 => 83853
  | 3 => -562923
  | 4 => 74844

/-- The concrete sequence satisfies the exact 4-decimated recurrence for ALL `k ≥ 0`. -/
theorem instQ_decimated (k : ℕ) :
    instQ (4 * k + 24) =
      13596 * instQ (4 * k + 20) +
      68961 * instQ (4 * k + 16) +
      83853 * instQ (4 * k + 12) +
      (-562923) * instQ (4 * k + 8) +
      74844 * instQ (4 * k + 4) := by
  have hv := congrArg (fun M => M.mulVec (stateVec k) 0) monoMat_poly
  have hs5 : (monoMat ^ 5).mulVec (stateVec k) 0 = instQ (4 * k + 24) := by
    rw [← stateVec_add k 5]; unfold stateVec; congr 1
  have hs4 : (monoMat ^ 4).mulVec (stateVec k) 0 = instQ (4 * k + 20) := by
    rw [← stateVec_add k 4]; unfold stateVec; congr 1
  have hs3 : (monoMat ^ 3).mulVec (stateVec k) 0 = instQ (4 * k + 16) := by
    rw [← stateVec_add k 3]; unfold stateVec; congr 1
  have hs2 : (monoMat ^ 2).mulVec (stateVec k) 0 = instQ (4 * k + 12) := by
    rw [← stateVec_add k 2]; unfold stateVec; congr 1
  have hs1 : monoMat.mulVec (stateVec k) 0 = instQ (4 * k + 8) := by
    have := stateVec_add k 1
    rw [pow_one] at this
    rw [← this]; unfold stateVec; congr 1
  have hs0 : (1 : Matrix (Fin 5) (Fin 5) ℤ).mulVec (stateVec k) 0 = instQ (4 * k + 4) := by
    simp [stateVec]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hs5, hs4, hs3, hs2, hs1, hs0] at hv
  exact hv

/-- Decimated 5×5 companion matrix `K` for `(c₁, …, c₅)`. -/
def decComp : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun r c =>
    if r = 0 then trueC c
    else if r.val = c.val + 1 then 1
    else 0

/-- 5×5 Krylov matrix `W t` with entry `(s, j) = instQ (4 * (t + j) + 20 - 4 * s)`. -/
def krylovMat (t : ℕ) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun s j => instQ (4 * (t + j.val) + 20 - 4 * s.val)

private lemma krylovMat_succ (t : ℕ) : krylovMat (t + 1) = decComp * krylovMat t := by
  ext s j
  fin_cases s
  · simp only [krylovMat, decComp, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five, trueC]
    have hrec := instQ_decimated (t + j.val)
    have h0 : 4 * (t + 1 + j.val) + 20 - 4 * 0 = 4 * (t + j.val) + 24 := by omega
    have h1 : 4 * (t + j.val) + 20 - 4 * (0 : Fin 5).val = 4 * (t + j.val) + 20 := by omega
    have h2 : 4 * (t + j.val) + 20 - 4 * (1 : Fin 5).val = 4 * (t + j.val) + 16 := by omega
    have h3 : 4 * (t + j.val) + 20 - 4 * (2 : Fin 5).val = 4 * (t + j.val) + 12 := by omega
    have h4 : 4 * (t + j.val) + 20 - 4 * (3 : Fin 5).val = 4 * (t + j.val) + 8 := by omega
    have h5 : 4 * (t + j.val) + 20 - 4 * (4 : Fin 5).val = 4 * (t + j.val) + 4 := by omega
    have h0' : (⟨0, by decide⟩ : Fin 5) = 0 := rfl
    simp only [h0', ↓reduceIte, h0, h1, h2, h3, h4, h5]
    exact hrec
  · simp only [krylovMat, decComp, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five]
    norm_num
    congr 1; omega
  · simp only [krylovMat, decComp, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five]
    norm_num
    congr 1; omega
  · simp only [krylovMat, decComp, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five]
    norm_num
    congr 1; omega
  · simp only [krylovMat, decComp, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five]
    norm_num
    congr 1; omega

private lemma krylovMat_eq_pow (t : ℕ) : krylovMat t = decComp ^ t * krylovMat 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [krylovMat_succ, ih, pow_succ', Matrix.mul_assoc]

private lemma stateVec_0_eq : stateVec 0 = ![7, 3, 5, -1, 2] := by
  ext j; fin_cases j <;> rfl

private lemma stateVec_1_eq : stateVec 1 = ![316626, 9360, 4410, 158, 7] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, stateVec_succ, stateVec_0_eq, monoMat_eq_lit]; decide

private lemma stateVec_2_eq : stateVec 2 = ![4306115880, 127112631, 59906679, 2103801, 316626] := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, stateVec_succ, stateVec_1_eq, monoMat_eq_lit]; decide

private lemma stateVec_3_eq :
    stateVec 3 = ![58567786383177, 1728868161969, 814795041681, 28614284286, 4306115880] := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, stateVec_succ, stateVec_2_eq, monoMat_eq_lit]; decide

private lemma stateVec_4_eq :
    stateVec 4 = ![796584604269124377, 23514458125849317, 11082084983004501,
      389184903683280, 58567786383177] := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, stateVec_succ, stateVec_3_eq, monoMat_eq_lit]; decide

private lemma stateVec_5_eq :
    stateVec 5 = ![10834403533662284650539, 319821807809871570636, 150728221530671197014,
      5293331396457530301, 796584604269124377] := by
  change stateVec (4 + 1) = _
  rw [stateVec_succ, stateVec_4_eq, monoMat_eq_lit]; decide

private lemma stateVec_6_eq :
    stateVec 6 = ![147359488623228028811470626, 4349919024429058631662677,
      2050065199882804680672021, 71994974644588798733463, 10834403533662284650539] := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, stateVec_succ, stateVec_5_eq, monoMat_eq_lit]; decide

private lemma stateVec_7_eq :
    stateVec 7 = ![2004246825386533154584186612005, 59163556258610504797588843266,
      27883081755298998749117791836, 979208741312474662585082115,
      147359488623228028811470626] := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, stateVec_succ, stateVec_6_eq, monoMat_eq_lit]; decide

private lemma stateVec_8_eq :
    stateVec 8 = ![27259902803699079294263439565131750, 804687712462693425905308054787886,
      379239766724069565555593461113720, 13318287335973509595880913181180,
      2004246825386533154584186612005] := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, stateVec_succ, stateVec_7_eq, monoMat_eq_lit]; decide

/-- Explicit 5×5 integer literal equal to `krylovMat 0`. -/
private def krylovMat0Lit : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![796584604269124377, 10834403533662284650539, 147359488623228028811470626,
      2004246825386533154584186612005, 27259902803699079294263439565131750],
    ![58567786383177, 796584604269124377, 10834403533662284650539,
      147359488623228028811470626, 2004246825386533154584186612005],
    ![4306115880, 58567786383177, 796584604269124377,
      10834403533662284650539, 147359488623228028811470626],
    ![316626, 4306115880, 58567786383177, 796584604269124377, 10834403533662284650539],
    ![7, 316626, 4306115880, 58567786383177, 796584604269124377]]

private lemma krylovMat_zero_eq_lit : krylovMat 0 = krylovMat0Lit := by
  have hq0 : instQ 4 = 7 := by simpa [stateVec] using congrFun stateVec_0_eq 0
  have hq1 : instQ 8 = 316626 := by simpa [stateVec] using congrFun stateVec_1_eq 0
  have hq2 : instQ 12 = 4306115880 := by simpa [stateVec] using congrFun stateVec_2_eq 0
  have hq3 : instQ 16 = 58567786383177 := by simpa [stateVec] using congrFun stateVec_3_eq 0
  have hq4 : instQ 20 = 796584604269124377 := by simpa [stateVec] using congrFun stateVec_4_eq 0
  have hq5 : instQ 24 = 10834403533662284650539 := by simpa [stateVec] using congrFun stateVec_5_eq 0
  have hq6 : instQ 28 = 147359488623228028811470626 := by simpa [stateVec] using congrFun stateVec_6_eq 0
  have hq7 : instQ 32 = 2004246825386533154584186612005 := by simpa [stateVec] using congrFun stateVec_7_eq 0
  have hq8 : instQ 36 = 27259902803699079294263439565131750 := by simpa [stateVec] using congrFun stateVec_8_eq 0
  ext s j
  fin_cases s <;> fin_cases j <;>
    simp [krylovMat, krylovMat0Lit, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8]

private lemma det_ne_zero_of_mul_inv_mod5 {A : Matrix (Fin 5) (Fin 5) ℤ}
    (B : Matrix (Fin 5) (Fin 5) (ZMod 5))
    (h : A.map (Int.cast : ℤ → ZMod 5) * B = 1) : A.det ≠ 0 := by
  intro h0
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hmap : (A.map (Int.cast : ℤ → ZMod 5)).det = (A.det : ZMod 5) :=
    (RingHom.map_det (Int.castRingHom (ZMod 5)) A).symm
  rw [hmap, h0, Int.cast_zero, zero_mul] at hdet
  exact absurd hdet (by decide)

private def decCompInvMod5 : Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  ![![0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1],
    ![4, 1, 1, 3, 2]]

private def krylov0InvMod5 : Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  ![![0, 1, 4, 4, 0],
    ![0, 3, 3, 1, 4],
    ![1, 1, 0, 3, 4],
    ![1, 4, 1, 3, 1],
    ![4, 1, 1, 0, 0]]

private lemma det_decComp_ne_zero : decComp.det ≠ 0 :=
  det_ne_zero_of_mul_inv_mod5 decCompInvMod5 (by decide)

private lemma det_krylovMat_zero_ne_zero : (krylovMat 0).det ≠ 0 := by
  rw [krylovMat_zero_eq_lit]
  exact det_ne_zero_of_mul_inv_mod5 krylov0InvMod5 (by decide)

private lemma det_krylovMat_ne_zero (t : ℕ) : (krylovMat t).det ≠ 0 := by
  rw [krylovMat_eq_pow, Matrix.det_mul, Matrix.det_pow]
  exact mul_ne_zero (pow_ne_zero t det_decComp_ne_zero) det_krylovMat_zero_ne_zero

/-- The special non-bijective tuple `(0, 3, 0, 1)` in `conjTuples4 4`. -/
def specialTuple : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 0
  | 3 => 1

private lemma specialTuple_mem : specialTuple ∈ conjTuples4 4 := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · decide
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · decide
    · decide
    · decide

private lemma specialTuple_prod (c0 : ℤ) (hc0 : c0 = 1 ∨ c0 = -1) :
    (∏ i : Fin 4, factorAt c0 instA i (specialTuple i)) = 1 := by
  have hsq : c0 * c0 = 1 := by rcases hc0 with rfl | rfl <;> rfl
  simp only [Fin.prod_univ_four, specialTuple, factorAt, instA]
  linear_combination hsq

private lemma instA_dvd_three_row0 (j : Fin 5) : (3 : ℤ) ∣ instA 0 j := by
  fin_cases j <;> decide

private lemma instA_dvd_three_row2 (j : Fin 5) : (3 : ℤ) ∣ instA 2 j := by
  fin_cases j <;> decide

private lemma instA_dvd_three_row1 (j : Fin 5) (hj : j ≠ 2) : (3 : ℤ) ∣ instA 1 j := by
  fin_cases j <;> first | exact absurd rfl hj | decide

private lemma instA_dvd_three_row3 (j : Fin 5) (hj : j ≠ 0) : (3 : ℤ) ∣ instA 3 j := by
  fin_cases j <;> first | exact absurd rfl hj | decide

private lemma other_tuples_dvd_three (c0 : ℤ) :
    ∀ t ∈ (conjTuples4 4).erase specialTuple,
      (3 : ℤ) ∣ ∏ i : Fin 4, factorAt c0 instA i (t i) := by
  intro t ht
  rw [Finset.mem_erase] at ht
  rcases ht with ⟨hne, hmem⟩
  have hsum : (t 0).val + (t 1).val + (t 2).val + (t 3).val = 4 := by
    have h1 := (Finset.mem_filter.mp hmem).2.1
    simpa [Fin.sum_univ_four, add_assoc] using h1
  rw [Fin.prod_univ_four]
  by_cases h0 : t 0 ≠ 0
  · rcases ht0 : t 0 with ⟨v, hv⟩
    cases v with
    | zero => exact False.elim (h0 (Fin.ext (by simp [ht0])))
    | succ k =>
      simp only [factorAt]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (instA_dvd_three_row0 ⟨k, by omega⟩) _) _) _
  · push Not at h0
    by_cases h2 : t 2 ≠ 0
    · rcases ht2 : t 2 with ⟨v, hv⟩
      cases v with
      | zero => exact False.elim (h2 (Fin.ext (by simp [ht2])))
      | succ k =>
        simp only [factorAt]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (instA_dvd_three_row2 ⟨k, by omega⟩) _) _
    · push Not at h2
      by_cases h1 : t 1 ≠ 0 ∧ t 1 ≠ 3
      · rcases ht1 : t 1 with ⟨v, hv⟩
        cases v with
        | zero => exact False.elim (h1.1 (Fin.ext (by simp [ht1])))
        | succ k =>
          have hk2 : (⟨k, by omega⟩ : Fin 5) ≠ 2 := by
            intro hEq
            have hkval : k = 2 := congrArg Fin.val hEq
            apply h1.2
            apply Fin.ext
            rw [ht1]; simp [hkval]
          simp only [factorAt]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (instA_dvd_three_row1 ⟨k, by omega⟩ hk2) _) _) _
      · by_cases h3 : t 3 ≠ 0 ∧ t 3 ≠ 1
        · rcases ht3 : t 3 with ⟨v, hv⟩
          cases v with
          | zero => exact False.elim (h3.1 (Fin.ext (by simp [ht3])))
          | succ k =>
            have hk0 : (⟨k, by omega⟩ : Fin 5) ≠ 0 := by
              intro hEq
              have hkval : k = 0 := congrArg Fin.val hEq
              apply h3.2
              apply Fin.ext
              rw [ht3]; simp [hkval]
            simp only [factorAt]
            exact dvd_mul_of_dvd_right (instA_dvd_three_row3 ⟨k, by omega⟩ hk0) _
        · exfalso
          have h1' : t 1 = 0 ∨ t 1 = 3 := by tauto
          have h3' : t 3 = 0 ∨ t 3 = 1 := by tauto
          have h1val : (t 1).val = 3 := by
            rcases h1' with h | h <;> rcases h3' with h' | h' <;>
              simp [h0, h2, h, h'] at hsum ⊢
          have h3val : (t 3).val = 1 := by
            rcases h1' with h | h <;> rcases h3' with h' | h' <;>
              simp [h0, h2, h, h'] at hsum ⊢
          apply hne
          ext i
          fin_cases i
          · simp [h0, specialTuple]
          · simpa [specialTuple] using h1val
          · simp [h2, specialTuple]
          · simpa [specialTuple] using h3val

private lemma conjCoeff_int_not_dvd_three (c0 : ℤ) (hc0 : c0 = 1 ∨ c0 = -1)
    (s : (Fin 4 → Fin 6) → ℤ) (hs : ∀ t, s t = 1 ∨ s t = -1) :
    ¬ ((3 : ℤ) ∣ conjCoeff c0 s instA 4) := by
  unfold conjCoeff
  rw [← Finset.add_sum_erase _ _ specialTuple_mem, specialTuple_prod c0 hc0, mul_one]
  have hdvd : (3 : ℤ) ∣ ∑ t ∈ (conjTuples4 4).erase specialTuple,
      s t * ∏ i : Fin 4, factorAt c0 instA i (t i) :=
    Finset.dvd_sum fun t ht => dvd_mul_of_dvd_right (other_tuples_dvd_three c0 t ht) _
  intro htot
  have hs3 : (3 : ℤ) ∣ s specialTuple := (Int.dvd_add_left hdvd).mp htot
  rcases hs specialTuple with h1 | h1 <;> rw [h1] at hs3 <;> omega

/-- **Main Disproof of Conjecture 1 (over `ℝ`, for all sign assignments and all cutoffs `N`):**
For `r = 4, m = 5` and either convention `c0 ∈ {1, -1}` for the `d_i = 0` factor, there is NO
sign function `s : (Fin 4 → Fin 6) → ℝ` with values in `{-1, 1}` such that every general
conditional sequence over `ℝ` eventually satisfies `q_n = ∑_{k=1}^5 A_{4k} q_{n - 4k}`. -/
theorem guday_sahin_conjecture_1_false_real (c0 : ℤ) (hc0 : c0 = 1 ∨ c0 = -1) :
    ¬ ∃ s : (Fin 4 → Fin 6) → ℝ,
        (∀ t, s t = 1 ∨ s t = -1) ∧
        ∀ (a : Fin 4 → Fin 5 → ℝ) (init : Fin 5 → ℝ),
          ∃ N : ℕ, ∀ n ≥ N,
            condSeq a init n =
              ∑ k : Fin 5,
                conjCoeff (c0 : ℝ) s a (4 * (k.val + 1)) *
                  condSeq a init (n - 4 * (k.val + 1)) := by
  rintro ⟨s, hs, hall⟩
  obtain ⟨N, hN⟩ := hall (fun i j => (instA i j : ℝ)) (fun j => (instInit j : ℝ))
  let δ : Fin 5 → ℝ := fun k =>
    conjCoeff (c0 : ℝ) s (fun i j => (instA i j : ℝ)) (4 * (k.val + 1)) - (trueC k : ℝ)
  have hvec : δ ᵥ* ((krylovMat N).map (Int.cast : ℤ → ℝ)) = 0 := by
    ext j
    have hge : 4 * (N + j.val) + 24 ≥ N := by omega
    have h1 := hN (4 * (N + j.val) + 24) hge
    rw [condSeq_map_intCast] at h1
    have h2 : (instQ (4 * (N + j.val) + 24) : ℝ) =
        ∑ k : Fin 5, (trueC k : ℝ) * (instQ (4 * (N + j.val) + 20 - 4 * k.val) : ℝ) := by
      have hq := instQ_decimated (N + j.val)
      have hcast := congrArg (Int.cast : ℤ → ℝ) hq
      simp only [Fin.sum_univ_five, trueC]
      have ha0 : 4 * (N + j.val) + 20 - 4 * (0 : Fin 5).val = 4 * (N + j.val) + 20 := by omega
      have ha1 : 4 * (N + j.val) + 20 - 4 * (1 : Fin 5).val = 4 * (N + j.val) + 16 := by omega
      have ha2 : 4 * (N + j.val) + 20 - 4 * (2 : Fin 5).val = 4 * (N + j.val) + 12 := by omega
      have ha3 : 4 * (N + j.val) + 20 - 4 * (3 : Fin 5).val = 4 * (N + j.val) + 8 := by omega
      have ha4 : 4 * (N + j.val) + 20 - 4 * (4 : Fin 5).val = 4 * (N + j.val) + 4 := by omega
      rw [ha0, ha1, ha2, ha3, ha4]
      push_cast at hcast ⊢
      exact hcast
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, krylovMat, Matrix.of_apply,
      Pi.zero_apply, δ, sub_mul, Finset.sum_sub_distrib]
    have hsum1 :
        (∑ k : Fin 5,
          conjCoeff (c0 : ℝ) s (fun i j => (instA i j : ℝ)) (4 * (k.val + 1)) *
            (instQ (4 * (N + j.val) + 20 - 4 * k.val) : ℝ)) =
        (instQ (4 * (N + j.val) + 24) : ℝ) := by
      change (instQ (4 * (N + j.val) + 24) : ℝ) = _ at h1
      rw [h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [condSeq_map_intCast]
      change _ = _ * (instQ (4 * (N + j.val) + 24 - 4 * (k.val + 1)) : ℝ)
      rw [show 4 * (N + j.val) + 24 - 4 * (k.val + 1) = 4 * (N + j.val) + 20 - 4 * k.val by omega]
    rw [hsum1, ← h2, sub_self]
  have hmul : (δ ᵥ* ((krylovMat N).map (Int.cast : ℤ → ℝ))) ᵥ*
      ((krylovMat N).map (Int.cast : ℤ → ℝ)).adjugate = 0 := by
    rw [hvec, Matrix.zero_vecMul]
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one] at hmul
  have hdet_ne : (((krylovMat N).map (Int.cast : ℤ → ℝ)).det) ≠ 0 := by
    have hmap : ((krylovMat N).map (Int.cast : ℤ → ℝ)).det = ((krylovMat N).det : ℝ) :=
      (RingHom.map_det (Int.castRingHom ℝ) (krylovMat N)).symm
    rw [hmap]
    exact Int.cast_ne_zero.mpr (det_krylovMat_ne_zero N)
  have hδ0 : δ 0 = 0 := by
    have h0 := congrFun hmul 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    exact (mul_eq_zero.mp h0).resolve_left hdet_ne
  have hA4_real : conjCoeff (c0 : ℝ) s (fun i j => (instA i j : ℝ)) 4 = (13596 : ℝ) := by
    have h := sub_eq_zero.mp hδ0
    simpa [δ, trueC] using h
  classical
  let sInt : (Fin 4 → Fin 6) → ℤ := fun t => if s t = 1 then 1 else -1
  have hsInt : ∀ t, sInt t = 1 ∨ sInt t = -1 := fun t => by
    dsimp only [sInt]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hsCast : ∀ t, (sInt t : ℝ) = s t := fun t => by
    dsimp only [sInt]
    rcases hs t with h1 | hm1
    · rw [if_pos h1, h1]; norm_num
    · rw [if_neg (by linarith), hm1]; norm_num
  have hcastCoeff :
      ((conjCoeff c0 sInt instA 4 : ℤ) : ℝ) =
        conjCoeff (c0 : ℝ) s (fun i j => (instA i j : ℝ)) 4 := by
    unfold conjCoeff
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hsCast t]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases hti : t i with ⟨v, hv⟩
    cases v with
    | zero => rfl
    | succ k => rfl
  have hA4_int : conjCoeff c0 sInt instA 4 = 13596 := by
    exact_mod_cast hcastCoeff.trans hA4_real
  have hdvd : (3 : ℤ) ∣ conjCoeff c0 sInt instA 4 := by
    rw [hA4_int]; decide
  exact conjCoeff_int_not_dvd_three c0 hc0 sInt hsInt hdvd

end GudaySahinConditionalSequences
