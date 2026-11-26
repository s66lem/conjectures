import Mathlib

/-!
# Proof of R. J. Mathar's OEIS A401159 Conjectures

We formalize and prove the general enumeration theorem for binary `n × m` matrices
with at most `k` ones in every row and every column (`m ≤ k` and `m = k + 1`),
and deduce both open conjectures stated by R. J. Mathar in OEIS A401159
(approved November 18, 2026):

* **Conjecture 1:** `T(n, 2) = A086601(n) = A000124(n)^2`.
* **Conjecture 2:** `T(n, 3) = 1 + n + 11n^2/4 + 13n^3/8 + n^4/8 + 3n^5/8 + n^6/8`.
-/

namespace MatharA401159

open Finset

/-- The `r`-th row sum of a binary `n × m` matrix `M`. -/
def rowSum {n m : ℕ} (M : Fin n → Fin m → Bool) (r : Fin n) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => M r c = true)).card

/-- The `c`-th column sum of a binary `n × m` matrix `M`. -/
def colSum {n m : ℕ} (M : Fin n → Fin m → Bool) (c : Fin m) : ℕ :=
  (Finset.univ.filter (fun r : Fin n => M r c = true)).card

/-- A binary `n × m` matrix is `k`-valid if every row sum and column sum is at most `k`. -/
def IsValidMatrix {n m : ℕ} (k : ℕ) (M : Fin n → Fin m → Bool) : Prop :=
  (∀ r : Fin n, rowSum M r ≤ k) ∧ (∀ c : Fin m, colSum M c ≤ k)

instance {n m : ℕ} (k : ℕ) (M : Fin n → Fin m → Bool) : Decidable (IsValidMatrix k M) := by
  unfold IsValidMatrix
  infer_instance

/-- `A(n, m, k)`: the number of `k`-valid binary `n × m` matrices. -/
def validMatrixCount (n m k : ℕ) : ℕ :=
  Fintype.card { M : Fin n → Fin m → Bool // IsValidMatrix k M }

/-- `T(n, m) = A(n, m, 2)`: the OEIS A401159 triangle. -/
def A401159 (n m : ℕ) : ℕ :=
  validMatrixCount n m 2

/-- `s(n, k) = ∑_{i=0}^{k} C(n, i)`: the number of subsets of `[n]` of size at most `k`. -/
def subsetCount (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), Nat.choose n i

/-- OEIS A000124: Lazy Caterer's sequence `n(n+1)/2 + 1`. -/
def A000124 (n : ℕ) : ℕ :=
  n * (n + 1) / 2 + 1

/-- OEIS A086601: `A000124(n)^2`. -/
def A086601 (n : ℕ) : ℕ :=
  (A000124 n) ^ 2

/-! ### Subset-counting lemmas -/

/-- Number of subsets of a finite set `W` of cardinality at most `t` equals `subsetCount W.card t`. -/
private lemma card_powerset_filter_le {α : Type*} [DecidableEq α] (W : Finset α) (t : ℕ) :
    (W.powerset.filter (fun V => V.card ≤ t)).card = subsetCount W.card t := by
  have hEq : W.powerset.filter (fun V => V.card ≤ t) =
      (Finset.range (t + 1)).biUnion (fun i => W.powersetCard i) := by
    ext V
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hVW, hcard⟩
      exact ⟨V.card, Nat.lt_succ_of_le hcard, hVW, rfl⟩
    · rintro ⟨i, hi, hVW, hcard⟩
      exact ⟨hVW, hcard ▸ Nat.lt_succ_iff.mp hi⟩
  rw [hEq, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, subsetCount]
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro V hVi hVj
    rw [mem_powersetCard] at hVi hVj
    exact hij (hVi.2.symm.trans hVj.2)

/-- Number of subsets of `Fin n` of size at most `k` equals `subsetCount n k`. -/
private lemma card_finset_card_le (n k : ℕ) :
    Fintype.card { U : Finset (Fin n) // U.card ≤ k } = subsetCount n k := by
  rw [Fintype.card_subtype]
  have hEq : (Finset.univ.filter (fun U : Finset (Fin n) => U.card ≤ k)) =
      (Finset.univ : Finset (Fin n)).powerset.filter (fun U => U.card ≤ k) := by
    ext U
    simp
  rw [hEq, card_powerset_filter_le, Finset.card_univ, Fintype.card_fin]

/-- Number of subsets `U` of `Fin n` containing `J` with `|U| ≤ k` (when `|J| ≤ k`). -/
private lemma card_finset_superset_card_le {n k : ℕ} (J : Finset (Fin n)) (hJ : J.card ≤ k) :
    Fintype.card { U : Finset (Fin n) // J ⊆ U ∧ U.card ≤ k } =
      subsetCount (n - J.card) (k - J.card) := by
  let e : { U : Finset (Fin n) // J ⊆ U ∧ U.card ≤ k } ≃
      { V : Finset (Fin n) // V ⊆ Jᶜ ∧ V.card ≤ k - J.card } :=
    { toFun := fun U =>
        ⟨U.1 \ J, by
          refine ⟨?_, ?_⟩
          · intro x hx
            rw [mem_sdiff] at hx
            exact mem_compl.mpr hx.2
          · rw [Finset.card_sdiff_of_subset U.2.1]
            exact Nat.sub_le_sub_right U.2.2 J.card⟩
      invFun := fun V =>
        ⟨J ∪ V.1, by
          have hdisj : Disjoint J V.1 := by
            rw [Finset.disjoint_left]
            intro x hxJ hxV
            exact (mem_compl.mp (V.2.1 hxV)) hxJ
          refine ⟨Finset.subset_union_left, ?_⟩
          rw [Finset.card_union_of_disjoint hdisj]
          omega⟩
      left_inv := fun U => by
        ext1
        exact Finset.union_sdiff_of_subset U.2.1
      right_inv := fun V => by
        ext1
        dsimp only
        have hdisj : Disjoint V.1 J := by
          rw [Finset.disjoint_left]
          intro x hxV hxJ
          exact (mem_compl.mp (V.2.1 hxV)) hxJ
        rw [Finset.union_sdiff_cancel_left hdisj.symm] }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  have hEq : (Finset.univ.filter (fun V : Finset (Fin n) => V ⊆ Jᶜ ∧ V.card ≤ k - J.card)) =
      (Jᶜ).powerset.filter (fun V => V.card ≤ k - J.card) := by
    ext V
    simp
  rw [hEq, card_powerset_filter_le, Finset.card_compl, Fintype.card_fin]

/-! ### Column-support bijection -/

/-- Bijection between binary `n × m` matrices and `m`-tuples of column supports in `Finset (Fin n)`. -/
private def matToColSupports (n m : ℕ) :
    (Fin n → Fin m → Bool) ≃ (Fin m → Finset (Fin n)) where
  toFun M c := Finset.univ.filter (fun r : Fin n => M r c = true)
  invFun S r c := decide (r ∈ S c)
  left_inv M := by
    funext r c
    simp
  right_inv S := by
    funext c
    ext r
    simp

private lemma colSum_eq_card_support {n m : ℕ} (M : Fin n → Fin m → Bool) (c : Fin m) :
    colSum M c = (matToColSupports n m M c).card := rfl

private lemma rowSum_eq_card_mem {n m : ℕ} (M : Fin n → Fin m → Bool) (r : Fin n) :
    rowSum M r = (Finset.univ.filter (fun c : Fin m => r ∈ matToColSupports n m M c)).card := by
  simp [rowSum, matToColSupports]

/-- Equivalence between `k`-valid matrices and `k`-valid column-support tuples. -/
private def validMatEquivTuples (n m k : ℕ) :
    { M : Fin n → Fin m → Bool // IsValidMatrix k M } ≃
      { S : Fin m → Finset (Fin n) //
          (∀ r : Fin n, (Finset.univ.filter (fun c : Fin m => r ∈ S c)).card ≤ k) ∧
          (∀ c : Fin m, (S c).card ≤ k) } where
  toFun M := ⟨matToColSupports n m M.1, by
    refine ⟨fun r => ?_, fun c => ?_⟩
    · rw [← rowSum_eq_card_mem]; exact M.2.1 r
    · rw [← colSum_eq_card_support]; exact M.2.2 c⟩
  invFun S := ⟨(matToColSupports n m).symm S.1, by
    refine ⟨fun r => ?_, fun c => ?_⟩
    · rw [rowSum_eq_card_mem, (matToColSupports n m).apply_symm_apply]; exact S.2.1 r
    · rw [colSum_eq_card_support, (matToColSupports n m).apply_symm_apply]; exact S.2.2 c⟩
  left_inv M := by ext1; exact (matToColSupports n m).symm_apply_apply M.1
  right_inv S := by ext1; exact (matToColSupports n m).apply_symm_apply S.1

/-! ### Part 1: `m ≤ k` -/

/-- **General Theorem (Part 1):** For `m ≤ k`, row sums are automatically `≤ k`,
so `A(n, m, k) = s(n, k)^m`. -/
theorem validMatrixCount_of_le (n m k : ℕ) (hm : m ≤ k) :
    validMatrixCount n m k = (subsetCount n k) ^ m := by
  unfold validMatrixCount
  rw [Fintype.card_congr (validMatEquivTuples n m k)]
  let e : { S : Fin m → Finset (Fin n) //
              (∀ r : Fin n, (Finset.univ.filter (fun c : Fin m => r ∈ S c)).card ≤ k) ∧
              (∀ c : Fin m, (S c).card ≤ k) } ≃
          (Fin m → { U : Finset (Fin n) // U.card ≤ k }) :=
    { toFun := fun S c => ⟨S.1 c, S.2.2 c⟩
      invFun := fun f =>
        ⟨fun c => (f c).1, by
          refine ⟨fun r => ?_, fun c => (f c).2⟩
          calc (Finset.univ.filter (fun c : Fin m => r ∈ (f c).1)).card
              ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
            _ = m := by simp
            _ ≤ k := hm⟩
      left_inv := fun S => by ext1; funext c; rfl
      right_inv := fun f => by funext c; rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, card_finset_card_le, Fintype.card_fin]

/-! ### Part 2: `m = k + 1` via Boolean-lattice inclusion–exclusion -/

/-- Alternating sum over subsets of a finite set `A` equals `1` if `A = ∅` and `0` otherwise. -/
private lemma sum_powerset_neg_one_pow {α : Type*} [DecidableEq α] (A : Finset α) :
    ∑ J ∈ A.powerset, (-1 : ℤ) ^ J.card = if A = ∅ then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha _ =>
    have hne : insert a s ≠ ∅ := Finset.insert_ne_empty a s
    rw [if_neg hne, Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · have hcancel : ∑ J ∈ s.powerset, (-1 : ℤ) ^ (insert a J).card =
            - ∑ J ∈ s.powerset, (-1 : ℤ) ^ J.card := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun J hJ => ?_)
          have haJ : a ∉ J := fun h => ha (Finset.mem_powerset.mp hJ h)
          rw [Finset.card_insert_of_notMem haJ, pow_succ]
          ring
        rw [hcancel]
        ring
      · intro J₁ hJ₁ J₂ hJ₂ hEq
        have ha₁ : a ∉ J₁ := fun h => ha (Finset.mem_powerset.mp hJ₁ h)
        have ha₂ : a ∉ J₂ := fun h => ha (Finset.mem_powerset.mp hJ₂ h)
        have := congrArg (fun X => X.erase a) hEq
        simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using this
    · rw [Finset.disjoint_left]
      intro X hX hXim
      rw [Finset.mem_image] at hXim
      rcases hXim with ⟨J, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hX (Finset.mem_insert_self a J))

/-- For `m = k + 1`, a row has sum `≤ k` iff not every column contains it. -/
private lemma row_le_iff_not_forall {n k : ℕ} (S : Fin (k + 1) → Finset (Fin n)) (r : Fin n) :
    (Finset.univ.filter (fun c : Fin (k + 1) => r ∈ S c)).card ≤ k ↔
      ¬ (∀ c : Fin (k + 1), r ∈ S c) := by
  constructor
  · intro hle hall
    have hEq : Finset.univ.filter (fun c : Fin (k + 1) => r ∈ S c) = Finset.univ := by
      ext c; simp [hall c]
    rw [hEq, Finset.card_univ, Fintype.card_fin] at hle
    omega
  · intro hnot
    push Not at hnot
    rcases hnot with ⟨c₀, hc₀⟩
    have hss : Finset.univ.filter (fun c : Fin (k + 1) => r ∈ S c) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_univ _, fun hEq => ?_⟩
      have hmem : c₀ ∈ Finset.univ.filter (fun c : Fin (k + 1) => r ∈ S c) := by
        rw [hEq]; exact Finset.mem_univ c₀
      exact hc₀ (Finset.mem_filter.mp hmem).2
    have hlt := Finset.card_lt_card hss
    rw [Finset.card_univ, Fintype.card_fin] at hlt
    omega

/-- **General Theorem (Part 2):** For all `n, k : ℕ`,
`A(n, k + 1, k) = ∑_{j=0}^{k} (-1)^j * C(n, j) * s(n - j, k - j)^(k + 1)`. -/
theorem validMatrixCount_succ (n k : ℕ) :
    (validMatrixCount n (k + 1) k : ℤ) =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ j * (Nat.choose n j : ℤ) * (subsetCount (n - j) (k - j) : ℤ) ^ (k + 1) := by
  let F := { U : Finset (Fin n) // U.card ≤ k }
  let badRows (f : Fin (k + 1) → F) : Finset (Fin n) :=
    Finset.univ.filter (fun r : Fin n => ∀ c : Fin (k + 1), r ∈ (f c).1)
  -- Express `validMatrixCount n (k + 1) k` as the number of `f : Fin (k + 1) → F` with `badRows f = ∅`
  have hcard_eq : validMatrixCount n (k + 1) k =
      (Finset.univ.filter (fun f : Fin (k + 1) → F => badRows f = ∅)).card := by
    unfold validMatrixCount
    rw [Fintype.card_congr (validMatEquivTuples n (k + 1) k), ← Fintype.card_subtype]
    let e : { S : Fin (k + 1) → Finset (Fin n) //
                (∀ r : Fin n, (Finset.univ.filter (fun c : Fin (k + 1) => r ∈ S c)).card ≤ k) ∧
                (∀ c : Fin (k + 1), (S c).card ≤ k) } ≃
            { f : Fin (k + 1) → F // badRows f = ∅ } :=
      { toFun := fun S =>
          ⟨fun c => ⟨S.1 c, S.2.2 c⟩, by
            ext r
            simp only [badRows, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
            exact (row_le_iff_not_forall S.1 r).mp (S.2.1 r)⟩
        invFun := fun f =>
          ⟨fun c => (f.1 c).1, by
            refine ⟨fun r => ?_, fun c => (f.1 c).2⟩
            rw [row_le_iff_not_forall]
            intro hall
            have hr : r ∈ badRows f.1 := by simp [badRows, hall]
            rw [f.2] at hr
            exact Finset.notMem_empty r hr⟩
        left_inv := fun S => by ext1; funext c; rfl
        right_inv := fun f => by ext1; funext c; rfl }
    exact Fintype.card_congr e
  -- Rewrite as a double sum via `sum_powerset_neg_one_pow`
  have hIE : (validMatrixCount n (k + 1) k : ℤ) =
      ∑ J : Finset (Fin n),
        (-1 : ℤ) ^ J.card *
          ((Finset.univ.filter (fun f : Fin (k + 1) → F => J ⊆ badRows f)).card : ℤ) := by
    rw [hcard_eq]
    have h1 : ((Finset.univ.filter (fun f : Fin (k + 1) → F => badRows f = ∅)).card : ℤ) =
        ∑ f : Fin (k + 1) → F, (if badRows f = ∅ then (1 : ℤ) else 0) := by
      simp [Finset.sum_boole]
    rw [h1]
    have h2 : ∀ f : Fin (k + 1) → F,
        (if badRows f = ∅ then (1 : ℤ) else 0) =
          ∑ J : Finset (Fin n), (if J ⊆ badRows f then (-1 : ℤ) ^ J.card else 0) := by
      intro f
      rw [← sum_powerset_neg_one_pow (badRows f)]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext J
      simp
    simp_rw [h2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Evaluate the inner count for each `J : Finset (Fin n)`
  have hinner : ∀ J : Finset (Fin n),
      ((Finset.univ.filter (fun f : Fin (k + 1) → F => J ⊆ badRows f)).card : ℤ) =
        if J.card ≤ k then (subsetCount (n - J.card) (k - J.card) : ℤ) ^ (k + 1) else 0 := by
    intro J
    split_ifs with hJ
    · have hEquiv : { f : Fin (k + 1) → F // J ⊆ badRows f } ≃
          (Fin (k + 1) → { U : Finset (Fin n) // J ⊆ U ∧ U.card ≤ k }) :=
        { toFun := fun f c =>
            ⟨(f.1 c).1, by
              refine ⟨?_, (f.1 c).2⟩
              intro r hr
              have hbad := f.2 hr
              exact (Finset.mem_filter.mp hbad).2 c⟩
          invFun := fun g =>
            ⟨fun c => ⟨(g c).1, (g c).2.2⟩, by
              intro r hr
              simp only [badRows, mem_filter, mem_univ, true_and]
              intro c
              exact (g c).2.1 hr⟩
          left_inv := fun f => by ext1; funext c; rfl
          right_inv := fun g => by funext c; rfl }
      rw [← Fintype.card_subtype, Fintype.card_congr hEquiv, Fintype.card_fun,
        card_finset_superset_card_le J hJ, Fintype.card_fin]
      push_cast
      rfl
    · have hempty : Finset.univ.filter (fun f : Fin (k + 1) → F => J ⊆ badRows f) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f hf
        have hsub := (Finset.mem_filter.mp hf).2
        have hsub0 : J ⊆ (f ⟨0, Nat.succ_pos k⟩).1 := fun r hr =>
          (Finset.mem_filter.mp (hsub hr)).2 ⟨0, Nat.succ_pos k⟩
        have hle := (Finset.card_le_card hsub0).trans (f ⟨0, Nat.succ_pos k⟩).2
        exact hJ hle
      rw [hempty, Finset.card_empty]
      rfl
  rw [hIE]
  simp_rw [hinner]
  -- Drop `J` with `J.card > k` and group by `j = J.card ∈ Finset.range (k + 1)`
  have hfilter : (∑ J : Finset (Fin n),
        (-1 : ℤ) ^ J.card *
          if J.card ≤ k then (subsetCount (n - J.card) (k - J.card) : ℤ) ^ (k + 1) else 0) =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card ≤ k),
        (-1 : ℤ) ^ J.card * (subsetCount (n - J.card) (k - J.card) : ℤ) ^ (k + 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    split_ifs <;> ring
  rw [hfilter]
  have hpart : (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card ≤ k) =
      (Finset.range (k + 1)).biUnion (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) := by
    ext J
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range, mem_powersetCard,
      subset_univ, true_and]
    constructor
    · intro hle; exact ⟨J.card, Nat.lt_succ_of_le hle, rfl⟩
    · rintro ⟨j, hj, hcard⟩; omega
  rw [hpart, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hconst : ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (-1 : ℤ) ^ J.card * (subsetCount (n - J.card) (k - J.card) : ℤ) ^ (k + 1) =
        ∑ _J ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (-1 : ℤ) ^ j * (subsetCount (n - j) (k - j) : ℤ) ^ (k + 1) := by
      refine Finset.sum_congr rfl (fun J hJ => ?_)
      rw [(Finset.mem_powersetCard.mp hJ).2]
    rw [hconst, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro J hJi hJj
    rw [mem_powersetCard] at hJi hJj
    exact hij (hJi.2.symm.trans hJj.2)

/-! ### Corollaries: both OEIS A401159 conjectures -/

private lemma subsetCount_two (n : ℕ) : subsetCount n 2 = A000124 n := by
  unfold subsetCount A000124
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_two_right]
  have h1 : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    apply Nat.mul_div_cancel'
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨t * (t + t - 1), by ring⟩
    · exact ⟨(2 * t + 1) * t, by rw [Nat.add_sub_cancel]; ring⟩
  have h2 : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    apply Nat.mul_div_cancel'
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨t * (t + t + 1), by ring⟩
    · exact ⟨(2 * t + 1) * (t + 1), by ring⟩
  have hmul : n * (n + 1) = n * (n - 1) + 2 * n := by
    cases n with
    | zero => simp
    | succ m => rw [Nat.add_sub_cancel]; ring
  omega

/-- **OEIS A401159, Conjecture 1:** `T(n, 2) = A086601(n) = A000124(n)^2` for all `n : ℕ`. -/
theorem mathar_A401159_conj1 (n : ℕ) : A401159 n 2 = A086601 n := by
  unfold A401159 A086601
  rw [validMatrixCount_of_le n 2 2 le_rfl, subsetCount_two]

/-- **OEIS A401159, Conjecture 2 (exact integer form):**
`8 * T(n, 3) = 8 + 8n + 22n^2 + 13n^3 + n^4 + 3n^5 + n^6` for all `n : ℕ`. -/
theorem mathar_A401159_conj2_nat (n : ℕ) :
    8 * A401159 n 3 =
      8 + 8 * n + 22 * n ^ 2 + 13 * n ^ 3 + n ^ 4 + 3 * n ^ 5 + n ^ 6 := by
  have hZ : (A401159 n 3 : ℤ) =
      (subsetCount n 2 : ℤ) ^ 3 - (n : ℤ) * (subsetCount (n - 1) 1 : ℤ) ^ 3 +
        (Nat.choose n 2 : ℤ) * (subsetCount (n - 2) 0 : ℤ) ^ 3 := by
    have h := validMatrixCount_succ n 2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, pow_zero, pow_one] at h
    norm_num at h
    unfold A401159
    linarith
  have hs0 : subsetCount (n - 2) 0 = 1 := by
    unfold subsetCount
    simp
  have hs1 : (n : ℤ) * (subsetCount (n - 1) 1 : ℤ) ^ 3 = (n : ℤ) ^ 4 := by
    rcases n with _ | m
    · simp
    · have hm : subsetCount m 1 = m + 1 := by
        unfold subsetCount
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        simp [Nat.add_comm]
      simp only [Nat.add_sub_cancel, hm]
      push_cast
      ring
  have hs2 : 2 * (subsetCount n 2 : ℤ) = (n : ℤ) ^ 2 + (n : ℤ) + 2 := by
    rw [subsetCount_two]
    unfold A000124
    have h2 : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
      apply Nat.mul_div_cancel'
      rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨t * (t + t + 1), by ring⟩
      · exact ⟨(2 * t + 1) * (t + 1), by ring⟩
    have h2Z : (2 : ℤ) * ((n * (n + 1) / 2 : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) + 1) := by
      exact_mod_cast h2
    push_cast
    linarith
  have hch2 : 2 * (Nat.choose n 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    rw [Nat.choose_two_right]
    have h2 : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
      apply Nat.mul_div_cancel'
      rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨t * (t + t - 1), by ring⟩
      · exact ⟨(2 * t + 1) * t, by rw [Nat.add_sub_cancel]; ring⟩
    rcases n with _ | m
    · simp
    · have h2Z : (2 : ℤ) * (((m + 1) * m / 2 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) * (m : ℤ) := by
        exact_mod_cast h2
      simp only [Nat.add_sub_cancel] at h2Z ⊢
      push_cast at h2Z ⊢
      linarith
  have h8Z : 8 * (A401159 n 3 : ℤ) =
      8 + 8 * (n : ℤ) + 22 * (n : ℤ) ^ 2 + 13 * (n : ℤ) ^ 3 +
        (n : ℤ) ^ 4 + 3 * (n : ℤ) ^ 5 + (n : ℤ) ^ 6 := by
    rw [hs0, hs1] at hZ
    have hcube : 8 * (subsetCount n 2 : ℤ) ^ 3 = ((n : ℤ) ^ 2 + (n : ℤ) + 2) ^ 3 := by
      calc 8 * (subsetCount n 2 : ℤ) ^ 3
          = (2 * (subsetCount n 2 : ℤ)) ^ 3 := by ring
        _ = ((n : ℤ) ^ 2 + (n : ℤ) + 2) ^ 3 := by rw [hs2]
    calc 8 * (A401159 n 3 : ℤ)
        = 8 * (subsetCount n 2 : ℤ) ^ 3 - 8 * (n : ℤ) ^ 4 +
            4 * (2 * (Nat.choose n 2 : ℤ)) := by rw [hZ]; ring
      _ = ((n : ℤ) ^ 2 + (n : ℤ) + 2) ^ 3 - 8 * (n : ℤ) ^ 4 +
            4 * ((n : ℤ) * ((n : ℤ) - 1)) := by rw [hcube, hch2]
      _ = 8 + 8 * (n : ℤ) + 22 * (n : ℤ) ^ 2 + 13 * (n : ℤ) ^ 3 +
            (n : ℤ) ^ 4 + 3 * (n : ℤ) ^ 5 + (n : ℤ) ^ 6 := by ring
  exact_mod_cast h8Z

/-- **OEIS A401159, Conjecture 2 (exact rational form from OEIS):**
`T(n, 3) = 1 + n + 11n^2/4 + 13n^3/8 + n^4/8 + 3n^5/8 + n^6/8` for all `n : ℕ`. -/
theorem mathar_A401159_conj2_rat (n : ℕ) :
    (A401159 n 3 : ℚ) =
      1 + (n : ℚ) + 11 * (n : ℚ) ^ 2 / 4 + 13 * (n : ℚ) ^ 3 / 8 +
        (n : ℚ) ^ 4 / 8 + 3 * (n : ℚ) ^ 5 / 8 + (n : ℚ) ^ 6 / 8 := by
  have hQ : (8 : ℚ) * (A401159 n 3 : ℚ) =
      8 + 8 * (n : ℚ) + 22 * (n : ℚ) ^ 2 + 13 * (n : ℚ) ^ 3 +
        (n : ℚ) ^ 4 + 3 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6 := by
    exact_mod_cast mathar_A401159_conj2_nat n
  linarith

end MatharA401159
