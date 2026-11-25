import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Codes of indexed forests (arXiv:2611.02210, Definition 2.4)

An indexed forest is stored as its code `(c₁, c₂, …)` with trailing zeros deleted; by
[Nadeau–Tewari, Prop. 3.3] the code determines the forest, which is rebuilt from the code in
`Structure.lean` by the right-to-left reconstruction of Definition 2.4.

This file contains the code-level operations used by the quasisymmetric divided differences:
terminal positions, deletion of a terminal node (`rem`), insertion of a cherry (`ins`), and the
set `IN F` of internal vertices, indexed by pairs `(i, t)` with `1 ≤ t ≤ cᵢ` (the `t`-th vertex
whose leftmost leaf is `i`).
-/

namespace QuasisymmetricBruhat

/-- Delete trailing zeros. -/
def trim : List ℕ → List ℕ
  | [] => []
  | a :: l =>
    match trim l with
    | [] => if a = 0 then [] else [a]
    | b :: t => a :: b :: t

/-- No trailing zero. -/
def NoTrail : List ℕ → Prop
  | [] => True
  | [a] => a ≠ 0
  | _ :: b :: t => NoTrail (b :: t)

lemma noTrail_tail {a : ℕ} {l : List ℕ} (h : NoTrail (a :: l)) : NoTrail l := by
  cases l with
  | nil => trivial
  | cons b t => exact h

lemma getD_trim (l : List ℕ) (i : ℕ) : (trim l).getD i 0 = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih
    simp only [trim]
    split
    · next h =>
      have hz : ∀ i, l.getD i 0 = 0 := fun i => by rw [← ih, h]; simp
      split_ifs with ha
      · cases i with
        | zero => simp [ha]
        | succ n => simp only [List.getD_cons_succ, List.getD_nil]; exact (hz n).symm
      · cases i with
        | zero => simp
        | succ n => simp only [List.getD_cons_succ, List.getD_nil]; exact (hz n).symm
    · next b t h =>
      cases i with
      | zero => simp
      | succ i => simp only [List.getD_cons_succ]; rw [← h, ih]

lemma noTrail_trim (l : List ℕ) : NoTrail (trim l) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    simp only [trim]
    split
    · split_ifs with ha
      · trivial
      · exact ha
    · next b t h => rw [h] at ih; exact ih

lemma length_trim_le (l : List ℕ) : (trim l).length ≤ l.length := by
  induction l with
  | nil => simp [trim]
  | cons a l ih =>
    simp only [trim]
    split
    · split_ifs <;> simp
    · next b t h => rw [h] at ih; simpa using ih

lemma exists_getD_ne_zero {a : ℕ} {l : List ℕ} (h : NoTrail (a :: l)) :
    (a :: l).getD l.length 0 ≠ 0 := by
  induction l generalizing a with
  | nil => simpa [NoTrail] using h
  | cons b t ih =>
    have := ih (show NoTrail (b :: t) from h)
    simpa using this

lemma eq_of_getD {l₁ l₂ : List ℕ} (h₁ : NoTrail l₁) (h₂ : NoTrail l₂)
    (h : ∀ i, l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t =>
      exfalso; apply exists_getD_ne_zero h₂; rw [← h]; simp
  | cons a t ih =>
    cases l₂ with
    | nil => exfalso; apply exists_getD_ne_zero h₁; rw [h]; simp
    | cons b s =>
      have hab : a = b := by simpa using h 0
      subst hab
      congr 1
      exact ih (noTrail_tail h₁) (noTrail_tail h₂) (fun i => by simpa using h (i + 1))

lemma getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i => simp only [List.getD_cons_succ, List.sum_cons]; have := ih i; omega

lemma getD_eq_zero_of_le (l : List ℕ) (i : ℕ) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- The list `[f 1, …, f n]`. -/
def ofFun (f : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map (fun i => f (i + 1))

lemma getD_ofFun (f : ℕ → ℕ) (n i : ℕ) :
    (ofFun f n).getD i 0 = if i < n then f (i + 1) else 0 := by
  rw [ofFun, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < n <;> simp [h]

lemma sum_range_getD (l : List ℕ) (n : ℕ) (h : l.length ≤ n) :
    ∑ i ∈ Finset.range n, l.getD i 0 = l.sum := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih m (by simp at h; omega)]; omega

/-- An indexed forest, stored as its code without trailing zeros (Definition 2.4). -/
structure Forest where
  code : List ℕ
  noTrail : NoTrail code
deriving DecidableEq

namespace Forest

/-- `F.c i = cᵢ(F)`, the number of internal vertices with leftmost leaf `i`; `F.c 0 = 0`. -/
def c (F : Forest) : ℕ → ℕ
  | 0 => 0
  | i + 1 => F.code.getD i 0

@[simp] lemma c_zero (F : Forest) : F.c 0 = 0 := rfl

lemma c_succ (F : Forest) (i : ℕ) : F.c (i + 1) = F.code.getD i 0 := rfl

/-- Length of the code. -/
def len (F : Forest) : ℕ := F.code.length

/-- Number of internal vertices (the rank `|IN(F)|`). -/
def size (F : Forest) : ℕ := F.code.sum

lemma c_eq_zero_of_lt (F : Forest) {i : ℕ} (h : F.len < i) : F.c i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact getD_eq_zero_of_le _ _ (by unfold len at h; omega)

lemma c_le_size (F : Forest) (i : ℕ) : F.c i ≤ F.size := by
  cases i with
  | zero => simp
  | succ i => exact getD_le_sum _ _

@[ext] lemma ext' {F G : Forest} (h : ∀ i, 1 ≤ i → F.c i = G.c i) : F = G := by
  obtain ⟨l₁, h₁⟩ := F
  obtain ⟨l₂, h₂⟩ := G
  have := eq_of_getD h₁ h₂ (fun i => h (i + 1) (by omega))
  subst this; rfl

/-- The forest with code `[f 1, …, f n]` (trailing zeros trimmed). -/
def ofCode (f : ℕ → ℕ) (n : ℕ) : Forest := ⟨trim (ofFun f n), noTrail_trim _⟩

lemma c_ofCode (f : ℕ → ℕ) (n i : ℕ) (hi : 1 ≤ i) :
    (ofCode f n).c i = if i ≤ n then f i else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [ofCode, c_succ, getD_trim, getD_ofFun]
  split_ifs <;> first | rfl | omega

lemma len_ofCode_le (f : ℕ → ℕ) (n : ℕ) : (ofCode f n).len ≤ n := by
  have := length_trim_le (ofFun f n)
  simpa [len, ofCode, ofFun] using this

/-- If `f` vanishes beyond `n` then `mk f n` has code `f`. -/
lemma c_ofCode_of (f : ℕ → ℕ) (n i : ℕ) (hi : 1 ≤ i) (hf : ∀ i, n < i → f i = 0) :
    (ofCode f n).c i = f i := by
  rw [c_ofCode f n i hi]; split_ifs with h
  · rfl
  · exact (hf i (by omega)).symm

/-- The empty forest `∅`. -/
def empty : Forest := ⟨[], trivial⟩

@[simp] lemma c_empty (i : ℕ) : empty.c i = 0 := by cases i <;> rfl

lemma eq_empty_iff_size (F : Forest) : F = empty ↔ F.size = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; ext i hi
    have := F.c_le_size i; simp; omega

/-- `j` is a terminal position of `F`: the vertex `(j, 1)` has the leaves `j, j+1` as children,
equivalently `cⱼ ≥ 1` and `cⱼ₊₁ = 0`. -/
def term (F : Forest) (j : ℕ) : Prop := 1 ≤ j ∧ 1 ≤ F.c j ∧ F.c (j + 1) = 0

instance (F : Forest) (j : ℕ) : Decidable (F.term j) := by unfold term; infer_instance

/-- Insert a cherry at leaf `j` (inverse of `rem j`). -/
def ins (j : ℕ) (F : Forest) : Forest :=
  ofCode (fun i => if i < j then F.c i else if i = j then F.c j + 1 else if i = j + 1 then 0
    else F.c (i - 1)) (F.len + j + 1)

/-- Delete the terminal node at `j`: `F/j` in NST notation. -/
def rem (j : ℕ) (F : Forest) : Forest :=
  ofCode (fun i => if i < j then F.c i else if i = j then F.c j - 1 else F.c (i + 1)) F.len

lemma c_ins (j : ℕ) (F : Forest) (i : ℕ) (hi : 1 ≤ i) :
    (ins j F).c i = if i < j then F.c i else if i = j then F.c j + 1 else if i = j + 1 then 0
      else F.c (i - 1) := by
  unfold ins
  rw [c_ofCode_of _ _ _ hi]
  intro k hk
  have : F.c (k - 1) = 0 := F.c_eq_zero_of_lt (by omega)
  split_ifs <;> omega

lemma c_rem (j : ℕ) (F : Forest) (i : ℕ) (hi : 1 ≤ i) :
    (rem j F).c i = if i < j then F.c i else if i = j then F.c j - 1 else F.c (i + 1) := by
  unfold rem
  rw [c_ofCode_of _ _ _ hi]
  intro k hk
  have h1 : F.c k = 0 := F.c_eq_zero_of_lt hk
  have h2 : F.c (k + 1) = 0 := F.c_eq_zero_of_lt (by omega)
  split_ifs <;> simp_all

lemma len_rem_le (j : ℕ) (F : Forest) : (rem j F).len ≤ F.len := len_ofCode_le _ _

lemma rem_ins {j : ℕ} (hj : 1 ≤ j) (F : Forest) : rem j (ins j F) = F := by
  ext i hi
  rw [c_rem _ _ _ hi]
  split_ifs with h1 h2
  · rw [c_ins _ _ _ hi, if_pos h1]
  · subst h2; rw [c_ins _ _ _ hi, if_neg (by omega), if_pos rfl]; omega
  · rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1

lemma term_ins {j : ℕ} (hj : 1 ≤ j) (F : Forest) : (ins j F).term j := by
  refine ⟨hj, ?_, ?_⟩
  · rw [c_ins _ _ _ hj, if_neg (by omega), if_pos rfl]; omega
  · rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

lemma ins_rem {F : Forest} {j : ℕ} (h : F.term j) : ins j (rem j F) = F := by
  obtain ⟨hj, h1, h2⟩ := h
  ext i hi
  rw [c_ins _ _ _ hi]
  split_ifs with a b d
  · rw [c_rem _ _ _ hi, if_pos a]
  · subst b; rw [c_rem _ _ _ hi, if_neg (by omega), if_pos rfl]; omega
  · subst d; exact h2.symm
  · rw [c_rem _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1; omega

lemma ins_injective {j : ℕ} (hj : 1 ≤ j) : Function.Injective (ins j) := by
  intro F G h
  rw [← rem_ins hj F, ← rem_ins hj G, h]

lemma rem_injOn {j : ℕ} {F G : Forest} (hF : F.term j) (hG : G.term j)
    (h : rem j F = rem j G) : F = G := by
  rw [← ins_rem hF, ← ins_rem hG, h]

/-! ### Internal vertices -/

/-- The internal vertices `IN(F)`: the pairs `(i, t)` with `1 ≤ t ≤ cᵢ`. The vertex `(i, t)` is
the `t`-th vertex (counted from the leaf upwards) whose leftmost leaf is `i`. -/
def IN (F : Forest) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 F.len ×ˢ Finset.Icc 1 F.size).filter (fun v => v.2 ≤ F.c v.1)

lemma mem_IN {F : Forest} {v : ℕ × ℕ} : v ∈ F.IN ↔ 1 ≤ v.1 ∧ 1 ≤ v.2 ∧ v.2 ≤ F.c v.1 := by
  unfold IN
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨a, -⟩, b, -⟩, c⟩; exact ⟨a, b, c⟩
  · rintro ⟨a, b, c⟩
    have h1 := F.c_le_size v.1
    have h2 : v.1 ≤ F.len := by
      by_contra h; have := F.c_eq_zero_of_lt (i := v.1) (by omega); omega
    exact ⟨⟨⟨a, h2⟩, b, by omega⟩, c⟩

/-- Reindexing of vertices from `F` to `ins j F`. -/
def psi (j : ℕ) (v : ℕ × ℕ) : ℕ × ℕ :=
  if v.1 < j then v else if v.1 = j then (j, v.2 + 1) else (v.1 + 1, v.2)

lemma psi_injective (j : ℕ) : Function.Injective (psi j) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [psi] at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> ext <;> simp <;> omega

lemma psi_ne (j : ℕ) (v : ℕ × ℕ) (hv : 1 ≤ v.2) : psi j v ≠ (j, 1) := by
  obtain ⟨a, b⟩ := v
  simp only [psi]; split_ifs <;> simp <;> omega

lemma IN_ins {j : ℕ} (hj : 1 ≤ j) (F : Forest) :
    (ins j F).IN = insert (j, 1) (F.IN.image (psi j)) := by
  ext ⟨a, b⟩
  simp only [mem_IN, Finset.mem_insert, Finset.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨ha, hb, hc⟩
    rw [c_ins _ _ _ ha] at hc
    split_ifs at hc with h1 h2 h3
    · exact Or.inr ⟨a, b, ⟨ha, hb, hc⟩, by simp [psi, h1]⟩
    · subst h2
      by_cases hb1 : b = 1
      · exact Or.inl ⟨rfl, hb1⟩
      · refine Or.inr ⟨a, b - 1, ⟨ha, by omega, by omega⟩, ?_⟩
        simp only [psi, lt_irrefl, if_false, if_true, Prod.mk.injEq]
        simp only [true_and]
        omega
    · omega
    · refine Or.inr ⟨a - 1, b, ⟨by omega, hb, hc⟩, ?_⟩
      simp only [psi]; rw [if_neg (by omega), if_neg (by omega)]; simp; omega
  · rintro (⟨rfl, rfl⟩ | ⟨x, y, ⟨hx, hy, hxy⟩, hp⟩)
    · refine ⟨hj, le_refl _, ?_⟩
      rw [c_ins _ _ _ hj, if_neg (by omega), if_pos rfl]; omega
    · simp only [psi] at hp
      split_ifs at hp with h1 h2 <;> simp only [Prod.mk.injEq] at hp <;>
        obtain ⟨rfl, rfl⟩ := hp
      · refine ⟨hx, hy, ?_⟩; rw [c_ins _ _ _ hx, if_pos h1]; exact hxy
      · subst h2; refine ⟨hx, by omega, ?_⟩
        rw [c_ins _ _ _ hx, if_neg (by omega), if_pos rfl]; omega
      · refine ⟨by omega, hy, ?_⟩
        rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simpa using hxy

lemma card_IN (F : Forest) : F.IN.card = F.size := by
  have : F.IN = Finset.map (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding
      ((Finset.Icc 1 F.len).sigma (fun i => Finset.Icc 1 (F.c i))) := by
    ext ⟨a, b⟩
    simp only [mem_IN, Finset.mem_map, Finset.mem_sigma, Finset.mem_Icc, Equiv.toEmbedding_apply,
      Sigma.exists, Equiv.sigmaEquivProd_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : a ≤ F.len := by
        by_contra h; have := F.c_eq_zero_of_lt (i := a) (by omega); omega
      exact ⟨a, b, ⟨⟨h1, this⟩, h2, h3⟩, rfl, rfl⟩
    · rintro ⟨x, y, ⟨⟨h1, -⟩, h2, h3⟩, rfl, rfl⟩; exact ⟨h1, h2, h3⟩
  rw [this, Finset.card_map, Finset.card_sigma]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, size,
    ← sum_range_getD F.code F.len le_rfl]
  apply Finset.sum_congr rfl; intro i _; rw [add_comm]; rfl

lemma size_ins {j : ℕ} (hj : 1 ≤ j) (F : Forest) : (ins j F).size = F.size + 1 := by
  rw [← card_IN, ← card_IN, IN_ins hj, Finset.card_insert_of_notMem, Finset.card_image_of_injective
    _ (psi_injective j)]
  simp only [Finset.mem_image, not_exists, not_and]
  intro v hv; exact psi_ne j v (mem_IN.1 hv).2.1

lemma size_rem {F : Forest} {j : ℕ} (h : F.term j) : (rem j F).size + 1 = F.size := by
  conv_rhs => rw [← ins_rem h]
  rw [size_ins h.1]

/-- The last position of a nonempty forest is terminal. -/
lemma term_len {F : Forest} (h : F ≠ empty) : F.term F.len := by
  obtain ⟨l, hl⟩ := F
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    refine ⟨by simp [len], ?_, ?_⟩
    · have := exists_getD_ne_zero hl
      simp only [len, List.length_cons, c_succ]; omega
    · exact c_eq_zero_of_lt _ (by omega)

lemma len_pos {F : Forest} (h : F ≠ empty) : 1 ≤ F.len := (term_len h).1

/-- The terminal positions, as a list. -/
def termList (F : Forest) : List ℕ := (List.range (F.len + 1)).filter (fun j => decide (F.term j))

lemma mem_termList {F : Forest} {j : ℕ} : j ∈ F.termList ↔ F.term j := by
  unfold termList
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨?_, h⟩
    by_contra hc; have := F.c_eq_zero_of_lt (i := j) (by omega); have := h.2.1; omega

end Forest

end QuasisymmetricBruhat
