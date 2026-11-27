import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Disproof of Hart–Rowley Conjecture 1.3 (Involution Length in Finite Coxeter Groups)

This file formalizes the refutation of Conjecture 1.3 of S. B. Hart and P. J. Rowley,
*A note on involution prefixes in Coxeter groups*, arXiv:2502.00777v1 (Archiv der Mathematik,
2026), for any `CoxeterSystem CoxeterMatrix.H₃ W` (rank 3, order 120).

Definitions (Hart–Rowley §1):
- `u` is a *prefix* of `w` if `cs.length u + cs.length (u⁻¹ * w) = cs.length w`.
- `a` is an *ancestor* of `w` if `a` is a prefix of `w`, `orderOf a = 2`, and `a` has
  strictly maximal Coxeter length among all involution prefixes of `w`.
- A Coxeter group has the *ancestor property* (Conjecture 1.2, proved in general by
  Gaetz–Gao, arXiv:2610.22857) if every `w ≠ 1` has a unique ancestor.
- The *involution length* `ilen(w)` is the number of factors in the greedy ancestor
  decomposition `w = a₁ a₂ ⋯ aₖ` where `a₁` is the ancestor of `w`, and `a₂ ⋯ aₖ` is the
  ancestor decomposition of `a₁⁻¹ * w` (with `ilen(1) = 0`).
- **Conjecture 1.3** asserts `ilen(w) ≤ rank(W)` for every `w` in a finite Coxeter group `W`.

We prove unconditionally for every `CoxeterSystem CoxeterMatrix.H₃ W`:
1. `H3Equiv`: `W` has exactly 120 elements, parametrized bijectively by 120 canonical reduced
   words `canonWord : Fin 120 → List (Fin 3)` via `cs.wordProd`, with exact Coxeter length
   `cs.length (cs.wordProd (canonWord k)) = (canonWord k).length`.
2. `H3_hasAncestorProperty`: every `w ≠ 1` in `W` has a unique ancestor (Conjecture 1.2 holds
   for `H₃`, making `ilen` completely unconditional on `H₃`).
3. `hart_rowley_conj_1_3_false_H3`: the element `w₁ = s₁ s₂ s₀ s₁ s₂ s₁ s₀` (length 7) has
   ancestor decomposition `(s₁ s₀ s₂ s₁)(s₂)(s₁)(s₀)` and involution length `4 > 3 = rank(H₃)`
   (and similarly `w₂ = s₁ s₂ s₁ s₂ s₀ s₁ s₂` has decomposition `(s₁ s₂ s₁)(s₀ s₂)(s₁)(s₂)`
   and involution length `4 > 3`). Thus Hart–Rowley Conjecture 1.3 is false.
-/

namespace HartRowleyCoxeterInvolutionLength

open CoxeterSystem

/-! ### Balanced binary lookup tree and pure-Bool bounded quantifiers for fast kernel reduction -/

private inductive LookupTree (α : Type)
  | leaf (v : α)
  | node (l r : LookupTree α)

private def LookupTree.get {α : Type} : LookupTree α → ℕ → α
  | .leaf v, _ => v
  | .node l r, n => if n % 2 == 0 then l.get (n / 2) else r.get (n / 2)

private def allPow2 : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, lo, f => f lo
  | d + 1, lo, f => allPow2 d lo f && allPow2 d (lo + 2 ^ d) f

private lemma allPow2_spec :
    ∀ (d lo : ℕ) (f : ℕ → Bool), allPow2 d lo f = true → ∀ k, lo ≤ k → k < lo + 2 ^ d → f k = true
  | 0, lo, f, h, k, hlo, hhi => by
    have hk : k = lo := by omega
    rw [hk]; exact h
  | d + 1, lo, f, h, k, hlo, hhi => by
    simp only [allPow2, Bool.and_eq_true] at h
    by_cases hlt : k < lo + 2 ^ d
    · exact allPow2_spec d lo f h.1 k hlo hlt
    · exact allPow2_spec d (lo + 2 ^ d) f h.2 k (by omega) (by rw [Nat.pow_succ] at hhi; omega)

private def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  allPow2 7 0 fun k => if k < n then f k else true

private lemma allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true)
    (k : ℕ) (hk : k < n) (hn : n ≤ 128 := by omega) :
    f k = true := by
  have h1 := allPow2_spec 7 0 (fun k => if k < n then f k else true) h k (Nat.zero_le k) (by omega)
  simpa [hk] using h1

/-! ### Definitions matching Hart–Rowley (arXiv:2502.00777v1, §1) -/

/-- `u` is a prefix of `w` in `(W, cs)` if `ℓ(u) + ℓ(u⁻¹ * w) = ℓ(w)`. -/
def IsPrefix {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (u w : W) : Prop :=
  cs.length u + cs.length (u⁻¹ * w) = cs.length w

/-- `a` is the unique longest involution prefix (the *ancestor*) of `w`. -/
def IsUniqueAncestor {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (a w : W) : Prop :=
  IsPrefix cs a w ∧ orderOf a = 2 ∧
    ∀ u : W, IsPrefix cs u w → orderOf u = 2 → u ≠ a → cs.length u < cs.length a

/-- A Coxeter system has the *ancestor property* if every non-identity element has a unique
longest involution prefix. -/
def HasAncestorProperty {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) : Prop :=
  ∀ w : W, w ≠ 1 → ∃ a : W, IsUniqueAncestor cs a w

/-- Inductive relation `HasInvolutionLength cs w k`: `w` has ancestor decomposition of length `k`
(Hart–Rowley §1: `ilen(1) = 0`, and for `w ≠ 1` with unique ancestor `a`,
`ilen(w) = 1 + ilen(a⁻¹ * w)`). -/
inductive HasInvolutionLength {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) : W → ℕ → Prop
  | one : HasInvolutionLength cs 1 0
  | step {w a : W} {k : ℕ} :
      w ≠ 1 → IsUniqueAncestor cs a w →
      HasInvolutionLength cs (a⁻¹ * w) k →
      HasInvolutionLength cs w (k + 1)

/-- The unique ancestor of `w`, when it exists, is unique. -/
lemma isUniqueAncestor_unique {B W : Type*} [Group W] {M : CoxeterMatrix B}
    {cs : CoxeterSystem M W} {a₁ a₂ w : W}
    (h₁ : IsUniqueAncestor cs a₁ w) (h₂ : IsUniqueAncestor cs a₂ w) : a₁ = a₂ := by
  by_contra hne
  have hlt1 := h₁.2.2 a₂ h₂.1 h₂.2.1 (Ne.symm hne)
  have hlt2 := h₂.2.2 a₁ h₁.1 h₁.2.1 hne
  omega

/-- `HasInvolutionLength` is functional (every element has at most one involution length). -/
lemma hasInvolutionLength_unique {B W : Type*} [Group W] {M : CoxeterMatrix B}
    {cs : CoxeterSystem M W} {w : W} {k₁ k₂ : ℕ}
    (h₁ : HasInvolutionLength cs w k₁) (h₂ : HasInvolutionLength cs w k₂) : k₁ = k₂ := by
  induction h₁ generalizing k₂ with
  | one =>
    cases h₂ with
    | one => rfl
    | step hne _ _ => exact False.elim (hne rfl)
  | step hne ha hrest ih =>
    cases h₂ with
    | one => exact False.elim (hne rfl)
    | step _ ha' hrest' =>
      have hEq := isUniqueAncestor_unique ha ha'
      subst hEq
      exact congrArg (· + 1) (ih hrest')

/-! ### Explicit root-system permutation representation of `H₃` on 30 roots -/

private def genTree0 : LookupTree ℕ := (.node (.node (.node (.node (.node (.leaf 15) (.leaf 18)) (.node (.leaf 5) (.leaf 26))) (.node (.node (.leaf 6) (.leaf 23)) (.node (.leaf 13) (.leaf 27)))) (.node (.node (.node (.leaf 2) (.leaf 16)) (.node (.leaf 7) (.leaf 24))) (.node (.node (.leaf 4) (.leaf 25)) (.node (.leaf 14) (.leaf 0))))) (.node (.node (.node (.node (.leaf 3) (.leaf 17)) (.node (.leaf 11) (.leaf 22))) (.node (.node (.leaf 8) (.leaf 19)) (.node (.leaf 12) (.leaf 29)))) (.node (.node (.node (.leaf 1) (.leaf 21)) (.node (.leaf 9) (.leaf 28))) (.node (.node (.leaf 10) (.leaf 20)) (.node (.leaf 0) (.leaf 0))))))
private def genTree1 : LookupTree ℕ := (.node (.node (.node (.node (.node (.leaf 3) (.leaf 1)) (.node (.leaf 8) (.leaf 21))) (.node (.node (.leaf 7) (.leaf 17)) (.node (.leaf 12) (.leaf 29)))) (.node (.node (.node (.leaf 5) (.leaf 15)) (.node (.leaf 11) (.leaf 25))) (.node (.node (.leaf 9) (.leaf 19)) (.node (.leaf 13) (.leaf 0))))) (.node (.node (.node (.node (.leaf 16) (.leaf 20)) (.node (.leaf 6) (.leaf 26))) (.node (.node (.leaf 2) (.leaf 24)) (.node (.leaf 14) (.leaf 28)))) (.node (.node (.node (.leaf 0) (.leaf 22)) (.node (.leaf 10) (.leaf 27))) (.node (.node (.leaf 4) (.leaf 23)) (.node (.leaf 18) (.leaf 0))))))
private def genTree2 : LookupTree ℕ := (.node (.node (.node (.node (.node (.leaf 0) (.leaf 19)) (.node (.leaf 10) (.leaf 27))) (.node (.node (.leaf 1) (.leaf 22)) (.node (.leaf 9) (.leaf 26)))) (.node (.node (.node (.leaf 17) (.leaf 21)) (.node (.leaf 8) (.leaf 28))) (.node (.node (.leaf 3) (.leaf 20)) (.node (.leaf 14) (.leaf 0))))) (.node (.node (.node (.node (.leaf 4) (.leaf 2)) (.node (.leaf 12) (.leaf 23))) (.node (.node (.leaf 7) (.leaf 18)) (.node (.leaf 11) (.leaf 29)))) (.node (.node (.node (.leaf 6) (.leaf 16)) (.node (.leaf 13) (.leaf 24))) (.node (.node (.leaf 5) (.leaf 25)) (.node (.leaf 15) (.leaf 0))))))

private def genNat : Fin 3 → ℕ → ℕ
  | 0, r => genTree0.get r
  | 1, r => genTree1.get r
  | 2, r => genTree2.get r

private lemma genNat_lt_bool :
    allBelow 30 (fun r => decide (genNat 0 r < 30) && decide (genNat 1 r < 30) && decide (genNat 2 r < 30)) = true := by
  decide

private lemma genNat_lt (i : Fin 3) {r : ℕ} (hr : r < 30) : genNat i r < 30 := by
  have h := allBelow_spec genNat_lt_bool r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

private def genFun (i : Fin 3) (r : Fin 30) : Fin 30 :=
  ⟨genNat i r.val, genNat_lt i r.isLt⟩

private lemma genNat_involutive_bool :
    allBelow 30 (fun r => (genNat 0 (genNat 0 r) == r) &&
      (genNat 1 (genNat 1 r) == r) && (genNat 2 (genNat 2 r) == r)) = true := by
  decide

private lemma genFun_involutive (i : Fin 3) : Function.Involutive (genFun i) := by
  intro r
  have h := allBelow_spec genNat_involutive_bool r.val r.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  apply Fin.ext
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

/-- Each generator as an involution in `Equiv.Perm (Fin 30)`. -/
def genPerm (i : Fin 3) : Equiv.Perm (Fin 30) where
  toFun := genFun i
  invFun := genFun i
  left_inv := genFun_involutive i
  right_inv := genFun_involutive i

private def applyWordNat : List (Fin 3) → ℕ → ℕ
  | [], r => r
  | i :: ω, r => genNat i (applyWordNat ω r)

private lemma genPerm_pow_apply (i j : Fin 3) (m : ℕ) (r : Fin 30) :
    (((genPerm i * genPerm j) ^ m) r).val =
      (Nat.iterate (fun x => genNat i (genNat j x)) m) r.val := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply]
    exact ih ((genPerm i * genPerm j) r)

private lemma genPerm_rel_bool :
    allBelow 30 (fun r =>
      (Nat.iterate (fun x => genNat 0 (genNat 1 x)) 3 r == r) &&
      (Nat.iterate (fun x => genNat 1 (genNat 0 x)) 3 r == r) &&
      (Nat.iterate (fun x => genNat 0 (genNat 2 x)) 2 r == r) &&
      (Nat.iterate (fun x => genNat 2 (genNat 0 x)) 2 r == r) &&
      (Nat.iterate (fun x => genNat 1 (genNat 2 x)) 5 r == r) &&
      (Nat.iterate (fun x => genNat 2 (genNat 1 x)) 5 r == r)) = true := by
  decide

private lemma genPerm_isLiftable : CoxeterMatrix.IsLiftable CoxeterMatrix.H₃ genPerm := by
  intro i j
  ext r
  rw [genPerm_pow_apply]
  have h := allBelow_spec genPerm_rel_bool r.val r.isLt
  have hinv := allBelow_spec genNat_involutive_bool r.val r.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at h hinv
  fin_cases i <;> fin_cases j
  · change Nat.iterate (fun x => genNat 0 (genNat 0 x)) (CoxeterMatrix.H₃ 0 0) r.val = r.val
    rw [show CoxeterMatrix.H₃ 0 0 = 1 by decide]; exact hinv.1.1
  · change Nat.iterate (fun x => genNat 0 (genNat 1 x)) (CoxeterMatrix.H₃ 0 1) r.val = r.val
    rw [show CoxeterMatrix.H₃ 0 1 = 3 by decide]; exact h.1.1.1.1.1
  · change Nat.iterate (fun x => genNat 0 (genNat 2 x)) (CoxeterMatrix.H₃ 0 2) r.val = r.val
    rw [show CoxeterMatrix.H₃ 0 2 = 2 by decide]; exact h.1.1.1.2
  · change Nat.iterate (fun x => genNat 1 (genNat 0 x)) (CoxeterMatrix.H₃ 1 0) r.val = r.val
    rw [show CoxeterMatrix.H₃ 1 0 = 3 by decide]; exact h.1.1.1.1.2
  · change Nat.iterate (fun x => genNat 1 (genNat 1 x)) (CoxeterMatrix.H₃ 1 1) r.val = r.val
    rw [show CoxeterMatrix.H₃ 1 1 = 1 by decide]; exact hinv.1.2
  · change Nat.iterate (fun x => genNat 1 (genNat 2 x)) (CoxeterMatrix.H₃ 1 2) r.val = r.val
    rw [show CoxeterMatrix.H₃ 1 2 = 5 by decide]; exact h.1.2
  · change Nat.iterate (fun x => genNat 2 (genNat 0 x)) (CoxeterMatrix.H₃ 2 0) r.val = r.val
    rw [show CoxeterMatrix.H₃ 2 0 = 2 by decide]; exact h.1.1.2
  · change Nat.iterate (fun x => genNat 2 (genNat 1 x)) (CoxeterMatrix.H₃ 2 1) r.val = r.val
    rw [show CoxeterMatrix.H₃ 2 1 = 5 by decide]; exact h.2
  · change Nat.iterate (fun x => genNat 2 (genNat 2 x)) (CoxeterMatrix.H₃ 2 2) r.val = r.val
    rw [show CoxeterMatrix.H₃ 2 2 = 1 by decide]; exact hinv.2

/-- Group homomorphism `φ : W →* Equiv.Perm (Fin 30)` from any `CoxeterSystem CoxeterMatrix.H₃ W`. -/
def rootRep {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    W →* Equiv.Perm (Fin 30) :=
  cs.lift ⟨genPerm, genPerm_isLiftable⟩

/-- Product of generator permutations along a word `ω : List (Fin 3)`. -/
def wordPerm : List (Fin 3) → Equiv.Perm (Fin 30)
  | [] => 1
  | i :: ω => genPerm i * wordPerm ω

lemma wordPerm_apply_val (ω : List (Fin 3)) (r : Fin 30) :
    (wordPerm ω r).val = applyWordNat ω r.val := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [wordPerm, Equiv.Perm.mul_apply, applyWordNat, ← ih]
    rfl

lemma rootRep_wordProd {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (ω : List (Fin 3)) :
    rootRep cs (cs.wordProd ω) = wordPerm ω := by
  induction ω with
  | nil => simp [wordProd, wordPerm]
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, ih, wordPerm]
    congr 1
    exact cs.lift_apply_simple genPerm_isLiftable i

/-- Number of positive roots (`0..14`) sent to negative roots (`15..29`) by `p`. -/
def invCount (p : Equiv.Perm (Fin 30)) : ℕ :=
  (Finset.univ.filter fun r : Fin 15 => 15 ≤ (p ⟨r.val, by omega⟩).val).card

private def countNegBelow (ω : List (Fin 3)) : ℕ → ℕ
  | 0 => 0
  | n + 1 => countNegBelow ω n + if 15 ≤ applyWordNat ω n then 1 else 0

private def invCountWord (ω : List (Fin 3)) : ℕ :=
  countNegBelow ω 15

private lemma countNegBelow_eq (ω : List (Fin 3)) (n : ℕ) (hn : n ≤ 15) :
    countNegBelow ω n =
      (Finset.univ.filter fun r : Fin 15 => r.val < n ∧ 15 ≤ applyWordNat ω r.val).card := by
  induction n with
  | zero =>
    simp [countNegBelow]
  | succ m ih =>
    have hm : m < 15 := by omega
    rw [countNegBelow, ih (by omega)]
    let m15 : Fin 15 := ⟨m, hm⟩
    by_cases hcond : 15 ≤ applyWordNat ω m
    · rw [if_pos hcond]
      have hset :
          (Finset.univ.filter fun r : Fin 15 => r.val < m + 1 ∧ 15 ≤ applyWordNat ω r.val) =
          insert m15 (Finset.univ.filter fun r : Fin 15 => r.val < m ∧ 15 ≤ applyWordNat ω r.val) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hlt, hge⟩
          by_cases hrm : r.val = m
          · left; exact Fin.ext hrm
          · right; exact ⟨by omega, hge⟩
        · rintro (rfl | ⟨hlt, hge⟩)
          · exact ⟨by simp [m15], hcond⟩
          · exact ⟨by omega, hge⟩
      have hnotmem : m15 ∉ Finset.univ.filter (fun r : Fin 15 => r.val < m ∧ 15 ≤ applyWordNat ω r.val) := by
        simp [m15]
      rw [hset, Finset.card_insert_of_notMem hnotmem]
    · rw [if_neg hcond, Nat.add_zero]
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hlt, hge⟩
        exact ⟨by omega, hge⟩
      · rintro ⟨hlt, hge⟩
        refine ⟨?_, hge⟩
        by_contra hgeM
        have hrm : r.val = m := by omega
        exact hcond (hrm ▸ hge)

private lemma invCount_wordPerm_eq (ω : List (Fin 3)) :
    invCount (wordPerm ω) = invCountWord ω := by
  unfold invCount invCountWord
  rw [countNegBelow_eq ω 15 (le_refl 15)]
  congr 1
  ext r
  simp [wordPerm_apply_val]

private lemma genFun_pos_map_bool :
    allBelow 15 (fun r =>
      (decide (r == 0) || decide (genNat 0 r < 15)) &&
      (decide (r == 1) || decide (genNat 1 r < 15)) &&
      (decide (r == 2) || decide (genNat 2 r < 15))) = true := by
  decide

private lemma genFun_pos_map (i : Fin 3) (r : Fin 15) (hne : r.val ≠ i.val) :
    (genFun i ⟨r.val, by omega⟩).val < 15 := by
  have h := allBelow_spec genFun_pos_map_bool r.val r.isLt
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  change genNat i r.val < 15
  fin_cases i
  · exact h.1.1.resolve_left hne
  · exact h.1.2.resolve_left hne
  · exact h.2.resolve_left hne

private lemma invCount_mul_genPerm_le (p : Equiv.Perm (Fin 30)) (i : Fin 3) :
    invCount (p * genPerm i) ≤ invCount p + 1 := by
  unfold invCount
  set S := Finset.univ.filter fun r : Fin 15 => 15 ≤ ((p * genPerm i) ⟨r.val, by omega⟩).val
  set T := Finset.univ.filter fun r : Fin 15 => 15 ≤ (p ⟨r.val, by omega⟩).val
  let i15 : Fin 15 := ⟨i.val, by omega⟩
  have hsub : S ⊆ insert i15 (S.erase i15) := by
    intro r hr
    by_cases hri : r = i15
    · rw [hri]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hri, hr⟩)
  have hcard1 : S.card ≤ (S.erase i15).card + 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  let f : Fin 15 → Fin 15 := fun r =>
    if h : r.val ≠ i.val then ⟨(genFun i ⟨r.val, by omega⟩).val, genFun_pos_map i r h⟩ else i15
  have hf_maps : Set.MapsTo f (S.erase i15 : Set (Fin 15)) (T : Set (Fin 15)) := by
    intro r hr
    rw [Finset.mem_coe, Finset.mem_erase] at hr
    have hne : r.val ≠ i.val := fun h => hr.1 (Fin.ext h)
    have hrS := (Finset.mem_filter.mp hr.2).2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hfin : (⟨(f r).val, by omega⟩ : Fin 30) = genFun i ⟨r.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [f]
      rw [dif_pos hne]
    rw [hfin]
    exact hrS
  have hf_inj : Set.InjOn f (S.erase i15 : Set (Fin 15)) := by
    intro r₁ hr₁ r₂ hr₂ heq
    rw [Finset.mem_coe, Finset.mem_erase] at hr₁ hr₂
    have hne₁ : r₁.val ≠ i.val := fun h => hr₁.1 (Fin.ext h)
    have hne₂ : r₂.val ≠ i.val := fun h => hr₂.1 (Fin.ext h)
    have hvalNat : (genFun i ⟨r₁.val, by omega⟩).val = (genFun i ⟨r₂.val, by omega⟩).val := by
      have h1 : (f r₁).val = (genFun i ⟨r₁.val, by omega⟩).val := by
        dsimp only [f]; rw [dif_pos hne₁]
      have h2 : (f r₂).val = (genFun i ⟨r₂.val, by omega⟩).val := by
        dsimp only [f]; rw [dif_pos hne₂]
      rw [← h1, ← h2, heq]
    have hfin : (⟨r₁.val, by omega⟩ : Fin 30) = ⟨r₂.val, by omega⟩ :=
      (genFun_involutive i).injective (Fin.ext hvalNat)
    exact Fin.ext (congrArg (Fin.val : Fin 30 → ℕ) hfin)
  have hcard2 : (S.erase i15).card ≤ T.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  omega

lemma invCount_wordPerm_le (ω : List (Fin 3)) : invCount (wordPerm ω) ≤ ω.length := by
  induction ω using List.reverseRecOn with
  | nil =>
    rw [invCount_wordPerm_eq]
    have : invCountWord [] = 0 := by decide
    simp [this]
  | append_singleton ω i ih =>
    have hmul : wordPerm (ω ++ [i]) = wordPerm ω * genPerm i := by
      clear ih
      induction ω with
      | nil => simp [wordPerm]
      | cons a l ihl => simp [wordPerm, ihl, mul_assoc]
    rw [hmul, List.length_append, List.length_singleton]
    exact (invCount_mul_genPerm_le (wordPerm ω) i).trans (Nat.add_le_add_right ih 1)

lemma invCount_rootRep_le_length {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (w : W) : invCount (rootRep cs w) ≤ cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [hω, rootRep_wordProd]
  exact invCount_wordPerm_le ω

/-! ### 120 canonical reduced words, O(log n) lookup trees, and reflection-checked braid certificates -/

private def canonTree : LookupTree (List (Fin 3)) :=
  (.node (.node (.node (.node (.node (.node (.node (.leaf []) (.leaf [0, 2, 1, 0, 2, 1, 0, 2])) (.node (.leaf [1, 2, 1, 0, 2]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 2, 1, 0]))) (.node (.node (.leaf [0, 1, 0, 2]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2, 1])) (.node (.leaf [0, 1, 0, 2, 1, 0, 2]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1])))) (.node (.node (.node (.leaf [2, 1]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0])) (.node (.leaf [0, 2, 1, 0, 2, 1]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]))) (.node (.node (.leaf [2, 1, 2, 1]) (.leaf [0, 2, 1, 0, 2, 1, 0, 2, 1, 0])) (.node (.leaf [1, 2, 1, 0, 2, 1, 0]) (.leaf []))))) (.node (.node (.node (.node (.leaf [0, 1]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2])) (.node (.leaf [0, 1, 0, 2, 1, 0]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]))) (.node (.node (.leaf [1, 0, 2, 1]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2])) (.node (.leaf [0, 2, 1, 0, 2, 1, 0]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1])))) (.node (.node (.node (.leaf [1, 0, 2]) (.leaf [0, 2, 1, 0, 2, 1, 0, 2, 1])) (.node (.leaf [1, 2, 1, 0, 2, 1]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]))) (.node (.node (.leaf [0, 2, 1, 0, 2]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2, 1, 0])) (.node (.leaf [0, 1, 0, 2, 1, 0, 2, 1]) (.leaf [])))))) (.node (.node (.node (.node (.node (.leaf [1]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0])) (.node (.leaf [2, 1, 0, 2, 1]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2, 1, 2]))) (.node (.node (.leaf [0, 2, 1, 0]) (.leaf [2, 1, 0, 2, 1, 0, 2, 1, 0])) (.node (.leaf [0, 1, 2, 1, 0, 2, 1]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1])))) (.node (.node (.node (.leaf [0, 1, 2]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2])) (.node (.leaf [1, 0, 2, 1, 0, 2]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]))) (.node (.node (.leaf [0, 1, 2, 1, 0]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2, 1])) (.node (.leaf [2, 1, 0, 2, 1, 0, 2]) (.leaf []))))) (.node (.node (.node (.node (.leaf [1, 0]) (.leaf [2, 1, 0, 2, 1, 0, 2, 1])) (.node (.leaf [0, 1, 2, 1, 0, 2]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]))) (.node (.node (.leaf [1, 2, 1, 2]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2, 1])) (.node (.leaf [1, 0, 2, 1, 0, 2, 1]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2])))) (.node (.node (.node (.leaf [2, 1, 0]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2])) (.node (.leaf [2, 1, 0, 2, 1, 0]) (.leaf [2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2]))) (.node (.node (.leaf [1, 0, 2, 1, 0]) (.leaf [2, 1, 0, 2, 1, 0, 2, 1, 0, 2])) (.node (.leaf [0, 1, 2, 1, 0, 2, 1, 0]) (.leaf []))))))) (.node (.node (.node (.node (.node (.node (.leaf [0]) (.leaf [0, 2, 1, 0, 2, 1, 2, 1])) (.node (.leaf [1, 2, 1, 2, 1]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2, 1, 0]))) (.node (.node (.leaf [0, 1, 2, 1]) (.leaf [1, 2, 1, 0, 2, 1, 2, 1, 0])) (.node (.leaf [0, 1, 0, 2, 1, 2, 1]) (.leaf [0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2])))) (.node (.node (.node (.leaf [0, 1, 0]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 2])) (.node (.leaf [0, 2, 1, 2, 1, 0]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2]))) (.node (.node (.leaf [0, 1, 0, 2, 1]) (.leaf [0, 2, 1, 0, 2, 1, 0, 2, 1, 2])) (.node (.leaf [1, 2, 1, 0, 2, 1, 2]) (.leaf []))))) (.node (.node (.node (.node (.leaf [0, 2]) (.leaf [1, 2, 1, 0, 2, 1, 2, 1])) (.node (.leaf [0, 1, 0, 2, 1, 2]) (.leaf [1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2]))) (.node (.node (.leaf [1, 2, 1, 0]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 2, 1])) (.node (.leaf [0, 2, 1, 0, 2, 1, 2]) (.leaf [0, 1, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2])))) (.node (.node (.node (.leaf [1, 2, 1]) (.leaf [0, 2, 1, 0, 2, 1, 2, 1, 0])) (.node (.leaf [1, 2, 1, 2, 1, 0]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1]))) (.node (.node (.leaf [0, 2, 1, 2, 1]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2, 1, 2])) (.node (.leaf [0, 1, 0, 2, 1, 2, 1, 0]) (.leaf [])))))) (.node (.node (.node (.node (.node (.leaf [2]) (.leaf [1, 0, 2, 1, 0, 2, 1, 2])) (.node (.leaf [2, 1, 2, 1, 0]) (.leaf [0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]))) (.node (.node (.leaf [0, 2, 1, 2]) (.leaf [2, 1, 0, 2, 1, 0, 2, 1, 2])) (.node (.leaf [0, 1, 2, 1, 2, 1, 0]) (.leaf [1, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2])))) (.node (.node (.node (.leaf [0, 2, 1]) (.leaf [0, 1, 2, 1, 0, 2, 1, 2, 1])) (.node (.leaf [1, 0, 2, 1, 2, 1]) (.leaf [0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1]))) (.node (.node (.leaf [0, 1, 2, 1, 2]) (.leaf [1, 0, 2, 1, 0, 2, 1, 2, 1, 0])) (.node (.leaf [2, 1, 0, 2, 1, 2, 1]) (.leaf []))))) (.node (.node (.node (.node (.leaf [1, 2]) (.leaf [2, 1, 0, 2, 1, 2, 1, 0])) (.node (.leaf [0, 1, 2, 1, 2, 1]) (.leaf [2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1]))) (.node (.node (.leaf [2, 1, 0, 2]) (.leaf [0, 1, 2, 1, 0, 2, 1, 2, 1, 0])) (.node (.leaf [1, 0, 2, 1, 2, 1, 0]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2])))) (.node (.node (.node (.leaf [2, 1, 2]) (.leaf [1, 0, 2, 1, 0, 2, 1, 2, 1])) (.node (.leaf [2, 1, 0, 2, 1, 2]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]))) (.node (.node (.leaf [1, 0, 2, 1, 2]) (.leaf [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1])) (.node (.leaf [0, 1, 2, 1, 0, 2, 1, 2]) (.leaf []))))))))

/-- Canonical reduced word for each of the 120 elements of `H₃`. -/
def canonWord (k : Fin 120) : List (Fin 3) :=
  canonTree.get k.val

private def lenTree : LookupTree ℕ :=
  (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 8)) (.node (.leaf 5) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 9)) (.node (.leaf 7) (.leaf 13)))) (.node (.node (.node (.leaf 2) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 4) (.leaf 10)) (.node (.leaf 7) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2) (.leaf 8)) (.node (.leaf 6) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 10)) (.node (.leaf 7) (.leaf 14)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 8) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 1) (.leaf 8)) (.node (.leaf 5) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 9)) (.node (.leaf 7) (.leaf 13)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 7) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2) (.leaf 8)) (.node (.leaf 6) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 10)) (.node (.leaf 7) (.leaf 14)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 8) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 8)) (.node (.leaf 5) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 9)) (.node (.leaf 7) (.leaf 13)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 7) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2) (.leaf 8)) (.node (.leaf 6) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 10)) (.node (.leaf 7) (.leaf 14)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 8) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 1) (.leaf 8)) (.node (.leaf 5) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 9)) (.node (.leaf 7) (.leaf 13)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 7) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2) (.leaf 8)) (.node (.leaf 6) (.leaf 11))) (.node (.node (.leaf 4) (.leaf 10)) (.node (.leaf 7) (.leaf 15)))) (.node (.node (.node (.leaf 3) (.leaf 9)) (.node (.leaf 6) (.leaf 13))) (.node (.node (.leaf 5) (.leaf 11)) (.node (.leaf 8) (.leaf 0))))))))

private def lenFastNat (k : ℕ) : ℕ :=
  lenTree.get k

private def lenFast (k : Fin 120) : ℕ :=
  lenTree.get k.val

private lemma lenFast_eq_bool :
    allBelow 120 (fun k => lenFastNat k == (canonTree.get k).length) = true := by
  decide

private lemma lenFast_eq (k : Fin 120) : lenFast k = (canonWord k).length := by
  have h := allBelow_spec lenFast_eq_bool k.val k.isLt
  exact beq_iff_eq.mp h

private def stepTree : LookupTree (ℕ × ℕ × ℕ) :=
  (.node (.node (.node (.node (.node (.node (.node (.leaf (1, 2, 3)) (.leaf (53, 76, 52))) (.node (.leaf (22, 44, 21)) (.leaf (85, 104, 87)))) (.node (.node (.leaf (10, 25, 9)) (.leaf (92, 68, 93))) (.node (.leaf (37, 60, 36)) (.leaf (107, 106, 117))))) (.node (.node (.node (.leaf (14, 3, 15)) (.leaf (60, 61, 84))) (.node (.leaf (52, 28, 53)) (.leaf (95, 96, 111)))) (.node (.node (.leaf (35, 15, 33)) (.leaf (76, 77, 99))) (.node (.leaf (44, 45, 68)) (.leaf (0, 0, 0)))))) (.node (.node (.node (.node (.leaf (9, 1, 10)) (.leaf (57, 80, 56))) (.node (.leaf (25, 26, 48)) (.leaf (90, 91, 108)))) (.node (.node (.leaf (30, 12, 31)) (.leaf (73, 95, 72))) (.node (.leaf (40, 41, 64)) (.leaf (114, 111, 119))))) (.node (.node (.node (.leaf (7, 20, 6)) (.leaf (88, 64, 89))) (.node (.leaf (56, 32, 57)) (.leaf (101, 114, 100)))) (.node (.node (.leaf (19, 40, 18)) (.leaf (80, 81, 102))) (.node (.leaf (72, 48, 73)) (.leaf (0, 0, 0))))))) (.node (.node (.node (.node (.node (.leaf (6, 0, 7)) (.leaf (54, 55, 78))) (.node (.leaf (46, 23, 47)) (.leaf (106, 89, 86)))) (.node (.node (.leaf (11, 14, 28)) (.leaf (70, 71, 94))) (.node (.leaf (62, 38, 63)) (.leaf (116, 108, 118))))) (.node (.node (.node (.leaf (16, 17, 4)) (.leaf (63, 86, 62))) (.node (.leaf (31, 54, 30)) (.leaf (98, 112, 97)))) (.node (.node (.leaf (17, 36, 38)) (.leaf (100, 78, 101))) (.node (.leaf (47, 70, 46)) (.leaf (0, 0, 0)))))) (.node (.node (.node (.node (.leaf (2, 9, 12)) (.leaf (82, 58, 83))) (.node (.leaf (27, 50, 26)) (.leaf (93, 109, 92)))) (.node (.node (.leaf (32, 33, 13)) (.leaf (97, 74, 98))) (.node (.leaf (66, 42, 67)) (.leaf (119, 115, 114))))) (.node (.node (.node (.leaf (8, 18, 23)) (.leaf (67, 90, 66))) (.node (.leaf (34, 35, 58)) (.leaf (115, 113, 103)))) (.node (.node (.leaf (20, 21, 42)) (.leaf (83, 103, 82))) (.node (.leaf (50, 51, 74)) (.leaf (0, 0, 0)))))))) (.node (.node (.node (.node (.node (.node (.leaf (0, 4, 5)) (.leaf (77, 53, 59))) (.node (.leaf (45, 22, 24)) (.leaf (86, 87, 106)))) (.node (.node (.leaf (26, 10, 27)) (.leaf (69, 92, 91))) (.node (.leaf (61, 37, 43)) (.leaf (117, 110, 107))))) (.node (.node (.node (.leaf (4, 6, 16)) (.leaf (84, 85, 60))) (.node (.leaf (29, 52, 51)) (.leaf (111, 101, 95)))) (.node (.node (.leaf (36, 16, 37)) (.leaf (99, 98, 76))) (.node (.leaf (68, 69, 44)) (.leaf (0, 0, 0)))))) (.node (.node (.node (.node (.leaf (3, 11, 1)) (.leaf (81, 57, 79))) (.node (.leaf (48, 49, 25)) (.leaf (108, 105, 90)))) (.node (.node (.leaf (13, 30, 32)) (.leaf (96, 73, 75))) (.node (.leaf (64, 65, 40)) (.leaf (113, 119, 112))))) (.node (.node (.node (.leaf (21, 7, 22)) (.leaf (65, 88, 71))) (.node (.leaf (33, 56, 35)) (.leaf (103, 102, 115)))) (.node (.node (.leaf (41, 19, 39)) (.leaf (102, 83, 80))) (.node (.leaf (49, 72, 55)) (.leaf (0, 0, 0))))))) (.node (.node (.node (.node (.node (.leaf (5, 8, 0)) (.leaf (78, 79, 54))) (.node (.leaf (24, 46, 45)) (.leaf (89, 107, 88)))) (.node (.node (.leaf (28, 29, 11)) (.leaf (94, 93, 70))) (.node (.leaf (39, 62, 41)) (.leaf (110, 118, 109))))) (.node (.node (.node (.leaf (18, 5, 19)) (.leaf (87, 63, 85))) (.node (.leaf (55, 31, 49)) (.leaf (112, 99, 113)))) (.node (.node (.leaf (38, 39, 17)) (.leaf (79, 100, 81))) (.node (.leaf (71, 47, 65)) (.leaf (0, 0, 0)))))) (.node (.node (.node (.node (.leaf (12, 13, 2)) (.leaf (59, 82, 77))) (.node (.leaf (51, 27, 29)) (.leaf (109, 94, 110)))) (.node (.node (.leaf (15, 34, 14)) (.leaf (75, 97, 96))) (.node (.leaf (43, 66, 61)) (.leaf (118, 117, 116))))) (.node (.node (.node (.leaf (23, 24, 8)) (.leaf (91, 67, 69))) (.node (.leaf (58, 59, 34)) (.leaf (105, 116, 104)))) (.node (.node (.leaf (42, 43, 20)) (.leaf (104, 84, 105))) (.node (.leaf (74, 75, 50)) (.leaf (0, 0, 0)))))))))

private def stepNat (k : ℕ) (i : Fin 3) : ℕ :=
  let t := stepTree.get k
  match i with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2

private lemma stepNat_lt_bool :
    allBelow 120 (fun k =>
      decide (stepNat k 0 < 120) && decide (stepNat k 1 < 120) && decide (stepNat k 2 < 120)) = true := by
  decide

private lemma stepNat_lt {k : ℕ} (hk : k < 120) (i : Fin 3) : stepNat k i < 120 := by
  have h := allBelow_spec stepNat_lt_bool k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

/-- Right multiplication table `k * s_i` on `Fin 120`. -/
def stepTable (k : Fin 120) (i : Fin 3) : Fin 120 :=
  ⟨stepNat k.val i, stepNat_lt k.isLt i⟩

/-- Rewrite rule catalog for `H₃` defining relations. -/
private def ruleLhs : Fin 9 → List (Fin 3)
  | 0 => [0, 0]
  | 1 => [1, 1]
  | 2 => [2, 2]
  | 3 => [0, 2]
  | 4 => [2, 0]
  | 5 => [0, 1, 0]
  | 6 => [1, 0, 1]
  | 7 => [1, 2, 1, 2, 1]
  | 8 => [2, 1, 2, 1, 2]

private def ruleRhs : Fin 9 → List (Fin 3)
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => [2, 0]
  | 4 => [0, 2]
  | 5 => [1, 0, 1]
  | 6 => [0, 1, 0]
  | 7 => [2, 1, 2, 1, 2]
  | 8 => [1, 2, 1, 2, 1]

private lemma inv_simple_eq {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (i : Fin 3) : (cs.simple i)⁻¹ = cs.simple i :=
  inv_eq_of_mul_eq_one_right (cs.simple_mul_simple_self i)

private lemma wordProd_rule_eq {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (r : Fin 9) : cs.wordProd (ruleLhs r) = cs.wordProd (ruleRhs r) := by
  have hinv := inv_simple_eq cs
  have h02 : cs.simple 0 * cs.simple 2 = cs.simple 2 * cs.simple 0 := by
    have h := cs.simple_mul_simple_pow 0 2
    have hm : CoxeterMatrix.H₃ 0 2 = 2 := by decide
    rw [hm, pow_two] at h
    have h1 : cs.simple 0 * cs.simple 2 = (cs.simple 0 * cs.simple 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left h
    rw [h1, mul_inv_rev, hinv, hinv]
  have h01 : cs.simple 0 * (cs.simple 1 * cs.simple 0) =
      cs.simple 1 * (cs.simple 0 * cs.simple 1) := by
    have h := cs.simple_mul_simple_pow 0 1
    have hm : CoxeterMatrix.H₃ 0 1 = 3 := by decide
    rw [hm, pow_succ, pow_two] at h
    calc
      cs.simple 0 * (cs.simple 1 * cs.simple 0)
          = ((cs.simple 0 * cs.simple 1) * (cs.simple 0 * cs.simple 1) * (cs.simple 0 * cs.simple 1)) *
              (cs.simple 1 * (cs.simple 0 * cs.simple 1)) := by
            simp only [mul_assoc, cs.simple_mul_simple_cancel_left, cs.simple_mul_simple_self, mul_one]
      _ = 1 * (cs.simple 1 * (cs.simple 0 * cs.simple 1)) := by rw [h]
      _ = cs.simple 1 * (cs.simple 0 * cs.simple 1) := one_mul _
  have h12 : cs.simple 1 * (cs.simple 2 * (cs.simple 1 * (cs.simple 2 * cs.simple 1))) =
      cs.simple 2 * (cs.simple 1 * (cs.simple 2 * (cs.simple 1 * cs.simple 2))) := by
    have h := cs.simple_mul_simple_pow 1 2
    have hm : CoxeterMatrix.H₃ 1 2 = 5 := by decide
    rw [hm] at h
    have hexp : (cs.simple 1 * cs.simple 2) ^ 5 =
        (cs.simple 1 * cs.simple 2) * (cs.simple 1 * cs.simple 2) * (cs.simple 1 * cs.simple 2) *
          (cs.simple 1 * cs.simple 2) * (cs.simple 1 * cs.simple 2) := by
      simp [pow_succ, pow_zero]
    rw [hexp] at h
    calc
      cs.simple 1 * (cs.simple 2 * (cs.simple 1 * (cs.simple 2 * cs.simple 1)))
          = ((cs.simple 1 * cs.simple 2) * (cs.simple 1 * cs.simple 2) * (cs.simple 1 * cs.simple 2) *
              (cs.simple 1 * cs.simple 2) * (cs.simple 1 * cs.simple 2)) *
              (cs.simple 2 * (cs.simple 1 * (cs.simple 2 * (cs.simple 1 * cs.simple 2)))) := by
            simp only [mul_assoc, cs.simple_mul_simple_cancel_left, cs.simple_mul_simple_self, mul_one]
      _ = 1 * (cs.simple 2 * (cs.simple 1 * (cs.simple 2 * (cs.simple 1 * cs.simple 2)))) := by rw [h]
      _ = cs.simple 2 * (cs.simple 1 * (cs.simple 2 * (cs.simple 1 * cs.simple 2))) := one_mul _
  fin_cases r <;> simp only [ruleLhs, ruleRhs, wordProd, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, cs.simple_mul_simple_self]
  · exact h02
  · exact h02.symm
  · exact h01
  · exact h01.symm
  · exact h12
  · exact h12.symm

private def applyStep (w : List (Fin 3)) (pos : ℕ) (r : Fin 9) : Option (List (Fin 3)) :=
  if (w.drop pos).take (ruleLhs r).length == ruleLhs r then
    some (w.take pos ++ ruleRhs r ++ (w.drop pos).drop (ruleLhs r).length)
  else
    none

private def applyCert : List (Fin 3) → List (ℕ × Fin 9) → Option (List (Fin 3))
  | w, [] => some w
  | w, (pos, r) :: rest =>
    match applyStep w pos r with
    | some w' => applyCert w' rest
    | none => none

private lemma applyStep_sound {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    {w w' : List (Fin 3)} {pos : ℕ} {r : Fin 9}
    (h : applyStep w pos r = some w') :
    cs.wordProd w = cs.wordProd w' := by
  dsimp only [applyStep] at h
  split_ifs at h with hcond
  simp only [Option.some.injEq] at h
  subst h
  have hEq : (w.drop pos).take (ruleLhs r).length = ruleLhs r := eq_of_beq hcond
  have hw : w = w.take pos ++ ((w.drop pos).take (ruleLhs r).length ++ (w.drop pos).drop (ruleLhs r).length) := by
    rw [List.take_append_drop, List.take_append_drop]
  conv_lhs => rw [hw, hEq]
  rw [cs.wordProd_append, cs.wordProd_append, wordProd_rule_eq cs r,
    ← cs.wordProd_append, ← cs.wordProd_append, List.append_assoc]

private lemma applyCert_sound {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    {w w' : List (Fin 3)} {steps : List (ℕ × Fin 9)}
    (h : applyCert w steps = some w') :
    cs.wordProd w = cs.wordProd w' := by
  induction steps generalizing w with
  | nil =>
    simp only [applyCert, Option.some.injEq] at h
    rw [h]
  | cons st rest ih =>
    rcases st with ⟨pos, r⟩
    simp only [applyCert] at h
    cases hst : applyStep w pos r with
    | none => rw [hst] at h; simp at h
    | some w₁ =>
      rw [hst] at h
      exact (applyStep_sound cs hst).trans (ih h)

private def certTree :
    LookupTree (List (ℕ × Fin 9) × List (ℕ × Fin 9) × List (ℕ × Fin 9)) :=
  (.node (.node (.node (.node (.node (.node (.node (.leaf ([], [], [])) (.leaf ([(6, 3), (7, 0)], [], [(7, 2)]))) (.node (.leaf ([(3, 3), (4, 0)], [], [(4, 2)])) (.leaf ([(10, 0)], [(9, 6), (8, 4)], [(2, 3), (10, 3), (3, 5), (5, 7), (9, 2)])))) (.node (.node (.leaf ([(2, 3), (3, 0)], [], [(3, 2)])) (.leaf ([], [(8, 1)], []))) (.node (.leaf ([(5, 3), (6, 0)], [], [(6, 2)])) (.leaf ([(4, 3), (10, 3), (5, 5), (11, 5), (1, 7), (5, 4), (7, 7), (6, 2), (9, 4), (4, 6), (3, 4)], [(12, 1)], []))))) (.node (.node (.node (.leaf ([], [(1, 1)], [])) (.leaf ([(8, 0)], [(5, 3), (6, 5), (8, 1)], []))) (.node (.leaf ([], [(5, 1)], [])) (.leaf ([(11, 0)], [(8, 3), (9, 5), (11, 1)], [])))) (.node (.node (.leaf ([], [(3, 1)], [(0, 8)])) (.leaf ([(9, 0)], [(6, 3), (7, 5), (9, 1)], []))) (.node (.leaf ([(6, 0)], [(3, 3), (4, 5), (6, 1)], [])) (.leaf ([], [], [])))))) (.node (.node (.node (.node (.leaf ([], [(1, 1)], [])) (.leaf ([(6, 3), (7, 0)], [], [(7, 2)]))) (.node (.leaf ([(5, 0)], [(2, 3), (3, 5), (5, 1)], [])) (.leaf ([(10, 0)], [(7, 3), (8, 5), (10, 1)], [])))) (.node (.node (.leaf ([], [(3, 1)], [])) (.leaf ([(8, 3), (9, 0)], [], [(9, 2)]))) (.node (.leaf ([(6, 0)], [(3, 3), (4, 5), (6, 1)], [])) (.leaf ([(5, 3), (11, 3), (0, 5), (6, 5), (12, 5), (2, 7), (6, 4), (8, 7), (7, 2), (10, 4), (5, 6), (4, 4)], [(13, 1)], []))))) (.node (.node (.node (.leaf ([(1, 3), (2, 0)], [], [(2, 2)])) (.leaf ([], [(8, 1)], []))) (.node (.leaf ([], [(5, 1)], [])) (.leaf ([(10, 3), (11, 0)], [], [(11, 2)])))) (.node (.node (.leaf ([(3, 3), (4, 0)], [], [(4, 2)])) (.leaf ([(9, 0)], [(6, 3), (7, 5), (9, 1)], []))) (.node (.leaf ([], [(7, 1)], [])) (.leaf ([], [], []))))))) (.node (.node (.node (.node (.node (.leaf ([], [(0, 1)], [])) (.leaf ([(7, 0)], [(4, 3), (5, 5), (7, 1)], []))) (.node (.leaf ([], [(4, 1)], [])) (.leaf ([(10, 4)], [(4, 3), (5, 5), (1, 7), (5, 4), (7, 7), (6, 2), (4, 6), (3, 4)], [(10, 2)])))) (.node (.node (.leaf ([(3, 0)], [(0, 3), (1, 5), (3, 1)], [])) (.leaf ([(8, 0)], [(5, 3), (6, 5), (8, 1)], []))) (.node (.leaf ([], [(6, 1)], [])) (.leaf ([(4, 3), (10, 3), (5, 5), (11, 5), (7, 7), (6, 3), (11, 4), (2, 8), (0, 6), (6, 6), (5, 4)], [(12, 1)], []))))) (.node (.node (.node (.leaf ([(2, 4)], [], [(2, 2)])) (.leaf ([(7, 3), (8, 0)], [], [(8, 2)]))) (.node (.leaf ([(4, 3), (5, 0)], [], [(5, 2)])) (.leaf ([(10, 3), (11, 0)], [], [(11, 2)])))) (.node (.node (.leaf ([(4, 0)], [(3, 6), (2, 4)], [])) (.leaf ([], [(9, 1)], []))) (.node (.leaf ([(5, 3), (6, 0)], [], [(6, 2)])) (.leaf ([], [], [])))))) (.node (.node (.node (.node (.leaf ([(1, 0)], [(0, 6)], [])) (.leaf ([], [(7, 1)], []))) (.node (.leaf ([(4, 3), (5, 0)], [], [(5, 2)])) (.leaf ([(9, 3), (10, 0)], [], [(10, 2)])))) (.node (.node (.leaf ([(3, 4)], [], [(3, 2)])) (.leaf ([], [(9, 1)], []))) (.node (.leaf ([], [(6, 1)], [])) (.leaf ([(4, 3), (10, 3), (13, 4), (5, 5), (11, 5), (7, 7), (6, 3), (11, 4), (2, 8), (0, 6), (6, 6), (5, 4)], [(1, 3), (7, 3), (2, 5), (8, 5), (4, 7), (8, 4), (10, 7), (9, 2), (7, 6), (6, 4)], [(13, 2)]))))) (.node (.node (.node (.leaf ([(2, 0)], [(1, 6), (0, 4)], [])) (.leaf ([(7, 3), (8, 0)], [], [(8, 2)]))) (.node (.leaf ([(5, 0)], [(2, 3), (3, 5), (5, 1)], [])) (.leaf ([(2, 3), (8, 3), (11, 4), (3, 5), (9, 5), (5, 7), (4, 3), (9, 4), (0, 8), (4, 6), (3, 4)], [(5, 3), (6, 5), (8, 7), (7, 3), (3, 8), (1, 6), (0, 4), (7, 6), (6, 4)], [(11, 2)])))) (.node (.node (.leaf ([(4, 0)], [(1, 3), (2, 5), (4, 1)], [])) (.leaf ([(8, 3), (9, 0)], [], [(9, 2)]))) (.node (.leaf ([(7, 0)], [(4, 3), (5, 5), (7, 1)], [])) (.leaf ([], [], [])))))))) (.node (.node (.node (.node (.node (.node (.leaf ([(0, 0)], [], [])) (.leaf ([], [(7, 1)], [(0, 3), (1, 5), (3, 7), (7, 2)]))) (.node (.leaf ([], [(4, 1)], [(0, 7), (4, 2)])) (.leaf ([(10, 0)], [(7, 3), (8, 5), (10, 1)], [])))) (.node (.node (.leaf ([], [(3, 1)], [])) (.leaf ([(8, 0)], [(7, 6), (6, 4)], [(8, 3), (4, 8), (2, 6), (1, 4)]))) (.node (.leaf ([], [(6, 1)], [(0, 5), (2, 7), (6, 2)])) (.leaf ([(3, 3), (9, 3), (12, 4), (4, 5), (10, 5), (6, 7), (5, 3), (10, 4), (1, 8), (5, 6), (4, 4)], [(0, 3), (6, 3), (1, 5), (7, 5), (3, 7), (7, 4), (9, 7), (8, 2), (6, 6), (5, 4)], [(12, 2)]))))) (.node (.node (.node (.leaf ([(2, 0)], [(0, 5), (2, 1)], [])) (.leaf ([(8, 4)], [], [(8, 2)]))) (.node (.leaf ([(5, 0)], [(4, 6), (3, 4)], [(5, 3), (1, 8)])) (.leaf ([(11, 4)], [(5, 3), (0, 5), (6, 5), (2, 7), (6, 4), (8, 7), (7, 2), (5, 6), (4, 4)], [(11, 2)])))) (.node (.node (.leaf ([], [(4, 1)], [])) (.leaf ([(9, 4)], [(3, 3), (4, 5), (6, 7), (5, 3), (1, 8), (5, 6), (4, 4)], [(9, 2)]))) (.node (.leaf ([(6, 4)], [], [(6, 2)])) (.leaf ([], [], [])))))) (.node (.node (.node (.node (.leaf ([(0, 3), (1, 0)], [], [(1, 2)])) (.leaf ([], [(7, 1)], [(4, 8), (2, 6), (1, 4)]))) (.node (.leaf ([(5, 4)], [], [(5, 2)])) (.leaf ([(10, 4)], [(4, 3), (5, 5), (7, 7), (6, 3), (2, 8), (0, 6), (6, 6), (5, 4)], [(10, 2)])))) (.node (.node (.leaf ([(3, 0)], [(2, 6), (1, 4)], [])) (.leaf ([], [(9, 1)], [(2, 3), (3, 5), (5, 7), (9, 2)]))) (.node (.leaf ([(6, 4)], [], [(6, 2)])) (.leaf ([(4, 3), (10, 3), (13, 4), (5, 5), (11, 5), (1, 7), (5, 4), (7, 7), (6, 2), (9, 4), (4, 6), (3, 4)], [(7, 3), (8, 5), (10, 7), (9, 3), (5, 8), (3, 6), (2, 4), (9, 6), (8, 4)], [(13, 2)]))))) (.node (.node (.node (.leaf ([], [(2, 1)], [])) (.leaf ([(8, 0)], [(7, 6), (6, 4)], [(0, 3), (8, 3), (1, 5), (3, 7), (7, 2)]))) (.node (.leaf ([(5, 0)], [(4, 6), (3, 4)], [(5, 3), (0, 7), (4, 2)])) (.leaf ([(3, 3), (9, 3), (4, 5), (10, 5), (0, 7), (4, 4), (6, 7), (5, 2), (8, 4), (3, 6), (2, 4)], [(11, 1)], [])))) (.node (.node (.leaf ([], [(4, 1)], [(1, 8)])) (.leaf ([(9, 4)], [(3, 3), (4, 5), (0, 7), (4, 4), (6, 7), (5, 2), (3, 6), (2, 4)], [(9, 2)]))) (.node (.leaf ([(7, 0)], [(6, 6), (5, 4)], [(7, 3), (0, 5), (2, 7), (6, 2)])) (.leaf ([], [], []))))))) (.node (.node (.node (.node (.node (.leaf ([(0, 4)], [], [(0, 2)])) (.leaf ([(7, 4)], [], [(7, 2)]))) (.node (.leaf ([(4, 0)], [(3, 6), (2, 4)], [(4, 3), (0, 8)])) (.leaf ([(9, 3), (10, 0)], [], [(10, 2)])))) (.node (.node (.leaf ([(3, 4)], [], [(3, 2)])) (.leaf ([(8, 4)], [(2, 3), (3, 5), (5, 7), (4, 3), (0, 8), (4, 6), (3, 4)], [(8, 2)]))) (.node (.leaf ([(6, 0)], [(5, 6), (4, 4)], [(6, 3), (1, 7), (5, 2)])) (.leaf ([(3, 3), (9, 3), (12, 4), (4, 5), (10, 5), (0, 7), (4, 4), (6, 7), (5, 2), (8, 4), (3, 6), (2, 4)], [(6, 3), (7, 5), (9, 7), (8, 3), (4, 8), (2, 6), (1, 4), (8, 6), (7, 4)], [(12, 2)]))))) (.node (.node (.node (.leaf ([], [(2, 1)], [])) (.leaf ([], [(8, 1)], [(5, 8), (3, 6), (2, 4)]))) (.node (.leaf ([], [(5, 1)], [(2, 8), (0, 6)])) (.leaf ([(3, 3), (9, 3), (4, 5), (10, 5), (6, 7), (5, 3), (10, 4), (1, 8), (5, 6), (4, 4)], [(11, 1)], [])))) (.node (.node (.leaf ([(4, 4)], [], [(4, 2)])) (.leaf ([(9, 0)], [(8, 6), (7, 4)], [(1, 3), (9, 3), (2, 5), (4, 7), (8, 2)]))) (.node (.leaf ([], [(6, 1)], [(3, 8), (1, 6), (0, 4)])) (.leaf ([], [], [])))))) (.node (.node (.node (.node (.leaf ([(1, 4)], [], [(1, 2)])) (.leaf ([(7, 0)], [(6, 6), (5, 4)], [(7, 3), (3, 8), (1, 6), (0, 4)]))) (.node (.leaf ([], [(5, 1)], [(1, 7), (5, 2)])) (.leaf ([(2, 3), (8, 3), (3, 5), (9, 5), (5, 7), (4, 3), (9, 4), (0, 8), (4, 6), (3, 4)], [(10, 1)], [])))) (.node (.node (.leaf ([(2, 3), (3, 0)], [], [(3, 2)])) (.leaf ([(9, 0)], [(8, 6), (7, 4)], [(9, 3), (5, 8), (3, 6), (2, 4)]))) (.node (.leaf ([(6, 0)], [(5, 6), (4, 4)], [(6, 3), (2, 8), (0, 6)])) (.leaf ([(5, 3), (11, 3), (14, 4), (0, 5), (6, 5), (12, 5), (2, 7), (6, 4), (8, 7), (7, 2), (10, 4), (5, 6), (4, 4)], [(2, 3), (8, 3), (3, 5), (9, 5), (5, 7), (9, 4), (11, 7), (10, 2), (8, 6), (7, 4)], [(14, 2)]))))) (.node (.node (.node (.leaf ([(2, 4)], [], [(2, 2)])) (.leaf ([], [(8, 1)], [(1, 3), (2, 5), (4, 7), (8, 2)]))) (.node (.leaf ([(5, 4)], [], [(5, 2)])) (.leaf ([(11, 3), (12, 0)], [], [(12, 2)])))) (.node (.node (.leaf ([(4, 4)], [], [(4, 2)])) (.leaf ([], [(10, 1)], []))) (.node (.leaf ([(7, 4)], [], [(7, 2)])) (.leaf ([], [], [])))))))))

private def stepCertNat (k : ℕ) (i : Fin 3) : List (ℕ × Fin 9) :=
  let t := certTree.get k
  match i with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2

private lemma stepCert_valid_bool :
    allBelow 120 (fun k =>
      let w := canonTree.get k
      (applyCert (w ++ [0]) (stepCertNat k 0) == some (canonTree.get (stepNat k 0))) &&
      (applyCert (w ++ [1]) (stepCertNat k 1) == some (canonTree.get (stepNat k 1))) &&
      (applyCert (w ++ [2]) (stepCertNat k 2) == some (canonTree.get (stepNat k 2)))) = true := by
  decide

private lemma stepCert_valid (k : Fin 120) (i : Fin 3) :
    applyCert (canonWord k ++ [i]) (stepCertNat k.val i) = some (canonWord (stepTable k i)) := by
  have h := allBelow_spec stepCert_valid_bool k.val k.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

lemma wordProd_canon_mul_simple {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (k : Fin 120) (i : Fin 3) :
    cs.wordProd (canonWord k) * cs.simple i = cs.wordProd (canonWord (stepTable k i)) := by
  rw [← cs.wordProd_concat, List.concat_eq_append]
  exact applyCert_sound cs (stepCert_valid k i)

/-! ### Exact bijection `Fin 120 ≃ W` and exact Coxeter length on `H₃` -/

private def foldStepNat (k : ℕ) : List (Fin 3) → ℕ
  | [] => k
  | i :: ω => foldStepNat (stepNat k i) ω

private lemma foldStepNat_lt {k : ℕ} (hk : k < 120) (ω : List (Fin 3)) :
    foldStepNat k ω < 120 := by
  induction ω generalizing k with
  | nil => exact hk
  | cons i ω ih => exact ih (stepNat_lt hk i)

/-- Fold right multiplication along a word in `Fin 120`. -/
def foldStep (k : Fin 120) (ω : List (Fin 3)) : Fin 120 :=
  ⟨foldStepNat k.val ω, foldStepNat_lt k.isLt ω⟩

lemma wordProd_foldStep {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (k : Fin 120) (ω : List (Fin 3)) :
    cs.wordProd (canonWord (foldStep k ω)) = cs.wordProd (canonWord k) * cs.wordProd ω := by
  induction ω generalizing k with
  | nil => simp [foldStep, foldStepNat, wordProd]
  | cons i ω ih =>
    have hstep : foldStep k (i :: ω) = foldStep (stepTable k i) ω := by
      apply Fin.ext; rfl
    rw [hstep, ih, cs.wordProd_cons, ← mul_assoc, wordProd_canon_mul_simple]

private lemma canonWord_zero : canonWord 0 = [] := by decide

lemma wordProd_canon_surjective {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    Function.Surjective (fun k : Fin 120 => cs.wordProd (canonWord k)) := by
  intro w
  refine cs.simple_induction_right (p := fun x => ∃ k : Fin 120, cs.wordProd (canonWord k) = x) w
    ⟨0, by simp [canonWord_zero, wordProd]⟩ ?_
  rintro x i ⟨k, rfl⟩
  exact ⟨stepTable k i, (wordProd_canon_mul_simple cs k i).symm⟩

/-- Packed action of a word on the three simple roots `(0, 1, 2)` as a single natural key. -/
private def rootKey (ω : List (Fin 3)) : ℕ :=
  applyWordNat ω 0 * 900 + applyWordNat ω 1 * 30 + applyWordNat ω 2

private def rootKeyTree : LookupTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.leaf 32) (.leaf 21147)) (.node (.leaf 21979) (.leaf 24466))) (.node (.node (.leaf 14753) (.leaf 10746)) (.node (.leaf 22944) (.leaf 16865)))) (.node (.node (.node (.leaf 5977) (.leaf 18763)) (.node (.leaf 8052) (.leaf 19507))) (.node (.node (.leaf 11401) (.leaf 20501)) (.node (.leaf 16034) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1448) (.leaf 15719)) (.node (.leaf 22989) (.leaf 17800))) (.node (.node (.leaf 7031) (.leaf 18388)) (.node (.leaf 21282) (.leaf 14072)))) (.node (.node (.node (.leaf 16490) (.leaf 7181)) (.node (.leaf 2624) (.leaf 17305))) (.node (.node (.leaf 17515) (.leaf 23916)) (.node (.leaf 5383) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 3185) (.leaf 21372)) (.node (.leaf 5323) (.leaf 8659))) (.node (.node (.leaf 17560) (.leaf 23109)) (.node (.leaf 2654) (.leaf 632)))) (.node (.node (.node (.leaf 1223) (.leaf 15689)) (.node (.leaf 20246) (.leaf 21829))) (.node (.node (.leaf 23436) (.leaf 4450)) (.node (.leaf 18448) (.leaf 0))))) (.node (.node (.node (.node (.leaf 16205) (.leaf 9879)) (.node (.leaf 23811) (.leaf 23721))) (.node (.node (.leaf 8179) (.leaf 8914)) (.node (.leaf 8082) (.leaf 557)))) (.node (.node (.node (.leaf 18907) (.leaf 21117)) (.node (.leaf 18643) (.leaf 923))) (.node (.node (.leaf 20351) (.leaf 22854)) (.node (.leaf 16094) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 13592) (.leaf 13275)) (.node (.leaf 11326) (.leaf 22114))) (.node (.node (.leaf 10656) (.leaf 25263)) (.node (.leaf 13215) (.leaf 3170)))) (.node (.node (.node (.leaf 14858) (.leaf 4708)) (.node (.leaf 25323) (.leaf 5872))) (.node (.node (.leaf 9789) (.leaf 6416)) (.node (.leaf 2159) (.leaf 0))))) (.node (.node (.node (.node (.leaf 13697) (.leaf 12483)) (.node (.leaf 9174) (.leaf 3625))) (.node (.node (.leaf 21694) (.leaf 11446)) (.node (.leaf 7437) (.leaf 16250)))) (.node (.node (.node (.leaf 8764) (.leaf 26355)) (.node (.leaf 24586) (.leaf 15158))) (.node (.node (.leaf 12393) (.leaf 10401)) (.node (.leaf 26415) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 137) (.leaf 7347)) (.node (.leaf 24481) (.leaf 20096))) (.node (.node (.leaf 3865) (.leaf 9054)) (.node (.leaf 25548) (.leaf 14513)))) (.node (.node (.node (.leaf 4240) (.leaf 11521)) (.node (.leaf 13290) (.leaf 3425))) (.node (.node (.leaf 9981) (.leaf 25458)) (.node (.leaf 13350) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2930) (.leaf 26250)) (.node (.leaf 12228) (.leaf 1688))) (.node (.node (.leaf 19282) (.leaf 24361)) (.node (.leaf 26310) (.leaf 13997)))) (.node (.node (.node (.leaf 5572) (.leaf 12288)) (.node (.leaf 4828) (.leaf 19042))) (.node (.node (.leaf 6566) (.leaf 6217)) (.node (.leaf 2099) (.leaf 0))))))))
private def sortedTree : LookupTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 115)) (.node (.leaf 67) (.leaf 21))) (.node (.node (.leaf 101) (.leaf 84)) (.node (.leaf 33) (.leaf 81)))) (.node (.node (.node (.leaf 63) (.leaf 6)) (.node (.leaf 83) (.leaf 26))) (.node (.node (.leaf 15) (.leaf 99)) (.node (.leaf 49) (.leaf 0))))) (.node (.node (.node (.node (.leaf 110) (.leaf 74)) (.node (.leaf 22) (.leaf 94))) (.node (.node (.leaf 73) (.leaf 14)) (.node (.leaf 39) (.leaf 71)))) (.node (.node (.node (.leaf 7) (.leaf 108)) (.node (.leaf 27) (.leaf 87))) (.node (.node (.leaf 89) (.leaf 78)) (.node (.leaf 1) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 118) (.leaf 9)) (.node (.leaf 40) (.leaf 32))) (.node (.node (.leaf 11) (.leaf 46)) (.node (.leaf 85) (.leaf 91)))) (.node (.node (.node (.leaf 44) (.leaf 12)) (.node (.leaf 25) (.leaf 38))) (.node (.node (.leaf 8) (.leaf 30)) (.node (.leaf 43) (.leaf 0))))) (.node (.node (.node (.node (.leaf 4) (.leaf 56)) (.node (.leaf 13) (.leaf 36))) (.node (.node (.leaf 34) (.leaf 23)) (.node (.leaf 29) (.leaf 77)))) (.node (.node (.node (.leaf 2) (.leaf 18)) (.node (.leaf 17) (.leaf 35))) (.node (.node (.leaf 20) (.leaf 52)) (.node (.leaf 119) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 3) (.leaf 16)) (.node (.leaf 53) (.leaf 106))) (.node (.node (.leaf 19) (.leaf 58)) (.node (.leaf 24) (.leaf 41)))) (.node (.node (.node (.leaf 57) (.leaf 117)) (.node (.leaf 37) (.leaf 102))) (.node (.node (.leaf 105) (.leaf 42)) (.node (.leaf 65) (.leaf 0))))) (.node (.node (.node (.node (.leaf 10) (.leaf 68)) (.node (.leaf 98) (.leaf 48))) (.node (.node (.leaf 47) (.leaf 111)) (.node (.leaf 79) (.leaf 55)))) (.node (.node (.node (.leaf 113) (.leaf 28)) (.node (.leaf 93) (.leaf 96))) (.node (.node (.leaf 31) (.leaf 64)) (.node (.leaf 5) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 114) (.leaf 109)) (.node (.leaf 54) (.leaf 97))) (.node (.node (.leaf 90) (.leaf 72)) (.node (.leaf 75) (.leaf 51)))) (.node (.node (.node (.leaf 50) (.leaf 112)) (.node (.leaf 70) (.leaf 92))) (.node (.node (.leaf 95) (.leaf 88)) (.node (.leaf 59) (.leaf 0))))) (.node (.node (.node (.node (.leaf 103) (.leaf 62)) (.node (.leaf 86) (.leaf 82))) (.node (.node (.leaf 60) (.leaf 104)) (.node (.leaf 69) (.leaf 61)))) (.node (.node (.node (.leaf 107) (.leaf 100)) (.node (.leaf 80) (.leaf 45))) (.node (.node (.leaf 76) (.leaf 66)) (.node (.leaf 116) (.leaf 0))))))))
private def rankTree : LookupTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 93)) (.node (.leaf 98) (.leaf 109))) (.node (.node (.leaf 65) (.leaf 47)) (.node (.leaf 101) (.leaf 75)))) (.node (.node (.node (.leaf 26) (.leaf 83)) (.node (.leaf 34) (.leaf 87))) (.node (.node (.leaf 49) (.leaf 91)) (.node (.leaf 70) (.leaf 0))))) (.node (.node (.node (.node (.leaf 6) (.leaf 69)) (.node (.leaf 102) (.leaf 79))) (.node (.node (.leaf 30) (.leaf 80)) (.node (.leaf 94) (.leaf 63)))) (.node (.node (.node (.leaf 74) (.leaf 31)) (.node (.leaf 10) (.leaf 76))) (.node (.node (.leaf 77) (.leaf 107)) (.node (.leaf 23) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 14) (.leaf 95)) (.node (.leaf 22) (.leaf 37))) (.node (.node (.leaf 78) (.leaf 103)) (.node (.leaf 11) (.leaf 3)))) (.node (.node (.node (.leaf 5) (.leaf 68)) (.node (.leaf 89) (.leaf 97))) (.node (.node (.leaf 104) (.leaf 19)) (.node (.leaf 81) (.leaf 0))))) (.node (.node (.node (.node (.leaf 72) (.leaf 43)) (.node (.leaf 106) (.leaf 105))) (.node (.node (.leaf 36) (.leaf 39)) (.node (.leaf 35) (.leaf 2)))) (.node (.node (.node (.leaf 84) (.leaf 92)) (.node (.leaf 82) (.leaf 4))) (.node (.node (.leaf 90) (.leaf 100)) (.node (.leaf 71) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 60) (.leaf 57)) (.node (.leaf 48) (.leaf 99))) (.node (.node (.leaf 46) (.leaf 112)) (.node (.leaf 56) (.leaf 13)))) (.node (.node (.node (.leaf 66) (.leaf 20)) (.node (.leaf 113) (.leaf 25))) (.node (.node (.leaf 42) (.leaf 28)) (.node (.leaf 9) (.leaf 0))))) (.node (.node (.node (.node (.leaf 61) (.leaf 55)) (.node (.leaf 41) (.leaf 16))) (.node (.node (.leaf 96) (.leaf 50)) (.node (.leaf 33) (.leaf 73)))) (.node (.node (.node (.leaf 38) (.leaf 118)) (.node (.leaf 111) (.leaf 67))) (.node (.node (.leaf 54) (.leaf 45)) (.node (.leaf 119) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 1) (.leaf 32)) (.node (.leaf 110) (.leaf 88))) (.node (.node (.leaf 17) (.leaf 40)) (.node (.leaf 115) (.leaf 64)))) (.node (.node (.node (.leaf 18) (.leaf 51)) (.node (.leaf 58) (.leaf 15))) (.node (.node (.leaf 44) (.leaf 114)) (.node (.leaf 59) (.leaf 0))))) (.node (.node (.node (.node (.leaf 12) (.leaf 116)) (.node (.leaf 52) (.leaf 7))) (.node (.node (.leaf 86) (.leaf 108)) (.node (.leaf 117) (.leaf 62)))) (.node (.node (.node (.leaf 24) (.leaf 53)) (.node (.leaf 21) (.leaf 85))) (.node (.node (.leaf 29) (.leaf 27)) (.node (.leaf 8) (.leaf 0))))))))

private lemma rootKey_canon_bool :
    allBelow 120 (fun k => rootKey (canonTree.get k) == rootKeyTree.get k) = true := by
  decide

private lemma sorted_rank_bool :
    allBelow 120 (fun k =>
      decide (rankTree.get k < 120) && (sortedTree.get (rankTree.get k) == k)) = true := by
  decide

private lemma sorted_strictMono_bool :
    allBelow 119 (fun i =>
      decide (rootKeyTree.get (sortedTree.get i) < rootKeyTree.get (sortedTree.get (i + 1)))) = true := by
  decide

private lemma sorted_strictMono_aux :
    ∀ (d i : ℕ), i + d < 120 → 0 < d →
      rootKeyTree.get (sortedTree.get i) < rootKeyTree.get (sortedTree.get (i + d)) := by
  intro d
  induction d with
  | zero => intro _ _ h0; omega
  | succ m ih =>
    intro i hlt _
    have hstep := decide_eq_true_eq.mp (allBelow_spec sorted_strictMono_bool (i + m) (by omega))
    by_cases hm : m = 0
    · subst hm; simpa using hstep
    · exact lt_trans (ih i (by omega) (by omega)) (by simpa [Nat.add_assoc] using hstep)

lemma wordProd_canon_injective {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    Function.Injective (fun k : Fin 120 => cs.wordProd (canonWord k)) := by
  intro k₁ k₂ heq
  dsimp only at heq
  have hperm : wordPerm (canonWord k₁) = wordPerm (canonWord k₂) := by
    rw [← rootRep_wordProd cs, ← rootRep_wordProd cs, heq]
  have hkey : rootKey (canonWord k₁) = rootKey (canonWord k₂) := by
    have hap : ∀ r : Fin 30, applyWordNat (canonWord k₁) r.val = applyWordNat (canonWord k₂) r.val := fun r => by
      rw [← wordPerm_apply_val, ← wordPerm_apply_val, hperm]
    have h0 : applyWordNat (canonWord k₁) 0 = applyWordNat (canonWord k₂) 0 := hap 0
    have h1 : applyWordNat (canonWord k₁) 1 = applyWordNat (canonWord k₂) 1 := hap 1
    have h2 : applyWordNat (canonWord k₁) 2 = applyWordNat (canonWord k₂) 2 := hap 2
    simp only [rootKey, h0, h1, h2]
  have hk1 := beq_iff_eq.mp (allBelow_spec rootKey_canon_bool k₁.val k₁.isLt)
  have hk2 := beq_iff_eq.mp (allBelow_spec rootKey_canon_bool k₂.val k₂.isLt)
  have hfast : rootKeyTree.get k₁.val = rootKeyTree.get k₂.val := by
    rw [← hk1, ← hk2]; exact hkey
  have hr1 := allBelow_spec sorted_rank_bool k₁.val k₁.isLt
  have hr2 := allBelow_spec sorted_rank_bool k₂.val k₂.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr1 hr2
  set i₁ := rankTree.get k₁.val
  set i₂ := rankTree.get k₂.val
  have hsr : rootKeyTree.get (sortedTree.get i₁) = rootKeyTree.get (sortedTree.get i₂) := by
    rw [hr1.2, hr2.2, hfast]
  have hiEq : i₁ = i₂ := by
    rcases lt_trichotomy i₁ i₂ with hlt | heqI | hgt
    · have := sorted_strictMono_aux (i₂ - i₁) i₁ (by omega) (by omega)
      rw [Nat.add_sub_cancel' (le_of_lt hlt)] at this
      omega
    · exact heqI
    · have := sorted_strictMono_aux (i₁ - i₂) i₂ (by omega) (by omega)
      rw [Nat.add_sub_cancel' (le_of_lt hgt)] at this
      omega
  apply Fin.ext
  rw [← hr1.2, ← hr2.2, hiEq]

/-- Canonical bijection `Fin 120 ≃ W` for any `CoxeterSystem CoxeterMatrix.H₃ W`. -/
noncomputable def H3Equiv {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    Fin 120 ≃ W :=
  Equiv.ofBijective (fun k : Fin 120 => cs.wordProd (canonWord k))
    ⟨wordProd_canon_injective cs, wordProd_canon_surjective cs⟩

private lemma invCountWord_canon_bool :
    allBelow 120 (fun k => invCountWord (canonTree.get k) == lenFastNat k) = true := by
  decide

private lemma invCountWord_canon_eq (k : Fin 120) : invCountWord (canonWord k) = lenFast k :=
  beq_iff_eq.mp (allBelow_spec invCountWord_canon_bool k.val k.isLt)

/-- Exact Coxeter length of every canonical element of `H₃`. -/
lemma length_canonWord {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (k : Fin 120) : cs.length (cs.wordProd (canonWord k)) = (canonWord k).length := by
  refine le_antisymm (cs.length_wordProd_le (canonWord k)) ?_
  have h1 := invCount_rootRep_le_length cs (cs.wordProd (canonWord k))
  rw [rootRep_wordProd, invCount_wordPerm_eq, invCountWord_canon_eq, lenFast_eq] at h1
  exact h1

/-! ### Exact involution, prefix, and ancestor predicates on `Fin 120` -/

/-- Decidable check for `orderOf (canon k) = 2` on `ℕ`. -/
private def isInvNat (k : ℕ) : Bool :=
  k != 0 && foldStepNat k (canonTree.get k) == 0

/-- Decidable check for `orderOf (canon k) = 2`. -/
def isInvIdx (k : Fin 120) : Bool :=
  isInvNat k.val

lemma orderOf_eq_two_iff_isInvIdx {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    (k : Fin 120) :
    orderOf (cs.wordProd (canonWord k)) = 2 ↔ isInvIdx k = true := by
  rw [orderOf_eq_iff (by decide : 0 < 2)]
  have h1 : cs.wordProd (canonWord k) ≠ 1 ↔ k.val ≠ 0 := by
    constructor
    · intro h hk
      have hk0 : k = 0 := Fin.ext hk
      subst hk0; exact h (by simp [canonWord_zero, wordProd])
    · intro hk h
      have hk0 : k = 0 := wordProd_canon_injective cs (by simpa [canonWord_zero, wordProd] using h)
      exact hk (congrArg Fin.val hk0)
  have hsq : cs.wordProd (canonWord k) ^ 2 = 1 ↔ foldStepNat k.val (canonTree.get k.val) = 0 := by
    rw [pow_two, ← wordProd_foldStep cs k (canonWord k)]
    constructor
    · intro h
      have h0 : foldStep k (canonWord k) = 0 :=
        wordProd_canon_injective cs (by simpa [canonWord_zero, wordProd] using h)
      exact congrArg Fin.val h0
    · intro h
      have h0 : foldStep k (canonWord k) = 0 := Fin.ext h
      rw [h0]; simp [canonWord_zero, wordProd]
  simp only [isInvIdx, isInvNat, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, hsq]
  constructor
  · rintro ⟨hs, hlt⟩
    refine ⟨h1.mp ?_, hs⟩
    have := hlt 1 (by omega) (by omega)
    simpa using this
  · rintro ⟨hk, hs⟩
    refine ⟨hs, fun m hm2 hm0 => ?_⟩
    have hm1 : m = 1 := by omega
    subst hm1
    simpa using h1.mpr hk

private lemma inv_eq_self_of_orderOf_two {G : Type*} [Group G] {u : G} (h : orderOf u = 2) :
    u⁻¹ = u := by
  have hsq : u * u = 1 := by
    rw [← pow_two]
    exact (orderOf_eq_iff (by decide : 0 < 2)).mp h |>.1
  exact inv_eq_of_mul_eq_one_right hsq

/-- For an involution `u`, `u⁻¹ * w = u * w` in `Fin 120` coordinates. -/
private def isInvPrefixNat (u w : ℕ) : Bool :=
  lenFastNat u + lenFastNat (foldStepNat u (canonTree.get w)) == lenFastNat w

lemma isPrefix_of_orderOf_two_iff {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    {u w : Fin 120} (hord : orderOf (cs.wordProd (canonWord u)) = 2) :
    IsPrefix cs (cs.wordProd (canonWord u)) (cs.wordProd (canonWord w)) ↔
      isInvPrefixNat u.val w.val = true := by
  unfold IsPrefix isInvPrefixNat
  rw [inv_eq_self_of_orderOf_two hord, ← wordProd_foldStep cs u (canonWord w),
    length_canonWord, length_canonWord, length_canonWord,
    ← lenFast_eq, ← lenFast_eq, ← lenFast_eq, beq_iff_eq]
  rfl

/-- The exact 31 involution indices of `H₃`. -/
private def invListNat : List ℕ := [1, 2, 3, 5, 9, 13, 15, 20, 26, 28, 33, 36, 47, 51, 54, 64, 69, 72, 83, 87, 90, 93, 99, 104, 106, 110, 114, 116, 117, 118, 119]

private lemma mem_invListNat_bool :
    allBelow 120 (fun u => !isInvNat u || invListNat.contains u) = true := by
  decide

private lemma mem_invListNat_of_isInvNat {u : ℕ} (hu : u < 120) (hinv : isInvNat u = true) :
    u ∈ invListNat := by
  have h := allBelow_spec mem_invListNat_bool u hu
  rw [hinv] at h
  simpa using h

/-- Decidable unique-ancestor check on `ℕ` (short-circuits on length bounds before folding). -/
private def isUniqueAncestorNat (a w : ℕ) : Bool :=
  let la := lenFastNat a
  let lw := lenFastNat w
  isInvNat a && isInvPrefixNat a w &&
    invListNat.all fun u =>
      let lu := lenFastNat u
      if u == a || decide (lu < la) || decide (lw < lu) then true
      else !isInvPrefixNat u w

/-- Decidable unique-ancestor check in `Fin 120` coordinates. -/
def isUniqueAncestorIdx (a w : Fin 120) : Bool :=
  isUniqueAncestorNat a.val w.val

lemma isUniqueAncestor_of_idx {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W)
    {a w : Fin 120} (h : isUniqueAncestorIdx a w = true) :
    IsUniqueAncestor cs (cs.wordProd (canonWord a)) (cs.wordProd (canonWord w)) := by
  unfold isUniqueAncestorIdx isUniqueAncestorNat at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  rcases h with ⟨⟨hinv, hpref⟩, hall⟩
  have haOrd : orderOf (cs.wordProd (canonWord a)) = 2 :=
    (orderOf_eq_two_iff_isInvIdx cs a).mpr hinv
  refine ⟨(isPrefix_of_orderOf_two_iff cs haOrd).mpr hpref, haOrd, ?_⟩
  intro x hxpref hxord hxne
  obtain ⟨u, rfl⟩ := wordProd_canon_surjective cs x
  have huinv : isInvNat u.val = true := (orderOf_eq_two_iff_isInvIdx cs u).mp hxord
  have hupref : isInvPrefixNat u.val w.val = true := (isPrefix_of_orderOf_two_iff cs hxord).mp hxpref
  have humem : u.val ∈ invListNat := mem_invListNat_of_isInvNat u.isLt huinv
  have hune : u.val ≠ a.val := fun hEq => hxne (by rw [Fin.ext hEq])
  have hspec := hall u.val humem
  have hlw : lenFastNat u.val ≤ lenFastNat w.val := by
    unfold isInvPrefixNat at hupref
    have heq := beq_iff_eq.mp hupref
    omega
  rw [length_canonWord, length_canonWord, ← lenFast_eq, ← lenFast_eq]
  change lenFastNat u.val < lenFastNat a.val
  by_contra hnotlt
  have hcond : (u.val == a.val || decide (lenFastNat u.val < lenFastNat a.val) ||
      decide (lenFastNat w.val < lenFastNat u.val)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    exact ⟨⟨hune, hnotlt⟩, by omega⟩
  rw [hcond] at hspec
  simp [hupref] at hspec

/-! ### Conjecture 1.2 holds on `H₃`, while Conjecture 1.3 fails (`ilen = 4 > 3`) -/

private def ancTree : LookupTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 64)) (.node (.leaf 13) (.leaf 87))) (.node (.node (.leaf 9) (.leaf 33)) (.node (.leaf 36) (.leaf 106)))) (.node (.node (.node (.leaf 3) (.leaf 72)) (.node (.leaf 28) (.leaf 104))) (.node (.node (.leaf 15) (.leaf 64)) (.node (.leaf 33) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 33)) (.node (.leaf 36) (.leaf 90))) (.node (.node (.leaf 20) (.leaf 72)) (.node (.leaf 28) (.leaf 116)))) (.node (.node (.node (.leaf 2) (.leaf 64)) (.node (.leaf 13) (.leaf 90))) (.node (.node (.leaf 28) (.leaf 69)) (.node (.leaf 36) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 2) (.leaf 54)) (.node (.leaf 15) (.leaf 64))) (.node (.node (.leaf 5) (.leaf 47)) (.node (.leaf 26) (.leaf 114)))) (.node (.node (.node (.leaf 1) (.leaf 51)) (.node (.leaf 20) (.leaf 106))) (.node (.node (.leaf 26) (.leaf 90)) (.node (.leaf 47) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2) (.leaf 47)) (.node (.leaf 26) (.leaf 93))) (.node (.node (.leaf 13) (.leaf 51)) (.node (.leaf 54) (.leaf 118)))) (.node (.node (.node (.leaf 3) (.leaf 54)) (.node (.leaf 15) (.leaf 110))) (.node (.node (.leaf 20) (.leaf 83)) (.node (.leaf 51) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 47)) (.node (.leaf 33) (.leaf 87))) (.node (.node (.leaf 1) (.leaf 69)) (.node (.leaf 20) (.leaf 110)))) (.node (.node (.node (.leaf 9) (.leaf 36)) (.node (.leaf 5) (.leaf 90))) (.node (.node (.leaf 9) (.leaf 64)) (.node (.leaf 13) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 69)) (.node (.leaf 9) (.leaf 90))) (.node (.node (.leaf 13) (.leaf 36)) (.node (.leaf 28) (.leaf 117)))) (.node (.node (.node (.leaf 13) (.leaf 47)) (.node (.leaf 33) (.leaf 93))) (.node (.node (.leaf 5) (.leaf 93)) (.node (.leaf 20) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 3) (.leaf 54)) (.node (.leaf 15) (.leaf 99))) (.node (.node (.leaf 5) (.leaf 83)) (.node (.leaf 51) (.leaf 110)))) (.node (.node (.node (.leaf 5) (.leaf 26)) (.node (.leaf 20) (.leaf 99))) (.node (.node (.leaf 1) (.leaf 69)) (.node (.leaf 47) (.leaf 0))))) (.node (.node (.node (.node (.leaf 2) (.leaf 47)) (.node (.leaf 5) (.leaf 83))) (.node (.node (.leaf 15) (.leaf 87)) (.node (.leaf 20) (.leaf 119)))) (.node (.node (.node (.leaf 15) (.leaf 69)) (.node (.leaf 47) (.leaf 104))) (.node (.node (.leaf 20) (.leaf 72)) (.node (.leaf 26) (.leaf 0))))))))

private def ancCheckNat (w : ℕ) : Bool :=
  if w == 0 then true
  else decide (ancTree.get w < 120) && isUniqueAncestorNat (ancTree.get w) w

private lemma ancIdx_valid_0 : allPow2 3 0 ancCheckNat = true := by decide
private lemma ancIdx_valid_1 : allPow2 3 8 ancCheckNat = true := by decide
private lemma ancIdx_valid_2 : allPow2 3 16 ancCheckNat = true := by decide
private lemma ancIdx_valid_3 : allPow2 3 24 ancCheckNat = true := by decide
private lemma ancIdx_valid_4 : allPow2 3 32 ancCheckNat = true := by decide
private lemma ancIdx_valid_5 : allPow2 3 40 ancCheckNat = true := by decide
private lemma ancIdx_valid_6 : allPow2 3 48 ancCheckNat = true := by decide
private lemma ancIdx_valid_7 : allPow2 3 56 ancCheckNat = true := by decide
private lemma ancIdx_valid_8 : allPow2 3 64 ancCheckNat = true := by decide
private lemma ancIdx_valid_9 : allPow2 3 72 ancCheckNat = true := by decide
private lemma ancIdx_valid_10 : allPow2 3 80 ancCheckNat = true := by decide
private lemma ancIdx_valid_11 : allPow2 3 88 ancCheckNat = true := by decide
private lemma ancIdx_valid_12 : allPow2 3 96 ancCheckNat = true := by decide
private lemma ancIdx_valid_13 : allPow2 3 104 ancCheckNat = true := by decide
private lemma ancIdx_valid_14 : allPow2 3 112 ancCheckNat = true := by decide

private lemma ancIdx_valid_all (k : ℕ) (hk : k < 120) : ancCheckNat k = true := by
  by_cases h0 : k < 8
  · exact allPow2_spec 3 0 ancCheckNat ancIdx_valid_0 k (by omega) (by omega)
  by_cases h1 : k < 16
  · exact allPow2_spec 3 8 ancCheckNat ancIdx_valid_1 k (by omega) (by omega)
  by_cases h2 : k < 24
  · exact allPow2_spec 3 16 ancCheckNat ancIdx_valid_2 k (by omega) (by omega)
  by_cases h3 : k < 32
  · exact allPow2_spec 3 24 ancCheckNat ancIdx_valid_3 k (by omega) (by omega)
  by_cases h4 : k < 40
  · exact allPow2_spec 3 32 ancCheckNat ancIdx_valid_4 k (by omega) (by omega)
  by_cases h5 : k < 48
  · exact allPow2_spec 3 40 ancCheckNat ancIdx_valid_5 k (by omega) (by omega)
  by_cases h6 : k < 56
  · exact allPow2_spec 3 48 ancCheckNat ancIdx_valid_6 k (by omega) (by omega)
  by_cases h7 : k < 64
  · exact allPow2_spec 3 56 ancCheckNat ancIdx_valid_7 k (by omega) (by omega)
  by_cases h8 : k < 72
  · exact allPow2_spec 3 64 ancCheckNat ancIdx_valid_8 k (by omega) (by omega)
  by_cases h9 : k < 80
  · exact allPow2_spec 3 72 ancCheckNat ancIdx_valid_9 k (by omega) (by omega)
  by_cases h10 : k < 88
  · exact allPow2_spec 3 80 ancCheckNat ancIdx_valid_10 k (by omega) (by omega)
  by_cases h11 : k < 96
  · exact allPow2_spec 3 88 ancCheckNat ancIdx_valid_11 k (by omega) (by omega)
  by_cases h12 : k < 104
  · exact allPow2_spec 3 96 ancCheckNat ancIdx_valid_12 k (by omega) (by omega)
  by_cases h13 : k < 112
  · exact allPow2_spec 3 104 ancCheckNat ancIdx_valid_13 k (by omega) (by omega)
  exact allPow2_spec 3 112 ancCheckNat ancIdx_valid_14 k (by omega) (by omega)

/-- **Theorem 1 (Ancestor Property for `H₃`):** Every non-identity element of any
`CoxeterSystem CoxeterMatrix.H₃ W` has a unique longest involution prefix (verifying
Hart–Rowley Conjecture 1.2 for `H₃` unconditionally). -/
theorem H3_hasAncestorProperty {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    HasAncestorProperty cs := by
  intro w hw
  obtain ⟨k, rfl⟩ := wordProd_canon_surjective cs w
  have hk0 : k.val ≠ 0 := by
    intro hk
    have h0 : k = 0 := Fin.ext hk
    subst h0; exact hw (by simp [canonWord_zero, wordProd])
  have h := ancIdx_valid_all k.val k.isLt
  unfold ancCheckNat at h
  have hk0b : (k.val == 0) = false := beq_eq_false_iff_ne.mpr hk0
  rw [hk0b] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
  let a : Fin 120 := ⟨ancTree.get k.val, h.1⟩
  exact ⟨cs.wordProd (canonWord a), isUniqueAncestor_of_idx cs h.2⟩

/-- Helper lemma: a single step in `Fin 120` coordinates lifts to `HasInvolutionLength`. -/
private lemma hasInvolutionLength_step_idx {W : Type*} [Group W]
    (cs : CoxeterSystem CoxeterMatrix.H₃ W) {w a r : Fin 120} {k : ℕ}
    (hw0 : w ≠ 0) (ha : isUniqueAncestorIdx a w = true)
    (hr : foldStep a (canonWord w) = r)
    (hrest : HasInvolutionLength cs (cs.wordProd (canonWord r)) k) :
    HasInvolutionLength cs (cs.wordProd (canonWord w)) (k + 1) := by
  have hanc := isUniqueAncestor_of_idx cs ha
  refine HasInvolutionLength.step ?_ hanc ?_
  · intro h1; exact hw0 (wordProd_canon_injective cs (by simpa [canonWord_zero, wordProd] using h1))
  · rw [inv_eq_self_of_orderOf_two hanc.2.1, ← wordProd_foldStep cs a (canonWord w), hr]
    exact hrest

/-- **Theorem 2 (Primary Counterexample in `H₃`):**
In any `CoxeterSystem CoxeterMatrix.H₃ W`, the element `w₁ = s₁ s₂ s₀ s₁ s₂ s₁ s₀`
(length `7`) has ancestor decomposition `(s₁ s₀ s₂ s₁)(s₂)(s₁)(s₀)` and exact
involution length `4 > 3 = rank(H₃)`. -/
theorem witness1_involutionLength {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    HasInvolutionLength cs (cs.wordProd [1, 2, 0, 1, 2, 1, 0]) 4 := by
  have hw_eq : cs.wordProd [1, 2, 0, 1, 2, 1, 0] = cs.wordProd (canonWord 55) := by
    have hcert : applyCert [1, 2, 0, 1, 2, 1, 0] [(1, 4)] = some (canonWord 55) := by decide
    exact applyCert_sound cs hcert
  rw [hw_eq]
  refine hasInvolutionLength_step_idx cs (a := 20) (r := 14) (by decide) (by decide) (by decide) ?_
  refine hasInvolutionLength_step_idx cs (a := 3) (r := 6) (by decide) (by decide) (by decide) ?_
  refine hasInvolutionLength_step_idx cs (a := 2) (r := 1) (by decide) (by decide) (by decide) ?_
  refine hasInvolutionLength_step_idx cs (a := 1) (r := 0) (by decide) (by decide) (by decide) ?_
  simpa [canonWord_zero, wordProd] using HasInvolutionLength.one (cs := cs)

/-- **Theorem 3 (Second Counterexample in `H₃`):**
The element `w₂ = s₁ s₂ s₁ s₂ s₀ s₁ s₂` (length `7`) has ancestor decomposition
`(s₁ s₂ s₁)(s₀ s₂)(s₁)(s₂)` and exact involution length `4 > 3 = rank(H₃)`. -/
theorem witness2_involutionLength {W : Type*} [Group W] (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    HasInvolutionLength cs (cs.wordProd [1, 2, 1, 2, 0, 1, 2]) 4 := by
  have hw_eq : cs.wordProd [1, 2, 1, 2, 0, 1, 2] = cs.wordProd (canonWord 57) := by
    have hcert : applyCert [1, 2, 1, 2, 0, 1, 2] [(3, 4)] = some (canonWord 57) := by decide
    exact applyCert_sound cs hcert
  rw [hw_eq]
  refine hasInvolutionLength_step_idx cs (a := 13) (r := 19) (by decide) (by decide) (by decide) ?_
  refine hasInvolutionLength_step_idx cs (a := 5) (r := 7) (by decide) (by decide) (by decide) ?_
  refine hasInvolutionLength_step_idx cs (a := 2) (r := 3) (by decide) (by decide) (by decide) ?_
  refine hasInvolutionLength_step_idx cs (a := 3) (r := 0) (by decide) (by decide) (by decide) ?_
  simpa [canonWord_zero, wordProd] using HasInvolutionLength.one (cs := cs)

/-- **Main Disproof (Refutation of Hart–Rowley Conjecture 1.3, arXiv:2502.00777v1):**
For every `CoxeterSystem CoxeterMatrix.H₃ W` (finite Coxeter group of type `H₃`, rank `3`,
order `120`), `W` satisfies the ancestor property (Conjecture 1.2), yet there exists an
element `w ∈ W` whose unique involution length `k` satisfies `k > Fintype.card (Fin 3) = 3`. -/
theorem hart_rowley_conj_1_3_false_H3 {W : Type*} [Group W]
    (cs : CoxeterSystem CoxeterMatrix.H₃ W) :
    HasAncestorProperty cs ∧
      ∃ (w : W) (k : ℕ), HasInvolutionLength cs w k ∧ Fintype.card (Fin 3) < k := by
  refine ⟨H3_hasAncestorProperty cs, cs.wordProd [1, 2, 0, 1, 2, 1, 0], 4,
    witness1_involutionLength cs, by decide⟩

end HartRowleyCoxeterInvolutionLength
