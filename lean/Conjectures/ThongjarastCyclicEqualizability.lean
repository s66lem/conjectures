import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Disproof of Thongjarast's Discard-Letter Conjecture on Cyclic Equalizability
# (`arXiv:2607.18452v1`, Problem 2 / `prob:discard`)

In *0-Cyclic Equalizability of Binary Words Characterized by Hamming Weight*
(`arXiv:2607.18452v1`, July 2026), S. Thongjarast posed Problem 2 (`prob:discard`):

> Let `Σ` be an alphabet of size at least `3`. Let `u` and `v` be words over `Σ`
> that are permutations of each other. Must there exist a letter `c ∈ Σ` such
> that `u` and `v` are `(Σ \ {c})`-equalizable?

We prove that the answer is **NO** for every alphabet `Σ` of size `m ≥ 3`:
for `Σ = Fin m` (and hence every finite alphabet `α` with `3 ≤ Fintype.card α`),
the length-`3m` words
  `u = ∏_{i=0}^{m-1} (x_i, x_i, x_{i+1})`
  `v = ∏_{i=0}^{m-1} (x_{i+1}, x_i, x_{i+1})`
(indices modulo `m`) are permutations of each other, use every letter of `Σ`,
and are **not** `(Σ \ {c})`-cyclically equalizable for **any** `c ∈ Σ`.

We also formally verify the smallest concrete instance (`m = 3`:
`u = aabbbccca`, `v = babcbcaca`) and exhibit an explicit full-alphabet
`Σ`-simultaneous insertion of length `15` showing that `(u, v)` is
`Σ`-cyclically equalizable when no letter is discarded.
-/

namespace ThongjarastCyclicEqualizability

/-! ### 1. Simultaneous Insertion and Cyclic Equalizability (Verbatim Definitions) -/

/-- Interleaving a word `w : Fin n → α` with `n + 1` inserted words `ins : Fin (n + 1) → List α`:
`ins 0 ++ [w 0] ++ ins 1 ++ [w 1] ++ ... ++ [w (n-1)] ++ ins n`. -/
def interleave {α : Type*} : ∀ {n : ℕ}, (Fin n → α) → (Fin (n + 1) → List α) → List α
  | 0, _, ins => ins 0
  | _ + 1, w, ins => ins 0 ++ w 0 :: interleave (fun j => w j.succ) (fun j => ins j.succ)

/-- Two lists `w₁, w₂` are cyclically equivalent iff they have the same length `L` and
some cyclic shift `d` satisfies `w₁[t] = w₂[(t + d) % L]` for all `0 ≤ t < L`. -/
def CycEquiv {α : Type*} (w₁ w₂ : List α) : Prop :=
  ∃ hlen : w₁.length = w₂.length,
    ∃ d : ℕ, ∀ (t : ℕ) (ht : t < w₁.length),
      w₁[t]'ht = w₂[(t + d) % w₂.length]'(Nat.mod_lt _ (by omega))

/-- Words `u, v : Fin n → α` are `σ`-cyclically equalizable iff there exist
insertion blocks `ins : Fin (n + 1) → List α` using only letters from `σ` such that
`interleave u ins` and `interleave v ins` are cyclically equivalent. -/
def CyclicallyEqualizable {α : Type*} [DecidableEq α] (σ : Finset α)
    {n : ℕ} (u v : Fin n → α) : Prop :=
  ∃ ins : Fin (n + 1) → List α,
    (∀ k : Fin (n + 1), ∀ a ∈ ins k, a ∈ σ) ∧
    CycEquiv (interleave u ins) (interleave v ins)

/-- Position of original letter `j : Fin n` inside `interleave w ins`. -/
private def origPos {α : Type*} : ∀ {n : ℕ}, (Fin (n + 1) → List α) → Fin n → ℕ
  | 0, _, j => j.elim0
  | _ + 1, ins, j =>
      Fin.cases (ins 0).length
        (fun j' => (ins 0).length + 1 + origPos (fun k => ins k.succ) j') j

private lemma interleave_length {α : Type*} :
    ∀ {n : ℕ} (u v : Fin n → α) (ins : Fin (n + 1) → List α),
      (interleave u ins).length = (interleave v ins).length
  | 0, _, _, _ => rfl
  | _ + 1, u, v, ins => by
      simp only [interleave, List.length_append, List.length_cons]
      rw [interleave_length (fun j => u j.succ) (fun j => v j.succ) (fun k => ins k.succ)]

private lemma origPos_lt_length {α : Type*} :
    ∀ {n : ℕ} (w : Fin n → α) (ins : Fin (n + 1) → List α) (j : Fin n),
      origPos ins j < (interleave w ins).length
  | 0, _, _, j => j.elim0
  | _ + 1, w, ins, j => by
      refine Fin.cases ?_ ?_ j
      · simp only [origPos, Fin.cases_zero, interleave, List.length_append, List.length_cons]
        omega
      · intro j'
        have ih := origPos_lt_length (fun k => w k.succ) (fun k => ins k.succ) j'
        simp only [origPos, Fin.cases_succ, interleave, List.length_append, List.length_cons]
        omega

private lemma origPos_strictMono {α : Type*} :
    ∀ {n : ℕ} (ins : Fin (n + 1) → List α), StrictMono (origPos ins)
  | 0, _ => fun j => j.elim0
  | _ + 1, ins => by
      intro i j hij
      revert hij
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · intro h; exact absurd h (lt_irrefl _)
        · intro j' _
          simp only [origPos, Fin.cases_zero, Fin.cases_succ]
          omega
      · intro i'
        refine Fin.cases ?_ ?_ j
        · intro h; exact absurd h (by simp)
        · intro j' hij
          simp only [origPos, Fin.cases_succ]
          have hlt : i' < j' := Fin.succ_lt_succ_iff.mp hij
          have ih := origPos_strictMono (fun k => ins k.succ) hlt
          omega

private lemma interleave_getElem_origPos {α : Type*} :
    ∀ {n : ℕ} (w : Fin n → α) (ins : Fin (n + 1) → List α) (j : Fin n),
      (interleave w ins)[origPos ins j]'(origPos_lt_length w ins j) = w j
  | 0, _, _, j => j.elim0
  | _ + 1, w, ins, j => by
      refine Fin.cases ?_ ?_ j
      · simp [origPos, interleave]
      · intro j'
        have ih := interleave_getElem_origPos (fun k => w k.succ) (fun k => ins k.succ) j'
        have hlen_lt : (ins 0).length < (ins 0).length + 1 + origPos (fun k => ins k.succ) j' := by omega
        simp only [origPos, Fin.cases_succ, interleave]
        rw [List.getElem_append_right (Nat.le_of_lt hlen_lt)]
        have hsub : (ins 0).length + 1 + origPos (fun k => ins k.succ) j' - (ins 0).length =
            origPos (fun k => ins k.succ) j' + 1 := by omega
        simp only [hsub, List.getElem_cons_succ]
        exact ih

private lemma interleave_getElem_not_origPos {α : Type*} [DecidableEq α] :
    ∀ {n : ℕ} (σ : Finset α) (u v : Fin n → α) (ins : Fin (n + 1) → List α)
      (_hins : ∀ k, ∀ a ∈ ins k, a ∈ σ)
      (t : ℕ) (ht : t < (interleave u ins).length)
      (_hnot : ∀ j : Fin n, origPos ins j ≠ t),
      (interleave u ins)[t]'ht =
        (interleave v ins)[t]'(interleave_length u v ins ▸ ht) ∧
      (interleave u ins)[t]'ht ∈ σ
  | 0, σ, _, _, ins, hins, t, ht, _ => by
      simp only [interleave] at ht ⊢
      exact ⟨trivial, hins 0 _ (List.getElem_mem ht)⟩
  | _ + 1, σ, u, v, ins, hins, t, ht, hnot => by
      by_cases ht0 : t < (ins 0).length
      · have h1 : (interleave u ins)[t]'ht = (ins 0)[t]'ht0 := by
          simp only [interleave]
          exact List.getElem_append_left ht0
        have h2 : (interleave v ins)[t]'(interleave_length u v ins ▸ ht) = (ins 0)[t]'ht0 := by
          simp only [interleave]
          exact List.getElem_append_left ht0
        rw [h1, h2]
        exact ⟨rfl, hins 0 _ (List.getElem_mem ht0)⟩
      · have hne0 : t ≠ (ins 0).length := by
          have h := hnot 0
          simpa [origPos] using h.symm
        have hgt : (ins 0).length + 1 ≤ t := by omega
        set t' := t - ((ins 0).length + 1)
        have ht' : t' < (interleave (fun j => u j.succ) (fun k => ins k.succ)).length := by
          simp only [interleave, List.length_append, List.length_cons] at ht
          omega
        have hnot' : ∀ j' : Fin _, origPos (fun k => ins k.succ) j' ≠ t' := by
          intro j' heq
          have h := hnot j'.succ
          simp only [origPos, Fin.cases_succ] at h
          omega
        have ih := interleave_getElem_not_origPos σ (fun j => u j.succ) (fun j => v j.succ)
          (fun k => ins k.succ) (fun k => hins k.succ) t' ht' hnot'
        have hsub : t - (ins 0).length = t' + 1 := by omega
        have hu : (interleave u ins)[t]'ht =
            (interleave (fun j => u j.succ) (fun k => ins k.succ))[t']'ht' := by
          simp only [interleave]
          rw [List.getElem_append_right (by omega : (ins 0).length ≤ t)]
          simp only [hsub, List.getElem_cons_succ]
        have hv : (interleave v ins)[t]'(interleave_length u v ins ▸ ht) =
            (interleave (fun j => v j.succ) (fun k => ins k.succ))[t']'
              (interleave_length (fun j => u j.succ) (fun j => v j.succ) (fun k => ins k.succ) ▸ ht') := by
          simp only [interleave]
          rw [List.getElem_append_right (by omega : (ins 0).length ≤ t)]
          simp only [hsub, List.getElem_cons_succ]
        rw [hu, hv]
        exact ih

/-! ### 2. Positional Characterization and Core Arithmetic Lemmas -/

/-- Step 3 arithmetic lemma: for `0 < e < L`, neither `(2e % L)` nor `(3e % L)` can
satisfy the cyclic orderings of Cases 2 or 3; and `2e % L = 0` forces `2e = L`. -/
theorem step3_arithmetic (L e : ℕ) (he0 : 0 < e) (heL : e < L) :
    ¬ (0 < (2 * e) % L ∧ (2 * e) % L < (3 * e) % L ∧ (3 * e) % L < e) ∧
    ¬ (0 < e ∧ e < (3 * e) % L ∧ (3 * e) % L < (2 * e) % L) ∧
    ((2 * e) % L = 0 → 2 * e = L) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, h23, h3e⟩
    by_cases h2L : 2 * e < L
    · have h2 : (2 * e) % L = 2 * e := Nat.mod_eq_of_lt h2L
      omega
    · have h2 : (2 * e) % L = 2 * e - L := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      by_cases h3L : 3 * e < 2 * L
      · have h3 : (3 * e) % L = 3 * e - L := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · have h3 : (3 * e) % L = 3 * e - 2 * L := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)]; omega
        omega
  · rintro ⟨_, he3, h32⟩
    by_cases h2L : 2 * e < L
    · have h2 : (2 * e) % L = 2 * e := Nat.mod_eq_of_lt h2L
      by_cases h3L : 3 * e < L
      · have h3 : (3 * e) % L = 3 * e := Nat.mod_eq_of_lt h3L
        omega
      · have h3 : (3 * e) % L = 3 * e - L := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    · have h2 : (2 * e) % L = 2 * e - L := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro h0
    by_cases h2L : 2 * e < L
    · rw [Nat.mod_eq_of_lt h2L] at h0; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h0; omega

/-! ### 3. Counterexample Family for Every `m ≥ 3` -/

/-- Counterexample word `u_m` of length `3m` over `Fin m`:
block `k` (`3k, 3k+1, 3k+2`) is `(k, k, (k + 1) % m)`. -/
def wordU (m : ℕ) (hm : 3 ≤ m) (j : Fin (3 * m)) : Fin m :=
  ⟨if j.1 % 3 = 2 then (j.1 / 3 + 1) % m else j.1 / 3, by
    split_ifs
    · exact Nat.mod_lt _ (by omega)
    · omega⟩

/-- Counterexample word `v_m` of length `3m` over `Fin m`:
block `k` (`3k, 3k+1, 3k+2`) is `((k + 1) % m, k, (k + 1) % m)`. -/
def wordV (m : ℕ) (hm : 3 ≤ m) (j : Fin (3 * m)) : Fin m :=
  ⟨if j.1 % 3 = 1 then j.1 / 3 else (j.1 / 3 + 1) % m, by
    split_ifs
    · omega
    · exact Nat.mod_lt _ (by omega)⟩

/-- `wordU m` and `wordV m` are permutations of each other (every letter occurs 3 times
in both, witnessed by a concrete involution/permutation on `Fin (3 * m)`). -/
theorem wordU_perm_wordV (m : ℕ) (hm : 3 ≤ m) :
    List.Perm (List.ofFn (wordU m hm)) (List.ofFn (wordV m hm)) := by
  -- Bijection `π : Fin (3*m) ≃ Fin (3*m)` sending `3k ↦ 3*((k+m-1)%m)` and fixing `3k+1, 3k+2`!
  -- Wait: `wordU (3k) = k`, and `wordV (3*((k+m-1)%m)) = ((k+m-1)%m + 1)%m = k`!
  let π : Fin (3 * m) ≃ Fin (3 * m) :=
    { toFun := fun j =>
        ⟨if j.1 % 3 = 0 then 3 * ((j.1 / 3 + m - 1) % m) else j.1, by
          split_ifs
          · have hlt := Nat.mod_lt (j.1 / 3 + m - 1) (by omega : 0 < m); omega
          · exact j.2⟩
      invFun := fun j =>
        ⟨if j.1 % 3 = 0 then 3 * ((j.1 / 3 + 1) % m) else j.1, by
          split_ifs
          · have hlt := Nat.mod_lt (j.1 / 3 + 1) (by omega : 0 < m); omega
          · exact j.2⟩
      left_inv := fun j => by
        ext; dsimp only
        by_cases h0 : j.1 % 3 = 0
        · simp only [h0, ↓reduceIte]
          have hmod0 : (3 * ((j.1 / 3 + m - 1) % m)) % 3 = 0 := by omega
          simp only [hmod0, ↓reduceIte]
          have hdiv : 3 * ((j.1 / 3 + m - 1) % m) / 3 = (j.1 / 3 + m - 1) % m := by omega
          rw [hdiv]
          have hlt : j.1 / 3 < m := by omega
          have hstep : ((j.1 / 3 + m - 1) % m + 1) % m = j.1 / 3 := by
            by_cases hz : j.1 / 3 = 0
            · rw [hz]; simp only [zero_add]
              rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]
              have : m - 1 + 1 = m := by omega
              rw [this, Nat.mod_self]
            · have heq : j.1 / 3 + m - 1 = (j.1 / 3 - 1) + m := by omega
              rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.1 / 3 - 1 < m)]
              have : j.1 / 3 - 1 + 1 = j.1 / 3 := by omega
              rw [this, Nat.mod_eq_of_lt hlt]
          rw [hstep]; omega
        · simp only [h0, ↓reduceIte]
      right_inv := fun j => by
        ext; dsimp only
        by_cases h0 : j.1 % 3 = 0
        · simp only [h0, ↓reduceIte]
          have hmod0 : (3 * ((j.1 / 3 + 1) % m)) % 3 = 0 := by omega
          simp only [hmod0, ↓reduceIte]
          have hdiv : 3 * ((j.1 / 3 + 1) % m) / 3 = (j.1 / 3 + 1) % m := by omega
          rw [hdiv]
          have hlt : j.1 / 3 < m := by omega
          have hstep : ((j.1 / 3 + 1) % m + m - 1) % m = j.1 / 3 := by
            by_cases htop : j.1 / 3 + 1 = m
            · rw [htop, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]; omega
            · rw [Nat.mod_eq_of_lt (by omega : j.1 / 3 + 1 < m)]
              have heq : j.1 / 3 + 1 + m - 1 = j.1 / 3 + m := by omega
              rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
          rw [hstep]; omega
        · simp only [h0, ↓reduceIte] }
  have hcomp : wordU m hm = wordV m hm ∘ π := by
    funext j
    ext
    dsimp only [Function.comp_apply, wordU, wordV, π, Equiv.coe_fn_mk]
    by_cases h0 : j.1 % 3 = 0
    · simp only [h0, ↓reduceIte]
      have hne2 : ¬ (0 = 2) := by decide
      rw [if_neg hne2]
      have hmod1 : (3 * ((j.1 / 3 + m - 1) % m)) % 3 ≠ 1 := by omega
      rw [if_neg hmod1]
      have hdiv : 3 * ((j.1 / 3 + m - 1) % m) / 3 = (j.1 / 3 + m - 1) % m := by omega
      rw [hdiv]
      have hlt : j.1 / 3 < m := by omega
      by_cases hz : j.1 / 3 = 0
      · rw [hz]; simp only [zero_add]
        rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]
        have : m - 1 + 1 = m := by omega
        rw [this, Nat.mod_self]
      · have heq : j.1 / 3 + m - 1 = (j.1 / 3 - 1) + m := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.1 / 3 - 1 < m)]
        have : j.1 / 3 - 1 + 1 = j.1 / 3 := by omega
        rw [this, Nat.mod_eq_of_lt hlt]
    · simp only [h0, ↓reduceIte]
      by_cases h1 : j.1 % 3 = 1
      · rw [if_pos h1, if_neg (by omega : j.1 % 3 ≠ 2)]
      · rw [if_neg h1, if_pos (by omega : j.1 % 3 = 2)]
  rw [hcomp, List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_map]
  have hperm_fin : ((List.finRange (3 * m)).map π).Perm (List.finRange (3 * m)) := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map π.injective) (List.nodup_finRange _)]
    intro x
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact ⟨π.symm x, π.apply_symm_apply x⟩
  exact hperm_fin.map (wordV m hm)

/-- `wordU m ≠ wordV m` for all `m ≥ 3` (they differ at position `0`). -/
theorem wordU_ne_wordV (m : ℕ) (hm : 3 ≤ m) : wordU m hm ≠ wordV m hm := by
  intro heq
  have h0 := congr_arg Fin.val (congr_fun heq ⟨0, by omega⟩)
  simp only [wordU, wordV] at h0
  rw [if_neg (by decide), if_neg (by decide)] at h0
  simp only [Nat.zero_div, zero_add] at h0
  rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at h0
  omega

/-- Every letter `c : Fin m` occurs in `wordU m`. -/
theorem wordU_surjective (m : ℕ) (hm : 3 ≤ m) : Function.Surjective (wordU m hm) := by
  intro c
  refine ⟨⟨3 * c.1, by omega⟩, ?_⟩
  ext; simp only [wordU]
  rw [if_neg (by omega)]
  omega

/-- **Main Family Theorem:** For every `m ≥ 3` and every letter `c : Fin m`, the pair
`(wordU m hm, wordV m hm)` is NOT `(Finset.univ.erase c)`-cyclically equalizable. -/
theorem family_not_equalizable (m : ℕ) (hm : 3 ≤ m) (c : Fin m) :
    ¬ CyclicallyEqualizable (Finset.univ.erase c) (wordU m hm) (wordV m hm) := by
  rintro ⟨ins, hins, hlen, d, hshift⟩
  set u := wordU m hm
  set v := wordV m hm
  set u' := interleave u ins
  set v' := interleave v ins
  set L := u'.length
  have hvlen : v'.length = L := hlen.symm
  have hL_pos : 0 < L := lt_of_le_of_lt (Nat.zero_le _) (origPos_lt_length u ins ⟨0, by omega⟩)
  set P : Fin (3 * m) → ℕ := origPos ins
  have hP_lt : ∀ j, P j < L := origPos_lt_length u ins
  have hP_mono : StrictMono P := origPos_strictMono ins
  have hu'_P : ∀ j, u'[P j]'(hP_lt j) = u j := interleave_getElem_origPos u ins
  have hv'_P : ∀ j, v'[P j]'(hvlen ▸ hP_lt j) = v j := interleave_getElem_origPos v ins
  have hshift' : ∀ (t : ℕ) (ht : t < L),
      u'[t]'ht = v'[(t + d) % L]'(by rw [hvlen]; exact Nat.mod_lt _ hL_pos) := by
    intro t ht
    have h := hshift t ht
    convert h using 2
    rw [hvlen]
  set e : ℕ := d % L
  have he_lt : e < L := Nat.mod_lt d hL_pos
  -- Step 1: `e ≠ 0` (else `u' = v'`, forcing `u = v`).
  have he_pos : 0 < e := by
    by_contra h0
    have he0 : d % L = 0 := by omega
    apply wordU_ne_wordV m hm
    funext j
    have h := hshift' (P j) (hP_lt j)
    have hmod : (P j + d) % L = P j := by
      rw [Nat.add_mod, he0, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (hP_lt j)]
    rw [hu'_P j] at h
    have h2 : v'[(P j + d) % L]'(by rw [hvlen]; exact Nat.mod_lt _ hL_pos) = v j := by
      have hEq : v'[(P j + d) % L]'(by rw [hvlen]; exact Nat.mod_lt _ hL_pos) = v'[P j]'(hvlen ▸ hP_lt j) := by
        congr 1
      exact hEq.trans (hv'_P j)
    exact h.trans h2
  -- Step 2: Every `c`-position `j` of `u` maps to a unique `c`-position `j'` of `v` with
  -- `P j' = (P j + e) % L` and `j' ≠ j`.
  have hc_step : ∀ j : Fin (3 * m), u j = c →
      ∃ j' : Fin (3 * m), v j' = c ∧ P j' = (P j + e) % L ∧ j' ≠ j := by
    intro j hj
    set t' := (P j + d) % L
    have ht'_lt : t' < L := Nat.mod_lt _ hL_pos
    have hv't' : v'[t']'(hvlen ▸ ht'_lt) = c := by
      rw [← hshift' (P j) (hP_lt j), hu'_P j, hj]
    have hex : ∃ j' : Fin (3 * m), P j' = t' := by
      by_contra hnot
      push Not at hnot
      obtain ⟨heq_uv, hmem⟩ := interleave_getElem_not_origPos (Finset.univ.erase c) u v ins hins t' ht'_lt hnot
      rw [hv't'] at heq_uv
      rw [heq_uv] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    rcases hex with ⟨j', hj'⟩
    have hvj' : v j' = c := by
      rw [← hv'_P j']
      have : v'[P j']'(hvlen ▸ hP_lt j') = v'[t']'(hvlen ▸ ht'_lt) := by congr 1
      exact this.trans hv't'
    have hmod_e : t' = (P j + e) % L := by
      dsimp only [t', e]; rw [Nat.add_mod, Nat.add_mod (P j) (d % L), Nat.mod_mod]
    have hne : j' ≠ j := by
      intro heq; subst heq
      have h1 : P j' = (P j' + e) % L := hj'.trans hmod_e
      have hlt := hP_lt j'
      by_cases hsum : P j' + e < L
      · rw [Nat.mod_eq_of_lt hsum] at h1; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
    exact ⟨j', hvj', hj'.trans hmod_e, hne⟩
  -- Explicit four positions `α, β, γ, δ` for letter `c`:
  set i : ℕ := c.1
  have hi_lt : i < m := c.2
  set ip : ℕ := (i + m - 1) % m
  have hip_lt : ip < m := Nat.mod_lt _ (by omega)
  have hip_succ : (ip + 1) % m = i := by
    dsimp only [ip]
    by_cases hz : i = 0
    · rw [hz]; simp only [zero_add]
      rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]
      have : m - 1 + 1 = m := by omega
      rw [this, Nat.mod_self]
    · have heq : i + m - 1 = (i - 1) + m := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < m)]
      have : i - 1 + 1 = i := by omega
      rw [this, Nat.mod_eq_of_lt hi_lt]
  have hip_ne : ip ≠ i := by
    intro h; rw [h] at hip_succ
    by_cases htop : i + 1 = m
    · rw [htop, Nat.mod_self] at hip_succ; omega
    · rw [Nat.mod_eq_of_lt (by omega : i + 1 < m)] at hip_succ; omega
  let α : Fin (3 * m) := ⟨3 * ip + 2, by omega⟩
  let β : Fin (3 * m) := ⟨3 * i, by omega⟩
  let γ : Fin (3 * m) := ⟨3 * i + 1, by omega⟩
  let δ : Fin (3 * m) := ⟨3 * ip, by omega⟩
  have hu_α : u α = c := by
    ext; simp only [u, wordU, α]
    rw [if_pos (by omega)]; have : (3 * ip + 2) / 3 = ip := by omega
    rw [this]; exact hip_succ
  have hu_β : u β = c := by
    ext; simp only [u, wordU, β]
    rw [if_neg (by omega)]; omega
  have hu_γ : u γ = c := by
    ext; simp only [u, wordU, γ]
    rw [if_neg (by omega)]; omega
  have hv_mem : ∀ j : Fin (3 * m), v j = c → j = α ∨ j = γ ∨ j = δ := by
    intro j hj
    have hv := congr_arg Fin.val hj
    simp only [v, wordV] at hv
    by_cases h1 : j.1 % 3 = 1
    · rw [if_pos h1] at hv
      right; left; ext; simp only [γ]; omega
    · rw [if_neg h1] at hv
      have hq_eq : j.1 / 3 = ip := by
        have hq_lt : j.1 / 3 < m := by omega
        change (j.1 / 3 + 1) % m = i at hv
        dsimp only [ip]
        by_cases hz : i = 0
        · rw [hz] at hv ⊢; simp only [zero_add]
          rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]
          by_cases htop : j.1 / 3 + 1 = m
          · omega
          · rw [Nat.mod_eq_of_lt (by omega : j.1 / 3 + 1 < m)] at hv; omega
        · have heq : i + m - 1 = (i - 1) + m := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < m)]
          by_cases htop : j.1 / 3 + 1 = m
          · rw [htop, Nat.mod_self] at hv; omega
          · rw [Nat.mod_eq_of_lt (by omega : j.1 / 3 + 1 < m)] at hv; omega
      by_cases h0 : j.1 % 3 = 0
      · right; right; ext; simp only [δ]; omega
      · left; ext; simp only [α]; omega
  -- Pairwise distinctness of `α, β, γ, δ`:
  have hαβ : α ≠ β := by intro h; have := congr_arg Fin.val h; simp only [α, β] at this; omega
  have hαγ : α ≠ γ := by intro h; have := congr_arg Fin.val h; simp only [α, γ] at this; omega
  have hαδ : α ≠ δ := by intro h; have := congr_arg Fin.val h; simp only [α, δ] at this; omega
  have hβγ : β ≠ γ := by intro h; have := congr_arg Fin.val h; simp only [β, γ] at this; omega
  have hβδ : β ≠ δ := by intro h; have := congr_arg Fin.val h; simp only [β, δ] at this; omega
  have hγδ : γ ≠ δ := by intro h; have := congr_arg Fin.val h; simp only [γ, δ] at this; omega
  -- Cyclic offsets measured from `P β`:
  let x : Fin (3 * m) → ℕ := fun j => (P j + L - P β) % L
  have hx_β : x β = 0 := by
    dsimp only [x]
    have hlt := hP_lt β
    have : P β + L - P β = L := by omega
    rw [this, Nat.mod_self]
  have hx_lt : ∀ j, x j < L := fun j => Nat.mod_lt _ hL_pos
  have hx_order : 0 < x γ ∧ x γ < x δ ∧ x δ < x α := by
    dsimp only [x]
    by_cases hz : i = 0
    · have hip_eq : ip = m - 1 := by
        dsimp only [ip]; rw [hz, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
      have h1 : P β < P γ := hP_mono (show β < γ by simp [Fin.lt_def, β, γ])
      have h2 : P γ < P δ := hP_mono (show γ < δ by simp [Fin.lt_def, γ, δ, hz, hip_eq]; omega)
      have h3 : P δ < P α := hP_mono (show δ < α by simp [Fin.lt_def, δ, α])
      have hPγ := hP_lt γ; have hPδ := hP_lt δ; have hPα := hP_lt α
      have eγ : (P γ + L - P β) % L = P γ - P β := by
        rw [show P γ + L - P β = (P γ - P β) + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have eδ : (P δ + L - P β) % L = P δ - P β := by
        rw [show P δ + L - P β = (P δ - P β) + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have eα : (P α + L - P β) % L = P α - P β := by
        rw [show P α + L - P β = (P α - P β) + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [eγ, eδ, eα]; omega
    · have hip_eq : ip = i - 1 := by
        dsimp only [ip]
        rw [show i + m - 1 = (i - 1) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h1 : P δ < P α := hP_mono (show δ < α by simp [Fin.lt_def, δ, α])
      have h2 : P α < P β := hP_mono (show α < β by simp [Fin.lt_def, α, β, hip_eq]; omega)
      have h3 : P β < P γ := hP_mono (show β < γ by simp [Fin.lt_def, β, γ])
      have hPγ := hP_lt γ; have hPβ := hP_lt β
      have eγ : (P γ + L - P β) % L = P γ - P β := by
        rw [show P γ + L - P β = (P γ - P β) + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have eδ : (P δ + L - P β) % L = P δ + L - P β := Nat.mod_eq_of_lt (by omega)
      have eα : (P α + L - P β) % L = P α + L - P β := Nat.mod_eq_of_lt (by omega)
      rw [eγ, eδ, eα]; omega
  -- Helper: `P j' = (P j + e) % L → x j' = (x j + e) % L`.
  have hx_step : ∀ j j' : Fin (3 * m), P j' = (P j + e) % L → x j' = (x j + e) % L := by
    intro j j' hP
    dsimp only [x]
    have hltj := hP_lt j; have hltβ := hP_lt β
    have h1 : (P j' + L - P β) % L = ((P j + e) % L + (L - P β)) % L := by
      rw [hP, show (P j + e) % L + L - P β = (P j + e) % L + (L - P β) by omega]
    have h2 : ((P j + L - P β) % L + e) % L = ((P j + (L - P β)) + e) % L := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        show P j + L - P β = P j + (L - P β) by omega]
    rw [h1, h2, Nat.add_mod ((P j + e) % L), Nat.mod_mod, ← Nat.add_mod]
    congr 1; omega
  -- Step 3: Apply `hc_step` to `α, β, γ` and deduce `2 * e = L`!
  obtain ⟨jα, hv_jα, hP_jα, hne_jα⟩ := hc_step α hu_α
  obtain ⟨jβ, hv_jβ, hP_jβ, hne_jβ⟩ := hc_step β hu_β
  obtain ⟨jγ, hv_jγ, hP_jγ, hne_jγ⟩ := hc_step γ hu_γ
  -- `jα, jβ, jγ` are pairwise distinct because `P` is injective and `e` is fixed:
  have hstep_inj : ∀ j₁ j₂ j₁' j₂' : Fin (3 * m),
      P j₁' = (P j₁ + e) % L → P j₂' = (P j₂ + e) % L → j₁' = j₂' → j₁ = j₂ := by
    intro j₁ j₂ j₁' j₂' h1 h2 heq
    subst heq
    have hmod : (P j₁ + e) % L = (P j₂ + e) % L := h1.symm.trans h2
    have hlt1 := hP_lt j₁; have hlt2 := hP_lt j₂
    have hPeq : P j₁ = P j₂ := by
      by_cases s1 : P j₁ + e < L <;> by_cases s2 : P j₂ + e < L
      · rw [Nat.mod_eq_of_lt s1, Nat.mod_eq_of_lt s2] at hmod; omega
      · rw [Nat.mod_eq_of_lt s1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt s2] at hmod; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
    exact hP_mono.injective hPeq
  have hjαβ : jα ≠ jβ := fun h => hαβ (hstep_inj α β jα jβ hP_jα hP_jβ h)
  have hjαγ : jα ≠ jγ := fun h => hαγ (hstep_inj α γ jα jγ hP_jα hP_jγ h)
  have hjβγ : jβ ≠ jγ := fun h => hβγ (hstep_inj β γ jβ jγ hP_jβ hP_jγ h)
  have harith := step3_arithmetic L e he_pos he_lt
  have h2e_eq_L : 2 * e = L := by
    have hα_c := hv_mem jα hv_jα
    have hβ_c := hv_mem jβ hv_jβ
    have hγ_c := hv_mem jγ hv_jγ
    rcases hβ_c with rfl | rfl | rfl
    · -- Case 2: `jβ = α`, forces `jα = γ`, `jγ = δ`!
      have hjγ_eq : jγ = δ := by
        rcases hγ_c with h | h | h
        · exact absurd h.symm hjβγ
        · exact absurd h hne_jγ
        · exact h
      have hjα_eq : jα = γ := by
        rcases hα_c with h | h | h
        · exact absurd h hne_jα
        · exact h
        · exact absurd (h.trans hjγ_eq.symm) hjαγ
      subst hjα_eq; subst hjγ_eq
      have hxα : x α = e := by
        have := hx_step β α hP_jβ; rw [hx_β, zero_add, Nat.mod_eq_of_lt he_lt] at this; exact this
      have hxγ : x γ = (2 * e) % L := by
        have := hx_step α γ hP_jα; rw [hxα] at this; rwa [show e + e = 2 * e by omega] at this
      have hxδ : x δ = (3 * e) % L := by
        have := hx_step γ δ hP_jγ
        rw [hxγ, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show 2 * e + e = 3 * e by omega] at this
        exact this
      rw [hxα, hxγ, hxδ] at hx_order
      exact absurd hx_order harith.1
    · -- Case 3: `jβ = γ`, forces `jγ = α`, `jα = δ`!
      have hjα_eq : jα = δ := by
        rcases hα_c with h | h | h
        · exact absurd h hne_jα
        · exact absurd h hjαβ
        · exact h
      have hjγ_eq : jγ = α := by
        rcases hγ_c with h | h | h
        · exact h
        · exact absurd h hne_jγ
        · exact absurd (hjα_eq.trans h.symm) hjαγ
      subst hjα_eq; subst hjγ_eq
      have hxγ : x γ = e := by
        have := hx_step β γ hP_jβ; rw [hx_β, zero_add, Nat.mod_eq_of_lt he_lt] at this; exact this
      have hxα : x α = (2 * e) % L := by
        have := hx_step γ α hP_jγ; rw [hxγ] at this; rwa [show e + e = 2 * e by omega] at this
      have hxδ : x δ = (3 * e) % L := by
        have := hx_step α δ hP_jα
        rw [hxα, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show 2 * e + e = 3 * e by omega] at this
        exact this
      rw [hxα, hxγ, hxδ] at hx_order
      exact absurd hx_order harith.2.1
    · -- Case 1: `jβ = δ`, forces `jα = γ` and `jγ = α`, hence `(2 * e) % L = 0`!
      have hjα_eq : jα = γ := by
        rcases hα_c with h | h | h
        · exact absurd h hne_jα
        · exact h
        · exact absurd h hjαβ
      have hjγ_eq : jγ = α := by
        rcases hγ_c with h | h | h
        · exact h
        · exact absurd h hne_jγ
        · exact absurd h.symm hjβγ
      subst hjα_eq; subst hjγ_eq
      have h1 := hx_step α γ hP_jα
      have h2 := hx_step γ α hP_jγ
      have hloop : x α = (x α + 2 * e) % L := by
        conv_lhs => rw [h2, h1]
        rw [Nat.add_mod ((x α + e) % L), Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      have h2e0 : (2 * e) % L = 0 := by
        have hxα_lt := hx_lt α
        by_cases h2L : 2 * e < L
        · by_cases hsum : x α + 2 * e < L
          · rw [Nat.mod_eq_of_lt hsum] at hloop; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hloop; omega
        · have hsub : 2 * e - L < L := by omega
          by_cases hsum : x α + (2 * e - L) < L
          · have : (x α + 2 * e) % L = x α + (2 * e - L) := by
              rw [show x α + 2 * e = (x α + (2 * e - L)) + L by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt hsum]
            rw [this] at hloop
            have : 2 * e = L := by omega
            rw [this, Nat.mod_self]
          · have : (x α + 2 * e) % L = x α + 2 * e - 2 * L := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
                Nat.mod_eq_of_lt (by omega)]; omega
            rw [this] at hloop; omega
      exact harith.2.2 h2e0
  -- Step 4: Antipodal swap at position `0` (`u 0 = 0`, `v 0 = 1`)!
  let j0 : Fin (3 * m) := ⟨0, by omega⟩
  have hu0 : u j0 = ⟨0, by omega⟩ := by
    ext; simp [u, wordU, j0]
  have hv0 : v j0 = ⟨1, by omega⟩ := by
    ext; simp [v, wordV, j0, Nat.mod_eq_of_lt (by omega : 1 < m)]
  set t0 := P j0
  have ht0_lt : t0 < L := hP_lt j0
  set t1 := (t0 + d) % L
  have ht1_lt : t1 < L := Nat.mod_lt _ hL_pos
  have ht1_back : (t1 + d) % L = t0 := by
    have h2d : (2 * d) % L = 0 :=
      calc (2 * d) % L = (2 % L * (d % L)) % L := Nat.mul_mod 2 d L
        _ = (2 % L * (e % L)) % L := by rw [show d % L = e from rfl, Nat.mod_eq_of_lt he_lt]
        _ = (2 * e) % L := (Nat.mul_mod 2 e L).symm
        _ = 0 := by rw [h2e_eq_L, Nat.mod_self]
    dsimp only [t1]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show t0 + d + d = t0 + 2 * d by omega,
      Nat.add_mod, h2d, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt ht0_lt]
  have hv't1 : v'[t1]'(hvlen ▸ ht1_lt) = ⟨0, by omega⟩ := by
    rw [← hshift' t0 ht0_lt, hu'_P j0, hu0]
  have hu't1 : u'[t1]'ht1_lt = ⟨1, by omega⟩ := by
    have h := hshift' t1 ht1_lt
    have h2 : v'[(t1 + d) % L]'(by rw [hvlen]; exact Nat.mod_lt _ hL_pos) = v'[t0]'(hvlen ▸ ht0_lt) := by
      congr 1
    rw [h, h2, hv'_P j0, hv0]
  have ht1_orig : ∃ j1 : Fin (3 * m), P j1 = t1 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨heq_uv, _⟩ := interleave_getElem_not_origPos (Finset.univ.erase c) u v ins hins t1 ht1_lt hnot
    rw [hu't1, hv't1] at heq_uv
    have := congr_arg Fin.val heq_uv
    simp at this
  rcases ht1_orig with ⟨j1, hj1⟩
  have hu1 : u j1 = ⟨1, by omega⟩ := by
    rw [← hu'_P j1]
    have : u'[P j1]'(hP_lt j1) = u'[t1]'ht1_lt := by congr 1
    exact this.trans hu't1
  have hv1 : v j1 = ⟨0, by omega⟩ := by
    rw [← hv'_P j1]
    have : v'[P j1]'(hvlen ▸ hP_lt j1) = v'[t1]'(hvlen ▸ ht1_lt) := by congr 1
    exact this.trans hv't1
  have h1val := congr_arg Fin.val hu1
  have h0val := congr_arg Fin.val hv1
  simp only [u, v, wordU, wordV] at h1val h0val
  by_cases hr1 : j1.1 % 3 = 1
  · rw [if_pos hr1] at h0val; rw [if_neg (by omega)] at h1val; omega
  · by_cases hr2 : j1.1 % 3 = 2
    · rw [if_pos hr2] at h1val; rw [if_neg hr1] at h0val; omega
    · rw [if_neg hr2] at h1val; rw [if_neg hr1] at h0val
      rw [h1val] at h0val
      rw [Nat.mod_eq_of_lt (by omega : 1 + 1 < m)] at h0val
      omega

/-! ### 4. Main Disproof for Arbitrary Alphabets of Size `≥ 3` and `m = 3` Full-Alphabet Witness -/

/-- **Transport lemma:** `CyclicallyEqualizable` is invariant under bijections of the alphabet. -/
private lemma cyclicallyEqualizable_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ≃ β) (σ : Finset α) {n : ℕ} (u v : Fin n → α)
    (h : CyclicallyEqualizable (σ.image f) (f ∘ u) (f ∘ v)) :
    CyclicallyEqualizable σ u v := by
  rcases h with ⟨ins, hins, hlen, d, hshift⟩
  refine ⟨fun k => (ins k).map f.symm, ?_, ?_⟩
  · intro k a ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp (hins k b hb) with ⟨x, hx, rfl⟩
    simpa using hx
  · have hinter : ∀ {m : ℕ} (ins' : Fin (m + 1) → List β) (w : Fin m → α),
        interleave w (fun k => (ins' k).map f.symm) = (interleave (f ∘ w) ins').map f.symm := by
      intro m
      induction m with
      | zero => intro ins' w; rfl
      | succ m ih =>
          intro ins' w
          simp only [interleave, List.map_append, List.map_cons, Function.comp_apply,
            Equiv.symm_apply_apply]
          congr 2
          exact ih (fun j => ins' j.succ) (fun j => w j.succ)
    refine ⟨by rw [hinter ins u, hinter ins v, List.length_map, List.length_map, hlen], d, ?_⟩
    intro t ht
    have htu : t < (interleave (f ∘ u) ins).length := by
      rw [hinter ins u, List.length_map] at ht; exact ht
    have hshift_t := hshift t htu
    have hmap_eq : ∀ (w : Fin n → α) (i : ℕ) (hi : i < (interleave w (fun k => (ins k).map f.symm)).length)
        (hi' : i < (interleave (f ∘ w) ins).length),
        (interleave w (fun k => (ins k).map f.symm))[i]'hi =
          f.symm ((interleave (f ∘ w) ins)[i]'hi') := by
      intro w i hi hi'
      have h1 : (interleave w (fun k => (ins k).map f.symm))[i]'hi =
          ((interleave (f ∘ w) ins).map f.symm)[i]'(by rwa [List.length_map]) := by
        congr 1; exact hinter ins w
      rw [h1, List.getElem_map]
    have hmod_len : (interleave v (fun k => (ins k).map f.symm)).length =
        (interleave (f ∘ v) ins).length := by rw [hinter ins v, List.length_map]
    rw [hmap_eq u t ht htu,
      hmap_eq v ((t + d) % (interleave v (fun k => (ins k).map f.symm)).length)
        (Nat.mod_lt _ (by omega))
        (by rw [hmod_len]; exact Nat.mod_lt _ (by omega))]
    congr 1
    convert hshift_t using 2
    rw [hmod_len]

/-- **Main Theorem (Disproof of Problem 2 / `prob:discard` of `arXiv:2607.18452v1`):**
For every finite alphabet `α` with `|α| ≥ 3`, there exist words `u, v` over `α` of length
`3|α|` that are permutations of each other, use every letter of `α`, and are NOT
`(α \ {c})`-cyclically equalizable for ANY letter `c ∈ α`. -/
theorem thongjarast_prob_discard_disproof {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) :
    ∃ (n : ℕ) (u v : Fin n → α),
      List.Perm (List.ofFn u) (List.ofFn v) ∧
      u ≠ v ∧
      Function.Surjective u ∧
      (∀ c : α, ¬ CyclicallyEqualizable (Finset.univ.erase c) u v) := by
  set m := Fintype.card α
  let e : Fin m ≃ α := (Fintype.equivFin α).symm
  refine ⟨3 * m, e ∘ wordU m hcard, e ∘ wordV m hcard, ?_, ?_, ?_, ?_⟩
  · rw [← List.map_ofFn, ← List.map_ofFn]
    exact (wordU_perm_wordV m hcard).map e
  · intro heq
    apply wordU_ne_wordV m hcard
    funext j
    exact e.injective (congr_fun heq j)
  · exact e.surjective.comp (wordU_surjective m hcard)
  · intro c hEq
    have himg : (Finset.univ.erase (e.symm c)).image e = Finset.univ.erase c := by
      ext a
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨x, hx, rfl⟩; intro h; exact hx (by simpa using congr_arg e.symm h)
      · intro hac; exact ⟨e.symm a, fun h => hac (by simpa using congr_arg e h), e.apply_symm_apply a⟩
    rw [← himg] at hEq
    exact family_not_equalizable m hcard (e.symm c)
      (cyclicallyEqualizable_map e (Finset.univ.erase (e.symm c)) (wordU m hcard) (wordV m hcard) hEq)

/-- **Contrast Theorem (Full-Alphabet Equalizability for `m = 3`):**
For the smallest counterexample `m = 3` (`u = aabbbccca`, `v = babcbcaca`),
`u` and `v` ARE `Σ`-cyclically equalizable when all 3 letters are allowed
(explicit length-15 insertion with cyclic shift `d = 10`). -/
theorem smallest_counterexample_full_alphabet_equalizable :
    CyclicallyEqualizable (Finset.univ : Finset (Fin 3))
      (wordU 3 (by decide)) (wordV 3 (by decide)) := by
  -- Insertions turning `001112220` / `101212020` into
  -- `001201012020120` / `101202012000120` (length 15, shift `d = 10`, since
  -- `u'[t] = v'[(t + 10) % 15]`).
  let ins : Fin 10 → List (Fin 3) :=
    ![[], [], [], [2, 0], [0], [], [0], [0, 1], [], []]
  refine ⟨ins, fun k a _ => Finset.mem_univ a, ?_⟩
  have hu : interleave (wordU 3 (by decide)) ins =
      [0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 2, 0, 1, 2, 0] := by decide
  have hv : interleave (wordV 3 (by decide)) ins =
      [1, 0, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 1, 2, 0] := by decide
  rw [hu, hv]
  refine ⟨rfl, 10, ?_⟩
  intro t ht
  have ht15 : t < 15 := ht
  interval_cases t <;> rfl

end ThongjarastCyclicEqualizability
