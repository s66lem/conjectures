import Mathlib

/-!
# Proof of Omar E. Pol's OEIS A400974, A280940, and A384225 Conjectures

This module gives a complete, self-contained proof of four interrelated OEIS conjectures
by Omar E. Pol connecting the symmetric representation of `σ(n)` (width word `A262045`,
per-part subpart counts `A280940`, central part subpart count `A384230`) to maximal
`2`-dense blocks of positive divisors of `n` (block lengths `A384222`, odd-divisor counts
`A384225`, central block length `A400974`), via the ruler function `A001511(n) = v₂(n) + 1`:

1. **OEIS A280940 (Jan 13 2026) & OEIS A384225 Conjecture 1 (Oct 13 2026):**
   For every `n ≥ 1`, the sequence of per-part width-one layer subpart counts (`A280940`)
   equals the sequence of odd-divisor counts in the maximal `2`-dense divisor blocks (`A384225`).
2. **OEIS A384225 Conjecture 2 (Oct 13 2026):**
   For every `n ≥ 1`, each maximal `2`-dense block has length equal to `(v₂(n) + 1)` times
   the number of odd divisors in that block (`A384222(n, k) = A001511(n) * A384225(n, k)`).
3. **OEIS A400974 (Oct 11 2026):**
   For every `n ≥ 1`, `A400974(n) = A001511(n) * A384230(n)`.
-/

namespace PolA400974

open Finset

/-! ### Section 1: List utilities (stutter compression, positive parts, layer runs, 2-dense blocks) -/

/-- Collapse consecutive equal elements in a list. -/
def dedupAdj : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => if x = y then dedupAdj (y :: xs) else x :: dedupAdj (y :: xs)

lemma dedupAdj_cons_same (x : ℕ) (xs : List ℕ) :
    dedupAdj (x :: x :: xs) = dedupAdj (x :: xs) := by
  simp [dedupAdj]

lemma dedupAdj_cons_ne {x y : ℕ} (h : x ≠ y) (xs : List ℕ) :
    dedupAdj (x :: y :: xs) = x :: dedupAdj (y :: xs) := by
  simp [dedupAdj, h]

lemma dedupAdj_ne_nil {L : List ℕ} (h : L ≠ []) : dedupAdj L ≠ [] := by
  match L with
  | [] => contradiction
  | [x] => simp [dedupAdj]
  | x :: y :: xs =>
    by_cases hxy : x = y
    · subst hxy
      rw [dedupAdj_cons_same]
      exact dedupAdj_ne_nil (List.cons_ne_nil _ _)
    · rw [dedupAdj_cons_ne hxy]
      exact List.cons_ne_nil _ _

lemma head_dedupAdj {x : ℕ} {xs : List ℕ} :
    (dedupAdj (x :: xs)).head (dedupAdj_ne_nil (List.cons_ne_nil x xs)) = x := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy
      simpa [dedupAdj] using ih (x := x)
    · simp [dedupAdj, hxy]

lemma headD_dedupAdj (x : ℕ) (xs : List ℕ) :
    (dedupAdj (x :: xs)).headD 0 = x := by
  have hne := dedupAdj_ne_nil (List.cons_ne_nil x xs)
  have hhd : (dedupAdj (x :: xs)).head hne = x := head_dedupAdj
  cases h : dedupAdj (x :: xs) with
  | nil => exact absurd h hne
  | cons z zs =>
    simp only [h, List.head_cons] at hhd
    simpa [List.headD_cons] using hhd

lemma dedupAdj_idem (M : List ℕ) : dedupAdj (dedupAdj M) = dedupAdj M := by
  induction M with
  | nil => rfl
  | cons x xs ih =>
    match xs with
    | [] => rfl
    | y :: ys =>
      by_cases hxy : x = y
      · subst hxy; simpa [dedupAdj] using ih
      · rw [dedupAdj_cons_ne hxy]
        have hhd := headD_dedupAdj y ys
        cases hD : dedupAdj (y :: ys) with
        | nil => exact absurd hD (dedupAdj_ne_nil (List.cons_ne_nil y ys))
        | cons z zs =>
          rw [hD, List.headD_cons] at hhd; subst hhd
          rw [dedupAdj_cons_ne hxy, ← hD, ih]

lemma dedupAdj_append_same_boundary (L₁ L₂ : List ℕ) (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ [])
    (hb : L₁.getLast h₁ = L₂.head h₂) :
    dedupAdj (L₁ ++ L₂) = dedupAdj L₁ ++ (dedupAdj L₂).tail := by
  induction L₁ with
  | nil => contradiction
  | cons x xs ih =>
    match xs with
    | [] =>
      match L₂ with
      | [] => contradiction
      | y :: ys =>
        simp only [List.getLast_singleton, List.head_cons] at hb
        subst hb
        simp only [List.singleton_append, dedupAdj_cons_same, dedupAdj]
        have hne : dedupAdj (x :: ys) ≠ [] := dedupAdj_ne_nil (List.cons_ne_nil x ys)
        have hhd : (dedupAdj (x :: ys)).head hne = x := head_dedupAdj
        cases hEq : dedupAdj (x :: ys) with
        | nil => exact absurd hEq hne
        | cons z zs =>
          simp only [hEq, List.head_cons] at hhd
          subst hhd
          simp
    | y :: ys =>
      have hne : y :: ys ≠ [] := List.cons_ne_nil y ys
      have hb' : (y :: ys).getLast hne = L₂.head h₂ := by
        simpa [List.getLast_cons hne] using hb
      have hrec := ih hne hb'
      by_cases hxy : x = y
      · subst hxy
        simp only [List.cons_append, dedupAdj_cons_same]
        simpa [List.cons_append] using hrec
      · simp only [List.cons_append, dedupAdj_cons_ne hxy]
        simpa [List.cons_append] using congrArg (x :: ·) hrec

lemma dedupAdj_append_ne_boundary (L₁ L₂ : List ℕ) (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ [])
    (hb : L₁.getLast h₁ ≠ L₂.head h₂) :
    dedupAdj (L₁ ++ L₂) = dedupAdj L₁ ++ dedupAdj L₂ := by
  induction L₁ with
  | nil => contradiction
  | cons x xs ih =>
    match xs with
    | [] =>
      match L₂ with
      | [] => contradiction
      | y :: ys =>
        simp only [List.getLast_singleton, List.head_cons] at hb
        simp [dedupAdj, hb]
    | y :: ys =>
      have hne : y :: ys ≠ [] := List.cons_ne_nil y ys
      have hb' : (y :: ys).getLast hne ≠ L₂.head h₂ := by
        simpa [List.getLast_cons hne] using hb
      have hrec := ih hne hb'
      by_cases hxy : x = y
      · subst hxy
        simp only [List.cons_append, dedupAdj_cons_same]
        simpa [List.cons_append] using hrec
      · simp only [List.cons_append, dedupAdj_cons_ne hxy]
        simpa [List.cons_append] using congrArg (x :: ·) hrec

lemma dedupAdj_reverse (L : List ℕ) : dedupAdj L.reverse = (dedupAdj L).reverse := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    match xs with
    | [] => rfl
    | y :: ys =>
      have hne : (y :: ys).reverse ≠ [] := by simp
      have hlast : (y :: ys).reverse.getLast hne = y := by simp
      rw [List.reverse_cons]
      by_cases hxy : x = y
      · subst hxy
        rw [dedupAdj_append_same_boundary (x :: ys).reverse [x] hne (List.cons_ne_nil _ _)
            (by simp)]
        rw [dedupAdj_cons_same, ih]
        simp [dedupAdj]
      · rw [dedupAdj_append_ne_boundary (y :: ys).reverse [x] hne (List.cons_ne_nil _ _)
            (by rw [hlast]; simp [ne_comm.mp hxy])]
        rw [dedupAdj_cons_ne hxy, List.reverse_cons, ← List.reverse_cons (a := y) (as := ys), ih]
        simp [dedupAdj]

/-- Auxiliary accumulator for splitting a list of natural numbers into maximal contiguous
positive runs (`> 0`). -/
def posPartsAux (cur : List ℕ) : List ℕ → List (List ℕ)
  | [] => if cur.isEmpty then [] else [cur.reverse]
  | 0 :: xs =>
    if cur.isEmpty then posPartsAux [] xs
    else cur.reverse :: posPartsAux [] xs
  | (a + 1) :: xs => posPartsAux ((a + 1) :: cur) xs

/-- Maximal contiguous runs of positive (`> 0`) entries in `L`. -/
def posParts (L : List ℕ) : List (List ℕ) := posPartsAux [] L

lemma posPartsAux_append_zero (cur L₁ L₂ : List ℕ) :
    posPartsAux cur (L₁ ++ 0 :: L₂) = posPartsAux cur L₁ ++ posPartsAux [] L₂ := by
  induction L₁ generalizing cur with
  | nil =>
    cases cur with
    | nil => simp [posPartsAux]
    | cons c cs => simp [posPartsAux]
  | cons x xs ih =>
    cases x with
    | zero =>
      cases cur with
      | nil => simpa [posPartsAux] using ih []
      | cons c cs => simpa [posPartsAux] using ih []
    | succ a =>
      simpa [posPartsAux] using ih ((a + 1) :: cur)

lemma posParts_append_zero (L₁ L₂ : List ℕ) :
    posParts (L₁ ++ 0 :: L₂) = posParts L₁ ++ posParts L₂ :=
  posPartsAux_append_zero [] L₁ L₂

lemma posPartsAux_all_pos (cur L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) :
    posPartsAux cur L = if (L.reverse ++ cur).isEmpty then [] else [(L.reverse ++ cur).reverse] := by
  induction L generalizing cur with
  | nil => simp [posPartsAux]
  | cons x xs ih =>
    cases x with
    | zero =>
      have := hpos 0 List.mem_cons_self
      omega
    | succ a =>
      have hxs : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
      simpa [posPartsAux, List.reverse_cons, List.append_assoc] using ih ((a + 1) :: cur) hxs

lemma posParts_all_pos {L : List ℕ} (hne : L ≠ []) (hpos : ∀ x ∈ L, 0 < x) :
    posParts L = [L] := by
  unfold posParts
  rw [posPartsAux_all_pos [] L hpos]
  simp [hne]

lemma posPartsAux_dedupAdj_cur (L : List ℕ) :
    ∀ cur : List ℕ,
      (posPartsAux (dedupAdj cur) L).map dedupAdj = (posPartsAux cur L).map dedupAdj := by
  induction L with
  | nil =>
    intro cur
    cases cur with
    | nil => rfl
    | cons c cs =>
      have hne : dedupAdj (c :: cs) ≠ [] := dedupAdj_ne_nil (List.cons_ne_nil c cs)
      have hne_b : (dedupAdj (c :: cs)).isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
      simp only [posPartsAux, hne_b, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.map_singleton]
      rw [dedupAdj_reverse, dedupAdj_reverse, dedupAdj_idem]
  | cons x xs ih =>
    intro cur
    cases x with
    | zero =>
      cases cur with
      | nil => simp [posPartsAux, dedupAdj]
      | cons c cs =>
        have hne : dedupAdj (c :: cs) ≠ [] := dedupAdj_ne_nil (List.cons_ne_nil c cs)
        have hne_b : (dedupAdj (c :: cs)).isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
        simp only [posPartsAux, hne_b, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
          List.map_cons]
        congr 1
        rw [dedupAdj_reverse, dedupAdj_reverse, dedupAdj_idem]
    | succ a =>
      simp only [posPartsAux]
      have h1 := ih ((a + 1) :: cur)
      have h2 := ih ((a + 1) :: dedupAdj cur)
      have hsame : dedupAdj ((a + 1) :: dedupAdj cur) = dedupAdj ((a + 1) :: cur) := by
        cases cur with
        | nil => rfl
        | cons c cs =>
          have hhd := headD_dedupAdj c cs
          cases hD : dedupAdj (c :: cs) with
          | nil => exact absurd hD (dedupAdj_ne_nil (List.cons_ne_nil c cs))
          | cons z zs =>
            rw [hD, List.headD_cons] at hhd
            rw [hhd] at hD ⊢
            by_cases hac : a + 1 = c
            · subst hac; rw [dedupAdj_cons_same, dedupAdj_cons_same, ← hD, dedupAdj_idem]
            · rw [dedupAdj_cons_ne hac, dedupAdj_cons_ne hac, ← hD, dedupAdj_idem]
      rw [← h2, hsame, h1]

lemma posParts_dedupAdj_aux (cur : List ℕ) (L : List ℕ) :
    (posPartsAux cur (dedupAdj L)).map dedupAdj =
      (posPartsAux cur L).map dedupAdj := by
  induction L generalizing cur with
  | nil => rfl
  | cons x xs ih =>
    match xs with
    | [] => rfl
    | y :: ys =>
      by_cases hxy : x = y
      · subst hxy
        rw [dedupAdj_cons_same]
        cases x with
        | zero =>
          cases cur with
          | nil => simpa [posPartsAux] using ih []
          | cons c cs =>
            have hhd := headD_dedupAdj 0 ys
            cases hD : dedupAdj (0 :: ys) with
            | nil => exact absurd hD (dedupAdj_ne_nil (List.cons_ne_nil 0 ys))
            | cons z zs =>
              rw [hD, List.headD_cons] at hhd; subst hhd
              simp only [posPartsAux, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
                List.map_cons]
              congr 1
              have hrec := ih []
              rw [hD] at hrec
              simpa [posPartsAux] using hrec
        | succ a =>
          rw [ih cur]
          simp only [posPartsAux]
          have h1 := posPartsAux_dedupAdj_cur ys ((a + 1) :: cur)
          have h2 := posPartsAux_dedupAdj_cur ys ((a + 1) :: (a + 1) :: cur)
          rw [dedupAdj_cons_same] at h2
          exact h1.symm.trans h2
      · rw [dedupAdj_cons_ne hxy]
        cases x with
        | zero =>
          cases cur with
          | nil => simpa [posPartsAux] using ih []
          | cons c cs =>
            simp only [posPartsAux, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
              List.map_cons]
            congr 1
            exact ih []
        | succ a =>
          simp only [posPartsAux]
          exact ih ((a + 1) :: cur)

lemma posParts_dedupAdj (L : List ℕ) :
    (posParts (dedupAdj L)).map dedupAdj = (posParts L).map dedupAdj :=
  posParts_dedupAdj_aux [] L

/-- Number of upward crossings across height `h` starting from previous height `prev`. -/
def risesAtHeight (h : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | prev, x :: xs => (if prev < h ∧ h ≤ x then 1 else 0) + risesAtHeight h x xs

/-- Total upward variation starting from `prev`. -/
def totalRise : ℕ → List ℕ → ℕ
  | _, [] => 0
  | prev, x :: xs => (x - prev) + totalRise x xs

/-- Number of maximal contiguous runs of entries `≥ h` in `p`. -/
def runsAtHeight (h : ℕ) (p : List ℕ) : ℕ :=
  (posParts (p.map (fun x => if h ≤ x then 1 else 0))).length

/-- Number of width-one layer subparts in a part `p` (sum of `runsAtHeight h p` over `1 ≤ h ≤ max p`). -/
def layerRuns (p : List ℕ) : ℕ :=
  ∑ h ∈ Finset.Icc 1 (p.foldr max 0), runsAtHeight h p

lemma posPartsAux_length_ind (h : ℕ) (cur : List ℕ) (prev : ℕ) (p : List ℕ)
    (hcur : cur.isEmpty = decide (prev < h)) :
    (posPartsAux cur (p.map (fun x => if h ≤ x then 1 else 0))).length =
      (if cur.isEmpty then 0 else 1) + risesAtHeight h prev p := by
  induction p generalizing cur prev with
  | nil =>
    cases cur with
    | nil => simp [posPartsAux, risesAtHeight]
    | cons c cs => simp [posPartsAux, risesAtHeight]
  | cons x xs ih =>
    simp only [List.map_cons, risesAtHeight]
    by_cases hx : h ≤ x
    · have hnot : ¬ (x < h) := by omega
      simp only [if_pos hx, posPartsAux]
      have hrec := ih (1 :: cur) x (by simp [hnot])
      rw [hrec]
      cases hce : cur.isEmpty with
      | true =>
        have hlt : prev < h := of_decide_eq_true (hcur.symm.trans hce)
        simp [hlt, hx]
      | false =>
        have hge : ¬ (prev < h) := of_decide_eq_false (hcur.symm.trans hce)
        simp [hge]
    · have hlt_x : x < h := by omega
      simp only [if_neg hx, posPartsAux]
      have hrec := ih [] x (by simp [hlt_x])
      cases hce : cur.isEmpty with
      | true =>
        simp only [↓reduceIte, zero_add, if_neg (show ¬ (prev < h ∧ h ≤ x) by omega)]
        simpa using hrec
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons,
          if_neg (show ¬ (prev < h ∧ h ≤ x) by omega), zero_add]
        rw [hrec]
        simp [add_comm]

lemma runsAtHeight_eq_risesAtHeight (h : ℕ) (hh : 1 ≤ h) (p : List ℕ) :
    runsAtHeight h p = risesAtHeight h 0 p := by
  unfold runsAtHeight posParts
  have h0 : ([] : List ℕ).isEmpty = decide (0 < h) := by
    simp [show 0 < h by omega]
  simpa using posPartsAux_length_ind h [] 0 p h0

lemma sum_risesAtHeight_eq_totalRise (M prev : ℕ) (p : List ℕ)
    (hprev : prev ≤ M) (hp : ∀ x ∈ p, x ≤ M) :
    ∑ h ∈ Finset.Icc 1 M, risesAtHeight h prev p = totalRise prev p := by
  induction p generalizing prev with
  | nil => simp [risesAtHeight, totalRise]
  | cons x xs ih =>
    simp only [risesAtHeight, totalRise, Finset.sum_add_distrib]
    have hxM : x ≤ M := hp x List.mem_cons_self
    have hxsM : ∀ y ∈ xs, y ≤ M := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    rw [ih x hxM hxsM]
    congr 1
    have hfilter : (Finset.Icc 1 M).filter (fun h => prev < h ∧ h ≤ x) = Finset.Ioc prev x := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
      hfilter, Nat.card_Ioc]

lemma le_foldr_max {p : List ℕ} {x : ℕ} (hx : x ∈ p) : x ≤ p.foldr max 0 := by
  induction p with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma layerRuns_eq_totalRise (p : List ℕ) : layerRuns p = totalRise 0 p := by
  unfold layerRuns
  have hcongr : ∑ h ∈ Finset.Icc 1 (p.foldr max 0), runsAtHeight h p =
      ∑ h ∈ Finset.Icc 1 (p.foldr max 0), risesAtHeight h 0 p := by
    apply Finset.sum_congr rfl
    intro h hh
    exact runsAtHeight_eq_risesAtHeight h (Finset.mem_Icc.mp hh).1 p
  rw [hcongr]
  exact sum_risesAtHeight_eq_totalRise (p.foldr max 0) 0 p (Nat.zero_le _)
    (fun x hx => le_foldr_max hx)

lemma totalRise_dedupAdj (prev : ℕ) (p : List ℕ) :
    totalRise prev (dedupAdj p) = totalRise prev p := by
  induction p generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    match xs with
    | [] => rfl
    | y :: ys =>
      by_cases hxy : x = y
      · subst hxy
        rw [dedupAdj_cons_same, ih prev]
        simp [totalRise]
      · rw [dedupAdj_cons_ne hxy]
        simp only [totalRise, ih x]

lemma layerRuns_dedupAdj (p : List ℕ) : layerRuns (dedupAdj p) = layerRuns p := by
  rw [layerRuns_eq_totalRise, layerRuns_eq_totalRise, totalRise_dedupAdj]

/-- Partition a sorted list of positive divisors into maximal `2`-dense blocks
(splitting whenever the next divisor exceeds twice the previous one). -/
def denseBlocksAux (prev : ℕ) (cur : List ℕ) : List ℕ → List (List ℕ)
  | [] => [cur.reverse]
  | x :: xs =>
    if x ≤ 2 * prev then denseBlocksAux x (x :: cur) xs
    else cur.reverse :: denseBlocksAux x [x] xs

def denseBlocks : List ℕ → List (List ℕ)
  | [] => []
  | x :: xs => denseBlocksAux x [x] xs

/-- Middle element of a list of odd length, or `0` if the list has even length. -/
def middleOrZero (L : List ℕ) : ℕ :=
  if L.length % 2 = 1 then L.getD (L.length / 2) 0 else 0

lemma middleOrZero_map_mul (c : ℕ) (L : List ℕ) :
    middleOrZero (L.map (fun x => c * x)) = c * middleOrZero L := by
  unfold middleOrZero
  rw [List.length_map]
  split_ifs with h
  · have hlt : L.length / 2 < L.length := by omega
    rw [List.getD_eq_getElem _ _ (by simpa using hlt),
      List.getD_eq_getElem _ _ hlt, List.getElem_map]
  · simp

/-! ### Section 2: OEIS definitions (`A237048`, `A249223`, `A262045`, `A280940`, `A384222`, `A384225`, `A384230`, `A400974`) -/

/-- `triMax n = max { j | j * (j + 1) ≤ 2 * n }`. -/
def triMax (n : ℕ) : ℕ := (Nat.sqrt (8 * n + 1) - 1) / 2

lemma le_triMax_iff (n j : ℕ) : j ≤ triMax n ↔ j * (j + 1) ≤ 2 * n := by
  unfold triMax
  have hs1 : 1 ≤ Nat.sqrt (8 * n + 1) := by
    rw [Nat.le_sqrt]; omega
  constructor
  · intro h
    have h2 : 2 * j + 1 ≤ Nat.sqrt (8 * n + 1) := by omega
    have hsq := (Nat.le_sqrt).mp h2
    nlinarith
  · intro h
    have hsq : (2 * j + 1) * (2 * j + 1) ≤ 8 * n + 1 := by nlinarith
    have h2 : 2 * j + 1 ≤ Nat.sqrt (8 * n + 1) := (Nat.le_sqrt).mpr hsq
    omega

/-- OEIS A237048 indicator for `1 ≤ j ≤ triMax n`. -/
def a237048 (n j : ℕ) : ℤ :=
  if j ∣ (n - j * (j + 1) / 2) then 1 else 0

/-- OEIS A249223 alternating partial sum of `A237048`. -/
def a249223 (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (j + 1) * a237048 n j

/-- Half-width word `[w_1, ..., w_r]` (nonnegative entries). -/
def halfWidths (n : ℕ) : List ℕ :=
  (List.range' 1 (triMax n)).map (fun k => (a249223 n k).toNat)

/-- Full width word of the symmetric representation of `σ(n)` (OEIS A262045). -/
def a262045 (n : ℕ) : List ℕ :=
  halfWidths n ++ (halfWidths n).reverse

/-- Sorted positive divisors of `n`. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  n.divisors.sort (· ≤ ·)

/-- OEIS A001511 (ruler function): `v₂(n) + 1`. -/
def a001511 (n : ℕ) : ℕ := padicValNat 2 n + 1

/-- Row `n` of OEIS A280940: width-one layer subpart counts of the parts of `σ(n)`. -/
def a280940Row (n : ℕ) : List ℕ :=
  (posParts (a262045 n)).map layerRuns

/-- Row `n` of OEIS A384222: lengths of maximal `2`-dense divisor blocks of `n`. -/
def a384222Row (n : ℕ) : List ℕ :=
  (denseBlocks (sortedDivisors n)).map List.length

/-- Row `n` of OEIS A384225: odd-divisor counts of maximal `2`-dense divisor blocks of `n`. -/
def a384225Row (n : ℕ) : List ℕ :=
  (denseBlocks (sortedDivisors n)).map (fun b => (b.filter (fun d => d % 2 = 1)).length)

/-- OEIS A384230: subparts in the central part of the symmetric representation of `σ(n)`. -/
def a384230 (n : ℕ) : ℕ := middleOrZero (a280940Row n)

/-- OEIS A400974: length of the central `2`-dense sublist of divisors of `n` (or `0`). -/
def a400974 (n : ℕ) : ℕ := middleOrZero (a384222Row n)

/-! ### Section 3: Interval-count width function `W n x` and exact match with `A249223` -/

/-- Odd part `m` of `n` (`n = 2^(v₂(n)) * m`). -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ (padicValNat 2 n)

/-- Dyadic scale `Q = 2^(v₂(n) + 1)`. -/
def dyadicQ (n : ℕ) : ℕ := 2 ^ (padicValNat 2 n + 1)

lemma pow_two_mul_oddPart (n : ℕ) : 2 ^ (padicValNat 2 n) * oddPart n = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

lemma oddPart_odd {n : ℕ} (hn : 0 < n) : oddPart n % 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  have h2 : 2 ∣ oddPart n := by omega
  rcases h2 with ⟨k, hk⟩
  have hdvd : 2 ^ (padicValNat 2 n + 1) ∣ n := by
    refine ⟨k, ?_⟩
    calc n = 2 ^ padicValNat 2 n * oddPart n := (pow_two_mul_oddPart n).symm
      _ = 2 ^ padicValNat 2 n * (2 * k) := by rw [hk]
      _ = 2 ^ (padicValNat 2 n + 1) * k := by rw [pow_succ]; ring
  have hle := (padicValNat_dvd_iff_le (Nat.ne_of_gt hn)).mp hdvd
  omega

lemma oddPart_pos {n : ℕ} (hn : 0 < n) : 0 < oddPart n := by
  have h := pow_two_mul_oddPart n
  by_contra h0
  have : oddPart n = 0 := by omega
  rw [this, mul_zero] at h
  omega

lemma dyadicQ_mul_oddPart (n : ℕ) : dyadicQ n * oddPart n = 2 * n := by
  unfold dyadicQ
  rw [pow_succ', mul_assoc, pow_two_mul_oddPart]

/-- Interval count `W n x = #{ d ∣ oddPart n | d ≤ x < dyadicQ n * d }`. -/
def W (n x : ℕ) : ℕ :=
  ((oddPart n).divisors.filter (fun d => d ≤ x ∧ x < dyadicQ n * d)).card

lemma W_zero (n : ℕ) : W n 0 = 0 := by
  unfold W
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  omega

lemma W_step_int {n : ℕ} (hn : 0 < n) (x : ℕ) :
    (W n (x + 1) : ℤ) - (W n x : ℤ) =
      (if (x + 1) ∣ oddPart n then (1 : ℤ) else 0) -
      (if ∃ d ∈ (oddPart n).divisors, x + 1 = dyadicQ n * d then (1 : ℤ) else 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm_pos : 0 < oddPart n := oddPart_pos hn
  have hQ_ge2 : 2 ≤ dyadicQ n := by
    unfold dyadicQ
    have : 1 ≤ 2 ^ padicValNat 2 n := Nat.one_le_pow _ 2 (by omega)
    rw [pow_succ']; omega
  set S0 := (oddPart n).divisors.filter (fun d => d ≤ x ∧ x < dyadicQ n * d)
  set S1 := (oddPart n).divisors.filter (fun d => d ≤ x + 1 ∧ x + 1 < dyadicQ n * d)
  set A := (oddPart n).divisors.filter (fun d => d = x + 1)
  set B := (oddPart n).divisors.filter (fun d => dyadicQ n * d = x + 1)
  set M := (oddPart n).divisors.filter (fun d => d ≤ x ∧ x + 1 < dyadicQ n * d)
  have hS1 : S1 = M ∪ A := by
    ext d
    simp only [S1, M, A, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hd, h1, h2⟩
      by_cases hdx : d ≤ x
      · exact Or.inl ⟨hd, hdx, h2⟩
      · exact Or.inr ⟨hd, by omega⟩
    · rintro (⟨hd, h1, h2⟩ | ⟨hd, rfl⟩)
      · exact ⟨hd, by omega, h2⟩
      · exact ⟨hd, le_refl _, by nlinarith [Nat.pos_of_mem_divisors hd]⟩
  have hS0 : S0 = M ∪ B := by
    ext d
    simp only [S0, M, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hd, h1, h2⟩
      by_cases hlt : x + 1 < dyadicQ n * d
      · exact Or.inl ⟨hd, h1, hlt⟩
      · exact Or.inr ⟨hd, by omega⟩
    · rintro (⟨hd, h1, h2⟩ | ⟨hd, hEq⟩)
      · exact ⟨hd, h1, by omega⟩
      · have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
        have : d ≤ x := by nlinarith
        exact ⟨hd, this, by omega⟩
  have hMA : Disjoint M A := by
    rw [Finset.disjoint_filter]; intro d _ h1 h2; omega
  have hMB : Disjoint M B := by
    rw [Finset.disjoint_filter]; intro d _ h1 h2; omega
  have hAcard : (A.card : ℤ) = if (x + 1) ∣ oddPart n then 1 else 0 := by
    split_ifs with hdvd
    · have hmem : x + 1 ∈ (oddPart n).divisors :=
        Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt hm_pos⟩
      have hAeq : A = {x + 1} := by
        ext d; simp only [A, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl; exact ⟨hmem, rfl⟩
      rw [hAeq, Finset.card_singleton]; rfl
    · have hAeq : A = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d hd heq
        rw [heq] at hd
        exact hdvd (Nat.dvd_of_mem_divisors hd)
      rw [hAeq, Finset.card_empty]; rfl
  have hBcard : (B.card : ℤ) =
      if ∃ d ∈ (oddPart n).divisors, x + 1 = dyadicQ n * d then 1 else 0 := by
    split_ifs with hex
    · rcases hex with ⟨d₀, hd₀, heq⟩
      have hBeq : B = {d₀} := by
        ext d; simp only [B, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hq⟩
          have : dyadicQ n * d = dyadicQ n * d₀ := by omega
          exact Nat.eq_of_mul_eq_mul_left (by omega) this
        · rintro rfl; exact ⟨hd₀, heq.symm⟩
      rw [hBeq, Finset.card_singleton]; rfl
    · have hBeq : B = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d hd hq
        exact hex ⟨d, hd, hq.symm⟩
      rw [hBeq, Finset.card_empty]; rfl
  change (S1.card : ℤ) - (S0.card : ℤ) = _
  rw [hS1, hS0, Finset.card_union_of_disjoint hMA, Finset.card_union_of_disjoint hMB]
  push_cast
  rw [hAcard, hBcard]
  ring

lemma a237048_characterization {n j : ℕ} (hn : 0 < n) (hj1 : 1 ≤ j) (hjr : j ≤ triMax n) :
    (j ∣ (n - j * (j + 1) / 2)) ↔
      ((j % 2 = 1 ∧ j ∣ oddPart n) ∨
       (j % 2 = 0 ∧ ∃ d ∈ (oddPart n).divisors, j = dyadicQ n * d)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htri : j * (j + 1) ≤ 2 * n := (le_triMax_iff n j).mp hjr
  have heven : 2 ∣ j * (j + 1) := Nat.even_mul_succ_self j |>.two_dvd
  have hmul2 : 2 * (j * (j + 1) / 2) = j * (j + 1) := Nat.mul_div_cancel' heven
  have hhalf_le : j * (j + 1) / 2 ≤ n := by omega
  have hm_odd : oddPart n % 2 = 1 := oddPart_odd hn
  have hm_pos : 0 < oddPart n := oddPart_pos hn
  have hQm : dyadicQ n * oddPart n = 2 * n := dyadicQ_mul_oddPart n
  -- First show: `j ∣ n - j*(j+1)/2 ↔ j ∣ 2*n ∧ (2*n / j) % 2 ≠ j % 2`
  have hstep1 : (j ∣ (n - j * (j + 1) / 2)) ↔ (j ∣ 2 * n ∧ (2 * n / j) % 2 ≠ j % 2) := by
    constructor
    · rintro ⟨q, hq⟩
      have h2eq : 2 * n = j * (2 * q + j + 1) := by
        have hq2 : 2 * (n - j * (j + 1) / 2) = 2 * (j * q) := congrArg (2 * ·) hq
        have hsub : 2 * n - 2 * (j * (j + 1) / 2) = 2 * (j * q) := by omega
        rw [hmul2] at hsub
        have hadd : 2 * n = 2 * (j * q) + j * (j + 1) := by omega
        linarith
      have hdvd : j ∣ 2 * n := ⟨2 * q + j + 1, h2eq⟩
      have hdiv : 2 * n / j = 2 * q + j + 1 := by
        rw [h2eq, Nat.mul_div_right _ (by omega)]
      exact ⟨hdvd, by omega⟩
    · rintro ⟨⟨t, ht⟩, hpar⟩
      have ht_eq : 2 * n / j = t := by rw [ht, Nat.mul_div_right _ (by omega)]
      rw [ht_eq] at hpar
      have hge : j + 1 ≤ t := by nlinarith
      have hev_diff : 2 ∣ (t - (j + 1)) := by omega
      rcases hev_diff with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have hteq : t = 2 * q + j + 1 := by omega
      have h2n : 2 * n = 2 * (j * q) + 2 * (j * (j + 1) / 2) := by
        rw [hmul2, ht, hteq]; ring
      omega
  rw [hstep1]
  constructor
  · rintro ⟨⟨t, ht⟩, hpar⟩
    have ht_eq : 2 * n / j = t := by rw [ht, Nat.mul_div_right _ (by omega)]
    rw [ht_eq] at hpar
    by_cases hjodd : j % 2 = 1
    · left
      refine ⟨hjodd, ?_⟩
      have hcop : Nat.Coprime j (dyadicQ n) := by
        unfold dyadicQ
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm]
        exact Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      have hmul : j ∣ dyadicQ n * oddPart n := by rw [hQm]; exact ⟨t, ht⟩
      exact hcop.dvd_of_dvd_mul_left hmul
    · right
      have hjeven : j % 2 = 0 := by omega
      have htodd : t % 2 = 1 := by omega
      refine ⟨hjeven, ?_⟩
      have hcop_t : Nat.Coprime (dyadicQ n) t := by
        unfold dyadicQ
        apply Nat.Coprime.pow_left
        exact Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      have hQ_dvd : dyadicQ n ∣ j := by
        have hmul : dyadicQ n ∣ j * t := by rw [← ht, ← hQm]; exact dvd_mul_right _ _
        exact hcop_t.dvd_of_dvd_mul_right hmul
      rcases hQ_dvd with ⟨d, rfl⟩
      have hd_dvd : d ∣ oddPart n := by
        refine ⟨t, ?_⟩
        have hQpos : 0 < dyadicQ n := by unfold dyadicQ; positivity
        have : dyadicQ n * oddPart n = dyadicQ n * (d * t) := by
          rw [hQm, ht]; ring
        exact Nat.eq_of_mul_eq_mul_left hQpos this
      exact ⟨d, Nat.mem_divisors.mpr ⟨hd_dvd, Nat.ne_of_gt hm_pos⟩, rfl⟩
  · rintro (⟨hjodd, hdvd_m⟩ | ⟨hjeven, d, hd, rfl⟩)
    · rcases hdvd_m with ⟨u, hu⟩
      have h2n : 2 * n = j * (dyadicQ n * u) := by
        rw [← hQm, hu]; ring
      have hQeven : 2 ∣ dyadicQ n := by
        unfold dyadicQ; rw [pow_succ']; exact dvd_mul_right _ _
      refine ⟨⟨dyadicQ n * u, h2n⟩, ?_⟩
      rw [h2n, Nat.mul_div_right _ (by omega)]
      rcases hQeven with ⟨q, hq⟩
      have h2 : (dyadicQ n * u) % 2 = 0 := by rw [hq, mul_assoc]; exact Nat.mul_mod_right 2 _
      omega
    · rcases Nat.dvd_of_mem_divisors hd with ⟨u, hu⟩
      have h2n : 2 * n = (dyadicQ n * d) * u := by
        rw [← hQm, hu]; ring
      have hu_odd : u % 2 = 1 := by
        have : (d * u) % 2 = 1 := by rw [← hu]; exact hm_odd
        by_contra h
        have : u % 2 = 0 := by omega
        have : (d * u) % 2 = 0 := by rw [Nat.mul_mod, this]; simp
        omega
      refine ⟨⟨u, h2n⟩, ?_⟩
      have hpos : 0 < dyadicQ n * d := by
        have hQpos : 0 < dyadicQ n := by unfold dyadicQ; positivity
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
        positivity
      rw [h2n, Nat.mul_div_right _ hpos]
      omega

lemma a249223_eq_W {n k : ℕ} (hn : 0 < n) (hk : k ≤ triMax n) :
    a249223 n k = (W n k : ℤ) := by
  induction k with
  | zero => simp [a249223, W_zero]
  | succ k ih =>
    have hk_le : k ≤ triMax n := by omega
    rw [a249223, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ← a249223, ih hk_le]
    have hstep := W_step_int hn k
    have hchar := a237048_characterization hn (by omega : 1 ≤ k + 1) hk
    have hQeven : 2 ∣ dyadicQ n := by
      unfold dyadicQ; rw [pow_succ']; exact dvd_mul_right _ _
    have hm_odd : oddPart n % 2 = 1 := oddPart_odd hn
    have hterm : (-1 : ℤ) ^ (k + 1 + 1) * a237048 n (k + 1) =
        (if (k + 1) ∣ oddPart n then (1 : ℤ) else 0) -
        (if ∃ d ∈ (oddPart n).divisors, k + 1 = dyadicQ n * d then (1 : ℤ) else 0) := by
      unfold a237048
      by_cases hk1_odd : (k + 1) % 2 = 1
      · have hsign : (-1 : ℤ) ^ (k + 1 + 1) = 1 := by
          have : Even (k + 1 + 1) := by rw [Nat.even_iff]; omega
          exact this.neg_one_pow
        have hno_even : ¬ (∃ d ∈ (oddPart n).divisors, k + 1 = dyadicQ n * d) := by
          rintro ⟨d, _, heq⟩
          rcases hQeven with ⟨q, hq⟩
          have : (k + 1) % 2 = 0 := by rw [heq, hq, mul_assoc]; exact Nat.mul_mod_right 2 _
          omega
        rw [hsign, one_mul, if_neg hno_even, sub_zero]
        have hiff : (k + 1 ∣ n - (k + 1) * (k + 1 + 1) / 2) ↔ (k + 1 ∣ oddPart n) := by
          rw [hchar]
          constructor
          · rintro (⟨_, h⟩ | ⟨he, _⟩)
            · exact h
            · omega
          · intro h; exact Or.inl ⟨hk1_odd, h⟩
        simp [hiff]
      · have hk1_even : (k + 1) % 2 = 0 := by omega
        have hsign : (-1 : ℤ) ^ (k + 1 + 1) = -1 := by
          have : Odd (k + 1 + 1) := by rw [Nat.odd_iff]; omega
          exact this.neg_one_pow
        have hno_odd : ¬ ((k + 1) ∣ oddPart n) := by
          rintro ⟨u, hu⟩
          have : (k + 1) * u % 2 = 0 := by rw [Nat.mul_mod, hk1_even]; simp
          omega
        rw [hsign, if_neg hno_odd, zero_sub]
        have hiff : (k + 1 ∣ n - (k + 1) * (k + 1 + 1) / 2) ↔
            (∃ d ∈ (oddPart n).divisors, k + 1 = dyadicQ n * d) := by
          rw [hchar]
          constructor
          · rintro (⟨ho, _⟩ | ⟨_, h⟩)
            · omega
            · exact h
          · intro h; exact Or.inr ⟨hk1_even, h⟩
        by_cases h : ∃ d ∈ (oddPart n).divisors, k + 1 = dyadicQ n * d
        · rw [if_pos (hiff.mpr h), if_pos h]; ring
        · rw [if_neg (mt hiff.mp h), if_neg h]; ring
    linarith

lemma halfWidths_eq_W {n : ℕ} (hn : 0 < n) :
    halfWidths n = (List.range' 1 (triMax n)).map (W n) := by
  unfold halfWidths
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range'] at hk
  have hk_le : k ≤ triMax n := by omega
  rw [a249223_eq_W hn hk_le]
  exact Int.toNat_natCast (W n k)

/-! ### Section 4: Symmetry of `W n` and equality of stutter-compressed words -/

/-- Exact reversal identity: for any divisor `e` of `2 * n`, `W n (2 * n / e) = W n (e - 1)`. -/
lemma W_div_eq_W_pred {n e : ℕ} (hn : 0 < n) (he : e ∣ 2 * n) :
    W n (2 * n / e) = W n (e - 1) := by
  have hm_pos : 0 < oddPart n := oddPart_pos hn
  have hQ_pos : 0 < dyadicQ n := by unfold dyadicQ; positivity
  have hQm : dyadicQ n * oddPart n = 2 * n := dyadicQ_mul_oddPart n
  have he_pos : 0 < e := Nat.pos_of_dvd_of_pos he (by omega)
  have he_mul : e * (2 * n / e) = dyadicQ n * oddPart n := by
    rw [hQm]; exact Nat.mul_div_cancel' he
  unfold W
  apply Finset.card_bij (fun d _ => oddPart n / d)
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    rcases hd with ⟨hd_mem, h1, h2⟩
    have hd_dvd : d ∣ oddPart n := Nat.dvd_of_mem_divisors hd_mem
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
    have hd_mul : d * (oddPart n / d) = oddPart n := Nat.mul_div_cancel' hd_dvd
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd_dvd, Nat.ne_of_gt hm_pos⟩, ?_, ?_⟩
    · have hmul : (dyadicQ n * d) * (oddPart n / d) < (dyadicQ n * d) * e := by
        calc (dyadicQ n * d) * (oddPart n / d) = dyadicQ n * (d * (oddPart n / d)) := by ring
          _ = dyadicQ n * oddPart n := by rw [hd_mul]
          _ = e * (2 * n / e) := he_mul.symm
          _ < e * (dyadicQ n * d) := Nat.mul_lt_mul_of_pos_left h2 he_pos
          _ = (dyadicQ n * d) * e := by ring
      have hlt : oddPart n / d < e := Nat.lt_of_mul_lt_mul_left hmul
      omega
    · have hmul : d * e ≤ d * (dyadicQ n * (oddPart n / d)) := by
        calc d * e ≤ (2 * n / e) * e := Nat.mul_le_mul_right e h1
          _ = e * (2 * n / e) := by ring
          _ = dyadicQ n * oddPart n := he_mul
          _ = dyadicQ n * (d * (oddPart n / d)) := by rw [hd_mul]
          _ = d * (dyadicQ n * (oddPart n / d)) := by ring
      have hle : e ≤ dyadicQ n * (oddPart n / d) := Nat.le_of_mul_le_mul_left hmul hd_pos
      omega
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₁).1)
    have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₂).1)
    have hdiv_pos : 0 < oddPart n / d₁ :=
      Nat.div_pos (Nat.le_of_dvd hm_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₁).1))
        (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd₁).1)
    have : d₁ * (oddPart n / d₁) = d₂ * (oddPart n / d₁) := by rw [h1, heq, h2]
    exact Nat.eq_of_mul_eq_mul_right hdiv_pos this
  · intro d' hd'
    simp only [Finset.mem_filter] at hd'
    rcases hd' with ⟨hd'_mem, h1, h2⟩
    have hd'_dvd : d' ∣ oddPart n := Nat.dvd_of_mem_divisors hd'_mem
    have hd'_pos : 0 < d' := Nat.pos_of_mem_divisors hd'_mem
    have hd'_mul : d' * (oddPart n / d') = oddPart n := Nat.mul_div_cancel' hd'_dvd
    refine ⟨oddPart n / d', ?_, Nat.div_div_self hd'_dvd (Nat.ne_of_gt hm_pos)⟩
    simp only [Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd'_dvd, Nat.ne_of_gt hm_pos⟩, ?_, ?_⟩
    · have hle_e : e ≤ dyadicQ n * d' := by omega
      have hmul : (d' * e) * (oddPart n / d') ≤ (d' * e) * (2 * n / e) := by
        calc (d' * e) * (oddPart n / d') = e * (d' * (oddPart n / d')) := by ring
          _ = e * oddPart n := by rw [hd'_mul]
          _ ≤ (dyadicQ n * d') * oddPart n := Nat.mul_le_mul_right _ hle_e
          _ = d' * (dyadicQ n * oddPart n) := by ring
          _ = d' * (e * (2 * n / e)) := by rw [he_mul]
          _ = (d' * e) * (2 * n / e) := by ring
      exact Nat.le_of_mul_le_mul_left hmul (by positivity)
    · have hlt_d : d' < e := by omega
      have hmul : (d' * e) * (2 * n / e) < (d' * e) * (dyadicQ n * (oddPart n / d')) := by
        calc (d' * e) * (2 * n / e) = d' * (e * (2 * n / e)) := by ring
          _ = d' * (dyadicQ n * oddPart n) := by rw [he_mul]
          _ < e * (dyadicQ n * oddPart n) := Nat.mul_lt_mul_of_pos_right hlt_d (by positivity)
          _ = e * (dyadicQ n * (d' * (oddPart n / d'))) := by rw [hd'_mul]
          _ = (d' * e) * (dyadicQ n * (oddPart n / d')) := by ring
      exact Nat.lt_of_mul_lt_mul_left hmul

/-- Helper: two sorted lists of `ℕ` (under `≤`) that are permutations are equal. -/
lemma eq_of_perm_of_sorted_le {L₁ L₂ : List ℕ} (hp : L₁.Perm L₂)
    (h₁ : L₁.Pairwise (· ≤ ·)) (h₂ : L₂.Pairwise (· ≤ ·)) : L₁ = L₂ :=
  hp.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba) h₁ h₂

/-- Set of all jump endpoints `{ d | d ∣ oddPart n } ∪ { dyadicQ n * d | d ∣ oddPart n }`. -/
def jumpSet (n : ℕ) : Finset ℕ :=
  (oddPart n).divisors ∪ (oddPart n).divisors.image (fun d => dyadicQ n * d)

lemma mem_jumpSet_iff {n x : ℕ} :
    x ∈ jumpSet n ↔
      (x ∈ (oddPart n).divisors ∨ ∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d) := by
  simp [jumpSet, eq_comm]

lemma jumpSet_dvd_two_mul {n x : ℕ} (hx : x ∈ jumpSet n) : x ∣ 2 * n := by
  rw [← dyadicQ_mul_oddPart n]
  rw [mem_jumpSet_iff] at hx
  rcases hx with hd | ⟨d, hd, rfl⟩
  · exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_divisors hd) _
  · exact mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors hd)

lemma W_ne_pred_iff_mem_jumpSet {n x : ℕ} (hn : 0 < n) (hx : 1 ≤ x) :
    W n x ≠ W n (x - 1) ↔ x ∈ jumpSet n := by
  have hm_pos : 0 < oddPart n := oddPart_pos hn
  have hm_odd : oddPart n % 2 = 1 := oddPart_odd hn
  have hQeven : 2 ∣ dyadicQ n := by
    unfold dyadicQ; rw [pow_succ']; exact dvd_mul_right _ _
  have hstep := W_step_int hn (x - 1)
  rw [Nat.sub_add_cancel hx] at hstep
  have hdisj : ¬ (x ∣ oddPart n ∧ ∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d) := by
    rintro ⟨⟨u, hu⟩, d, _, rfl⟩
    rcases hQeven with ⟨q, hq⟩
    have h2 : (dyadicQ n * d * u) % 2 = 0 := by
      rw [hq, mul_assoc, mul_assoc]; exact Nat.mul_mod_right 2 _
    omega
  rw [mem_jumpSet_iff, Nat.mem_divisors]
  constructor
  · intro hne
    by_contra hnot
    have h1 : ¬ (x ∣ oddPart n) := fun hd => hnot (Or.inl ⟨hd, Nat.ne_of_gt hm_pos⟩)
    have h2 : ¬ (∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d) := fun hex => hnot (Or.inr hex)
    rw [if_neg h1, if_neg h2, sub_self] at hstep
    exact hne (by omega)
  · rintro (⟨hd, _⟩ | hex)
    · have h2 : ¬ (∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d) := fun hex => hdisj ⟨hd, hex⟩
      rw [if_pos hd, if_neg h2, sub_zero] at hstep
      omega
    · have h1 : ¬ (x ∣ oddPart n) := fun hd => hdisj ⟨hd, hex⟩
      rw [if_neg h1, if_pos hex, zero_sub] at hstep
      omega

/-- Helper: `dedupAdj ((range' a k).map f)` equals the values of `f` at `a` and at every
point `x ∈ (a, a+k)` where `f x ≠ f (x-1)`. -/
lemma dedupAdj_map_range' (f : ℕ → ℕ) :
    ∀ k a : ℕ, 1 ≤ k →
      dedupAdj ((List.range' a k).map f) =
        f a :: ((List.range' (a + 1) (k - 1)).filter (fun x => decide (f x ≠ f (x - 1)))).map f := by
  intro k
  induction k with
  | zero => intro a hk; omega
  | succ k ih =>
    intro a _
    cases k with
    | zero => simp [dedupAdj]
    | succ k' =>
      rw [List.range'_succ, List.range'_succ, List.map_cons, List.map_cons]
      have hrec := ih (a + 1) (by omega)
      rw [List.range'_succ, List.map_cons] at hrec
      have hstep : List.range' (a + 1) (k' + 1) = (a + 1) :: List.range' (a + 2) k' :=
        List.range'_succ
      rw [show k' + 1 + 1 - 1 = k' + 1 by omega, hstep, List.filter_cons]
      by_cases heq : f a = f (a + 1)
      · rw [dedupAdj_cons_same_of_eq heq, hrec]
        · simp [heq]
      · rw [dedupAdj_cons_ne heq, hrec]
        simp [ne_comm.mp heq]
where
  dedupAdj_cons_same_of_eq {x y : ℕ} (h : x = y) (xs : List ℕ) :
      dedupAdj (x :: y :: xs) = dedupAdj (y :: xs) := by
    subst h; exact dedupAdj_cons_same x xs

lemma filter_range'_eq_sort (S : Finset ℕ) (a k : ℕ)
    (hS : ∀ x ∈ S, a ≤ x ∧ x < a + k) :
    (List.range' a k).filter (fun x => decide (x ∈ S)) = S.sort (· ≤ ·) := by
  apply eq_of_perm_of_sorted_le
  · apply (List.perm_ext_iff_of_nodup
      ((List.nodup_range' (s := a) (n := k)).filter _) (S.sort_nodup (· ≤ ·))).mpr
    intro x
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq, Finset.mem_sort]
    constructor
    · exact fun h => h.2
    · intro hx; have := hS x hx; exact ⟨⟨this.1, this.2⟩, hx⟩
  · exact ((List.pairwise_lt_range' (s := a) (n := k)).imp (fun h => Nat.le_of_lt h)).filter _
  · exact S.pairwise_sort (· ≤ ·)

lemma jumpSet_bounds {n x : ℕ} (hn : 0 < n) (hx : x ∈ jumpSet n) : 1 ≤ x ∧ x ≤ 2 * n := by
  have hdvd := jumpSet_dvd_two_mul hx
  exact ⟨Nat.pos_of_dvd_of_pos hdvd (by omega), Nat.le_of_dvd (by omega) hdvd⟩

lemma one_mem_jumpSet {n : ℕ} (hn : 0 < n) : 1 ∈ jumpSet n := by
  rw [mem_jumpSet_iff]
  exact Or.inl (Nat.one_mem_divisors.mpr (Nat.ne_of_gt (oddPart_pos hn)))

lemma two_mul_mem_jumpSet {n : ℕ} (hn : 0 < n) : 2 * n ∈ jumpSet n := by
  rw [mem_jumpSet_iff]
  right
  refine ⟨oddPart n, Nat.mem_divisors.mpr ⟨dvd_refl _, Nat.ne_of_gt (oddPart_pos hn)⟩, ?_⟩
  exact (dyadicQ_mul_oddPart n).symm

lemma jumpSet_div_mem {n x : ℕ} (hn : 0 < n) (hx : x ∈ jumpSet n) :
    2 * n / x ∈ jumpSet n := by
  have hm_pos : 0 < oddPart n := oddPart_pos hn
  have hQ_pos : 0 < dyadicQ n := by unfold dyadicQ; positivity
  have hQm : dyadicQ n * oddPart n = 2 * n := dyadicQ_mul_oddPart n
  rw [mem_jumpSet_iff] at hx ⊢
  rcases hx with hd | ⟨d, hd, rfl⟩
  · right
    have hd_dvd := Nat.dvd_of_mem_divisors hd
    refine ⟨oddPart n / x, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd_dvd, Nat.ne_of_gt hm_pos⟩, ?_⟩
    rw [← hQm, Nat.mul_div_assoc _ hd_dvd]
  · left
    have hd_dvd := Nat.dvd_of_mem_divisors hd
    have hdiv : 2 * n / (dyadicQ n * d) = oddPart n / d := by
      rw [← hQm, Nat.mul_div_mul_left _ _ hQ_pos]
    rw [hdiv]
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd_dvd, Nat.ne_of_gt hm_pos⟩

lemma jumpSet_ne_div {n x : ℕ} (hn : 0 < n) (hx : x ∈ jumpSet n) : x ≠ 2 * n / x := by
  intro heq
  have hm_odd : oddPart n % 2 = 1 := oddPart_odd hn
  have hQeven : 2 ∣ dyadicQ n := by
    unfold dyadicQ; rw [pow_succ']; exact dvd_mul_right _ _
  rw [mem_jumpSet_iff] at hx
  rcases hx with hd | ⟨d, hd, rfl⟩
  · have hxodd : x % 2 = 1 := by
      rcases Nat.dvd_of_mem_divisors hd with ⟨u, hu⟩
      by_contra h
      have h0 : x % 2 = 0 := by omega
      have : (x * u) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
      omega
    have hdiv : 2 * n / x = dyadicQ n * (oddPart n / x) := by
      rw [← dyadicQ_mul_oddPart n, Nat.mul_div_assoc _ (Nat.dvd_of_mem_divisors hd)]
    rw [hdiv] at heq
    rcases hQeven with ⟨q, hq⟩
    have : x % 2 = 0 := by rw [heq, hq, mul_assoc]; exact Nat.mul_mod_right 2 _
    omega
  · have hxeven : (dyadicQ n * d) % 2 = 0 := by
      rcases hQeven with ⟨q, hq⟩; rw [hq, mul_assoc]; exact Nat.mul_mod_right 2 _
    have hQpos : 0 < dyadicQ n := by unfold dyadicQ; positivity
    have hdiv : 2 * n / (dyadicQ n * d) = oddPart n / d := by
      rw [← dyadicQ_mul_oddPart n, Nat.mul_div_mul_left _ _ hQpos]
    rw [hdiv] at heq
    have hd_dvd := Nat.dvd_of_mem_divisors hd
    have hodd2 : (oddPart n / d) % 2 = 1 := by
      have hmul := Nat.mul_div_cancel' hd_dvd
      by_contra h
      have h0 : (oddPart n / d) % 2 = 0 := by omega
      have : (d * (oddPart n / d)) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
      omega
    omega

lemma jumpSet_le_triMax_iff {n x : ℕ} (hn : 0 < n) (hx : x ∈ jumpSet n) :
    x ≤ triMax n ↔ x < 2 * n / x := by
  have hdvd := jumpSet_dvd_two_mul hx
  have hmul : x * (2 * n / x) = 2 * n := Nat.mul_div_cancel' hdvd
  rw [le_triMax_iff]
  constructor
  · intro h
    by_contra hge
    have hne : x ≠ 2 * n / x := jumpSet_ne_div hn hx
    have hlt : 2 * n / x + 1 ≤ x := by omega
    have hmul_le : x * (2 * n / x + 1) ≤ x * x := Nat.mul_le_mul_left x hlt
    nlinarith
  · intro h
    have : x + 1 ≤ 2 * n / x := h
    nlinarith

/-- Key structural theorem: the stutter-compressed full width word `A262045(n)` equals the
stutter-compressed integer sampling `[W n 1, W n 2, ..., W n (2n - 1)]`. -/
theorem dedupAdj_a262045_eq_W {n : ℕ} (hn : 0 < n) :
    dedupAdj (a262045 n) = dedupAdj ((List.range' 1 (2 * n - 1)).map (W n)) := by
  have hr1 : 1 ≤ triMax n := by
    rw [le_triMax_iff]; omega
  set E_full := (jumpSet n).erase (2 * n)
  set E_lo := (jumpSet n).filter (fun x => x ≤ triMax n)
  set E_hi := E_full.filter (fun x => triMax n < x)
  have h1_lo : 1 ∈ E_lo := Finset.mem_filter.mpr ⟨one_mem_jumpSet hn, hr1⟩
  have h1_full : 1 ∈ E_full := Finset.mem_erase.mpr ⟨by omega, one_mem_jumpSet hn⟩
  -- Step 1: `dedupAdj (halfWidths n) = (E_lo.sort (· ≤ ·)).map (W n)`
  have hdedup_half : dedupAdj (halfWidths n) = (E_lo.sort (· ≤ ·)).map (W n) := by
    rw [halfWidths_eq_W hn, dedupAdj_map_range' (W n) (triMax n) 1 hr1]
    have hfilt : (List.range' 2 (triMax n - 1)).filter
        (fun x => decide (W n x ≠ W n (x - 1))) = (E_lo.erase 1).sort (· ≤ ·) := by
      have hcongr : (List.range' 2 (triMax n - 1)).filter (fun x => decide (W n x ≠ W n (x - 1))) =
          (List.range' 2 (triMax n - 1)).filter (fun x => decide (x ∈ E_lo.erase 1)) := by
        apply List.filter_congr
        intro x hx
        rw [List.mem_range'] at hx
        simp only [decide_eq_decide, Finset.mem_erase, Finset.mem_filter, E_lo]
        rw [W_ne_pred_iff_mem_jumpSet hn (by omega)]
        constructor
        · intro hmem; exact ⟨by omega, hmem, by omega⟩
        · exact fun h => h.2.1
      rw [hcongr]
      apply filter_range'_eq_sort
      intro x hx
      rw [Finset.mem_erase, Finset.mem_filter] at hx
      have hb := jumpSet_bounds hn hx.2.1
      omega
    rw [hfilt]
    have hsort : E_lo.sort (· ≤ ·) = 1 :: (E_lo.erase 1).sort (· ≤ ·) := by
      apply eq_of_perm_of_sorted_le
      · apply (List.perm_ext_iff_of_nodup (E_lo.sort_nodup _) _).mpr
        · intro x
          simp only [Finset.mem_sort, List.mem_cons, Finset.mem_erase]
          constructor
          · intro hx
            by_cases h1 : x = 1
            · exact Or.inl h1
            · exact Or.inr ⟨h1, hx⟩
          · rintro (rfl | ⟨_, hx⟩)
            · exact h1_lo
            · exact hx
        · rw [List.nodup_cons]
          exact ⟨by simp [Finset.mem_sort], (E_lo.erase 1).sort_nodup _⟩
      · exact E_lo.pairwise_sort _
      · rw [List.pairwise_cons]
        refine ⟨fun y hy => ?_, (E_lo.erase 1).pairwise_sort _⟩
        rw [Finset.mem_sort, Finset.mem_erase, Finset.mem_filter] at hy
        exact (jumpSet_bounds hn hy.2.1).1
    rw [hsort, List.map_cons]
  -- Step 2: `dedupAdj ((range' 1 (2*n - 1)).map (W n)) = (E_full.sort (· ≤ ·)).map (W n)`
  have hdedup_full : dedupAdj ((List.range' 1 (2 * n - 1)).map (W n)) =
      (E_full.sort (· ≤ ·)).map (W n) := by
    rw [dedupAdj_map_range' (W n) (2 * n - 1) 1 (by omega)]
    have hfilt : (List.range' 2 (2 * n - 1 - 1)).filter
        (fun x => decide (W n x ≠ W n (x - 1))) = (E_full.erase 1).sort (· ≤ ·) := by
      have hcongr : (List.range' 2 (2 * n - 1 - 1)).filter
          (fun x => decide (W n x ≠ W n (x - 1))) =
          (List.range' 2 (2 * n - 1 - 1)).filter (fun x => decide (x ∈ E_full.erase 1)) := by
        apply List.filter_congr
        intro x hx
        rw [List.mem_range'] at hx
        simp only [decide_eq_decide, Finset.mem_erase, E_full]
        rw [W_ne_pred_iff_mem_jumpSet hn (by omega)]
        constructor
        · intro hmem; exact ⟨by omega, by omega, hmem⟩
        · exact fun h => h.2.2
      rw [hcongr]
      apply filter_range'_eq_sort
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase] at hx
      have hb := jumpSet_bounds hn hx.2.2
      omega
    rw [hfilt]
    have hsort : E_full.sort (· ≤ ·) = 1 :: (E_full.erase 1).sort (· ≤ ·) := by
      apply eq_of_perm_of_sorted_le
      · apply (List.perm_ext_iff_of_nodup (E_full.sort_nodup _) _).mpr
        · intro x
          simp only [Finset.mem_sort, List.mem_cons, Finset.mem_erase]
          constructor
          · intro hx
            by_cases h1 : x = 1
            · exact Or.inl h1
            · exact Or.inr ⟨h1, hx⟩
          · rintro (rfl | ⟨_, hx⟩)
            · exact h1_full
            · exact hx
        · rw [List.nodup_cons]
          exact ⟨by simp [Finset.mem_sort], (E_full.erase 1).sort_nodup _⟩
      · exact E_full.pairwise_sort _
      · rw [List.pairwise_cons]
        refine ⟨fun y hy => ?_, (E_full.erase 1).pairwise_sort _⟩
        rw [Finset.mem_sort, Finset.mem_erase, Finset.mem_erase] at hy
        exact (jumpSet_bounds hn hy.2.2).1
    rw [hsort, List.map_cons]
  -- Step 3: `E_full.sort = E_lo.sort ++ E_hi.sort`
  have hE_split : E_full.sort (· ≤ ·) = E_lo.sort (· ≤ ·) ++ E_hi.sort (· ≤ ·) := by
    apply eq_of_perm_of_sorted_le
    · apply (List.perm_ext_iff_of_nodup (E_full.sort_nodup _) _).mpr
      · intro x
        simp only [Finset.mem_sort, List.mem_append, Finset.mem_filter, Finset.mem_erase,
          E_lo, E_hi, E_full]
        constructor
        · rintro ⟨hne, hx⟩
          by_cases hle : x ≤ triMax n
          · exact Or.inl ⟨hx, hle⟩
          · exact Or.inr ⟨⟨hne, hx⟩, by omega⟩
        · rintro (⟨hx, hle⟩ | ⟨⟨hne, hx⟩, _⟩)
          · have h2n_gt : triMax n < 2 * n := by
              by_contra h
              have := (le_triMax_iff n (2 * n)).mp (by omega)
              nlinarith
            exact ⟨by omega, hx⟩
          · exact ⟨hne, hx⟩
      · rw [List.nodup_append]
        refine ⟨E_lo.sort_nodup _, E_hi.sort_nodup _, fun a ha b hb => ?_⟩
        rw [Finset.mem_sort, Finset.mem_filter] at ha hb
        omega
    · exact E_full.pairwise_sort _
    · rw [List.pairwise_append]
      refine ⟨E_lo.pairwise_sort _, E_hi.pairwise_sort _, fun a ha b hb => ?_⟩
      rw [Finset.mem_sort, Finset.mem_filter] at ha hb
      omega
  -- Step 4: `E_hi.sort = ((E_lo.erase 1).sort.map (fun e => 2*n / e)).reverse`
  have hE_hi : E_hi.sort (· ≤ ·) =
      (((E_lo.erase 1).sort (· ≤ ·)).map (fun e => 2 * n / e)).reverse := by
    apply eq_of_perm_of_sorted_le
    · have hnodup_rhs : (((E_lo.erase 1).sort (· ≤ ·)).map (fun e => 2 * n / e)).reverse.Nodup := by
        rw [List.nodup_reverse, List.nodup_map_iff_inj_on ((E_lo.erase 1).sort_nodup _)]
        intro a ha b hb heq
        rw [Finset.mem_sort, Finset.mem_erase, Finset.mem_filter] at ha hb
        have hda := jumpSet_dvd_two_mul ha.2.1
        have hdb := jumpSet_dvd_two_mul hb.2.1
        have hma := Nat.mul_div_cancel' hda
        have hmb := Nat.mul_div_cancel' hdb
        have hdiv_pos : 0 < 2 * n / a :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hda) (Nat.pos_of_dvd_of_pos hda (by omega))
        have : a * (2 * n / a) = b * (2 * n / a) := by rw [hma, heq, hmb]
        exact Nat.eq_of_mul_eq_mul_right hdiv_pos this
      apply (List.perm_ext_iff_of_nodup (E_hi.sort_nodup _) hnodup_rhs).mpr
      intro x
      simp only [Finset.mem_sort, List.mem_reverse, List.mem_map, Finset.mem_filter,
        Finset.mem_erase, E_hi, E_full, E_lo]
      constructor
      · rintro ⟨⟨hne, hx⟩, hgt⟩
        refine ⟨2 * n / x, ?_, Nat.div_div_self (jumpSet_dvd_two_mul hx) (by omega)⟩
        have hdiv_mem := jumpSet_div_mem hn hx
        have hnotle : ¬ (x ≤ triMax n) := by omega
        have hnotlt : ¬ (x < 2 * n / x) := mt (jumpSet_le_triMax_iff hn hx).mpr hnotle
        have hdvd := jumpSet_dvd_two_mul hx
        have hdiv_ne1 : 2 * n / x ≠ 1 := by
          intro h1
          have := Nat.mul_div_cancel' hdvd
          rw [h1, mul_one] at this
          exact hne this
        have hdiv_lt : 2 * n / x < 2 * n / (2 * n / x) := by
          rw [Nat.div_div_self hdvd (by omega)]
          exact lt_of_le_of_ne (by omega) (Ne.symm (jumpSet_ne_div hn hx))
        exact ⟨hdiv_ne1, hdiv_mem, (jumpSet_le_triMax_iff hn hdiv_mem).mpr hdiv_lt⟩
      · rintro ⟨e, ⟨he1, he_mem, he_le⟩, rfl⟩
        have hdiv_mem := jumpSet_div_mem hn he_mem
        have hdvd := jumpSet_dvd_two_mul he_mem
        have hne2n : 2 * n / e ≠ 2 * n := by
          intro heq
          have := Nat.mul_div_cancel' hdvd
          rw [heq] at this
          have : e = 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) (by linarith)
          exact he1 this
        have hlt := (jumpSet_le_triMax_iff hn he_mem).mp he_le
        have hgt : triMax n < 2 * n / e := by
          by_contra hle
          have hlt2 := (jumpSet_le_triMax_iff hn hdiv_mem).mp (by omega)
          rw [Nat.div_div_self hdvd (by omega)] at hlt2
          omega
        exact ⟨⟨hne2n, hdiv_mem⟩, hgt⟩
    · exact E_hi.pairwise_sort _
    · rw [List.pairwise_reverse, List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ ((E_lo.erase 1).pairwise_sort _)
      intro a b ha hb hab
      rw [Finset.mem_sort, Finset.mem_erase, Finset.mem_filter] at ha hb
      exact Nat.div_le_div_left hab (jumpSet_bounds hn ha.2.1).1
  -- Step 5: Map `W n` over `E_hi.sort` and match with `(E_lo.sort.map (W n)).reverse.tail`
  have hmap_hi : (E_hi.sort (· ≤ ·)).map (W n) =
      ((E_lo.sort (· ≤ ·)).map (W n)).reverse.tail := by
    have hE_lo_cons : E_lo.sort (· ≤ ·) = 1 :: (E_lo.erase 1).sort (· ≤ ·) := by
      apply eq_of_perm_of_sorted_le
      · apply (List.perm_ext_iff_of_nodup (E_lo.sort_nodup _) _).mpr
        · intro x
          simp only [Finset.mem_sort, List.mem_cons, Finset.mem_erase]
          constructor
          · intro hx
            by_cases h1 : x = 1
            · exact Or.inl h1
            · exact Or.inr ⟨h1, hx⟩
          · rintro (rfl | ⟨_, hx⟩)
            · exact h1_lo
            · exact hx
        · rw [List.nodup_cons]
          exact ⟨by simp [Finset.mem_sort], (E_lo.erase 1).sort_nodup _⟩
      · exact E_lo.pairwise_sort _
      · rw [List.pairwise_cons]
        refine ⟨fun y hy => ?_, (E_lo.erase 1).pairwise_sort _⟩
        rw [Finset.mem_sort, Finset.mem_erase, Finset.mem_filter] at hy
        exact (jumpSet_bounds hn hy.2.1).1
    rw [hE_hi, List.map_reverse, List.map_map, ← List.map_reverse]
    have htail_rev : ((E_lo.sort (· ≤ ·)).map (W n)).reverse.tail =
        ((E_lo.sort (· ≤ ·)).dropLast.map (W n)).reverse := by
      rw [← List.map_reverse, ← List.map_tail, List.tail_reverse, List.map_reverse]
    rw [htail_rev]
    have hconst : ∀ a b : ℕ, a < b → (∀ z, a < z → z < b → z ∉ jumpSet n) →
        W n (b - 1) = W n a := by
      intro a b hab hno
      have : ∀ k, k ≤ b - 1 - a → W n (a + k) = W n a := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          have hne_jmp : a + k + 1 ∉ jumpSet n := hno (a + k + 1) (by omega) (by omega)
          have hstep : W n (a + k + 1) = W n (a + k + 1 - 1) := by
            by_contra hne
            exact hne_jmp ((W_ne_pred_iff_mem_jumpSet hn (by omega)).mp hne)
          have hpred : a + k + 1 - 1 = a + k := by omega
          rw [hpred] at hstep
          rw [← Nat.add_assoc, hstep, ih (by omega)]
      have h := this (b - 1 - a) (le_refl _)
      rwa [show a + (b - 1 - a) = b - 1 by omega] at h
    have hgen : ∀ (L : List ℕ), L ≠ [] →
        L.Pairwise (· < ·) →
        (∀ x ∈ L, x ∈ jumpSet n) →
        (∀ i (hi : i + 1 < L.length), ∀ z, L[i] < z → z < L[i + 1] → z ∉ jumpSet n) →
        L.tail.map (fun e => W n (2 * n / e)) = L.dropLast.map (W n) := by
      intro L
      induction L with
      | nil => intro h; contradiction
      | cons a rest ih =>
        intro _ hpair hmem hgap
        match rest with
        | [] => simp
        | b :: bs =>
          simp only [List.tail_cons, List.dropLast_cons_of_ne_nil (List.cons_ne_nil b bs),
            List.map_cons]
          have hab : a < b := (List.pairwise_cons.mp hpair).1 b List.mem_cons_self
          have hb_mem : b ∈ jumpSet n := hmem b (List.mem_cons_of_mem _ List.mem_cons_self)
          have hno_ab : ∀ z, a < z → z < b → z ∉ jumpSet n := fun z h1 h2 =>
            hgap 0 (by simp) z h1 h2
          have hhead : W n (2 * n / b) = W n a := by
            rw [W_div_eq_W_pred hn (jumpSet_dvd_two_mul hb_mem)]
            exact hconst a b hab hno_ab
          congr 1
          exact ih (List.cons_ne_nil b bs) (List.pairwise_cons.mp hpair).2
            (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
            (fun i hi z h1 h2 => hgap (i + 1) (by simpa using hi) z h1 h2)
    have hE_lo_lt : (E_lo.sort (· ≤ ·)).Pairwise (· < ·) := by
      have h1 := E_lo.pairwise_sort (· ≤ ·)
      have h2 := List.nodup_iff_pairwise_ne.mp (E_lo.sort_nodup (· ≤ ·))
      rw [List.pairwise_iff_getElem] at h1 h2 ⊢
      intro i j hi hj hij
      exact lt_of_le_of_ne (h1 i j hi hj hij) (h2 i j hi hj hij)
    have hE_lo_gap : ∀ i (hi : i + 1 < (E_lo.sort (· ≤ ·)).length),
        ∀ z, (E_lo.sort (· ≤ ·))[i] < z → z < (E_lo.sort (· ≤ ·))[i + 1] → z ∉ jumpSet n := by
      intro i hi z h1 h2 hz
      have hhi_mem : (E_lo.sort (· ≤ ·))[i + 1] ∈ E_lo :=
        (Finset.mem_sort _).mp (List.getElem_mem hi)
      have hz_le : z ≤ triMax n := le_trans (le_of_lt h2) (Finset.mem_filter.mp hhi_mem).2
      have hz_mem : z ∈ E_lo.sort (· ≤ ·) := (Finset.mem_sort _).mpr (Finset.mem_filter.mpr ⟨hz, hz_le⟩)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz_mem
      have hlt := List.pairwise_iff_getElem.mp hE_lo_lt
      have hij : i < j := by
        by_contra hle
        rcases eq_or_lt_of_le (show j ≤ i by omega) with rfl | hji
        · omega
        · have := hlt j i hj (by omega) hji; omega
      have hji1 : j < i + 1 := by
        by_contra hle
        rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with rfl | hi1j
        · omega
        · have := hlt (i + 1) j hi hj hi1j; omega
      omega
    have hres := hgen (E_lo.sort (· ≤ ·))
      (by rw [hE_lo_cons]; exact List.cons_ne_nil _ _)
      hE_lo_lt
      (fun x hx => (Finset.mem_filter.mp ((Finset.mem_sort _).mp hx)).1)
      hE_lo_gap
    rw [hE_lo_cons] at hres ⊢
    simpa [Function.comp_def] using hres
  -- Step 6: Combine everything!
  have hhalf_ne : halfWidths n ≠ [] := by
    rw [halfWidths_eq_W hn]
    have : 0 < triMax n := by omega
    cases h : triMax n with
    | zero => omega
    | succ m => simp [List.range'_succ]
  have hrev_ne : (halfWidths n).reverse ≠ [] := by simpa using hhalf_ne
  have hbdry : (halfWidths n).getLast hhalf_ne = (halfWidths n).reverse.head hrev_ne := by
    simp [List.head_reverse]
  rw [a262045, dedupAdj_append_same_boundary _ _ hhalf_ne hrev_ne hbdry,
    dedupAdj_reverse, hdedup_half, hdedup_full, hE_split, List.map_append, hmap_hi]

/-! ### Section 5: Positive runs of `W n` correspond to `2`-dense blocks of divisors of `n` -/

lemma divisor_iff_pow_two_mul_oddPart {n e : ℕ} (hn : 0 < n) :
    e ∣ n ↔ ∃ i ≤ padicValNat 2 n, ∃ d, d ∣ oddPart n ∧ e = 2 ^ i * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm_odd : oddPart n % 2 = 1 := oddPart_odd hn
  have hn_eq : n = 2 ^ padicValNat 2 n * oddPart n := (pow_two_mul_oddPart n).symm
  constructor
  · intro he
    have he_pos : 0 < e := Nat.pos_of_dvd_of_pos he hn
    have hv_le : padicValNat 2 e ≤ padicValNat 2 n :=
      (padicValNat_dvd_iff_le (Nat.ne_of_gt hn)).mp (dvd_trans pow_padicValNat_dvd he)
    refine ⟨padicValNat 2 e, hv_le, oddPart e, ?_, (pow_two_mul_oddPart e).symm⟩
    have hcop : Nat.Coprime (oddPart e) (2 ^ padicValNat 2 n) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm]
      exact Nat.prime_two.coprime_iff_not_dvd.mpr (by have := oddPart_odd he_pos; omega)
    have hdvd_n : oddPart e ∣ 2 ^ padicValNat 2 n * oddPart n := by
      rw [← hn_eq]
      exact dvd_trans ⟨2 ^ padicValNat 2 e, by rw [mul_comm, pow_two_mul_oddPart]⟩ he
    exact hcop.dvd_of_dvd_mul_left hdvd_n
  · rintro ⟨i, hi, d, hd, rfl⟩
    rw [hn_eq]
    exact mul_dvd_mul (pow_dvd_pow 2 hi) hd

lemma W_pos_iff_exists_divisor {n x : ℕ} (hn : 0 < n) :
    0 < W n x ↔ ∃ e ∈ n.divisors, e ≤ x ∧ x < 2 * e := by
  have hm_pos : 0 < oddPart n := oddPart_pos hn
  unfold W
  rw [Finset.card_pos]
  constructor
  · rintro ⟨d, hd⟩
    simp only [Finset.mem_filter] at hd
    rcases hd with ⟨hd_mem, h1, h2⟩
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
    -- Find largest `i ≤ v₂(n)` with `2^i * d ≤ x`
    have hq_pos : 0 < x / d := Nat.div_pos h1 hd_pos
    have hq_lt : x / d < dyadicQ n := (Nat.div_lt_iff_lt_mul hd_pos).mpr (by linarith)
    set i := Nat.log 2 (x / d)
    have hi_le : i ≤ padicValNat 2 n := by
      have : i < padicValNat 2 n + 1 := (Nat.log_lt_iff_lt_pow (by omega) (Nat.ne_of_gt hq_pos)).mpr
        (by simpa [dyadicQ] using hq_lt)
      omega
    have hpow_le : 2 ^ i ≤ x / d := Nat.pow_log_le_self 2 (Nat.ne_of_gt hq_pos)
    have hlt_pow : x / d < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by omega) (x / d)
    refine ⟨2 ^ i * d, Nat.mem_divisors.mpr ⟨?_, Nat.ne_of_gt hn⟩, ?_, ?_⟩
    · exact (divisor_iff_pow_two_mul_oddPart hn).mpr ⟨i, hi_le, d, Nat.dvd_of_mem_divisors hd_mem, rfl⟩
    · exact (Nat.le_div_iff_mul_le hd_pos).mp hpow_le
    · have : x < 2 ^ (i + 1) * d := (Nat.div_lt_iff_lt_mul hd_pos).mp hlt_pow
      rw [pow_succ'] at this
      linarith
  · rintro ⟨e, he_mem, h1, h2⟩
    have he_dvd := Nat.dvd_of_mem_divisors he_mem
    obtain ⟨i, hi, d, hd_dvd, rfl⟩ := (divisor_iff_pow_two_mul_oddPart hn).mp he_dvd
    refine ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd_dvd, Nat.ne_of_gt hm_pos⟩, ?_, ?_⟩⟩
    · have h1i : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
      nlinarith
    · have hle : 2 * 2 ^ i ≤ dyadicQ n := by
        unfold dyadicQ
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith

/-- Predicate for a single nonempty strictly-increasing `2`-dense block. -/
def IsDenseBlock (b : List ℕ) : Prop :=
  b ≠ [] ∧ b.Pairwise (· < ·) ∧ ∀ i (hi : i + 1 < b.length), b[i + 1] ≤ 2 * b[i]

/-- Gap condition between consecutive blocks: `2 * last(b₁) < first(b₂)`. -/
def HasGaps : List (List ℕ) → Prop
  | [] => True
  | [_] => True
  | b₁ :: b₂ :: bs => 2 * b₁.getLastD 0 < b₂.headD 0 ∧ HasGaps (b₂ :: bs)

lemma headD_append_of_ne_nil {L₁ L₂ : List ℕ} (h : L₁ ≠ []) :
    (L₁ ++ L₂).headD 0 = L₁.headD 0 := by
  cases L₁ with
  | nil => contradiction
  | cons a as => rfl

lemma getLastD_singleton {α : Type*} (x d : α) : ([x] : List α).getLastD d = x := rfl

lemma getLastD_eq_getLast {α : Type*} {L : List α} (h : L ≠ []) (d : α) :
    L.getLastD d = L.getLast h := by
  induction L with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      rw [List.getLast_cons (List.cons_ne_nil b bs)]
      exact ih (List.cons_ne_nil b bs)

lemma getLastD_append_singleton (L : List ℕ) (x : ℕ) :
    (L ++ [x]).getLastD 0 = x := by
  rw [getLastD_eq_getLast (by simp), List.getLast_append_singleton]

lemma getLastD_reverse_cons (a : ℕ) (as : List ℕ) :
    (a :: as).reverse.getLastD 0 = a := by
  rw [List.reverse_cons, getLastD_append_singleton]

lemma headD_reverse_of_ne_nil {L : List ℕ} (h : L ≠ []) :
    L.reverse.headD 0 = L.getLastD 0 := by
  rw [getLastD_eq_getLast h]
  induction L with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      rw [List.reverse_cons, headD_append_of_ne_nil (by simp),
        List.getLast_cons (List.cons_ne_nil b bs)]
      exact ih (List.cons_ne_nil b bs)

lemma denseBlocksAux_spec (prev : ℕ) (cur : List ℕ) (xs : List ℕ)
    (hcur_ne : cur ≠ [])
    (hcur_head : cur.headD 0 = prev)
    (hcur_dense : IsDenseBlock cur.reverse)
    (hxs_lt : (prev :: xs).Pairwise (· < ·)) :
    (denseBlocksAux prev cur xs).flatten = cur.reverse ++ xs ∧
    (∀ b ∈ denseBlocksAux prev cur xs, IsDenseBlock b) ∧
    HasGaps (denseBlocksAux prev cur xs) ∧
    (denseBlocksAux prev cur xs) ≠ [] ∧
    ((denseBlocksAux prev cur xs).headD []).headD 0 = cur.reverse.headD 0 ∧
    ((denseBlocksAux prev cur xs).getLastD []).getLastD 0 = (cur.reverse ++ xs).getLastD 0 := by
  induction xs generalizing prev cur with
  | nil =>
    refine ⟨by simp [denseBlocksAux], by simp [denseBlocksAux, hcur_dense],
      by simp [denseBlocksAux, HasGaps], by simp [denseBlocksAux],
      by simp [denseBlocksAux], by simp [denseBlocksAux]⟩
  | cons x xs ih =>
    have hprev_lt_x : prev < x := (List.pairwise_cons.mp hxs_lt).1 x List.mem_cons_self
    have hxs_lt' : (x :: xs).Pairwise (· < ·) := (List.pairwise_cons.mp hxs_lt).2
    have hcur_last : cur.reverse.getLastD 0 = prev := by
      cases cur with
      | nil => contradiction
      | cons a as =>
        simp only [List.headD_cons] at hcur_head
        subst hcur_head
        exact getLastD_reverse_cons a as
    simp only [denseBlocksAux]
    by_cases hle : x ≤ 2 * prev
    · rw [if_pos hle]
      have hrev_last_elem :
          cur.reverse[cur.reverse.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hcur_dense.1) (by omega)) = prev := by
        rw [← hcur_last, getLastD_eq_getLast hcur_dense.1, List.getLast_eq_getElem hcur_dense.1]
      have hnew_dense : IsDenseBlock (x :: cur).reverse := by
        rw [List.reverse_cons]
        refine ⟨by simp, ?_, ?_⟩
        · rw [List.pairwise_append]
          refine ⟨hcur_dense.2.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          have ha_le : a ≤ prev := by
            rcases List.getElem_of_mem ha with ⟨i, hi, rfl⟩
            have hlast_idx : cur.reverse.length - 1 < cur.reverse.length :=
              Nat.sub_lt (List.length_pos_of_ne_nil hcur_dense.1) (by omega)
            by_cases hi_eq : i = cur.reverse.length - 1
            · rw [← hrev_last_elem]
              have : cur.reverse[i]'hi = cur.reverse[cur.reverse.length - 1]'hlast_idx := by
                congr 1
              omega
            · have hilt : i < cur.reverse.length - 1 := by omega
              have := List.pairwise_iff_getElem.mp hcur_dense.2.1 i (cur.reverse.length - 1) hi hlast_idx hilt
              rw [hrev_last_elem] at this
              omega
          omega
        · intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hilt : i + 1 < cur.reverse.length
          · rw [List.getElem_append_left hilt, List.getElem_append_left (by omega)]
            exact hcur_dense.2.2 i hilt
          · have hi_eq : i = cur.reverse.length - 1 := by omega
            have hi_lt : i < cur.reverse.length := by omega
            rw [List.getElem_append_left hi_lt,
              List.getElem_append_right (by omega : cur.reverse.length ≤ i + 1)]
            have hidx0 : i + 1 - cur.reverse.length = 0 := by omega
            simp only [hidx0, List.getElem_singleton]
            have hgetLast : cur.reverse[i]'hi_lt = prev := by
              rw [← hrev_last_elem]; congr 1
            rw [hgetLast]
            exact hle
      have hrec := ih x (x :: cur) (List.cons_ne_nil x cur) rfl hnew_dense hxs_lt'
      refine ⟨?_, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using hrec.1
      · rw [hrec.2.2.2.2.1, List.reverse_cons, headD_append_of_ne_nil hcur_dense.1]
      · simpa [List.reverse_cons, List.append_assoc] using hrec.2.2.2.2.2
    · rw [if_neg hle]
      have hx_dense : IsDenseBlock [x].reverse := by
        refine ⟨by simp, by simp, fun i hi => by simp at hi⟩
      have hrec := ih x [x] (List.cons_ne_nil x []) rfl hx_dense hxs_lt'
      have hrec_ne : denseBlocksAux x [x] xs ≠ [] := hrec.2.2.2.1
      refine ⟨?_, ?_, ?_, List.cons_ne_nil _ _, rfl, ?_⟩
      · simpa [List.flatten_cons, List.append_assoc] using congrArg (cur.reverse ++ ·) hrec.1
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hcur_dense
        · exact hrec.2.1 b hb'
      · cases hdb : denseBlocksAux x [x] xs with
        | nil => exact absurd hdb hrec_ne
        | cons b₂ bs =>
          simp only [HasGaps]
          refine ⟨?_, by simpa [hdb] using hrec.2.2.1⟩
          have hb₂_head : b₂.headD 0 = x := by
            simpa [hdb] using hrec.2.2.2.2.1
          rw [hcur_last, hb₂_head]
          omega
      · cases hdb : denseBlocksAux x [x] xs with
        | nil => exact absurd hdb hrec_ne
        | cons b₂ bs =>
          have hlast1 : (cur.reverse :: b₂ :: bs).getLastD [] = (b₂ :: bs).getLastD [] := by
            rw [getLastD_eq_getLast (List.cons_ne_nil _ _),
              getLastD_eq_getLast (List.cons_ne_nil _ _),
              List.getLast_cons (List.cons_ne_nil _ _)]
          rw [hlast1]
          have hlast2 : ((b₂ :: bs).getLastD []).getLastD 0 = (x :: xs).getLastD 0 := by
            simpa [hdb] using hrec.2.2.2.2.2
          rw [hlast2]
          have hlast3 : (cur.reverse ++ x :: xs).getLastD 0 = (x :: xs).getLastD 0 := by
            rw [getLastD_eq_getLast (by simp),
              List.getLast_append_of_ne_nil _ (List.cons_ne_nil x xs),
              ← getLastD_eq_getLast (List.cons_ne_nil x xs)]
          exact hlast3.symm

lemma denseBlocks_spec {L : List ℕ} (hL_ne : L ≠ []) (hL_lt : L.Pairwise (· < ·)) :
    (denseBlocks L).flatten = L ∧
    (∀ b ∈ denseBlocks L, IsDenseBlock b) ∧
    HasGaps (denseBlocks L) ∧
    denseBlocks L ≠ [] ∧
    ((denseBlocks L).headD []).headD 0 = L.headD 0 ∧
    ((denseBlocks L).getLastD []).getLastD 0 = L.getLastD 0 := by
  cases L with
  | nil => contradiction
  | cons x xs =>
    unfold denseBlocks
    have hx_dense : IsDenseBlock [x].reverse := ⟨by simp, by simp, fun i hi => by simp at hi⟩
    simpa using denseBlocksAux_spec x [x] xs (List.cons_ne_nil x []) rfl hx_dense hL_lt

/-- Inside a single `2`-dense block `b`, every integer `x ∈ [b.headD 0, 2 * b.getLastD 0)`
is covered by `[e, 2 * e)` for some `e ∈ b`. -/
lemma denseBlock_covers {b : List ℕ} (hb : IsDenseBlock b) {x : ℕ}
    (hx1 : b.headD 0 ≤ x) (hx2 : x < 2 * b.getLastD 0) :
    ∃ e ∈ b, e ≤ x ∧ x < 2 * e := by
  induction b with
  | nil => exact absurd rfl hb.1
  | cons a as ih =>
    cases as with
    | nil =>
      simp only [List.headD_cons, getLastD_singleton] at hx1 hx2
      exact ⟨a, List.mem_cons_self, hx1, hx2⟩
    | cons b₁ bs =>
      by_cases hx_lt : x < 2 * a
      · exact ⟨a, List.mem_cons_self, by simpa using hx1, hx_lt⟩
      · have hb₁_le : b₁ ≤ 2 * a := by
          have := hb.2.2 0 (by simp)
          simpa using this
        have hx1' : (b₁ :: bs).headD 0 ≤ x := by simp; omega
        have hx2' : x < 2 * (b₁ :: bs).getLastD 0 := by
          have hlast : (a :: b₁ :: bs).getLastD 0 = (b₁ :: bs).getLastD 0 := by
            rw [getLastD_eq_getLast (List.cons_ne_nil _ _),
              getLastD_eq_getLast (List.cons_ne_nil _ _),
              List.getLast_cons]
          rwa [← hlast]
        have hb' : IsDenseBlock (b₁ :: bs) :=
          ⟨List.cons_ne_nil _ _, (List.pairwise_cons.mp hb.2.1).2,
            fun i hi => hb.2.2 (i + 1) (by simpa using hi)⟩
        obtain ⟨e, he, h1, h2⟩ := ih hb' hx1' hx2'
        exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩

lemma mem_denseBlock_bounds {b : List ℕ} (hb : IsDenseBlock b) {e : ℕ} (he : e ∈ b) :
    b.headD 0 ≤ e ∧ e ≤ b.getLastD 0 := by
  rcases hb with ⟨hne, hlt, _⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hlen : 0 < b.length := List.length_pos_of_ne_nil hne
  have hhead : b.headD 0 = b[0] := by
    cases b with | nil => contradiction | cons a as => rfl
  have hlast : b.getLastD 0 = b[b.length - 1] := by
    rw [getLastD_eq_getLast hne, List.getLast_eq_getElem hne]
  rw [hhead, hlast]
  constructor
  · by_cases hi0 : i = 0
    · subst hi0; exact le_refl _
    · exact le_of_lt (List.pairwise_iff_getElem.mp hlt 0 i hlen hi (by omega))
  · by_cases hil : i = b.length - 1
    · subst hil; exact le_refl _
    · exact le_of_lt (List.pairwise_iff_getElem.mp hlt i (b.length - 1) hi (by omega) (by omega))

/-- For any `2`-dense block list with gaps covering `[a, endX)`, if `W` is positive on every
`[b.headD 0, 2 * b.getLastD 0)` and zero on every gap `[2 * b₁.getLastD 0, b₂.headD 0)`, then
`posParts` of the integer sampling on `[a, endX)` extracts exactly those intervals! -/
lemma posParts_of_blocks {f : ℕ → ℕ} :
    ∀ (B : List (List ℕ)), B ≠ [] →
      (∀ b ∈ B, IsDenseBlock b) →
      HasGaps B →
      (∀ b ∈ B, ∀ x, b.headD 0 ≤ x → x < 2 * b.getLastD 0 → 0 < f x) →
      (∀ b ∈ B, 0 < b.headD 0) →
      (∀ i (hi : i + 1 < B.length),
        ∀ x, 2 * B[i].getLastD 0 ≤ x → x < B[i + 1].headD 0 → f x = 0) →
      posParts ((List.range' ((B.headD []).headD 0)
          (2 * (B.getLastD []).getLastD 0 - (B.headD []).headD 0)).map f) =
        B.map (fun b => (List.range' (b.headD 0) (2 * b.getLastD 0 - b.headD 0)).map f) := by
  intro B
  induction B with
  | nil => intro h; contradiction
  | cons b₁ rest ih =>
    intro _ hdense hgaps hpos hminpos hzero
    have hb₁ := hdense b₁ List.mem_cons_self
    have ha₁_pos : 0 < b₁.headD 0 := hminpos b₁ List.mem_cons_self
    have ha₁_le_c₁ : b₁.headD 0 ≤ b₁.getLastD 0 := by
      have hmem : b₁.headD 0 ∈ b₁ := by
        cases h : b₁ with | nil => exact absurd h hb₁.1 | cons a as => simp
      exact (mem_denseBlock_bounds hb₁ hmem).2
    have hlen₁_pos : 0 < 2 * b₁.getLastD 0 - b₁.headD 0 := by omega
    match rest with
    | [] =>
      simp only [List.headD_cons, getLastD_singleton, List.map_singleton]
      apply posParts_all_pos
      · cases h : 2 * b₁.getLastD 0 - b₁.headD 0 with
        | zero => omega
        | succ k => simp [List.range'_succ]
      · intro y hy
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        rw [List.mem_range'_1] at hx
        exact hpos b₁ List.mem_cons_self x hx.1 (by omega)
    | b₂ :: bs =>
      have hgap₁₂ : 2 * b₁.getLastD 0 < b₂.headD 0 := hgaps.1
      have hrest_ne : b₂ :: bs ≠ [] := List.cons_ne_nil _ _
      have hrest_dense : ∀ b ∈ b₂ :: bs, IsDenseBlock b := fun b hb =>
        hdense b (List.mem_cons_of_mem _ hb)
      have hrest_minpos : ∀ b ∈ b₂ :: bs, 0 < b.headD 0 := fun b hb =>
        hminpos b (List.mem_cons_of_mem _ hb)
      have hmono : ∀ (L : List (List ℕ)), L ≠ [] → (∀ b ∈ L, IsDenseBlock b) →
          HasGaps L → (∀ b ∈ L, 0 < b.headD 0) →
          (L.headD []).headD 0 ≤ 2 * (L.getLastD []).getLastD 0 := by
        intro L
        induction L with
        | nil => intro h; contradiction
        | cons u us ihL =>
          intro _ hdL hgL hmL
          have hu := hdL u List.mem_cons_self
          have hum : u.headD 0 ≤ u.getLastD 0 := by
            have hmem : u.headD 0 ∈ u := by
              cases h : u with | nil => exact absurd h hu.1 | cons a as => simp
            exact (mem_denseBlock_bounds hu hmem).2
          have hup : 0 < u.headD 0 := hmL u List.mem_cons_self
          match us with
          | [] => simp only [List.headD_cons, getLastD_singleton]; omega
          | v :: vs =>
            have hgv : 2 * u.getLastD 0 < v.headD 0 := hgL.1
            have hrec := ihL (List.cons_ne_nil _ _)
              (fun b hb => hdL b (List.mem_cons_of_mem _ hb)) hgL.2
              (fun b hb => hmL b (List.mem_cons_of_mem _ hb))
            simp only [List.headD_cons] at hrec ⊢
            have hlast : (u :: v :: vs).getLastD [] = (v :: vs).getLastD [] := by
              rw [getLastD_eq_getLast (List.cons_ne_nil _ _),
                getLastD_eq_getLast (List.cons_ne_nil _ _),
                List.getLast_cons]
            rw [hlast]
            omega
      have hend_ge : b₂.headD 0 ≤ 2 * ((b₂ :: bs).getLastD []).getLastD 0 :=
        hmono (b₂ :: bs) hrest_ne hrest_dense hgaps.2 hrest_minpos
      set a₁ := b₁.headD 0
      set g₁ := 2 * b₁.getLastD 0
      set a₂ := b₂.headD 0
      set endX := 2 * ((b₂ :: bs).getLastD []).getLastD 0
      have hlast_eq : (b₁ :: b₂ :: bs).getLastD [] = (b₂ :: bs).getLastD [] := by
        rw [getLastD_eq_getLast (List.cons_ne_nil _ _),
          getLastD_eq_getLast (List.cons_ne_nil _ _),
          List.getLast_cons]
      simp only [List.headD_cons, hlast_eq, List.map_cons]
      have hsplit_range : List.range' a₁ (endX - a₁) =
          List.range' a₁ (g₁ - a₁) ++ g₁ :: (List.range' (g₁ + 1) (a₂ - g₁ - 1) ++
            List.range' a₂ (endX - a₂)) := by
        have h1 : List.range' a₁ (g₁ - a₁) ++ List.range' g₁ (endX - g₁) =
            List.range' a₁ (endX - a₁) := by
          have := List.range'_append (s := a₁) (m := g₁ - a₁) (n := endX - g₁) (step := 1)
          simp only [one_mul, show a₁ + (g₁ - a₁) = g₁ by omega,
            show g₁ - a₁ + (endX - g₁) = endX - a₁ by omega] at this
          exact this
        have h2 : List.range' (g₁ + 1) (a₂ - g₁ - 1) ++ List.range' a₂ (endX - a₂) =
            List.range' (g₁ + 1) (endX - (g₁ + 1)) := by
          have := List.range'_append (s := g₁ + 1) (m := a₂ - g₁ - 1) (n := endX - a₂) (step := 1)
          simp only [one_mul, show g₁ + 1 + (a₂ - g₁ - 1) = a₂ by omega,
            show a₂ - g₁ - 1 + (endX - a₂) = endX - (g₁ + 1) by omega] at this
          exact this
        have h3 : List.range' g₁ (endX - g₁) = g₁ :: List.range' (g₁ + 1) (endX - (g₁ + 1)) := by
          rw [show endX - g₁ = (endX - (g₁ + 1)) + 1 by omega, List.range'_succ]
        rw [← h1, h3, h2]
      rw [hsplit_range, List.map_append, List.map_cons, List.map_append]
      have hfg₁ : f g₁ = 0 := hzero 0 (by simp) g₁ (le_refl _) hgap₁₂
      rw [hfg₁, posParts_append_zero]
      have hpart1 : posParts ((List.range' a₁ (g₁ - a₁)).map f) =
          [(List.range' a₁ (g₁ - a₁)).map f] := by
        apply posParts_all_pos
        · cases h : g₁ - a₁ with
          | zero => omega
          | succ k => simp [List.range'_succ]
        · intro y hy
          rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
          rw [List.mem_range'_1] at hx
          exact hpos b₁ List.mem_cons_self x hx.1 (by omega)
      have hzeros : ∀ y ∈ (List.range' (g₁ + 1) (a₂ - g₁ - 1)).map f, y = 0 := by
        intro y hy
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        rw [List.mem_range'_1] at hx
        have h1 : 2 * (b₁ :: b₂ :: bs)[0].getLastD 0 ≤ x := by
          change 2 * b₁.getLastD 0 ≤ x
          omega
        have h2 : x < (b₁ :: b₂ :: bs)[0 + 1].headD 0 := by
          change x < b₂.headD 0
          omega
        exact hzero 0 (by simp) x h1 h2
      have hdrop_zeros : ∀ (Z R : List ℕ), (∀ z ∈ Z, z = 0) → posParts (Z ++ R) = posParts R := by
        intro Z R hZ
        induction Z with
        | nil => rfl
        | cons z zs ihZ =>
          have hz0 : z = 0 := hZ z List.mem_cons_self
          subst hz0
          have hzs : ∀ w ∈ zs, w = 0 := fun w hw => hZ w (List.mem_cons_of_mem _ hw)
          simpa [posParts, posPartsAux] using ihZ hzs
      rw [hpart1, hdrop_zeros _ _ hzeros, List.singleton_append]
      congr 1
      exact ih hrest_ne hrest_dense hgaps.2
        (fun b hb => hpos b (List.mem_cons_of_mem _ hb)) hrest_minpos
        (fun i hi => hzero (i + 1) (by simpa using hi))

/-! ### Section 6: Exact blockwise counts and the four OEIS conjectures -/

lemma totalRise_range' (f : ℕ → ℕ) (a k prev : ℕ) :
    totalRise prev ((List.range' a k).map f) =
      match k with
      | 0 => 0
      | k' + 1 => (f a - prev) + ∑ i ∈ Finset.range k', (f (a + i + 1) - f (a + i)) := by
  induction k generalizing a prev with
  | zero => simp [totalRise]
  | succ k ih =>
    rw [List.range'_succ, List.map_cons, totalRise, ih (a + 1) (f a)]
    cases k with
    | zero => simp
    | succ k' =>
      simp only
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hshift : ∑ i ∈ Finset.range k', (f (a + 1 + i + 1) - f (a + 1 + i)) =
          ∑ i ∈ Finset.range k', (f (a + (i + 1) + 1) - f (a + (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show a + 1 + i = a + (i + 1) by omega]
      rw [hshift]
      omega

lemma W_rise_eq_indicator {n x : ℕ} (hn : 0 < n) (hx : 1 ≤ x) :
    W n x - W n (x - 1) = if x ∣ oddPart n then 1 else 0 := by
  have hm_odd : oddPart n % 2 = 1 := oddPart_odd hn
  have hQeven : 2 ∣ dyadicQ n := by
    unfold dyadicQ; rw [pow_succ']; exact dvd_mul_right _ _
  have hstep := W_step_int hn (x - 1)
  rw [Nat.sub_add_cancel hx] at hstep
  have hdisj : ¬ (x ∣ oddPart n ∧ ∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d) := by
    rintro ⟨⟨u, hu⟩, d, _, rfl⟩
    rcases hQeven with ⟨q, hq⟩
    have h2 : (dyadicQ n * d * u) % 2 = 0 := by
      rw [hq, mul_assoc, mul_assoc]; exact Nat.mul_mod_right 2 _
    omega
  by_cases h1 : x ∣ oddPart n
  · have h2 : ¬ (∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d) := fun hex => hdisj ⟨h1, hex⟩
    rw [if_pos h1, if_neg h2, sub_zero] at hstep
    rw [if_pos h1]
    omega
  · rw [if_neg h1] at hstep ⊢
    by_cases h2 : ∃ d ∈ (oddPart n).divisors, x = dyadicQ n * d
    · rw [if_pos h2, zero_sub] at hstep
      omega
    · rw [if_neg h2, sub_self] at hstep
      omega

lemma layerRuns_block_eq_oddDivisors {n a c : ℕ} (hn : 0 < n)
    (ha_pos : 0 < a) (ha_le : a ≤ c) (hpred_zero : W n (a - 1) = 0) :
    layerRuns ((List.range' a (2 * c - a)).map (W n)) =
      ((oddPart n).divisors.filter (fun d => a ≤ d ∧ d < 2 * c)).card := by
  rw [layerRuns_eq_totalRise, totalRise_range']
  have hk_pos : 1 ≤ 2 * c - a := by omega
  set k' := 2 * c - a - 1
  have hk_eq : 2 * c - a = k' + 1 := by omega
  rw [hk_eq]
  simp only
  rw [← hpred_zero, W_rise_eq_indicator hn ha_pos]
  have hsum_ind : ∑ i ∈ Finset.range k', (W n (a + i + 1) - W n (a + i)) =
      ∑ i ∈ Finset.range k', (if (a + i + 1) ∣ oddPart n then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    have := W_rise_eq_indicator hn (show 1 ≤ a + i + 1 by omega)
    simpa [Nat.add_sub_cancel] using this
  rw [hsum_ind]
  have hcomb : (if a ∣ oddPart n then 1 else 0) +
      ∑ i ∈ Finset.range k', (if (a + i + 1) ∣ oddPart n then 1 else 0) =
      ∑ x ∈ Finset.Ico a (2 * c), (if x ∣ oddPart n then 1 else 0) := by
    have hIco : Finset.Ico a (2 * c) = insert a (Finset.Ico (a + 1) (2 * c)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnotmem : a ∉ Finset.Ico (a + 1) (2 * c) := by simp
    rw [hIco, Finset.sum_insert hnotmem]
    congr 1
    apply Finset.sum_nbij (fun i => a + i + 1)
    · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Ico]; omega
    · intro i₁ _ i₂ _ h; dsimp only at h; omega
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_Ico] at hx
      exact ⟨x - a - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
    · intro _ _; rfl
  rw [hcomb, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    mul_one]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ico, Nat.mem_divisors]
  have hm_ne : oddPart n ≠ 0 := Nat.ne_of_gt (oddPart_pos hn)
  tauto

lemma sortedDivisors_spec {n : ℕ} (hn : 0 < n) :
    sortedDivisors n ≠ [] ∧
    (sortedDivisors n).Pairwise (· < ·) ∧
    (sortedDivisors n).Nodup ∧
    (∀ e, e ∈ sortedDivisors n ↔ e ∈ n.divisors) ∧
    (sortedDivisors n).headD 0 = 1 ∧
    (sortedDivisors n).getLastD 0 = n := by
  have hmem : ∀ e, e ∈ sortedDivisors n ↔ e ∈ n.divisors := fun e => Finset.mem_sort _
  have hnodup : (sortedDivisors n).Nodup := n.divisors.sort_nodup (· ≤ ·)
  have hsorted : (sortedDivisors n).Pairwise (· ≤ ·) := n.divisors.pairwise_sort (· ≤ ·)
  have hlt : (sortedDivisors n).Pairwise (· < ·) := by
    have hne_pair := List.nodup_iff_pairwise_ne.mp hnodup
    rw [List.pairwise_iff_getElem] at hsorted hne_pair ⊢
    intro i j hi hj hij
    exact lt_of_le_of_ne (hsorted i j hi hj hij) (hne_pair i j hi hj hij)
  have h1mem : 1 ∈ sortedDivisors n := (hmem 1).mpr (Nat.one_mem_divisors.mpr (Nat.ne_of_gt hn))
  have hnmem : n ∈ sortedDivisors n :=
    (hmem n).mpr (Nat.mem_divisors.mpr ⟨dvd_refl n, Nat.ne_of_gt hn⟩)
  have hne : sortedDivisors n ≠ [] := List.ne_nil_of_mem h1mem
  have hhead : (sortedDivisors n).headD 0 = 1 := by
    cases h : sortedDivisors n with
    | nil => exact absurd h hne
    | cons a as =>
      have ha_pos : 1 ≤ a := by
        have := (hmem a).mp (by rw [h]; exact List.mem_cons_self)
        exact Nat.pos_of_mem_divisors this
      have ha_le1 : a ≤ 1 := by
        rw [h] at h1mem hsorted
        rcases List.mem_cons.mp h1mem with rfl | h1in
        · exact le_refl 1
        · exact (List.pairwise_cons.mp hsorted).1 1 h1in
      simp [show a = 1 by omega]
  have hlast : (sortedDivisors n).getLastD 0 = n := by
    have hlast_mem : (sortedDivisors n).getLastD 0 ∈ sortedDivisors n := by
      rw [getLastD_eq_getLast hne]
      exact List.getLast_mem hne
    have hle_n : (sortedDivisors n).getLastD 0 ≤ n :=
      Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors ((hmem _).mp hlast_mem))
    have hn_le : n ≤ (sortedDivisors n).getLastD 0 := by
      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hnmem
      rw [getLastD_eq_getLast hne, List.getLast_eq_getElem hne]
      by_cases hil : i = (sortedDivisors n).length - 1
      · exact le_of_eq (calc n = (sortedDivisors n)[i] := hgi.symm
          _ = (sortedDivisors n)[(sortedDivisors n).length - 1] := by congr 1)
      · calc n = (sortedDivisors n)[i] := hgi.symm
          _ ≤ (sortedDivisors n)[(sortedDivisors n).length - 1] :=
            List.pairwise_iff_getElem.mp hsorted i ((sortedDivisors n).length - 1) hi
              (Nat.sub_lt (List.length_pos_of_ne_nil hne) (by omega)) (by omega)
    omega
  exact ⟨hne, hlt, hnodup, hmem, hhead, hlast⟩

/-- Helper: ordering between elements of earlier and later blocks when `B.flatten` is strictly increasing. -/
lemma blocks_order {B : List (List ℕ)} (hflat_lt : B.flatten.Pairwise (· < ·))
    {i j : ℕ} (hi : i < B.length) (hj : j < B.length) (hij : i < j)
    {x y : ℕ} (hx : x ∈ B[i]) (hy : y ∈ B[j]) : x < y := by
  set bi := B[i]
  set bj := B[j]
  have hBeq : B = B.take i ++ [bi] ++ (B.drop (i + 1)).take (j - i - 1) ++ [bj] ++ B.drop (j + 1) := by
    have h1 : B = B.take i ++ bi :: B.drop (i + 1) := by
      have h := (List.take_append_drop i B).symm
      rw [← List.cons_getElem_drop_succ (h := hi)] at h
      exact h
    have hlt_j : j - i - 1 < (B.drop (i + 1)).length := by simp; omega
    have hget_j : (B.drop (i + 1))[j - i - 1] = bj := by
      rw [List.getElem_drop]; simp only [bj]; congr 1; omega
    have h2 : B.drop (i + 1) = (B.drop (i + 1)).take (j - i - 1) ++
        bj :: (B.drop (i + 1)).drop (j - i - 1 + 1) := by
      have h := (List.take_append_drop (j - i - 1) (B.drop (i + 1))).symm
      rw [← List.cons_getElem_drop_succ (h := hlt_j), hget_j] at h
      exact h
    have hdrop : (B.drop (i + 1)).drop (j - i - 1 + 1) = B.drop (j + 1) := by
      rw [List.drop_drop]; congr 1; omega
    rw [hdrop] at h2
    calc B = B.take i ++ bi :: B.drop (i + 1) := h1
      _ = B.take i ++ bi :: ((B.drop (i + 1)).take (j - i - 1) ++ bj :: B.drop (j + 1)) := by
        exact congrArg (fun t => B.take i ++ bi :: t) h2
      _ = B.take i ++ [bi] ++ (B.drop (i + 1)).take (j - i - 1) ++ [bj] ++ B.drop (j + 1) := by
        simp [List.append_assoc]
  have hflat : B.flatten = (B.take i).flatten ++ bi ++ ((B.drop (i + 1)).take (j - i - 1)).flatten ++
      bj ++ (B.drop (j + 1)).flatten := by
    conv_lhs => rw [hBeq]
    simp [List.flatten_append, List.append_assoc]
  rw [hflat] at hflat_lt
  have hpair1 := (List.pairwise_append.mp hflat_lt).1
  have hpair2 := (List.pairwise_append.mp hpair1).2.2
  exact hpair2 x (by simp [hx]) y hy

/-- Helper: extract `HasGaps` at index `k`. -/
lemma hasGaps_getElem {B : List (List ℕ)} (hg : HasGaps B)
    {k : ℕ} (hk : k + 1 < B.length) :
    2 * B[k].getLastD 0 < B[k + 1].headD 0 := by
  induction B generalizing k with
  | nil => simp at hk
  | cons u us ih =>
    match us with
    | [] => simp at hk
    | v :: vs =>
      cases k with
      | zero => exact hg.1
      | succ k' => exact ih hg.2 (by simpa using hk)

/-- Exact blockwise correspondence: for every `n ≥ 1`, every block `b` in
`denseBlocks (sortedDivisors n)` has:
1. `layerRuns` of its corresponding `W`-part equal to `(b.filter (· % 2 = 1)).length`, and
2. `b.length = a001511 n * (b.filter (· % 2 = 1)).length`. -/
theorem pol_A280940_eq_A384225 (n : ℕ) (hn : 0 < n) :
    a280940Row n = a384225Row n := by
  obtain ⟨hne, hlt, hnodup, hmem, hhead, hlast⟩ := sortedDivisors_spec hn
  let D := sortedDivisors n
  let B := denseBlocks D
  obtain ⟨hflat, hB_dense, hB_gaps, hB_ne, hB_head, hB_last⟩ := denseBlocks_spec hne hlt
  have hB_mem_div : ∀ b ∈ B, ∀ e ∈ b, e ∈ n.divisors := by
    intro b hb e he
    have : e ∈ B.flatten := List.mem_flatten.mpr ⟨b, hb, he⟩
    rw [hflat] at this
    exact (hmem e).mp this
  have hB_minpos : ∀ b ∈ B, 0 < b.headD 0 := by
    intro b hb
    have hd := hB_dense b hb
    have hhm : b.headD 0 ∈ b := by
      cases h : b with | nil => exact absurd h hd.1 | cons a as => simp
    exact Nat.pos_of_mem_divisors (hB_mem_div b hb _ hhm)
  have hB_order : ∀ i j (hi : i < B.length) (hj : j < B.length), i < j →
      ∀ x ∈ B[i], ∀ y ∈ B[j], x < y :=
    fun _ _ hi hj hij _ hx _ hy => blocks_order (by rwa [hflat]) hi hj hij hx hy
  have hB_gap_zero : ∀ i (hi : i + 1 < B.length),
      ∀ x, 2 * B[i].getLastD 0 ≤ x → x < B[i + 1].headD 0 → W n x = 0 := by
    intro i hi x hx1 hx2
    by_contra hne0
    have hpos : 0 < W n x := Nat.pos_of_ne_zero hne0
    obtain ⟨e, he_div, he1, he2⟩ := (W_pos_iff_exists_divisor hn).mp hpos
    have he_flat : e ∈ B.flatten := by rw [hflat]; exact (hmem e).mpr he_div
    obtain ⟨b, hb_mem, he_b⟩ := List.mem_flatten.mp he_flat
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb_mem
    by_cases hji : j ≤ i
    · have he_le : e ≤ B[i].getLastD 0 := by
        rcases eq_or_lt_of_le hji with rfl | hlt_ji
        · exact (mem_denseBlock_bounds (hB_dense B[j] (List.getElem_mem hj)) he_b).2
        · have hlast_mem : B[i].getLastD 0 ∈ B[i] := by
            have hd := hB_dense B[i] (List.getElem_mem (show i < B.length by omega))
            rw [getLastD_eq_getLast hd.1]; exact List.getLast_mem hd.1
          exact le_of_lt (hB_order j i hj (show i < B.length by omega) hlt_ji e he_b _ hlast_mem)
      omega
    · have hi1_le : i + 1 ≤ j := by omega
      have hhead_le : B[i + 1].headD 0 ≤ e := by
        rcases eq_or_lt_of_le hi1_le with rfl | hlt_ij
        · exact (mem_denseBlock_bounds (hB_dense B[i + 1] (List.getElem_mem hj)) he_b).1
        · have hhead_mem : B[i + 1].headD 0 ∈ B[i + 1] := by
            have hd := hB_dense B[i + 1] (List.getElem_mem hi)
            cases h : B[i + 1] with | nil => exact absurd h hd.1 | cons a as => simp
          exact le_of_lt (hB_order (i + 1) j hi hj hlt_ij _ hhead_mem e he_b)
      omega
  have hB_pos : ∀ b ∈ B, ∀ x, b.headD 0 ≤ x → x < 2 * b.getLastD 0 → 0 < W n x := by
    intro b hb x hx1 hx2
    obtain ⟨e, he, h1, h2⟩ := denseBlock_covers (hB_dense b hb) hx1 hx2
    exact (W_pos_iff_exists_divisor hn).mpr ⟨e, hB_mem_div b hb e he, h1, h2⟩
  have hposParts_W :
      posParts ((List.range' 1 (2 * n - 1)).map (W n)) =
        B.map (fun b => (List.range' (b.headD 0) (2 * b.getLastD 0 - b.headD 0)).map (W n)) := by
    have h := posParts_of_blocks (f := W n) B hB_ne hB_dense hB_gaps hB_pos hB_minpos hB_gap_zero
    rwa [hB_head, hhead, hB_last, hlast] at h
  have ha280940 : a280940Row n =
      (posParts ((List.range' 1 (2 * n - 1)).map (W n))).map layerRuns := by
    unfold a280940Row
    have h1 : ∀ L : List ℕ, (posParts L).map layerRuns =
        ((posParts L).map dedupAdj).map layerRuns := by
      intro L
      rw [List.map_map]
      apply List.map_congr_left
      intro p _
      exact (layerRuns_dedupAdj p).symm
    rw [h1 (a262045 n), ← posParts_dedupAdj, dedupAdj_a262045_eq_W hn, posParts_dedupAdj,
      ← h1]
  rw [ha280940, hposParts_W, List.map_map]
  unfold a384225Row
  apply List.ext_getElem (by simp [B, D])
  intro i hi1 hi2
  simp only [List.length_map] at hi1 hi2
  rw [List.getElem_map, List.getElem_map, Function.comp_apply]
  let b := B[i]
  have hb_mem : b ∈ B := List.getElem_mem hi1
  have hb_dense : IsDenseBlock b := hB_dense b hb_mem
  have ha_pos : 0 < b.headD 0 := hB_minpos b hb_mem
  have ha_le_c : b.headD 0 ≤ b.getLastD 0 := by
    have hhm : b.headD 0 ∈ b := by
      cases h : b with | nil => exact absurd h hb_dense.1 | cons a as => simp
    exact (mem_denseBlock_bounds hb_dense hhm).2
  have hpred_zero : W n (b.headD 0 - 1) = 0 := by
    by_cases hi0 : i = 0
    · have hb0 : b = B.headD [] := by
        cases hB : B with
        | nil => exact absurd hB hB_ne
        | cons u us => simp [b, hi0, hB]
      rw [hb0, hB_head, hhead]
      exact W_zero n
    · have him1 : i - 1 + 1 < B.length := by omega
      have hgap : 2 * B[i - 1].getLastD 0 < b.headD 0 := by
        have h := hasGaps_getElem hB_gaps him1
        simpa [b, show i - 1 + 1 = i by omega] using h
      exact hB_gap_zero (i - 1) him1 (b.headD 0 - 1) (by omega) (by
        have : B[i - 1 + 1] = b := by simp [b, show i - 1 + 1 = i by omega]
        rw [this]; omega)
  rw [layerRuns_block_eq_oddDivisors hn ha_pos ha_le_c hpred_zero]
  have hb_nodup : b.Nodup := hb_dense.2.1.imp (fun h => Nat.ne_of_lt h)
  rw [← List.toFinset_card_of_nodup (hb_nodup.filter _)]
  congr 1
  ext d
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hd_m, h1, h2⟩
    have hd_odd : d % 2 = 1 := by
      have hm_odd := oddPart_odd hn
      rcases Nat.dvd_of_mem_divisors hd_m with ⟨u, hu⟩
      by_contra h
      have h0 : d % 2 = 0 := by omega
      have : (d * u) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
      omega
    have hd_n : d ∈ n.divisors := by
      refine Nat.mem_divisors.mpr ⟨?_, Nat.ne_of_gt hn⟩
      exact (divisor_iff_pow_two_mul_oddPart hn).mpr
        ⟨0, Nat.zero_le _, d, Nat.dvd_of_mem_divisors hd_m, by simp⟩
    have hd_flat : d ∈ B.flatten := by rw [hflat]; exact (hmem d).mpr hd_n
    obtain ⟨b', hb'_mem, hd_b'⟩ := List.mem_flatten.mp hd_flat
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'_mem
    have hji : j = i := by
      rcases lt_trichotomy j i with hlt_ji | rfl | hgt_ji
      · have hhead_mem : b.headD 0 ∈ b := by
          cases h : b with | nil => exact absurd h hb_dense.1 | cons a as => simp
        have := hB_order j i hj hi1 hlt_ji d hd_b' _ hhead_mem
        omega
      · rfl
      · have hi1_lt : i + 1 < B.length := by omega
        have hgap : 2 * b.getLastD 0 < B[i + 1].headD 0 := hasGaps_getElem hB_gaps hi1_lt
        have hle_d : B[i + 1].headD 0 ≤ d := by
          rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with rfl | hlt_ij
          · exact (mem_denseBlock_bounds (hB_dense B[i + 1] (List.getElem_mem hj)) hd_b').1
          · have hhm : B[i + 1].headD 0 ∈ B[i + 1] := by
              have hd1 := hB_dense B[i + 1] (List.getElem_mem hi1_lt)
              cases h : B[i + 1] with | nil => exact absurd h hd1.1 | cons a as => simp
            exact le_of_lt (hB_order (i + 1) j hi1_lt hj hlt_ij _ hhm d hd_b')
        omega
    subst hji
    exact ⟨hd_b', hd_odd⟩
  · rintro ⟨hd_b, hd_odd⟩
    have hd_n := hB_mem_div b hb_mem d hd_b
    obtain ⟨k, _, d₀, hd₀, hdeq⟩ := (divisor_iff_pow_two_mul_oddPart hn).mp (Nat.dvd_of_mem_divisors hd_n)
    have hk0 : k = 0 := by
      by_contra hk
      rcases dvd_pow_self 2 hk with ⟨q, hq⟩
      have h2 : d % 2 = 0 := by rw [hdeq, hq, mul_assoc]; exact Nat.mul_mod_right 2 _
      omega
    subst hk0
    simp only [pow_zero, one_mul] at hdeq
    subst hdeq
    have hbnd := mem_denseBlock_bounds hb_dense hd_b
    exact ⟨Nat.mem_divisors.mpr ⟨hd₀, Nat.ne_of_gt (oddPart_pos hn)⟩, hbnd.1, by omega⟩

/-- OEIS A384225 Conjecture 2 (Oct 13 2026): every maximal `2`-dense divisor block of `n`
has length `(v₂(n) + 1)` times its number of odd divisors. -/
theorem pol_A384222_eq_ruler_mul_A384225 (n : ℕ) (hn : 0 < n) :
    a384222Row n = (a384225Row n).map (fun c => a001511 n * c) := by
  obtain ⟨hne, hlt, hnodup, hmem, hhead, hlast⟩ := sortedDivisors_spec hn
  let D := sortedDivisors n
  let B := denseBlocks D
  obtain ⟨hflat, hB_dense, hB_gaps, hB_ne, hB_head, hB_last⟩ := denseBlocks_spec hne hlt
  have hB_mem_div : ∀ b ∈ B, ∀ e ∈ b, e ∈ n.divisors := by
    intro b hb e he
    have : e ∈ B.flatten := List.mem_flatten.mpr ⟨b, hb, he⟩
    rw [hflat] at this
    exact (hmem e).mp this
  have hB_order : ∀ i j (hi : i < B.length) (hj : j < B.length), i < j →
      ∀ x ∈ B[i], ∀ y ∈ B[j], x < y :=
    fun _ _ hi hj hij _ hx _ hy => blocks_order (by rwa [hflat]) hi hj hij hx hy
  have hsame_block : ∀ i (hi : i < B.length) (e : ℕ),
      e ∈ B[i] → 2 * e ∈ n.divisors → 2 * e ∈ B[i] := by
    intro i hi e he h2e_div
    have h2e_flat : 2 * e ∈ B.flatten := by rw [hflat]; exact (hmem _).mpr h2e_div
    obtain ⟨b', hb'_mem, h2e_b'⟩ := List.mem_flatten.mp h2e_flat
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'_mem
    have he_pos : 0 < e := Nat.pos_of_mem_divisors (hB_mem_div B[i] (List.getElem_mem hi) e he)
    have hji : j = i := by
      rcases lt_trichotomy j i with hlt_ji | rfl | hgt_ji
      · have := hB_order j i hj hi hlt_ji (2 * e) h2e_b' e he
        omega
      · rfl
      · have hi1 : i + 1 < B.length := by omega
        have hgap : 2 * B[i].getLastD 0 < B[i + 1].headD 0 := hasGaps_getElem hB_gaps hi1
        have he_le : e ≤ B[i].getLastD 0 :=
          (mem_denseBlock_bounds (hB_dense B[i] (List.getElem_mem hi)) he).2
        have hle_2e : B[i + 1].headD 0 ≤ 2 * e := by
          rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with rfl | hlt_ij
          · exact (mem_denseBlock_bounds (hB_dense B[i + 1] (List.getElem_mem hj)) h2e_b').1
          · have hhm : B[i + 1].headD 0 ∈ B[i + 1] := by
              have hd1 := hB_dense B[i + 1] (List.getElem_mem hi1)
              cases h : B[i + 1] with | nil => exact absurd h hd1.1 | cons a as => simp
            exact le_of_lt (hB_order (i + 1) j hi1 hj hlt_ij _ hhm (2 * e) h2e_b')
        omega
    subst hji
    exact h2e_b'
  have hsame_block_down : ∀ i (hi : i < B.length) (e : ℕ),
      2 * e ∈ B[i] → e ∈ n.divisors → e ∈ B[i] := by
    intro i hi e h2e he_div
    have he_flat : e ∈ B.flatten := by rw [hflat]; exact (hmem _).mpr he_div
    obtain ⟨b', hb'_mem, he_b'⟩ := List.mem_flatten.mp he_flat
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'_mem
    have h2e_in_j := hsame_block j hj e he_b' (hB_mem_div B[i] (List.getElem_mem hi) _ h2e)
    have hji : j = i := by
      rcases lt_trichotomy j i with hlt_ji | rfl | hgt_ji
      · have := hB_order j i hj hi hlt_ji (2 * e) h2e_in_j (2 * e) h2e; omega
      · rfl
      · have := hB_order i j hi hj hgt_ji (2 * e) h2e (2 * e) h2e_in_j; omega
    subst hji
    exact he_b'
  have hchain : ∀ i (hi : i < B.length) (d : ℕ) (hd : d ∣ oddPart n) (k : ℕ),
      k ≤ padicValNat 2 n → (2 ^ k * d ∈ B[i] ↔ d ∈ B[i]) := by
    intro i hi d hd k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hdiv_k : 2 ^ k * d ∈ n.divisors :=
        Nat.mem_divisors.mpr ⟨(divisor_iff_pow_two_mul_oddPart hn).mpr ⟨k, by omega, d, hd, rfl⟩,
          Nat.ne_of_gt hn⟩
      have hdiv_k1 : 2 * (2 ^ k * d) ∈ n.divisors := by
        rw [← mul_assoc, ← pow_succ']
        exact Nat.mem_divisors.mpr ⟨(divisor_iff_pow_two_mul_oddPart hn).mpr
          ⟨k + 1, hk, d, hd, rfl⟩, Nat.ne_of_gt hn⟩
      rw [pow_succ', mul_assoc]
      constructor
      · intro h
        exact hprev.mp (hsame_block_down i hi (2 ^ k * d) h hdiv_k)
      · intro h
        exact hsame_block i hi (2 ^ k * d) (hprev.mpr h) hdiv_k1
  unfold a384222Row a384225Row
  rw [List.map_map]
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.length_map] at hi1 hi2
  rw [List.getElem_map, List.getElem_map, Function.comp_apply]
  let b := B[i]
  have hb_dense := hB_dense b (List.getElem_mem hi1)
  have hb_nodup : b.Nodup := hb_dense.2.1.imp (fun h => Nat.ne_of_lt h)
  rw [← List.toFinset_card_of_nodup hb_nodup,
    ← List.toFinset_card_of_nodup (hb_nodup.filter _),
    ← Finset.card_range (a001511 n), ← Finset.card_product]
  apply Finset.card_bij (fun e _ => (padicValNat 2 e, oddPart e))
  · intro e he
    rw [List.mem_toFinset] at he
    have he_div := hB_mem_div b (List.getElem_mem hi1) e he
    have he_dvd := Nat.dvd_of_mem_divisors he_div
    have he_pos := Nat.pos_of_mem_divisors he_div
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hv_le : padicValNat 2 e ≤ padicValNat 2 n :=
      (padicValNat_dvd_iff_le (Nat.ne_of_gt hn)).mp (dvd_trans pow_padicValNat_dvd he_dvd)
    have hd_dvd : oddPart e ∣ oddPart n := by
      have hcop : Nat.Coprime (oddPart e) (2 ^ padicValNat 2 n) := by
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm]
        exact Nat.prime_two.coprime_iff_not_dvd.mpr (by have := oddPart_odd he_pos; omega)
      have : oddPart e ∣ 2 ^ padicValNat 2 n * oddPart n := by
        rw [pow_two_mul_oddPart]
        exact dvd_trans ⟨2 ^ padicValNat 2 e, by rw [mul_comm, pow_two_mul_oddPart]⟩ he_dvd
      exact hcop.dvd_of_dvd_mul_left this
    have he_eq : 2 ^ padicValNat 2 e * oddPart e = e := pow_two_mul_oddPart e
    have hd_mem_b : oddPart e ∈ b := (hchain i hi1 (oddPart e) hd_dvd (padicValNat 2 e) hv_le).mp
      (by rwa [he_eq])
    simp only [Finset.mem_product, Finset.mem_range, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq, a001511]
    exact ⟨by omega, hd_mem_b, oddPart_odd he_pos⟩
  · intro e₁ _ e₂ _ heq
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    calc e₁ = 2 ^ padicValNat 2 e₁ * oddPart e₁ := (pow_two_mul_oddPart e₁).symm
      _ = 2 ^ padicValNat 2 e₂ * oddPart e₂ := by rw [h1, h2]
      _ = e₂ := pow_two_mul_oddPart e₂
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq, a001511] at hp
    rcases hp with ⟨hp1, hp2_mem, hp2_odd⟩
    have hd_div := hB_mem_div b (List.getElem_mem hi1) p.2 hp2_mem
    obtain ⟨k, _, d₀, hd₀, hdeq⟩ := (divisor_iff_pow_two_mul_oddPart hn).mp
      (Nat.dvd_of_mem_divisors hd_div)
    have hk0 : k = 0 := by
      by_contra hk
      rcases dvd_pow_self 2 hk with ⟨q, hq⟩
      have h2 : p.2 % 2 = 0 := by rw [hdeq, hq, mul_assoc]; exact Nat.mul_mod_right 2 _
      omega
    subst hk0
    simp only [pow_zero, one_mul] at hdeq
    subst hdeq
    have hmem_prod : 2 ^ p.1 * p.2 ∈ b :=
      (hchain i hi1 p.2 hd₀ p.1 (by omega)).mpr hp2_mem
    refine ⟨2 ^ p.1 * p.2, List.mem_toFinset.mpr hmem_prod, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hv_p2 : padicValNat 2 p.2 = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    have hpos_p2 : p.2 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd_div)
    have hv_prod : padicValNat 2 (2 ^ p.1 * p.2) = p.1 := by
      rw [padicValNat.mul (by positivity) hpos_p2, padicValNat.prime_pow, hv_p2, add_zero]
    apply Prod.ext
    · exact hv_prod
    · unfold oddPart
      rw [hv_prod, Nat.mul_div_right _ (by positivity)]

/-- Omar E. Pol's OEIS A400974 conjecture (Oct 11 2026):
for every positive integer `n`, `A400974(n) = A001511(n) * A384230(n)`. -/
theorem pol_A400974_conjecture (n : ℕ) (hn : 0 < n) :
    a400974 n = a001511 n * a384230 n := by
  unfold a400974 a384230
  rw [pol_A384222_eq_ruler_mul_A384225 n hn, middleOrZero_map_mul, pol_A280940_eq_A384225 n hn]

end PolA400974

