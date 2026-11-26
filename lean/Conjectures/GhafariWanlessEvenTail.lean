import Mathlib.Tactic
import Conjectures.GhafariWanlessTailBase

/-!
# Parametric Even-`h` Tail Construction (Mod 16 Classes `0, 4, 8, 12`)

Constructs two completely disjoint `ValidTail fam.h (4 * p + fam.R)` instances for every `p : ℕ`
from any verified `EvenTailData` witness, covering all `n ≡ 0, 4, 8, 12 (mod 16)` from their
respective thresholds (`112, 116, 120, 108`) to infinity.
-/

namespace GhafariWanless

open GhafariWanless.Data

private structure EvenParams where
  d : ℕ
  e1_0 : ℕ
  e2_0 : ℕ
  s1_0 : ℕ
  s2_0 : ℕ
  U0_0 : ℕ
  U1_0 : ℕ
  j1_0 : ℕ
  U3_0 : ℕ
  j3_0 : ℕ
  U2_0 : ℕ

private def mkEvenParams (fam : EvenTailData) : EvenParams :=
  let d := fam.h / 2
  let e1_0 := fam.R - d
  let e2_0 := 2 * fam.R + d
  let s1_0 := e1_0 + fam.d1
  let s2_0 := e2_0 + fam.d2
  let U0_0 := s1_0 - 1
  let U1_0 := (s1_0 + 1) % 2
  let j1_0 := (s1_0 + 1 - U1_0) / 2
  let U3_0 := 2 * fam.R - (s2_0 - 1) % 2
  let j3_0 := (s2_0 - 1 - U3_0) / 2
  let U2_0 := s2_0 + 1 - 2 * fam.R
  ⟨d, e1_0, e2_0, s1_0, s2_0, U0_0, U1_0, j1_0, U3_0, j3_0, U2_0⟩

private def evenSlotU (fam : EvenTailData) (idx : ℕ) : ℕ :=
  let pr := fam.pairs.getD (idx / 2) (0, 0)
  if idx % 2 = 0 then pr.1 else pr.2

private def evenSlotS (fam : EvenTailData) (idx : ℕ) : ℕ × ℕ :=
  let P := mkEvenParams fam
  let ji := idx / 2
  let ui := evenSlotU fam idx
  let cj := rjSlope P.j3_0 P.j1_0 ji
  let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
  (2 * ji + ui + 1, 2 * cj + cu)

/-- Complete decidable checker for an `EvenTailData` family (proves validity for ALL `p : ℕ`). -/
def checkEvenTailData (fam : EvenTailData) : Bool :=
  let P := mkEvenParams fam
  (2 * P.d == fam.h) && (P.d ≤ fam.R) && (1 ≤ P.s1_0) && (1 ≤ P.s2_0) &&
  (P.U0_0 + 1 == P.s1_0) &&
  (2 * P.j1_0 + P.U1_0 == P.s1_0 + 1) &&
  (2 * P.j3_0 + P.U3_0 == P.s2_0 - 1) &&
  (2 * fam.R + P.U2_0 == P.s2_0 + 1) &&
  (P.e1_0 ≤ P.s1_0) && (P.s1_0 ≤ P.e1_0 + fam.R) &&
  (P.e2_0 ≤ P.s2_0) && (P.s2_0 ≤ P.e2_0 + fam.R) &&
  (P.j3_0 ≤ P.j1_0) && (P.j1_0 ≤ fam.R) &&
  (P.U1_0 ≤ P.U2_0) && (P.U2_0 ≤ P.U0_0) && (P.U0_0 ≤ P.U3_0) && (P.U3_0 ≤ 2 * fam.R) &&
  (fam.pairs.length == fam.R) &&
  allLt (2 * fam.R) (fun idx =>
    let ui := evenSlotU fam idx
    let sc := evenSlotS fam idx
    (ui < 2 * fam.R) &&
    inSGaps P.e1_0 P.s1_0 P.s1_0 (P.e1_0 + fam.R) P.e2_0 P.s2_0 P.s2_0 (P.e2_0 + fam.R) sc.1 sc.2) &&
  allPairsDistinct (2 * fam.R) (evenSlotU fam) &&
  allPairsDistinct (2 * fam.R) (evenSlotS fam)

/-- For quadruple `j < 4 * p + fam.R`, returns `(ua, ub)` assigned to `j`. -/
private def evenPairU (fam : EvenTailData) (p j : ℕ) : ℕ × ℕ :=
  let P := mkEvenParams fam
  if j < p then (P.U0_0 + 4 * p + 2 * j, P.U0_0 + 4 * p + 2 * j + 1)
  else if j < P.j3_0 + p then
    let pr := fam.pairs.getD (j - p) (0, 0)
    (evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p pr.1, evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p pr.2)
  else if j < P.j3_0 + 2 * p then
    let r := j - (P.j3_0 + p)
    (P.U3_0 + 6 * p + 2 * r, P.U3_0 + 6 * p + 2 * r + 1)
  else if j < P.j1_0 + 2 * p then
    let pr := fam.pairs.getD (j - 2 * p) (0, 0)
    (evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p pr.1, evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p pr.2)
  else if j < P.j1_0 + 3 * p then
    let r := j - (P.j1_0 + 2 * p)
    (P.U1_0 + 2 * r, P.U1_0 + 2 * r + 1)
  else if j < fam.R + 3 * p then
    let pr := fam.pairs.getD (j - 3 * p) (0, 0)
    (evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p pr.1, evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p pr.2)
  else
    let r := j - (fam.R + 3 * p)
    (P.U2_0 + 2 * p + 2 * r, P.U2_0 + 2 * p + 2 * r + 1)

private def evenSelU (fam : EvenTailData) (p j : ℕ) (b : Bool) : ℕ :=
  let pr := evenPairU fam p j
  if b then pr.2 else pr.1

/-- Explicit column map for the even-`h` parametric tail (`swapped = false` or `true`). -/
def evenTailCol (fam : EvenTailData) (p : ℕ) (swapped : Bool) (i : ℕ) : ℕ :=
  let pr := evenPairU fam p (i / 4)
  let ua := if swapped then pr.2 else pr.1
  let ub := if swapped then pr.1 else pr.2
  match i % 4 with
  | 0 => 2 * ua + 1
  | 1 => 2 * ub + 1
  | 2 => 2 * ua
  | _ => 2 * ub

/-- Unpacked proposition equivalent to `checkEvenTailData fam = true`. -/
private structure EvenChecked (fam : EvenTailData) : Prop where
  hd : 2 * (mkEvenParams fam).d = fam.h
  hdR : (mkEvenParams fam).d ≤ fam.R
  hs1_pos : 1 ≤ (mkEvenParams fam).s1_0
  hs2_pos : 1 ≤ (mkEvenParams fam).s2_0
  hU0 : (mkEvenParams fam).U0_0 + 1 = (mkEvenParams fam).s1_0
  hj1 : 2 * (mkEvenParams fam).j1_0 + (mkEvenParams fam).U1_0 = (mkEvenParams fam).s1_0 + 1
  hj3 : 2 * (mkEvenParams fam).j3_0 + (mkEvenParams fam).U3_0 = (mkEvenParams fam).s2_0 - 1
  hU2 : 2 * fam.R + (mkEvenParams fam).U2_0 = (mkEvenParams fam).s2_0 + 1
  he1s1 : (mkEvenParams fam).e1_0 ≤ (mkEvenParams fam).s1_0
  hs1e1 : (mkEvenParams fam).s1_0 ≤ (mkEvenParams fam).e1_0 + fam.R
  he2s2 : (mkEvenParams fam).e2_0 ≤ (mkEvenParams fam).s2_0
  hs2e2 : (mkEvenParams fam).s2_0 ≤ (mkEvenParams fam).e2_0 + fam.R
  hj31 : (mkEvenParams fam).j3_0 ≤ (mkEvenParams fam).j1_0
  hj1R : (mkEvenParams fam).j1_0 ≤ fam.R
  hU12 : (mkEvenParams fam).U1_0 ≤ (mkEvenParams fam).U2_0
  hU20 : (mkEvenParams fam).U2_0 ≤ (mkEvenParams fam).U0_0
  hU03 : (mkEvenParams fam).U0_0 ≤ (mkEvenParams fam).U3_0
  hU3R : (mkEvenParams fam).U3_0 ≤ 2 * fam.R
  hslot_u : ∀ idx < 2 * fam.R, evenSlotU fam idx < 2 * fam.R
  hslot_s : ∀ idx < 2 * fam.R,
    let P := mkEvenParams fam
    let sc := evenSlotS fam idx
    inSGaps P.e1_0 P.s1_0 P.s1_0 (P.e1_0 + fam.R) P.e2_0 P.s2_0 P.s2_0 (P.e2_0 + fam.R) sc.1 sc.2 = true
  hu_inj : ∀ i < 2 * fam.R, ∀ j < 2 * fam.R, evenSlotU fam i = evenSlotU fam j → i = j
  hs_inj : ∀ i < 2 * fam.R, ∀ j < 2 * fam.R, evenSlotS fam i = evenSlotS fam j → i = j

private lemma unpack_even {fam : EvenTailData} (h : checkEvenTailData fam = true) :
    EvenChecked fam := by
  unfold checkEvenTailData at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, _⟩, h20⟩, h21⟩, h22⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have := allLt_true h20 idx hidx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · intro idx hidx
    have := allLt_true h20 idx hidx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · intro i hi j hj heq; exact allPairsDistinct_inj h21 hi hj heq
  · intro i hi j hj heq; exact allPairsDistinct_inj h22 hi hj heq

/-- Classification of `(j, b)` into either one of the 4 parametric blocks or a leftover slot. -/
private lemma evenSelU_cases {fam : EvenTailData} (C : EvenChecked fam) (p j : ℕ) (b : Bool)
    (hj : j < 4 * p + fam.R) :
    let P := mkEvenParams fam
    let u := evenSelU fam p j b
    let bval := if b then 1 else 0
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j + bval ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * j + bval) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧
      u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + bval ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p)) + bval) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧
      u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + bval ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 2 + bval) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧
      u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + bval ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 2 + bval) ∨
    (∃ idx < 2 * fam.R,
      j = evalRJ P.j3_0 P.j1_0 p (idx / 2) ∧
      (b = (idx % 2 == 1)) ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (evenSlotU fam idx) ∧
      2 * j + u + 1 = (evenSlotS fam idx).1 + (evenSlotS fam idx).2 * p) := by
  have hd := C.hd; have hdR := C.hdR; have hs1p := C.hs1_pos; have hs2p := C.hs2_pos
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only
  unfold evenSelU evenPairU; dsimp only
  by_cases h1 : j < p
  · simp only [if_pos h1]; left; cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte] <;> exact ⟨by omega, by simp, by omega⟩
  · by_cases h2 : j < (mkEvenParams fam).j3_0 + p
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte]
      · refine ⟨2 * (j - p), by omega, ?_, by simp, ?_, ?_⟩
        · unfold evalRJ rjSlope; rw [show 2 * (j - p) / 2 = j - p by omega, if_pos (by omega)]; omega
        · unfold evenSlotU; simp only [show 2 * (j - p) / 2 = j - p by omega, show 2 * (j - p) % 2 = 0 by omega, ↓reduceIte]
        · unfold evenSlotS evenSlotU evalRU rjSlope
          simp only [show 2 * (j - p) / 2 = j - p by omega, show 2 * (j - p) % 2 = 0 by omega, ↓reduceIte,
            if_pos (show j - p < (mkEvenParams fam).j3_0 by omega)]; ring_nf; omega
      · refine ⟨2 * (j - p) + 1, by omega, ?_, by simp, ?_, ?_⟩
        · unfold evalRJ rjSlope; rw [show (2 * (j - p) + 1) / 2 = j - p by omega, if_pos (by omega)]; omega
        · unfold evenSlotU; simp only [show (2 * (j - p) + 1) / 2 = j - p by omega, show (2 * (j - p) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]
        · unfold evenSlotS evenSlotU evalRU rjSlope
          simp only [show (2 * (j - p) + 1) / 2 = j - p by omega, show (2 * (j - p) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
            if_pos (show j - p < (mkEvenParams fam).j3_0 by omega)]; ring_nf; omega
    · by_cases h3 : j < (mkEvenParams fam).j3_0 + 2 * p
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left
        cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte] <;> exact ⟨by omega, by omega, by simp, by omega⟩
      · by_cases h4 : j < (mkEvenParams fam).j1_0 + 2 * p
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte]
          · refine ⟨2 * (j - 2 * p), by omega, ?_, by simp, ?_, ?_⟩
            · unfold evalRJ rjSlope; rw [show 2 * (j - 2 * p) / 2 = j - 2 * p by omega, if_neg (by omega), if_pos (by omega)]; omega
            · unfold evenSlotU; simp only [show 2 * (j - 2 * p) / 2 = j - 2 * p by omega, show 2 * (j - 2 * p) % 2 = 0 by omega, ↓reduceIte]
            · unfold evenSlotS evenSlotU evalRU rjSlope
              simp only [show 2 * (j - 2 * p) / 2 = j - 2 * p by omega, show 2 * (j - 2 * p) % 2 = 0 by omega, ↓reduceIte,
                if_neg (show ¬ (j - 2 * p < (mkEvenParams fam).j3_0) by omega),
                if_pos (show j - 2 * p < (mkEvenParams fam).j1_0 by omega)]; ring_nf; omega
          · refine ⟨2 * (j - 2 * p) + 1, by omega, ?_, by simp, ?_, ?_⟩
            · unfold evalRJ rjSlope; rw [show (2 * (j - 2 * p) + 1) / 2 = j - 2 * p by omega, if_neg (by omega), if_pos (by omega)]; omega
            · unfold evenSlotU; simp only [show (2 * (j - 2 * p) + 1) / 2 = j - 2 * p by omega, show (2 * (j - 2 * p) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]
            · unfold evenSlotS evenSlotU evalRU rjSlope
              simp only [show (2 * (j - 2 * p) + 1) / 2 = j - 2 * p by omega, show (2 * (j - 2 * p) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
                if_neg (show ¬ (j - 2 * p < (mkEvenParams fam).j3_0) by omega),
                if_pos (show j - 2 * p < (mkEvenParams fam).j1_0 by omega)]; ring_nf; omega
        · by_cases h5 : j < (mkEvenParams fam).j1_0 + 3 * p
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left
            cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte] <;> exact ⟨by omega, by omega, by simp, by omega⟩
          · by_cases h6 : j < fam.R + 3 * p
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte]
              · refine ⟨2 * (j - 3 * p), by omega, ?_, by simp, ?_, ?_⟩
                · unfold evalRJ rjSlope; rw [show 2 * (j - 3 * p) / 2 = j - 3 * p by omega, if_neg (by omega), if_neg (by omega)]; omega
                · unfold evenSlotU; simp only [show 2 * (j - 3 * p) / 2 = j - 3 * p by omega, show 2 * (j - 3 * p) % 2 = 0 by omega, ↓reduceIte]
                · unfold evenSlotS evenSlotU evalRU rjSlope
                  simp only [show 2 * (j - 3 * p) / 2 = j - 3 * p by omega, show 2 * (j - 3 * p) % 2 = 0 by omega, ↓reduceIte,
                    if_neg (show ¬ (j - 3 * p < (mkEvenParams fam).j3_0) by omega),
                    if_neg (show ¬ (j - 3 * p < (mkEvenParams fam).j1_0) by omega)]; ring_nf; omega
              · refine ⟨2 * (j - 3 * p) + 1, by omega, ?_, by simp, ?_, ?_⟩
                · unfold evalRJ rjSlope; rw [show (2 * (j - 3 * p) + 1) / 2 = j - 3 * p by omega, if_neg (by omega), if_neg (by omega)]; omega
                · unfold evenSlotU; simp only [show (2 * (j - 3 * p) + 1) / 2 = j - 3 * p by omega, show (2 * (j - 3 * p) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]
                · unfold evenSlotS evenSlotU evalRU rjSlope
                  simp only [show (2 * (j - 3 * p) + 1) / 2 = j - 3 * p by omega, show (2 * (j - 3 * p) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
                    if_neg (show ¬ (j - 3 * p < (mkEvenParams fam).j3_0) by omega),
                    if_neg (show ¬ (j - 3 * p < (mkEvenParams fam).j1_0) by omega)]; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left
              cases b <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte] <;> exact ⟨by omega, by omega, by simp, by omega⟩

private lemma evenSelU_lt {fam : EvenTailData} (C : EvenChecked fam) (p j : ℕ) (b : Bool)
    (hj : j < 4 * p + fam.R) :
    evenSelU fam p j b < 2 * (4 * p + fam.R) := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases evenSelU_cases C p j b hj with h | h | h | h | ⟨idx, hidx, _, _, hu, _⟩
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega
  · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (C.hslot_u idx hidx)

private lemma evenSelU_inj {fam : EvenTailData} (C : EvenChecked fam) (p : ℕ)
    {j₁ j₂ : ℕ} {b₁ b₂ : Bool} (hj₁ : j₁ < 4 * p + fam.R) (hj₂ : j₂ < 4 * p + fam.R)
    (heq : evenSelU fam p j₁ b₁ = evenSelU fam p j₂ b₂) :
    j₁ = j₂ ∧ b₁ = b₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  have hc1 := evenSelU_cases C p j₁ b₁ hj₁
  have hc2 := evenSelU_cases C p j₂ b₂ hj₂
  rcases hc1 with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hb1e, hu1, _⟩ <;>
    rcases hc2 with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hb2e, hu2, _⟩
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 <;> omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 <;> omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 <;> omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 <;> omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 <;> omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 <;> omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 <;> omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) (C.hslot_u i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 <;> omega
  · have hru : evenSlotU fam i1 = evenSlotU fam i2 := evalRU_inj h12 h20 h03 (by rw [← hu1, ← hu2, heq])
    have hi : i1 = i2 := C.hu_inj i1 hi1 i2 hi2 hru
    subst hi; exact ⟨by rw [hj1e, hj2e], by rw [hb1e, hb2e]⟩

private lemma evenSelU_hs_band {fam : EvenTailData} (C : EvenChecked fam) (p j : ℕ) (b : Bool)
    (hj : j < 4 * p + fam.R) :
    let P := mkEvenParams fam
    let hs := 2 * j + evenSelU fam p j b + 1
    (P.e1_0 + 4 * p ≤ hs ∧ hs < P.e1_0 + fam.R + 8 * p) ∨
    (P.e2_0 + 8 * p ≤ hs ∧ hs < P.e2_0 + fam.R + 12 * p) := by
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hdR := C.hdR
  have hc1a2 : (mkEvenParams fam).e1_0 + fam.R ≤ (mkEvenParams fam).e2_0 := by
    unfold mkEvenParams; dsimp only; omega
  rcases evenSelU_cases C p j b hj with h | h | h | h | ⟨idx, hidx, _, _, _, hhs⟩
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> left <;> omega
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> right <;> omega
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> left <;> omega
  · cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> right <;> omega
  · have hgap := inSGaps_spec (q := p) ⟨he1s1, by omega, hs1e1, hc1a2, he2s2, by omega, hs2e2⟩ (C.hslot_s idx hidx)
    dsimp only at hgap
    rw [hhs]; exact hgap.1

private lemma evenSelU_hs_inj {fam : EvenTailData} (C : EvenChecked fam) (p : ℕ)
    {j₁ j₂ : ℕ} {b₁ b₂ : Bool} (hj₁ : j₁ < 4 * p + fam.R) (hj₂ : j₂ < 4 * p + fam.R)
    (heq : 2 * j₁ + evenSelU fam p j₁ b₁ + 1 = 2 * j₂ + evenSelU fam p j₂ b₂ + 1) :
    j₁ = j₂ ∧ b₁ = b₂ := by
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hdR := C.hdR
  have hc1a2 : (mkEvenParams fam).e1_0 + fam.R ≤ (mkEvenParams fam).e2_0 := by
    unfold mkEvenParams; dsimp only; omega
  have hord := (⟨he1s1, by omega, hs1e1, hc1a2, he2s2, by omega, hs2e2⟩ :
    (mkEvenParams fam).e1_0 ≤ (mkEvenParams fam).s1_0 ∧
    (mkEvenParams fam).s1_0 + 4 * p ≤ (mkEvenParams fam).s1_0 + 8 * p ∧
    (mkEvenParams fam).s1_0 ≤ (mkEvenParams fam).e1_0 + fam.R ∧
    (mkEvenParams fam).e1_0 + fam.R ≤ (mkEvenParams fam).e2_0 ∧
    (mkEvenParams fam).e2_0 ≤ (mkEvenParams fam).s2_0 ∧
    (mkEvenParams fam).s2_0 + 8 * p ≤ (mkEvenParams fam).s2_0 + 12 * p ∧
    (mkEvenParams fam).s2_0 ≤ (mkEvenParams fam).e2_0 + fam.R)
  have hc1 := evenSelU_cases C p j₁ b₁ hj₁
  have hc2 := evenSelU_cases C p j₂ b₂ hj₂
  rcases hc1 with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hb1e, _, hhs1⟩ <;>
    rcases hc2 with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hb2e, _, hhs2⟩
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hg := inSGaps_spec hord (C.hslot_s i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 hg <;> omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hg := inSGaps_spec hord (C.hslot_s i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 hg <;> omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hg := inSGaps_spec hord (C.hslot_s i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 hg <;> omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 <;> first | exact ⟨by omega, rfl⟩ | omega
  · have hg := inSGaps_spec hord (C.hslot_s i2 hi2)
    cases b₁ <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 hg <;> omega
  · have hg := inSGaps_spec hord (C.hslot_s i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 hg <;> omega
  · have hg := inSGaps_spec hord (C.hslot_s i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 hg <;> omega
  · have hg := inSGaps_spec hord (C.hslot_s i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 hg <;> omega
  · have hg := inSGaps_spec hord (C.hslot_s i1 hi1)
    cases b₂ <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 hg <;> omega
  · have hpair := inSGaps_inj hord (C.hslot_s i1 hi1) (C.hslot_s i2 hi2) (by rw [← hhs1, ← hhs2, heq])
    have heqs : evenSlotS fam i1 = evenSlotS fam i2 := Prod.ext hpair.1 hpair.2
    have hi : i1 = i2 := C.hs_inj i1 hi1 i2 hi2 heqs
    subst hi; exact ⟨by rw [hj1e, hj2e], by rw [hb1e, hb2e]⟩

private def evenRowSlot (swapped : Bool) (k : ℕ) : Bool :=
  let base := decide (k = 1 ∨ k = 3)
  xor base swapped

private lemma evenTailCol_eq_sel (fam : EvenTailData) (p : ℕ) (swapped : Bool) (i : ℕ) :
    let u := evenSelU fam p (i / 4) (evenRowSlot swapped (i % 4))
    evenTailCol fam p swapped i = if i % 4 < 2 then 2 * u + 1 else 2 * u := by
  unfold evenTailCol evenSelU evenRowSlot
  have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hk with h | h | h | h <;> cases swapped <;> simp [h]

private lemma evenTailSym_eq (fam : EvenTailData) (p : ℕ) (swapped : Bool) (i : ℕ) :
    let j := i / 4
    let u := evenSelU fam p j (evenRowSlot swapped (i % 4))
    let hs := 2 * j + u + 1
    (i : ℤ) + (evenTailCol fam p swapped i : ℤ) + tailDelta i (evenTailCol fam p swapped i) =
      if i % 4 = 0 ∨ i % 4 = 3 then ((2 * hs + 1 : ℕ) : ℤ) else ((2 * hs : ℕ) : ℤ) := by
  have hcol := evenTailCol_eq_sel fam p swapped i
  dsimp only at hcol ⊢
  rw [hcol]
  set j := i / 4
  set u := evenSelU fam p j (evenRowSlot swapped (i % 4))
  have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hk with h | h | h | h
  · have hi : i = 4 * j := by omega
    rw [if_pos (by omega), if_pos (Or.inl h), hi]; exact tailDelta_mod0_odd j u
  · have hi : i = 4 * j + 1 := by omega
    rw [if_pos (by omega), if_neg (by omega), hi]; exact tailDelta_mod1_odd j u
  · have hi : i = 4 * j + 2 := by omega
    rw [if_neg (by omega), if_neg (by omega), hi]; exact tailDelta_mod2_even j u
  · have hi : i = 4 * j + 3 := by omega
    rw [if_neg (by omega), if_pos (Or.inr h), hi]; exact tailDelta_mod3_even j u

/-- Construct a `ValidTail fam.h (4 * p + fam.R)` for any verified `EvenTailData` and any `p : ℕ`. -/
def evenTailValid (fam : EvenTailData) (hchk : checkEvenTailData fam = true) (p : ℕ)
    (swapped : Bool) : ValidTail fam.h (4 * p + fam.R) := by
  have C := unpack_even hchk
  refine {
    col := evenTailCol fam p swapped
    col_lt := fun i hi => by
      have hcol := evenTailCol_eq_sel fam p swapped i
      dsimp only at hcol; rw [hcol]
      have hu := evenSelU_lt C p (i / 4) (evenRowSlot swapped (i % 4)) (by omega)
      split_ifs <;> omega
    col_inj := fun i₁ hi₁ i₂ hi₂ heq => by
      have hc1 := evenTailCol_eq_sel fam p swapped i₁
      have hc2 := evenTailCol_eq_sel fam p swapped i₂
      dsimp only at hc1 hc2; rw [hc1, hc2] at heq
      have hpar : (i₁ % 4 < 2) ↔ (i₂ % 4 < 2) := by split_ifs at heq <;> omega
      have hu_eq : evenSelU fam p (i₁ / 4) (evenRowSlot swapped (i₁ % 4)) =
                   evenSelU fam p (i₂ / 4) (evenRowSlot swapped (i₂ % 4)) := by
        split_ifs at heq <;> omega
      have ⟨hj, hb⟩ := evenSelU_inj C p (by omega) (by omega) hu_eq
      have hk1 : i₁ % 4 = 0 ∨ i₁ % 4 = 1 ∨ i₁ % 4 = 2 ∨ i₁ % 4 = 3 := by omega
      have hk2 : i₂ % 4 = 0 ∨ i₂ % 4 = 1 ∨ i₂ % 4 = 2 ∨ i₂ % 4 = 3 := by omega
      unfold evenRowSlot at hb
      rcases hk1 with k1 | k1 | k1 | k1 <;> rcases hk2 with k2 | k2 | k2 | k2 <;>
        cases swapped <;> simp [k1, k2] at hb hpar <;> omega
    sym_band := fun i hi => by
      dsimp only; rw [evenTailSym_eq]
      have hb := evenSelU_hs_band C p (i / 4) (evenRowSlot swapped (i % 4)) (by omega)
      have hd := C.hd; have hdR := C.hdR
      have he1 : (mkEvenParams fam).e1_0 = fam.R - (mkEvenParams fam).d := rfl
      have he2 : (mkEvenParams fam).e2_0 = 2 * fam.R + (mkEvenParams fam).d := rfl
      dsimp only at hb; rw [he1, he2] at hb
      split_ifs <;> rcases hb with ⟨_, _⟩ | ⟨_, _⟩
      · left; omega
      · right; omega
      · left; omega
      · right; omega
    sym_inj := fun i₁ hi₁ i₂ hi₂ heq => by
      rw [evenTailSym_eq, evenTailSym_eq] at heq
      have hpar : (i₁ % 4 = 0 ∨ i₁ % 4 = 3) ↔ (i₂ % 4 = 0 ∨ i₂ % 4 = 3) := by
        split_ifs at heq <;> omega
      have hhs_eq :
          2 * (i₁ / 4) + evenSelU fam p (i₁ / 4) (evenRowSlot swapped (i₁ % 4)) + 1 =
          2 * (i₂ / 4) + evenSelU fam p (i₂ / 4) (evenRowSlot swapped (i₂ % 4)) + 1 := by
        split_ifs at heq <;> omega
      have ⟨hj, hb⟩ := evenSelU_hs_inj C p (by omega) (by omega) hhs_eq
      have hk1 : i₁ % 4 = 0 ∨ i₁ % 4 = 1 ∨ i₁ % 4 = 2 ∨ i₁ % 4 = 3 := by omega
      have hk2 : i₂ % 4 = 0 ∨ i₂ % 4 = 1 ∨ i₂ % 4 = 2 ∨ i₂ % 4 = 3 := by omega
      unfold evenRowSlot at hb
      rcases hk1 with k1 | k1 | k1 | k1 <;> rcases hk2 with k2 | k2 | k2 | k2 <;>
        cases swapped <;> simp [k1, k2] at hb hpar <;> omega
  }

/-- The unswapped and swapped tails of any verified `EvenTailData` are completely disjoint. -/
theorem evenTail_disjoint (fam : EvenTailData) (hchk : checkEvenTailData fam = true) (p : ℕ) :
    ∀ i < 4 * (4 * p + fam.R),
      (evenTailValid fam hchk p false).col i ≠ (evenTailValid fam hchk p true).col i := by
  have C := unpack_even hchk
  intro i hi heq
  change evenTailCol fam p false i = evenTailCol fam p true i at heq
  rw [evenTailCol_eq_sel, evenTailCol_eq_sel] at heq
  have hu : evenSelU fam p (i / 4) (evenRowSlot false (i % 4)) =
            evenSelU fam p (i / 4) (evenRowSlot true (i % 4)) := by
    split_ifs at heq <;> omega
  have ⟨_, hb⟩ := evenSelU_inj C p (by omega) (by omega) hu
  have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hk with k | k | k | k <;> simp [evenRowSlot, k] at hb

theorem checkEvenTail_0 : checkEvenTailData evenTail_0 = true := by decide
theorem checkEvenTail_4 : checkEvenTailData evenTail_4 = true := by decide
theorem checkEvenTail_8 : checkEvenTailData evenTail_8 = true := by decide
theorem checkEvenTail_12 : checkEvenTailData evenTail_12 = true := by decide

end GhafariWanless
