import Mathlib.Tactic
import Conjectures.GhafariWanlessTailBase

/-!
# Parametric Odd-`h` Tail Construction (Mod 16 Classes `2, 6, 10, 14`)

Constructs two completely disjoint `ValidTail fam.h (4 * (q + 1) + fam.R)` instances for every
`q : ℕ` (`p = q + 1 ≥ 1`) from any verified `OddTailData` witness, covering all
`n ≡ 2, 6, 10, 14 (mod 16)` from their respective thresholds (`114, 102, 122, 126`) to infinity.
-/

namespace GhafariWanless

open GhafariWanless.Data

private structure OddParams where
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

private def mkOddParams (fam : OddTailData) : OddParams :=
  let d := fam.h / 2
  let e1_0 := fam.R - d
  let e2_0 := 2 * fam.R + d + 1
  let s1_0 := e1_0 + fam.d1
  let s2_0 := e2_0 + fam.d2
  let U0_0 := s1_0 - 1
  let U1_0 := s1_0 % 2
  let j1_0 := (s1_0 - U1_0) / 2
  let U3_0 := 2 * fam.R - (s2_0 - 1) % 2
  let j3_0 := (s2_0 - 1 - U3_0) / 2
  let U2_0 := s2_0 - 2 * fam.R
  ⟨d, e1_0, e2_0, s1_0, s2_0, U0_0, U1_0, j1_0, U3_0, j3_0, U2_0⟩

private def s1EvSlotU (fam : OddTailData) (idx : ℕ) : ℕ :=
  let pr := fam.s1EvPairs.getD (idx / 2) (0, 0)
  if idx % 2 = 0 then pr.1 else pr.2

private def s2OdSlotU (fam : OddTailData) (idx : ℕ) : ℕ :=
  let pr := fam.s2OdPairs.getD (idx / 2) (0, 0)
  if idx % 2 = 0 then pr.1 else pr.2

private def ja1Lin (fam : OddTailData) (idx : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  if idx < fam.R then
    let cj := rjSlope P.j3_0 P.j1_0 idx
    (idx + cj, cj)
  else if idx = fam.R then (0, 0)
  else if idx = fam.R + 1 then (P.j1_0 + 2, 2)
  else if idx = fam.R + 2 then (fam.R + 3, 3)
  else (P.j3_0 + 1, 1)

private def ua1Lin (fam : OddTailData) (a : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  if a < fam.R then
    let ui := (fam.s1EvPairs.getD a (0, 0)).1
    let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
    (ui + cu, cu)
  else if a = fam.R then (P.U0_0 + 4, 6)
  else if a = fam.R + 1 then (P.U1_0, 2)
  else if a = fam.R + 2 then (P.U2_0 + 2, 4)
  else (P.U3_0 + 6, 8)

private def jb2Lin (fam : OddTailData) (m : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  if m < fam.R then
    let cj := rjSlope P.j3_0 P.j1_0 m
    (m + cj, cj)
  else if m = fam.R then (0, 1)
  else if m = fam.R + 1 then (P.j1_0 + 2, 3)
  else if m = fam.R + 2 then (fam.R + 3, 4)
  else (P.j3_0 + 1, 2)

private def ub2Lin (fam : OddTailData) (b : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  if b < fam.R then
    let ui := (fam.s2OdPairs.getD b (0, 0)).2
    let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
    (ui + cu, cu)
  else if b = fam.R then (P.U0_0 + 4, 4)
  else if b = fam.R + 1 then (P.U1_0, 0)
  else if b = fam.R + 2 then (P.U2_0 + 2, 2)
  else (P.U3_0 + 6, 6)

private def s1EvSlotS (fam : OddTailData) (idx : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  let ji := idx / 2
  let ui := s1EvSlotU fam idx
  let cj := rjSlope P.j3_0 P.j1_0 ji
  let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
  let off := if idx % 2 = 0 then 1 else 2
  (2 * (ji + cj) + (ui + cu) + off, 2 * cj + cu)

private def s1OdSlotS (fam : OddTailData) (idx : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  if idx < fam.R + 4 then
    let j := ja1Lin fam idx
    let u := ua1Lin fam (fam.s1OdA.getD idx 0)
    (2 * j.1 + u.1 + 1, 2 * j.2 + u.2)
  else
    let ji := idx - (fam.R + 4)
    let j := ja1Lin fam ji
    let b := fam.s1OdB.getD ji 0
    let ui := (fam.s1EvPairs.getD b (0, 0)).2
    let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
    (2 * j.1 + (ui + cu), 2 * j.2 + cu)

private def s2OdSlotS (fam : OddTailData) (idx : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  let ji := idx / 2
  let ui := s2OdSlotU fam idx
  let cj := rjSlope P.j3_0 P.j1_0 ji
  let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
  let off := if idx % 2 = 0 then 1 else 0
  (2 * (ji + cj) + (ui + cu) + off, 2 * cj + cu)

private def s2EvSlotS (fam : OddTailData) (idx : ℕ) : ℕ × ℕ :=
  let P := mkOddParams fam
  if idx < fam.R then
    let j := jb2Lin fam idx
    let a := fam.s2EvA.getD idx 0
    let ui := (fam.s2OdPairs.getD a (0, 0)).1
    let cu := ruSlope P.U1_0 P.U2_0 P.U0_0 P.U3_0 ui
    (2 * j.1 + (ui + cu) + 1, 2 * j.2 + cu)
  else
    let m := idx - fam.R
    let j := jb2Lin fam m
    let u := ub2Lin fam (fam.s2EvB.getD m 0)
    (2 * j.1 + u.1 + 2, 2 * j.2 + u.2)

/-- Complete decidable checker for an `OddTailData` family (proves validity for ALL `q : ℕ`, `p = q + 1`). -/
def checkOddTailData (fam : OddTailData) : Bool :=
  let P := mkOddParams fam
  (2 * P.d + 1 == fam.h) && (P.d + 1 ≤ fam.R) && (1 ≤ P.s1_0) && (1 ≤ P.s2_0) &&
  (P.U0_0 + 1 == P.s1_0) &&
  (2 * P.j1_0 + P.U1_0 == P.s1_0) &&
  (2 * P.j3_0 + P.U3_0 == P.s2_0 - 1) &&
  (2 * fam.R + P.U2_0 == P.s2_0) &&
  (P.e1_0 ≤ P.s1_0) && (P.s1_0 ≤ P.e1_0 + fam.R) &&
  (P.e2_0 ≤ P.s2_0) && (P.s2_0 ≤ P.e2_0 + fam.R) &&
  (P.j3_0 ≤ P.j1_0) && (P.j1_0 ≤ fam.R) &&
  (P.U1_0 ≤ P.U2_0) && (P.U2_0 ≤ P.U0_0) && (P.U0_0 ≤ P.U3_0) && (P.U3_0 ≤ 2 * fam.R) &&
  allLt (2 * fam.R) (fun idx =>
    let sc1 := s1EvSlotS fam idx
    let sc2 := s2OdSlotS fam idx
    (s1EvSlotU fam idx < 2 * fam.R) && (s2OdSlotU fam idx < 2 * fam.R) &&
    inSGaps (P.e1_0 + 4) (P.s1_0 + 4) (P.s1_0 + 8) (P.e1_0 + fam.R + 8)
            (P.e2_0 + 8) (P.s2_0 + 8) (P.s2_0 + 12) (P.e2_0 + fam.R + 12) sc1.1 sc1.2 &&
    inSGaps (P.e1_0 + 3) (P.s1_0 + 3) (P.s1_0 + 7) (P.e1_0 + fam.R + 7)
            (P.e2_0 + 7) (P.s2_0 + 7) (P.s2_0 + 11) (P.e2_0 + fam.R + 11) sc2.1 sc2.2) &&
  allPairsDistinct (2 * fam.R) (s1EvSlotU fam) &&
  allPairsDistinct (2 * fam.R) (s2OdSlotU fam) &&
  allPairsDistinct (2 * fam.R) (s1EvSlotS fam) &&
  allPairsDistinct (2 * fam.R) (s2OdSlotS fam) &&
  allLt (fam.R + 4) (fun i => fam.s1OdA.getD i 0 < fam.R + 4 && fam.s2EvB.getD i 0 < fam.R + 4) &&
  allLt fam.R (fun i => fam.s1OdB.getD i 0 < fam.R && fam.s2EvA.getD i 0 < fam.R) &&
  allPairsDistinct (fam.R + 4) (fun i => fam.s1OdA.getD i 0) &&
  allPairsDistinct fam.R (fun i => fam.s1OdB.getD i 0) &&
  allPairsDistinct fam.R (fun i => fam.s2EvA.getD i 0) &&
  allPairsDistinct (fam.R + 4) (fun i => fam.s2EvB.getD i 0) &&
  allLt (2 * fam.R + 4) (fun idx =>
    let sc1 := s1OdSlotS fam idx
    let sc2 := s2EvSlotS fam idx
    inSGaps (P.e1_0 + 3) (P.s1_0 + 4) (P.s1_0 + 6) (P.e1_0 + fam.R + 7)
            (P.e2_0 + 7) (P.s2_0 + 8) (P.s2_0 + 10) (P.e2_0 + fam.R + 11) sc1.1 sc1.2 &&
    inSGaps (P.e1_0 + 4) (P.s1_0 + 5) (P.s1_0 + 7) (P.e1_0 + fam.R + 8)
            (P.e2_0 + 8) (P.s2_0 + 9) (P.s2_0 + 11) (P.e2_0 + fam.R + 12) sc2.1 sc2.2) &&
  allPairsDistinct (2 * fam.R + 4) (s1OdSlotS fam) &&
  allPairsDistinct (2 * fam.R + 4) (s2EvSlotS fam) &&
  allLt fam.R (fun ji =>
    let a := fam.s1OdA.getD ji 0
    let b := fam.s2EvB.getD ji 0
    (fam.R ≤ a || (fam.s1EvPairs.getD a (0, 0)).1 != (fam.s2OdPairs.getD ji (0, 0)).1) &&
    ((fam.s1EvPairs.getD (fam.s1OdB.getD ji 0) (0, 0)).2 != (fam.s2OdPairs.getD ji (0, 0)).2) &&
    ((fam.s1EvPairs.getD ji (0, 0)).1 != (fam.s2OdPairs.getD (fam.s2EvA.getD ji 0) (0, 0)).1) &&
    (fam.R ≤ b || (fam.s1EvPairs.getD ji (0, 0)).2 != (fam.s2OdPairs.getD b (0, 0)).2))

private def evalUA1 (fam : OddTailData) (q a : ℕ) : ℕ :=
  let bc := ua1Lin fam a
  bc.1 + bc.2 * q

private def evalUB2 (fam : OddTailData) (q b : ℕ) : ℕ :=
  let bc := ub2Lin fam b
  bc.1 + bc.2 * q

/-- Column `u` for Sol 1, row class `k ∈ {0, 1, 2, 3}` at quadruple `j < 4*(q+1) + R`. -/
private def odd1U0 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j = 0 then evalUA1 fam q (fam.s1OdA.getD fam.R 0)
  else if j < p then P.U0_0 + 4 * p + 2 * (j - 1)
  else if j < P.j3_0 + p then evalUA1 fam q (fam.s1OdA.getD (j - p) 0)
  else if j = P.j3_0 + p then evalUA1 fam q (fam.s1OdA.getD (fam.R + 3) 0)
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p) - 1)
  else if j < P.j1_0 + 2 * p then evalUA1 fam q (fam.s1OdA.getD (j - 2 * p) 0)
  else if j = P.j1_0 + 2 * p then evalUA1 fam q (fam.s1OdA.getD (fam.R + 1) 0)
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p) - 1)
  else if j < fam.R + 3 * p then evalUA1 fam q (fam.s1OdA.getD (j - 3 * p) 0)
  else if j = fam.R + 3 * p then evalUA1 fam q (fam.s1OdA.getD (fam.R + 2) 0)
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p) - 1)

private def odd1U1 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < p then P.U0_0 + 4 * p + 2 * j + 1
  else if j < P.j3_0 + p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (fam.s1OdB.getD (j - p) 0) (0, 0)).2
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1
  else if j < P.j1_0 + 2 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (fam.s1OdB.getD (j - 2 * p) 0) (0, 0)).2
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1
  else if j < fam.R + 3 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (fam.s1OdB.getD (j - 3 * p) 0) (0, 0)).2
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1

private def odd1U2 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < p then P.U0_0 + 4 * p + 2 * j
  else if j < P.j3_0 + p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (j - p) (0, 0)).1
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p))
  else if j < P.j1_0 + 2 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (j - 2 * p) (0, 0)).1
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p))
  else if j < fam.R + 3 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (j - 3 * p) (0, 0)).1
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p))

private def odd1U3 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < p then P.U0_0 + 4 * p + 2 * j + 1
  else if j < P.j3_0 + p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (j - p) (0, 0)).2
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1
  else if j < P.j1_0 + 2 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (j - 2 * p) (0, 0)).2
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1
  else if j < fam.R + 3 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (j - 3 * p) (0, 0)).2
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1

/-- Column `u` for Sol 2, row class `k ∈ {0, 1, 2, 3}` at quadruple `j < 4*(q+1) + R`. -/
private def odd2U0 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < p then P.U0_0 + 4 * p + 2 * j + 1
  else if j < P.j3_0 + p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (j - p) (0, 0)).1
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1
  else if j < P.j1_0 + 2 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (j - 2 * p) (0, 0)).1
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1
  else if j < fam.R + 3 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (j - 3 * p) (0, 0)).1
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1

private def odd2U1 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < p then P.U0_0 + 4 * p + 2 * j
  else if j < P.j3_0 + p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (j - p) (0, 0)).2
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p))
  else if j < P.j1_0 + 2 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (j - 2 * p) (0, 0)).2
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p))
  else if j < fam.R + 3 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (j - 3 * p) (0, 0)).2
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p))

private def odd2U2 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < p then P.U0_0 + 4 * p + 2 * j + 1
  else if j < P.j3_0 + p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (fam.s2EvA.getD (j - p) 0) (0, 0)).1
  else if j < P.j3_0 + 2 * p then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1
  else if j < P.j1_0 + 2 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (fam.s2EvA.getD (j - 2 * p) 0) (0, 0)).1
  else if j < P.j1_0 + 3 * p then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1
  else if j < fam.R + 3 * p then
    evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (fam.s2EvA.getD (j - 3 * p) 0) (0, 0)).1
  else P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1

private def odd2U3 (fam : OddTailData) (q j : ℕ) : ℕ :=
  let P := mkOddParams fam; let p := q + 1
  if j < q then P.U0_0 + 4 * p + 2 * (j + 1)
  else if j = q then evalUB2 fam q (fam.s2EvB.getD fam.R 0)
  else if j < P.j3_0 + p then evalUB2 fam q (fam.s2EvB.getD (j - p) 0)
  else if j < P.j3_0 + 2 * p - 1 then P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p) + 1)
  else if j = P.j3_0 + 2 * p - 1 then evalUB2 fam q (fam.s2EvB.getD (fam.R + 3) 0)
  else if j < P.j1_0 + 2 * p then evalUB2 fam q (fam.s2EvB.getD (j - 2 * p) 0)
  else if j < P.j1_0 + 3 * p - 1 then P.U1_0 + 2 * (j - (P.j1_0 + 2 * p) + 1)
  else if j = P.j1_0 + 3 * p - 1 then evalUB2 fam q (fam.s2EvB.getD (fam.R + 1) 0)
  else if j < fam.R + 3 * p then evalUB2 fam q (fam.s2EvB.getD (j - 3 * p) 0)
  else if j < fam.R + 4 * p - 1 then P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p) + 1)
  else evalUB2 fam q (fam.s2EvB.getD (fam.R + 2) 0)

def oddTail1Col (fam : OddTailData) (q i : ℕ) : ℕ :=
  match i % 4 with
  | 0 => 2 * odd1U0 fam q (i / 4) + 1
  | 1 => 2 * odd1U1 fam q (i / 4)
  | 2 => 2 * odd1U2 fam q (i / 4)
  | _ => 2 * odd1U3 fam q (i / 4) + 1

def oddTail2Col (fam : OddTailData) (q i : ℕ) : ℕ :=
  match i % 4 with
  | 0 => 2 * odd2U0 fam q (i / 4) + 1
  | 1 => 2 * odd2U1 fam q (i / 4)
  | 2 => 2 * odd2U2 fam q (i / 4)
  | _ => 2 * odd2U3 fam q (i / 4) + 1

private structure OddChecked (fam : OddTailData) : Prop where
  hd : 2 * (mkOddParams fam).d + 1 = fam.h
  hdR : (mkOddParams fam).d + 1 ≤ fam.R
  hs1_pos : 1 ≤ (mkOddParams fam).s1_0
  hs2_pos : 1 ≤ (mkOddParams fam).s2_0
  hU0 : (mkOddParams fam).U0_0 + 1 = (mkOddParams fam).s1_0
  hj1 : 2 * (mkOddParams fam).j1_0 + (mkOddParams fam).U1_0 = (mkOddParams fam).s1_0
  hj3 : 2 * (mkOddParams fam).j3_0 + (mkOddParams fam).U3_0 = (mkOddParams fam).s2_0 - 1
  hU2 : 2 * fam.R + (mkOddParams fam).U2_0 = (mkOddParams fam).s2_0
  he1s1 : (mkOddParams fam).e1_0 ≤ (mkOddParams fam).s1_0
  hs1e1 : (mkOddParams fam).s1_0 ≤ (mkOddParams fam).e1_0 + fam.R
  he2s2 : (mkOddParams fam).e2_0 ≤ (mkOddParams fam).s2_0
  hs2e2 : (mkOddParams fam).s2_0 ≤ (mkOddParams fam).e2_0 + fam.R
  hj31 : (mkOddParams fam).j3_0 ≤ (mkOddParams fam).j1_0
  hj1R : (mkOddParams fam).j1_0 ≤ fam.R
  hU12 : (mkOddParams fam).U1_0 ≤ (mkOddParams fam).U2_0
  hU20 : (mkOddParams fam).U2_0 ≤ (mkOddParams fam).U0_0
  hU03 : (mkOddParams fam).U0_0 ≤ (mkOddParams fam).U3_0
  hU3R : (mkOddParams fam).U3_0 ≤ 2 * fam.R
  hs1ev_u : ∀ idx < 2 * fam.R, s1EvSlotU fam idx < 2 * fam.R
  hs2od_u : ∀ idx < 2 * fam.R, s2OdSlotU fam idx < 2 * fam.R
  hs1ev_g : ∀ idx < 2 * fam.R,
    let P := mkOddParams fam; let sc := s1EvSlotS fam idx
    inSGaps (P.e1_0 + 4) (P.s1_0 + 4) (P.s1_0 + 8) (P.e1_0 + fam.R + 8)
            (P.e2_0 + 8) (P.s2_0 + 8) (P.s2_0 + 12) (P.e2_0 + fam.R + 12) sc.1 sc.2 = true
  hs2od_g : ∀ idx < 2 * fam.R,
    let P := mkOddParams fam; let sc := s2OdSlotS fam idx
    inSGaps (P.e1_0 + 3) (P.s1_0 + 3) (P.s1_0 + 7) (P.e1_0 + fam.R + 7)
            (P.e2_0 + 7) (P.s2_0 + 7) (P.s2_0 + 11) (P.e2_0 + fam.R + 11) sc.1 sc.2 = true
  hs1ev_uinj : ∀ i < 2 * fam.R, ∀ j < 2 * fam.R, s1EvSlotU fam i = s1EvSlotU fam j → i = j
  hs2od_uinj : ∀ i < 2 * fam.R, ∀ j < 2 * fam.R, s2OdSlotU fam i = s2OdSlotU fam j → i = j
  hs1ev_sinj : ∀ i < 2 * fam.R, ∀ j < 2 * fam.R, s1EvSlotS fam i = s1EvSlotS fam j → i = j
  hs2od_sinj : ∀ i < 2 * fam.R, ∀ j < 2 * fam.R, s2OdSlotS fam i = s2OdSlotS fam j → i = j
  hs1oda_lt : ∀ i < fam.R + 4, fam.s1OdA.getD i 0 < fam.R + 4
  hs2evb_lt : ∀ i < fam.R + 4, fam.s2EvB.getD i 0 < fam.R + 4
  hs1odb_lt : ∀ i < fam.R, fam.s1OdB.getD i 0 < fam.R
  hs2eva_lt : ∀ i < fam.R, fam.s2EvA.getD i 0 < fam.R
  hs1oda_inj : ∀ i < fam.R + 4, ∀ j < fam.R + 4, fam.s1OdA.getD i 0 = fam.s1OdA.getD j 0 → i = j
  hs1odb_inj : ∀ i < fam.R, ∀ j < fam.R, fam.s1OdB.getD i 0 = fam.s1OdB.getD j 0 → i = j
  hs2eva_inj : ∀ i < fam.R, ∀ j < fam.R, fam.s2EvA.getD i 0 = fam.s2EvA.getD j 0 → i = j
  hs2evb_inj : ∀ i < fam.R + 4, ∀ j < fam.R + 4, fam.s2EvB.getD i 0 = fam.s2EvB.getD j 0 → i = j
  hs1od_g : ∀ idx < 2 * fam.R + 4,
    let P := mkOddParams fam; let sc := s1OdSlotS fam idx
    inSGaps (P.e1_0 + 3) (P.s1_0 + 4) (P.s1_0 + 6) (P.e1_0 + fam.R + 7)
            (P.e2_0 + 7) (P.s2_0 + 8) (P.s2_0 + 10) (P.e2_0 + fam.R + 11) sc.1 sc.2 = true
  hs2ev_g : ∀ idx < 2 * fam.R + 4,
    let P := mkOddParams fam; let sc := s2EvSlotS fam idx
    inSGaps (P.e1_0 + 4) (P.s1_0 + 5) (P.s1_0 + 7) (P.e1_0 + fam.R + 8)
            (P.e2_0 + 8) (P.s2_0 + 9) (P.s2_0 + 11) (P.e2_0 + fam.R + 12) sc.1 sc.2 = true
  hs1od_sinj : ∀ i < 2 * fam.R + 4, ∀ j < 2 * fam.R + 4, s1OdSlotS fam i = s1OdSlotS fam j → i = j
  hs2ev_sinj : ∀ i < 2 * fam.R + 4, ∀ j < 2 * fam.R + 4, s2EvSlotS fam i = s2EvSlotS fam j → i = j
  hdisj_0 : ∀ ji < fam.R, fam.s1OdA.getD ji 0 < fam.R →
    (fam.s1EvPairs.getD (fam.s1OdA.getD ji 0) (0, 0)).1 ≠ (fam.s2OdPairs.getD ji (0, 0)).1
  hdisj_1 : ∀ ji < fam.R,
    (fam.s1EvPairs.getD (fam.s1OdB.getD ji 0) (0, 0)).2 ≠ (fam.s2OdPairs.getD ji (0, 0)).2
  hdisj_2 : ∀ ji < fam.R,
    (fam.s1EvPairs.getD ji (0, 0)).1 ≠ (fam.s2OdPairs.getD (fam.s2EvA.getD ji 0) (0, 0)).1
  hdisj_3 : ∀ ji < fam.R, fam.s2EvB.getD ji 0 < fam.R →
    (fam.s1EvPairs.getD ji (0, 0)).2 ≠ (fam.s2OdPairs.getD (fam.s2EvB.getD ji 0) (0, 0)).2

private lemma unpack_odd {fam : OddTailData} (h : checkOddTailData fam = true) :
    OddChecked fam := by
  unfold checkOddTailData at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩,
    h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have := allLt_true h19 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.1.1
  · intro i hi; have := allLt_true h19 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.1.2
  · intro i hi; have := allLt_true h19 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.2
  · intro i hi; have := allLt_true h19 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  · intro i hi j hj e; exact allPairsDistinct_inj h20 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h21 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h22 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h23 hi hj e
  · intro i hi; have := allLt_true h24 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  · intro i hi; have := allLt_true h24 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  · intro i hi; have := allLt_true h25 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  · intro i hi; have := allLt_true h25 i hi; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  · intro i hi j hj e; exact allPairsDistinct_inj h26 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h27 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h28 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h29 hi hj e
  · intro i hi; have := allLt_true h30 i hi; simp only [Bool.and_eq_true] at this; exact this.1
  · intro i hi; have := allLt_true h30 i hi; simp only [Bool.and_eq_true] at this; exact this.2
  · intro i hi j hj e; exact allPairsDistinct_inj h31 hi hj e
  · intro i hi j hj e; exact allPairsDistinct_inj h32 hi hj e
  · intro ji hji ha
    have := allLt_true h33 ji hji
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at this
    rcases this.1.1.1 with hge | hne
    · omega
    · exact hne
  · intro ji hji
    have := allLt_true h33 ji hji
    simp only [Bool.and_eq_true, bne_iff_ne] at this; exact this.1.1.2
  · intro ji hji
    have := allLt_true h33 ji hji
    simp only [Bool.and_eq_true, bne_iff_ne] at this; exact this.1.2
  · intro ji hji hb
    have := allLt_true h33 ji hji
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at this
    rcases this.2 with hge | hne
    · omega
    · exact hne

/-- Helper: `s1EvPairs` / `s2OdPairs` bounds & injectivity unpacked from `s1EvSlotU` / `s2OdSlotU`. -/
private lemma s1Ev_fst_lt {fam : OddTailData} (C : OddChecked fam) {a : ℕ} (ha : a < fam.R) :
    (fam.s1EvPairs.getD a (0, 0)).1 < 2 * fam.R := by
  have := C.hs1ev_u (2 * a) (by omega)
  unfold s1EvSlotU at this; simp [show 2 * a / 2 = a by omega] at this; exact this

private lemma s1Ev_snd_lt {fam : OddTailData} (C : OddChecked fam) {a : ℕ} (ha : a < fam.R) :
    (fam.s1EvPairs.getD a (0, 0)).2 < 2 * fam.R := by
  have := C.hs1ev_u (2 * a + 1) (by omega)
  unfold s1EvSlotU at this
  simp [show (2 * a + 1) / 2 = a by omega, show (2 * a + 1) % 2 = 1 by omega] at this
  exact this

private lemma s1Ev_fst_inj {fam : OddTailData} (C : OddChecked fam) {a b : ℕ}
    (ha : a < fam.R) (hb : b < fam.R)
    (heq : (fam.s1EvPairs.getD a (0, 0)).1 = (fam.s1EvPairs.getD b (0, 0)).1) : a = b := by
  have h := C.hs1ev_uinj (2 * a) (by omega) (2 * b) (by omega) (by
    unfold s1EvSlotU
    simp only [show 2 * a / 2 = a by omega, show 2 * b / 2 = b by omega,
      show 2 * a % 2 = 0 by omega, show 2 * b % 2 = 0 by omega, ↓reduceIte, heq])
  omega

private lemma s1Ev_snd_inj {fam : OddTailData} (C : OddChecked fam) {a b : ℕ}
    (ha : a < fam.R) (hb : b < fam.R)
    (heq : (fam.s1EvPairs.getD a (0, 0)).2 = (fam.s1EvPairs.getD b (0, 0)).2) : a = b := by
  have h := C.hs1ev_uinj (2 * a + 1) (by omega) (2 * b + 1) (by omega) (by
    unfold s1EvSlotU
    simp only [show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega,
      show (2 * a + 1) % 2 = 1 by omega, show (2 * b + 1) % 2 = 1 by omega,
      Nat.one_ne_zero, ↓reduceIte, heq])
  omega

private lemma s1Ev_fst_ne_snd {fam : OddTailData} (C : OddChecked fam) {a b : ℕ}
    (ha : a < fam.R) (hb : b < fam.R) :
    (fam.s1EvPairs.getD a (0, 0)).1 ≠ (fam.s1EvPairs.getD b (0, 0)).2 := by
  intro heq
  have h := C.hs1ev_uinj (2 * a) (by omega) (2 * b + 1) (by omega) (by
    unfold s1EvSlotU
    simp only [show 2 * a / 2 = a by omega, show (2 * b + 1) / 2 = b by omega,
      show 2 * a % 2 = 0 by omega, show (2 * b + 1) % 2 = 1 by omega,
      Nat.one_ne_zero, ↓reduceIte, heq])
  omega

private lemma s2Od_fst_lt {fam : OddTailData} (C : OddChecked fam) {a : ℕ} (ha : a < fam.R) :
    (fam.s2OdPairs.getD a (0, 0)).1 < 2 * fam.R := by
  have := C.hs2od_u (2 * a) (by omega)
  unfold s2OdSlotU at this; simp only [show 2 * a / 2 = a by omega, show 2 * a % 2 = 0 by omega, ↓reduceIte] at this; exact this

private lemma s2Od_snd_lt {fam : OddTailData} (C : OddChecked fam) {a : ℕ} (ha : a < fam.R) :
    (fam.s2OdPairs.getD a (0, 0)).2 < 2 * fam.R := by
  have := C.hs2od_u (2 * a + 1) (by omega)
  unfold s2OdSlotU at this
  simp only [show (2 * a + 1) / 2 = a by omega, show (2 * a + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte] at this
  exact this

private lemma s2Od_fst_inj {fam : OddTailData} (C : OddChecked fam) {a b : ℕ}
    (ha : a < fam.R) (hb : b < fam.R)
    (heq : (fam.s2OdPairs.getD a (0, 0)).1 = (fam.s2OdPairs.getD b (0, 0)).1) : a = b := by
  have h := C.hs2od_uinj (2 * a) (by omega) (2 * b) (by omega) (by
    unfold s2OdSlotU
    simp only [show 2 * a / 2 = a by omega, show 2 * b / 2 = b by omega,
      show 2 * a % 2 = 0 by omega, show 2 * b % 2 = 0 by omega, ↓reduceIte, heq])
  omega

private lemma s2Od_snd_inj {fam : OddTailData} (C : OddChecked fam) {a b : ℕ}
    (ha : a < fam.R) (hb : b < fam.R)
    (heq : (fam.s2OdPairs.getD a (0, 0)).2 = (fam.s2OdPairs.getD b (0, 0)).2) : a = b := by
  have h := C.hs2od_uinj (2 * a + 1) (by omega) (2 * b + 1) (by omega) (by
    unfold s2OdSlotU
    simp only [show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega,
      show (2 * a + 1) % 2 = 1 by omega, show (2 * b + 1) % 2 = 1 by omega,
      Nat.one_ne_zero, ↓reduceIte, heq])
  omega

private lemma s2Od_fst_ne_snd {fam : OddTailData} (C : OddChecked fam) {a b : ℕ}
    (ha : a < fam.R) (hb : b < fam.R) :
    (fam.s2OdPairs.getD a (0, 0)).1 ≠ (fam.s2OdPairs.getD b (0, 0)).2 := by
  intro heq
  have h := C.hs2od_uinj (2 * a) (by omega) (2 * b + 1) (by omega) (by
    unfold s2OdSlotU
    simp only [show 2 * a / 2 = a by omega, show (2 * b + 1) / 2 = b by omega,
      show 2 * a % 2 = 0 by omega, show (2 * b + 1) % 2 = 1 by omega,
      Nat.one_ne_zero, ↓reduceIte, heq])
  omega

/-- Classification of `u` values into the 6 disjoint families: 4 u-blocks (with parity), `ru`, and bounds. -/
private def inUBlockEven (P : OddParams) (p u : ℕ) : Prop :=
  (P.U1_0 ≤ u ∧ u < P.U1_0 + 2 * p ∧ (u - P.U1_0) % 2 = 0) ∨
  (P.U2_0 + 2 * p ≤ u ∧ u < P.U2_0 + 4 * p ∧ (u - (P.U2_0 + 2 * p)) % 2 = 0) ∨
  (P.U0_0 + 4 * p ≤ u ∧ u < P.U0_0 + 6 * p ∧ (u - (P.U0_0 + 4 * p)) % 2 = 0) ∨
  (P.U3_0 + 6 * p ≤ u ∧ u < P.U3_0 + 8 * p ∧ (u - (P.U3_0 + 6 * p)) % 2 = 0)

private def inUBlockOdd (P : OddParams) (p u : ℕ) : Prop :=
  (P.U1_0 ≤ u ∧ u < P.U1_0 + 2 * p ∧ (u - P.U1_0) % 2 = 1) ∨
  (P.U2_0 + 2 * p ≤ u ∧ u < P.U2_0 + 4 * p ∧ (u - (P.U2_0 + 2 * p)) % 2 = 1) ∨
  (P.U0_0 + 4 * p ≤ u ∧ u < P.U0_0 + 6 * p ∧ (u - (P.U0_0 + 4 * p)) % 2 = 1) ∨
  (P.U3_0 + 6 * p ≤ u ∧ u < P.U3_0 + 8 * p ∧ (u - (P.U3_0 + 6 * p)) % 2 = 1)

private lemma inUBlockEven_not_odd {P : OddParams} {p u : ℕ}
    (h12 : P.U1_0 ≤ P.U2_0) (h20 : P.U2_0 ≤ P.U0_0) (h03 : P.U0_0 ≤ P.U3_0)
    (he : inUBlockEven P p u) (ho : inUBlockOdd P p u) : False := by
  unfold inUBlockEven at he; unfold inUBlockOdd at ho
  rcases he with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases ho with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

private lemma evalRU_not_even_block {P : OddParams} {R p ui : ℕ}
    (h12 : P.U1_0 ≤ P.U2_0) (h20 : P.U2_0 ≤ P.U0_0) (h03 : P.U0_0 ≤ P.U3_0) (h3R : P.U3_0 ≤ 2 * R)
    (hui : ui < 2 * R) (he : inUBlockEven P p (evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p ui)) : False := by
  have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) hui
  unfold inUBlockEven at he
  rcases he with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

private lemma evalRU_not_odd_block {P : OddParams} {R p ui : ℕ}
    (h12 : P.U1_0 ≤ P.U2_0) (h20 : P.U2_0 ≤ P.U0_0) (h03 : P.U0_0 ≤ P.U3_0) (h3R : P.U3_0 ≤ 2 * R)
    (hui : ui < 2 * R) (ho : inUBlockOdd P p (evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p ui)) : False := by
  have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := p) hui
  unfold inUBlockOdd at ho
  rcases ho with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- Exact formula & properties of `evalUA1` (`a < R + 4`). -/
private lemma evalUA1_spec {fam : OddTailData} (C : OddChecked fam) (q a : ℕ) (ha : a < fam.R + 4) :
    let P := mkOddParams fam; let p := q + 1; let u := evalUA1 fam q a
    u < 2 * (4 * p + fam.R) ∧
    (a < fam.R → u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD a (0, 0)).1) ∧
    (a = fam.R → u = P.U0_0 + 4 * p + 2 * q) ∧
    (a = fam.R + 1 → u = P.U1_0 + 2 * q) ∧
    (a = fam.R + 2 → u = P.U2_0 + 2 * p + 2 * q) ∧
    (a = fam.R + 3 → u = P.U3_0 + 6 * p + 2 * q) := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  unfold evalUA1 ua1Lin; dsimp only
  split_ifs with h0 h1 h2 h3
  · have hlt := s1Ev_fst_lt C h0
    have heq : (fam.s1EvPairs.getD a (0, 0)).1 +
        ruSlope (mkOddParams fam).U1_0 (mkOddParams fam).U2_0 (mkOddParams fam).U0_0 (mkOddParams fam).U3_0
          (fam.s1EvPairs.getD a (0, 0)).1 +
        ruSlope (mkOddParams fam).U1_0 (mkOddParams fam).U2_0 (mkOddParams fam).U0_0 (mkOddParams fam).U3_0
          (fam.s1EvPairs.getD a (0, 0)).1 * q =
        evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0 (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1)
          (fam.s1EvPairs.getD a (0, 0)).1 := by unfold evalRU; ring
    refine ⟨by rw [heq]; exact evalRU_lt h12 h20 h03 h3R hlt, fun _ => heq,
      fun e => by omega, fun e => by omega, fun e => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun _ => by omega, fun e => by omega, fun e => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun e => by omega, fun _ => by omega, fun e => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun e => by omega, fun e => by omega, fun _ => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun e => by omega, fun e => by omega, fun e => by omega, fun _ => by omega⟩

private lemma evalUA1_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ) {a b : ℕ}
    (ha : a < fam.R + 4) (hb : b < fam.R + 4)
    (heq : evalUA1 fam q a = evalUA1 fam q b) : a = b := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  have sa := evalUA1_spec C q a ha; have sb := evalUA1_spec C q b hb
  dsimp only at sa sb
  rcases (by omega : a < fam.R ∨ a = fam.R ∨ a = fam.R + 1 ∨ a = fam.R + 2 ∨ a = fam.R + 3) with
    ha0 | ha1 | ha2 | ha3 | ha4 <;>
    rcases (by omega : b < fam.R ∨ b = fam.R ∨ b = fam.R + 1 ∨ b = fam.R + 2 ∨ b = fam.R + 3) with
      hb0 | hb1 | hb2 | hb3 | hb4
  · rw [sa.2.1 ha0, sb.2.1 hb0] at heq
    exact s1Ev_fst_inj C ha0 hb0 (evalRU_inj h12 h20 h03 heq)
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.1 hb1] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.2.1 hb2] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.2.2.1 hb3] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hb0)
    rw [sa.2.2.1 ha1, sb.2.1 hb0] at heq; omega
  · omega
  · rw [sa.2.2.1 ha1, sb.2.2.2.1 hb2] at heq; omega
  · rw [sa.2.2.1 ha1, sb.2.2.2.2.1 hb3] at heq; omega
  · rw [sa.2.2.1 ha1, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hb0)
    rw [sa.2.2.2.1 ha2, sb.2.1 hb0] at heq; omega
  · rw [sa.2.2.2.1 ha2, sb.2.2.1 hb1] at heq; omega
  · omega
  · rw [sa.2.2.2.1 ha2, sb.2.2.2.2.1 hb3] at heq; omega
  · rw [sa.2.2.2.1 ha2, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hb0)
    rw [sa.2.2.2.2.1 ha3, sb.2.1 hb0] at heq; omega
  · rw [sa.2.2.2.2.1 ha3, sb.2.2.1 hb1] at heq; omega
  · rw [sa.2.2.2.2.1 ha3, sb.2.2.2.1 hb2] at heq; omega
  · omega
  · rw [sa.2.2.2.2.1 ha3, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hb0)
    rw [sa.2.2.2.2.2 ha4, sb.2.1 hb0] at heq; omega
  · rw [sa.2.2.2.2.2 ha4, sb.2.2.1 hb1] at heq; omega
  · rw [sa.2.2.2.2.2 ha4, sb.2.2.2.1 hb2] at heq; omega
  · rw [sa.2.2.2.2.2 ha4, sb.2.2.2.2.1 hb3] at heq; omega
  · omega

/-- Exact formula & properties of `evalUB2` (`b < R + 4`). -/
private lemma evalUB2_spec {fam : OddTailData} (C : OddChecked fam) (q b : ℕ) (hb : b < fam.R + 4) :
    let P := mkOddParams fam; let p := q + 1; let u := evalUB2 fam q b
    u < 2 * (4 * p + fam.R) ∧
    (b < fam.R → u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD b (0, 0)).2) ∧
    (b = fam.R → u = P.U0_0 + 4 * p) ∧
    (b = fam.R + 1 → u = P.U1_0) ∧
    (b = fam.R + 2 → u = P.U2_0 + 2 * p) ∧
    (b = fam.R + 3 → u = P.U3_0 + 6 * p) := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  unfold evalUB2 ub2Lin; dsimp only
  split_ifs with h0 h1 h2 h3
  · have hlt := s2Od_snd_lt C h0
    have heq : (fam.s2OdPairs.getD b (0, 0)).2 +
        ruSlope (mkOddParams fam).U1_0 (mkOddParams fam).U2_0 (mkOddParams fam).U0_0 (mkOddParams fam).U3_0
          (fam.s2OdPairs.getD b (0, 0)).2 +
        ruSlope (mkOddParams fam).U1_0 (mkOddParams fam).U2_0 (mkOddParams fam).U0_0 (mkOddParams fam).U3_0
          (fam.s2OdPairs.getD b (0, 0)).2 * q =
        evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0 (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1)
          (fam.s2OdPairs.getD b (0, 0)).2 := by unfold evalRU; ring
    refine ⟨by rw [heq]; exact evalRU_lt h12 h20 h03 h3R hlt, fun _ => heq,
      fun e => by omega, fun e => by omega, fun e => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun _ => by omega, fun e => by omega, fun e => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun e => by omega, fun _ => by omega, fun e => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun e => by omega, fun e => by omega, fun _ => by omega, fun e => by omega⟩
  · refine ⟨by omega, fun e => by omega, fun e => by omega, fun e => by omega, fun e => by omega, fun _ => by omega⟩

private lemma evalUB2_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ) {a b : ℕ}
    (ha : a < fam.R + 4) (hb : b < fam.R + 4)
    (heq : evalUB2 fam q a = evalUB2 fam q b) : a = b := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  have sa := evalUB2_spec C q a ha; have sb := evalUB2_spec C q b hb
  dsimp only at sa sb
  rcases (by omega : a < fam.R ∨ a = fam.R ∨ a = fam.R + 1 ∨ a = fam.R + 2 ∨ a = fam.R + 3) with
    ha0 | ha1 | ha2 | ha3 | ha4 <;>
    rcases (by omega : b < fam.R ∨ b = fam.R ∨ b = fam.R + 1 ∨ b = fam.R + 2 ∨ b = fam.R + 3) with
      hb0 | hb1 | hb2 | hb3 | hb4
  · rw [sa.2.1 ha0, sb.2.1 hb0] at heq
    exact s2Od_snd_inj C ha0 hb0 (evalRU_inj h12 h20 h03 heq)
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.1 hb1] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.2.1 hb2] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.2.2.1 hb3] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C ha0)
    rw [sa.2.1 ha0, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hb0)
    rw [sa.2.2.1 ha1, sb.2.1 hb0] at heq; omega
  · omega
  · rw [sa.2.2.1 ha1, sb.2.2.2.1 hb2] at heq; omega
  · rw [sa.2.2.1 ha1, sb.2.2.2.2.1 hb3] at heq; omega
  · rw [sa.2.2.1 ha1, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hb0)
    rw [sa.2.2.2.1 ha2, sb.2.1 hb0] at heq; omega
  · rw [sa.2.2.2.1 ha2, sb.2.2.1 hb1] at heq; omega
  · omega
  · rw [sa.2.2.2.1 ha2, sb.2.2.2.2.1 hb3] at heq; omega
  · rw [sa.2.2.2.1 ha2, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hb0)
    rw [sa.2.2.2.2.1 ha3, sb.2.1 hb0] at heq; omega
  · rw [sa.2.2.2.2.1 ha3, sb.2.2.1 hb1] at heq; omega
  · rw [sa.2.2.2.2.1 ha3, sb.2.2.2.1 hb2] at heq; omega
  · omega
  · rw [sa.2.2.2.2.1 ha3, sb.2.2.2.2.2 hb4] at heq; omega
  · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hb0)
    rw [sa.2.2.2.2.2 ha4, sb.2.1 hb0] at heq; omega
  · rw [sa.2.2.2.2.2 ha4, sb.2.2.1 hb1] at heq; omega
  · rw [sa.2.2.2.2.2 ha4, sb.2.2.2.1 hb2] at heq; omega
  · rw [sa.2.2.2.2.2 ha4, sb.2.2.2.2.1 hb3] at heq; omega
  · omega

/-! ### Helper Classification Lemmas for Sol 1 (`odd1U0..3`) and Sol 2 (`odd2U0..3`) -/

private lemma odd1U0_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd1U0 fam q j
    (0 < j ∧ j < p ∧ u = P.U0_0 + 4 * p + 2 * (j - 1) ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * (j - 1) + 2) ∨
    (P.j3_0 + p < j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p) - 1) ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p) - 1) + 2) ∨
    (P.j1_0 + 2 * p < j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p) - 1) ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p) - 1) + 3) ∨
    (fam.R + 3 * p < j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p) - 1) ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p) - 1) + 3) ∨
    (∃ idx < fam.R + 4,
      j = (ja1Lin fam idx).1 + (ja1Lin fam idx).2 * q ∧
      u = evalUA1 fam q (fam.s1OdA.getD idx 0) ∧
      2 * j + u + 1 = (s1OdSlotS fam idx).1 + (s1OdSlotS fam idx).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd1U0; dsimp only
  by_cases h1 : j = 0
  · simp only [if_pos h1]; right; right; right; right
    refine ⟨fam.R, by omega, ?_, rfl, ?_⟩
    · unfold ja1Lin; simp only [show ¬ (fam.R < fam.R) by omega, ↓reduceIte]; omega
    · unfold s1OdSlotS evalUA1 ja1Lin
      simp only [show fam.R < fam.R + 4 by omega, show ¬ (fam.R < fam.R) by omega, ↓reduceIte]; ring_nf; omega
  · by_cases h2 : j < q + 1
    · simp only [if_neg h1, if_pos h2]; left; exact ⟨by omega, by omega, trivial, by omega⟩
    · by_cases h3 : j < (mkOddParams fam).j3_0 + (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; right; right; right
        refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
        · unfold ja1Lin rjSlope; rw [if_pos (by omega), if_pos (by omega)]; dsimp only; omega
        · unfold s1OdSlotS evalUA1 ja1Lin rjSlope
          rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]; dsimp only; ring_nf; omega
      · by_cases h4 : j = (mkOddParams fam).j3_0 + (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨fam.R + 3, by omega, ?_, rfl, ?_⟩
          · unfold ja1Lin; simp only [show ¬ (fam.R + 3 < fam.R) by omega,
              show ¬ (fam.R + 3 = fam.R) by omega, show ¬ (fam.R + 3 = fam.R + 1) by omega,
              show ¬ (fam.R + 3 = fam.R + 2) by omega, ↓reduceIte]; omega
          · unfold s1OdSlotS evalUA1 ja1Lin
            simp only [show fam.R + 3 < fam.R + 4 by omega, show ¬ (fam.R + 3 < fam.R) by omega,
              show ¬ (fam.R + 3 = fam.R) by omega, show ¬ (fam.R + 3 = fam.R + 1) by omega,
              show ¬ (fam.R + 3 = fam.R + 2) by omega, ↓reduceIte]; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold ja1Lin rjSlope; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; dsimp only; omega
              · unfold s1OdSlotS evalUA1 ja1Lin rjSlope
                rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
                dsimp only; ring_nf; omega
            · by_cases h7 : j = (mkOddParams fam).j1_0 + 2 * (q + 1)
              · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]; right; right; right; right
                refine ⟨fam.R + 1, by omega, ?_, rfl, ?_⟩
                · unfold ja1Lin; simp only [show ¬ (fam.R + 1 < fam.R) by omega,
                    show ¬ (fam.R + 1 = fam.R) by omega, ↓reduceIte]; omega
                · unfold s1OdSlotS evalUA1 ja1Lin
                  simp only [show fam.R + 1 < fam.R + 4 by omega, show ¬ (fam.R + 1 < fam.R) by omega,
                    show ¬ (fam.R + 1 = fam.R) by omega, ↓reduceIte]; ring_nf; omega
              · by_cases h8 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
                · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
                · by_cases h9 : j < fam.R + 3 * (q + 1)
                  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9]; right; right; right; right
                    refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
                    · unfold ja1Lin rjSlope; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]; dsimp only; omega
                    · unfold s1OdSlotS evalUA1 ja1Lin rjSlope
                      rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
                      dsimp only; ring_nf; omega
                  · by_cases h10 : j = fam.R + 3 * (q + 1)
                    · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10]; right; right; right; right
                      refine ⟨fam.R + 2, by omega, ?_, rfl, ?_⟩
                      · unfold ja1Lin; simp only [show ¬ (fam.R + 2 < fam.R) by omega,
                          show ¬ (fam.R + 2 = fam.R) by omega, show ¬ (fam.R + 2 = fam.R + 1) by omega, ↓reduceIte]; omega
                      · unfold s1OdSlotS evalUA1 ja1Lin
                        simp only [show fam.R + 2 < fam.R + 4 by omega, show ¬ (fam.R + 2 < fam.R) by omega,
                          show ¬ (fam.R + 2 = fam.R) by omega, show ¬ (fam.R + 2 = fam.R + 1) by omega, ↓reduceIte]
                        ring_nf; omega
                    · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd1U1_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd1U1 fam q j
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j + 1 ∧ 2 * j + u = P.s1_0 + 4 * p + 4 * j) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1 ∧
      2 * j + u = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p))) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1 ∧
      2 * j + u = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 1) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1 ∧
      2 * j + u = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 1) ∨
    (∃ ji < fam.R,
      j = evalRJ P.j3_0 P.j1_0 p ji ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD (fam.s1OdB.getD ji 0) (0, 0)).2 ∧
      2 * j + u = (s1OdSlotS fam (fam.R + 4 + ji)).1 + (s1OdSlotS fam (fam.R + 4 + ji)).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd1U1; dsimp only
  by_cases h1 : j < q + 1
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j < (mkOddParams fam).j3_0 + (q + 1)
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
      · unfold evalRJ rjSlope; rw [if_pos (by omega)]; omega
      · unfold s1OdSlotS ja1Lin evalRU rjSlope
        rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left, if_pos (by omega), if_pos (by omega)]
        dsimp only; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
      · by_cases h4 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
          · unfold evalRJ rjSlope; rw [if_neg (by omega), if_pos (by omega)]; omega
          · unfold s1OdSlotS ja1Lin evalRU rjSlope
            rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
            dsimp only; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < fam.R + 3 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold evalRJ rjSlope; rw [if_neg (by omega), if_neg (by omega)]; omega
              · unfold s1OdSlotS ja1Lin evalRU rjSlope
                rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
                dsimp only; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd1U2_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd1U2 fam q j
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j ∧ 2 * j + u + 1 = P.s1_0 + 4 * p + 4 * j) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p))) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 1) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 1) ∨
    (∃ ji < fam.R,
      j = evalRJ P.j3_0 P.j1_0 p ji ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD ji (0, 0)).1 ∧
      2 * j + u + 1 = (s1EvSlotS fam (2 * ji)).1 + (s1EvSlotS fam (2 * ji)).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd1U2; dsimp only
  by_cases h1 : j < q + 1
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j < (mkOddParams fam).j3_0 + (q + 1)
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
      · unfold evalRJ rjSlope; rw [if_pos (by omega)]; omega
      · unfold s1EvSlotS s1EvSlotU evalRU rjSlope
        simp only [show 2 * (j - (q + 1)) / 2 = j - (q + 1) by omega,
          show 2 * (j - (q + 1)) % 2 = 0 by omega,
          ↓reduceIte, if_pos (show j - (q + 1) < (mkOddParams fam).j3_0 by omega)]; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
      · by_cases h4 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
          · unfold evalRJ rjSlope; rw [if_neg (by omega), if_pos (by omega)]; omega
          · unfold s1EvSlotS s1EvSlotU evalRU rjSlope
            simp only [show 2 * (j - 2 * (q + 1)) / 2 = j - 2 * (q + 1) by omega,
              show 2 * (j - 2 * (q + 1)) % 2 = 0 by omega, ↓reduceIte,
              if_neg (show ¬ (j - 2 * (q + 1) < (mkOddParams fam).j3_0) by omega),
              if_pos (show j - 2 * (q + 1) < (mkOddParams fam).j1_0 by omega)]; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < fam.R + 3 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold evalRJ rjSlope; rw [if_neg (by omega), if_neg (by omega)]; omega
              · unfold s1EvSlotS s1EvSlotU evalRU rjSlope
                simp only [show 2 * (j - 3 * (q + 1)) / 2 = j - 3 * (q + 1) by omega,
                  show 2 * (j - 3 * (q + 1)) % 2 = 0 by omega, ↓reduceIte,
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j3_0) by omega),
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j1_0) by omega)]; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd1U3_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd1U3 fam q j
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j + 1 ∧ 2 * j + u + 2 = P.s1_0 + 4 * p + 4 * j + 2) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1 ∧
      2 * j + u + 2 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p)) + 2) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1 ∧
      2 * j + u + 2 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 3) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1 ∧
      2 * j + u + 2 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 3) ∨
    (∃ ji < fam.R,
      j = evalRJ P.j3_0 P.j1_0 p ji ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s1EvPairs.getD ji (0, 0)).2 ∧
      2 * j + u + 2 = (s1EvSlotS fam (2 * ji + 1)).1 + (s1EvSlotS fam (2 * ji + 1)).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd1U3; dsimp only
  by_cases h1 : j < q + 1
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j < (mkOddParams fam).j3_0 + (q + 1)
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
      · unfold evalRJ rjSlope; rw [if_pos (by omega)]; omega
      · unfold s1EvSlotS s1EvSlotU evalRU rjSlope
        simp only [show (2 * (j - (q + 1)) + 1) / 2 = j - (q + 1) by omega,
          show (2 * (j - (q + 1)) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
          if_pos (show j - (q + 1) < (mkOddParams fam).j3_0 by omega)]; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
      · by_cases h4 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
          · unfold evalRJ rjSlope; rw [if_neg (by omega), if_pos (by omega)]; omega
          · unfold s1EvSlotS s1EvSlotU evalRU rjSlope
            simp only [show (2 * (j - 2 * (q + 1)) + 1) / 2 = j - 2 * (q + 1) by omega,
              show (2 * (j - 2 * (q + 1)) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
              if_neg (show ¬ (j - 2 * (q + 1) < (mkOddParams fam).j3_0) by omega),
              if_pos (show j - 2 * (q + 1) < (mkOddParams fam).j1_0 by omega)]; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < fam.R + 3 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold evalRJ rjSlope; rw [if_neg (by omega), if_neg (by omega)]; omega
              · unfold s1EvSlotS s1EvSlotU evalRU rjSlope
                simp only [show (2 * (j - 3 * (q + 1)) + 1) / 2 = j - 3 * (q + 1) by omega,
                  show (2 * (j - 3 * (q + 1)) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j3_0) by omega),
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j1_0) by omega)]; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd2U0_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd2U0 fam q j
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j + 1 ∧ 2 * j + u + 1 = P.s1_0 + 4 * p + 4 * j + 1) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1 ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p)) + 1) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1 ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 2) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1 ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 2) ∨
    (∃ ji < fam.R,
      j = evalRJ P.j3_0 P.j1_0 p ji ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD ji (0, 0)).1 ∧
      2 * j + u + 1 = (s2OdSlotS fam (2 * ji)).1 + (s2OdSlotS fam (2 * ji)).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd2U0; dsimp only
  by_cases h1 : j < q + 1
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j < (mkOddParams fam).j3_0 + (q + 1)
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
      · unfold evalRJ rjSlope; rw [if_pos (by omega)]; omega
      · unfold s2OdSlotS s2OdSlotU evalRU rjSlope
        simp only [show 2 * (j - (q + 1)) / 2 = j - (q + 1) by omega,
          show 2 * (j - (q + 1)) % 2 = 0 by omega,
          ↓reduceIte, if_pos (show j - (q + 1) < (mkOddParams fam).j3_0 by omega)]; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
      · by_cases h4 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
          · unfold evalRJ rjSlope; rw [if_neg (by omega), if_pos (by omega)]; omega
          · unfold s2OdSlotS s2OdSlotU evalRU rjSlope
            simp only [show 2 * (j - 2 * (q + 1)) / 2 = j - 2 * (q + 1) by omega,
              show 2 * (j - 2 * (q + 1)) % 2 = 0 by omega, ↓reduceIte,
              if_neg (show ¬ (j - 2 * (q + 1) < (mkOddParams fam).j3_0) by omega),
              if_pos (show j - 2 * (q + 1) < (mkOddParams fam).j1_0 by omega)]; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < fam.R + 3 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold evalRJ rjSlope; rw [if_neg (by omega), if_neg (by omega)]; omega
              · unfold s2OdSlotS s2OdSlotU evalRU rjSlope
                simp only [show 2 * (j - 3 * (q + 1)) / 2 = j - 3 * (q + 1) by omega,
                  show 2 * (j - 3 * (q + 1)) % 2 = 0 by omega, ↓reduceIte,
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j3_0) by omega),
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j1_0) by omega)]; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd2U1_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd2U1 fam q j
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j ∧ 2 * j + u = P.s1_0 + 4 * p - 1 + 4 * j) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) ∧
      2 * j + u = P.s2_0 + 8 * p - 1 + 4 * (j - (P.j3_0 + p))) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) ∧
      2 * j + u = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p))) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) ∧
      2 * j + u = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p))) ∨
    (∃ ji < fam.R,
      j = evalRJ P.j3_0 P.j1_0 p ji ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD ji (0, 0)).2 ∧
      2 * j + u = (s2OdSlotS fam (2 * ji + 1)).1 + (s2OdSlotS fam (2 * ji + 1)).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs1p := C.hs1_pos; have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd2U1; dsimp only
  by_cases h1 : j < q + 1
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j < (mkOddParams fam).j3_0 + (q + 1)
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
      · unfold evalRJ rjSlope; rw [if_pos (by omega)]; omega
      · unfold s2OdSlotS s2OdSlotU evalRU rjSlope
        simp only [show (2 * (j - (q + 1)) + 1) / 2 = j - (q + 1) by omega,
          show (2 * (j - (q + 1)) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
          if_pos (show j - (q + 1) < (mkOddParams fam).j3_0 by omega)]; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
      · by_cases h4 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
          · unfold evalRJ rjSlope; rw [if_neg (by omega), if_pos (by omega)]; omega
          · unfold s2OdSlotS s2OdSlotU evalRU rjSlope
            simp only [show (2 * (j - 2 * (q + 1)) + 1) / 2 = j - 2 * (q + 1) by omega,
              show (2 * (j - 2 * (q + 1)) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
              if_neg (show ¬ (j - 2 * (q + 1) < (mkOddParams fam).j3_0) by omega),
              if_pos (show j - 2 * (q + 1) < (mkOddParams fam).j1_0 by omega)]; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < fam.R + 3 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold evalRJ rjSlope; rw [if_neg (by omega), if_neg (by omega)]; omega
              · unfold s2OdSlotS s2OdSlotU evalRU rjSlope
                simp only [show (2 * (j - 3 * (q + 1)) + 1) / 2 = j - 3 * (q + 1) by omega,
                  show (2 * (j - 3 * (q + 1)) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j3_0) by omega),
                  if_neg (show ¬ (j - 3 * (q + 1) < (mkOddParams fam).j1_0) by omega)]; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd2U2_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd2U2 fam q j
    (j < p ∧ u = P.U0_0 + 4 * p + 2 * j + 1 ∧ 2 * j + u + 1 = P.s1_0 + 4 * p + 4 * j + 1) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p)) + 1 ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p)) + 1) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p)) + 1 ∧
      2 * j + u + 1 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 2) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p)) + 1 ∧
      2 * j + u + 1 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 2) ∨
    (∃ ji < fam.R,
      j = evalRJ P.j3_0 P.j1_0 p ji ∧
      u = evalRU P.U1_0 P.U2_0 P.U0_0 P.U3_0 p (fam.s2OdPairs.getD (fam.s2EvA.getD ji 0) (0, 0)).1 ∧
      2 * j + u + 1 = (s2EvSlotS fam ji).1 + (s2EvSlotS fam ji).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd2U2; dsimp only
  by_cases h1 : j < q + 1
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j < (mkOddParams fam).j3_0 + (q + 1)
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
      · unfold evalRJ rjSlope; rw [if_pos (by omega)]; omega
      · unfold s2EvSlotS jb2Lin evalRU rjSlope
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]; dsimp only; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + 2 * (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
      · by_cases h4 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; right; right; right
          refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
          · unfold evalRJ rjSlope; rw [if_neg (by omega), if_pos (by omega)]; omega
          · unfold s2EvSlotS jb2Lin evalRU rjSlope
            rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
            dsimp only; ring_nf; omega
        · by_cases h5 : j < (mkOddParams fam).j1_0 + 3 * (q + 1)
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
          · by_cases h6 : j < fam.R + 3 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold evalRJ rjSlope; rw [if_neg (by omega), if_neg (by omega)]; omega
              · unfold s2EvSlotS jb2Lin evalRU rjSlope
                rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
                dsimp only; ring_nf; omega
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩

private lemma odd2U3_cases {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    let P := mkOddParams fam; let p := q + 1; let u := odd2U3 fam q j
    (j < q ∧ u = P.U0_0 + 4 * p + 2 * (j + 1) ∧ 2 * j + u + 2 = P.s1_0 + 4 * p + 4 * j + 3) ∨
    (P.j3_0 + p ≤ j ∧ j < P.j3_0 + 2 * p - 1 ∧ u = P.U3_0 + 6 * p + 2 * (j - (P.j3_0 + p) + 1) ∧
      2 * j + u + 2 = P.s2_0 + 8 * p + 4 * (j - (P.j3_0 + p)) + 3) ∨
    (P.j1_0 + 2 * p ≤ j ∧ j < P.j1_0 + 3 * p - 1 ∧ u = P.U1_0 + 2 * (j - (P.j1_0 + 2 * p) + 1) ∧
      2 * j + u + 2 = P.s1_0 + 4 * p + 4 * (j - (P.j1_0 + 2 * p)) + 4) ∨
    (fam.R + 3 * p ≤ j ∧ j < fam.R + 4 * p - 1 ∧ u = P.U2_0 + 2 * p + 2 * (j - (fam.R + 3 * p) + 1) ∧
      2 * j + u + 2 = P.s2_0 + 8 * p + 4 * (j - (fam.R + 3 * p)) + 4) ∨
    (∃ m < fam.R + 4,
      j = (jb2Lin fam m).1 + (jb2Lin fam m).2 * q ∧
      u = evalUB2 fam q (fam.s2EvB.getD m 0) ∧
      2 * j + u + 2 = (s2EvSlotS fam (fam.R + m)).1 + (s2EvSlotS fam (fam.R + m)).2 * q) := by
  have hU0 := C.hU0; have hj1 := C.hj1; have hj3 := C.hj3; have hU2 := C.hU2
  have hs2p := C.hs2_pos; have hj31 := C.hj31; have hj1R := C.hj1R
  dsimp only; unfold odd2U3; dsimp only
  by_cases h1 : j < q
  · simp only [if_pos h1]; left; exact ⟨by omega, trivial, by omega⟩
  · by_cases h2 : j = q
    · simp only [if_neg h1, if_pos h2]; right; right; right; right
      refine ⟨fam.R, by omega, ?_, rfl, ?_⟩
      · unfold jb2Lin; simp only [show ¬ (fam.R < fam.R) by omega, ↓reduceIte]; omega
      · unfold s2EvSlotS evalUB2 jb2Lin
        rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left]
        simp only [show ¬ (fam.R < fam.R) by omega, ↓reduceIte]; ring_nf; omega
    · by_cases h3 : j < (mkOddParams fam).j3_0 + (q + 1)
      · simp only [if_neg h1, if_neg h2, if_pos h3]; right; right; right; right
        refine ⟨j - (q + 1), by omega, ?_, rfl, ?_⟩
        · unfold jb2Lin rjSlope; rw [if_pos (by omega), if_pos (by omega)]; dsimp only; omega
        · unfold s2EvSlotS evalUB2 jb2Lin rjSlope
          rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left, if_pos (by omega), if_pos (by omega)]
          dsimp only; ring_nf; omega
      · by_cases h4 : j < (mkOddParams fam).j3_0 + 2 * (q + 1) - 1
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
        · by_cases h5 : j = (mkOddParams fam).j3_0 + 2 * (q + 1) - 1
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; right; right; right; right
            refine ⟨fam.R + 3, by omega, ?_, rfl, ?_⟩
            · unfold jb2Lin; simp only [show ¬ (fam.R + 3 < fam.R) by omega,
                show ¬ (fam.R + 3 = fam.R) by omega, show ¬ (fam.R + 3 = fam.R + 1) by omega,
                show ¬ (fam.R + 3 = fam.R + 2) by omega, ↓reduceIte]; omega
            · unfold s2EvSlotS evalUB2 jb2Lin
              rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left]
              simp only [show ¬ (fam.R + 3 < fam.R) by omega, show ¬ (fam.R + 3 = fam.R) by omega,
                show ¬ (fam.R + 3 = fam.R + 1) by omega, show ¬ (fam.R + 3 = fam.R + 2) by omega, ↓reduceIte]
              ring_nf; omega
          · by_cases h6 : j < (mkOddParams fam).j1_0 + 2 * (q + 1)
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; right; right; right; right
              refine ⟨j - 2 * (q + 1), by omega, ?_, rfl, ?_⟩
              · unfold jb2Lin rjSlope; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; dsimp only; omega
              · unfold s2EvSlotS evalUB2 jb2Lin rjSlope
                rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
                dsimp only; ring_nf; omega
            · by_cases h7 : j < (mkOddParams fam).j1_0 + 3 * (q + 1) - 1
              · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
              · by_cases h8 : j = (mkOddParams fam).j1_0 + 3 * (q + 1) - 1
                · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8]; right; right; right; right
                  refine ⟨fam.R + 1, by omega, ?_, rfl, ?_⟩
                  · unfold jb2Lin; simp only [show ¬ (fam.R + 1 < fam.R) by omega,
                      show ¬ (fam.R + 1 = fam.R) by omega, ↓reduceIte]; omega
                  · unfold s2EvSlotS evalUB2 jb2Lin
                    rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left]
                    simp only [show ¬ (fam.R + 1 < fam.R) by omega, show ¬ (fam.R + 1 = fam.R) by omega, ↓reduceIte]
                    ring_nf; omega
                · by_cases h9 : j < fam.R + 3 * (q + 1)
                  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9]; right; right; right; right
                    refine ⟨j - 3 * (q + 1), by omega, ?_, rfl, ?_⟩
                    · unfold jb2Lin rjSlope; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]; dsimp only; omega
                    · unfold s2EvSlotS evalUB2 jb2Lin rjSlope
                      rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
                      dsimp only; ring_nf; omega
                  · by_cases h10 : j < fam.R + 4 * (q + 1) - 1
                    · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10]; right; right; right; left; exact ⟨by omega, by omega, trivial, by omega⟩
                    · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]; right; right; right; right
                      refine ⟨fam.R + 2, by omega, ?_, rfl, ?_⟩
                      · unfold jb2Lin; simp only [show ¬ (fam.R + 2 < fam.R) by omega,
                          show ¬ (fam.R + 2 = fam.R) by omega, show ¬ (fam.R + 2 = fam.R + 1) by omega, ↓reduceIte]; omega
                      · unfold s2EvSlotS evalUB2 jb2Lin
                        rw [if_neg (by omega)]; dsimp only; rw [Nat.add_sub_cancel_left]
                        simp only [show ¬ (fam.R + 2 < fam.R) by omega, show ¬ (fam.R + 2 = fam.R) by omega,
                          show ¬ (fam.R + 2 = fam.R + 1) by omega, ↓reduceIte]
                        ring_nf; omega

/-! ### Sol 1 ValidTail Proof -/

private lemma odd1U_lt {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    odd1U0 fam q j < 2 * (4 * (q + 1) + fam.R) ∧
    odd1U1 fam q j < 2 * (4 * (q + 1) + fam.R) ∧
    odd1U2 fam q j < 2 * (4 * (q + 1) + fam.R) ∧
    odd1U3 fam q j < 2 * (4 * (q + 1) + fam.R) := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases odd1U0_cases C q j hj with h | h | h | h | ⟨idx, hidx, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact (evalUA1_spec C q _ (C.hs1oda_lt idx hidx)).1
  · rcases odd1U1_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (s1Ev_snd_lt C (C.hs1odb_lt ji hji))
  · rcases odd1U2_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (s1Ev_fst_lt C hji)
  · rcases odd1U3_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (s1Ev_snd_lt C hji)

private lemma odd1U0_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd1U0 fam q j₁ = odd1U0 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  have block_ne_rem : ∀ (a : ℕ) (ha : a < fam.R + 4) (u : ℕ),
      ((∃ r < q, u = (mkOddParams fam).U0_0 + 4 * (q + 1) + 2 * r) ∨
       (∃ r < q, u = (mkOddParams fam).U3_0 + 6 * (q + 1) + 2 * r) ∨
       (∃ r < q, u = (mkOddParams fam).U1_0 + 2 * r) ∨
       (∃ r < q, u = (mkOddParams fam).U2_0 + 2 * (q + 1) + 2 * r)) →
      u ≠ evalUA1 fam q a := by
    intro a ha u hblk he
    have sa := evalUA1_spec C q a ha; dsimp only at sa
    rcases (by omega : a < fam.R ∨ a = fam.R ∨ a = fam.R + 1 ∨ a = fam.R + 2 ∨ a = fam.R + 3) with
      ha0 | ha1 | ha2 | ha3 | ha4
    · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C ha0)
      rw [sa.2.1 ha0] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sa.2.2.1 ha1] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sa.2.2.2.1 ha2] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sa.2.2.2.2.1 ha3] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sa.2.2.2.2.2 ha4] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
  rcases odd1U0_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd1U0_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs1oda_lt i2 hi2) _ (Or.inl ⟨j₁ - 1, by omega, h1.2.2.1⟩))
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs1oda_lt i2 hi2) _ (Or.inr (Or.inl ⟨j₁ - ((mkOddParams fam).j3_0 + (q + 1)) - 1, by omega, h1.2.2.1⟩)))
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs1oda_lt i2 hi2) _ (Or.inr (Or.inr (Or.inl ⟨j₁ - ((mkOddParams fam).j1_0 + 2 * (q + 1)) - 1, by omega, h1.2.2.1⟩))))
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs1oda_lt i2 hi2) _ (Or.inr (Or.inr (Or.inr ⟨j₁ - (fam.R + 3 * (q + 1)) - 1, by omega, h1.2.2.1⟩))))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs1oda_lt i1 hi1) _ (Or.inl ⟨j₂ - 1, by omega, h2.2.2.1⟩))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs1oda_lt i1 hi1) _ (Or.inr (Or.inl ⟨j₂ - ((mkOddParams fam).j3_0 + (q + 1)) - 1, by omega, h2.2.2.1⟩)))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs1oda_lt i1 hi1) _ (Or.inr (Or.inr (Or.inl ⟨j₂ - ((mkOddParams fam).j1_0 + 2 * (q + 1)) - 1, by omega, h2.2.2.1⟩))))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs1oda_lt i1 hi1) _ (Or.inr (Or.inr (Or.inr ⟨j₂ - (fam.R + 3 * (q + 1)) - 1, by omega, h2.2.2.1⟩))))
  · have ha := evalUA1_inj C q (C.hs1oda_lt i1 hi1) (C.hs1oda_lt i2 hi2) (by rw [← hu1, ← hu2, heq])
    have hi := C.hs1oda_inj i1 hi1 i2 hi2 ha
    subst hi; rw [hj1e, hj2e]

private lemma odd1U1_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd1U1 fam q j₁ = odd1U1 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases odd1U1_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd1U1_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i2 hi2)); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i2 hi2)); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i2 hi2)); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i2 hi2)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i1 hi1)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i1 hi1)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i1 hi1)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C (C.hs1odb_lt i1 hi1)); omega
  · have hru := evalRU_inj h12 h20 h03 (hu1.symm.trans (heq.trans hu2))
    have hb := s1Ev_snd_inj C (C.hs1odb_lt i1 hi1) (C.hs1odb_lt i2 hi2) hru
    have hi := C.hs1odb_inj i1 hi1 i2 hi2 hb
    subst hi; rw [hj1e, hj2e]

private lemma odd1U2_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd1U2 fam q j₁ = odd1U2 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases odd1U2_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd1U2_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi2); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_fst_lt C hi1); omega
  · have hru := evalRU_inj h12 h20 h03 (hu1.symm.trans (heq.trans hu2))
    have hi := s1Ev_fst_inj C hi1 hi2 hru
    subst hi; rw [hj1e, hj2e]

private lemma odd1U3_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd1U3 fam q j₁ = odd1U3 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases odd1U3_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd1U3_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi2); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hi1); omega
  · have hru := evalRU_inj h12 h20 h03 (hu1.symm.trans (heq.trans hu2))
    have hi := s1Ev_snd_inj C hi1 hi2 hru
    subst hi; rw [hj1e, hj2e]

/-- Every `odd1U0` / `odd1U2` value is either in `inUBlockEven` or `evalRU (s1EvPairs[a].1)`. -/
private lemma odd1U0_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockEven (mkOddParams fam) (q + 1) (odd1U0 fam q j) ∨
    ∃ a < fam.R, odd1U0 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s1EvPairs.getD a (0, 0)).1 := by
  rcases odd1U0_cases C q j hj with h | h | h | h | ⟨idx, hidx, _, hu, _⟩
  · left; unfold inUBlockEven; right; right; left; omega
  · left; unfold inUBlockEven; right; right; right; omega
  · left; unfold inUBlockEven; left; omega
  · left; unfold inUBlockEven; right; left; omega
  · set a := fam.s1OdA.getD idx 0
    have ha := C.hs1oda_lt idx hidx
    have sa := evalUA1_spec C q a ha; dsimp only at sa
    rcases (by omega : a < fam.R ∨ a = fam.R ∨ a = fam.R + 1 ∨ a = fam.R + 2 ∨ a = fam.R + 3) with
      h0 | h1 | h2 | h3 | h4
    · right; exact ⟨a, h0, by rw [hu, sa.2.1 h0]⟩
    · left; unfold inUBlockEven; right; right; left; rw [hu, sa.2.2.1 h1]; omega
    · left; unfold inUBlockEven; left; rw [hu, sa.2.2.2.1 h2]; omega
    · left; unfold inUBlockEven; right; left; rw [hu, sa.2.2.2.2.1 h3]; omega
    · left; unfold inUBlockEven; right; right; right; rw [hu, sa.2.2.2.2.2 h4]; omega

private lemma odd1U2_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockEven (mkOddParams fam) (q + 1) (odd1U2 fam q j) ∨
    ∃ a < fam.R, odd1U2 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s1EvPairs.getD a (0, 0)).1 := by
  rcases odd1U2_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
  · left; unfold inUBlockEven; right; right; left; omega
  · left; unfold inUBlockEven; right; right; right; omega
  · left; unfold inUBlockEven; left; omega
  · left; unfold inUBlockEven; right; left; omega
  · right; exact ⟨ji, hji, hu⟩

private lemma odd1U1_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockOdd (mkOddParams fam) (q + 1) (odd1U1 fam q j) ∨
    ∃ b < fam.R, odd1U1 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s1EvPairs.getD b (0, 0)).2 := by
  rcases odd1U1_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
  · left; unfold inUBlockOdd; right; right; left; omega
  · left; unfold inUBlockOdd; right; right; right; omega
  · left; unfold inUBlockOdd; left; omega
  · left; unfold inUBlockOdd; right; left; omega
  · right; exact ⟨fam.s1OdB.getD ji 0, C.hs1odb_lt ji hji, hu⟩

private lemma odd1U3_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockOdd (mkOddParams fam) (q + 1) (odd1U3 fam q j) ∨
    ∃ b < fam.R, odd1U3 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s1EvPairs.getD b (0, 0)).2 := by
  rcases odd1U3_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
  · left; unfold inUBlockOdd; right; right; left; omega
  · left; unfold inUBlockOdd; right; right; right; omega
  · left; unfold inUBlockOdd; left; omega
  · left; unfold inUBlockOdd; right; left; omega
  · right; exact ⟨ji, hji, hu⟩

private lemma odd1_ev_disj {fam : OddTailData} (C : OddChecked fam) (q u : ℕ)
    (hA : inUBlockEven (mkOddParams fam) (q + 1) u ∨
      ∃ a < fam.R, u = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
        (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s1EvPairs.getD a (0, 0)).1)
    (hB : inUBlockOdd (mkOddParams fam) (q + 1) u ∨
      ∃ b < fam.R, u = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
        (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s1EvPairs.getD b (0, 0)).2) :
    False := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases hA with he | ⟨a, ha, rfl⟩ <;> rcases hB with ho | ⟨b, hb, hbe⟩
  · exact inUBlockEven_not_odd h12 h20 h03 he ho
  · rw [hbe] at he; exact evalRU_not_even_block h12 h20 h03 h3R (s1Ev_snd_lt C hb) he
  · exact evalRU_not_odd_block h12 h20 h03 h3R (s1Ev_fst_lt C ha) ho
  · exact s1Ev_fst_ne_snd C ha hb (evalRU_inj h12 h20 h03 hbe)

private lemma odd1_hs00 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd1U0 fam q j₁ + 1 = 2 * j₂ + odd1U0 fam q j₂ + 1) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd1U0_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨a1, ha1, hj1e, _, hs1⟩ <;>
    rcases odd1U0_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨a2, ha2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a2 (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a2 (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a2 (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a2 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩
      (C.hs1od_g a1 (by omega)) (C.hs1od_g a2 (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs1od_sinj a1 (by omega) a2 (by omega) (Prod.ext hp.1 hp.2)
    subst ha; omega

private lemma odd1_hs01 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd1U0 fam q j₁ + 1 = 2 * j₂ + odd1U1 fam q j₂) : False := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd1U0_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨a1, ha1, _, _, hs1⟩ <;>
    rcases odd1U1_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, _, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g a1 (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩
      (C.hs1od_g a1 (by omega)) (C.hs1od_g (fam.R + 4 + j2) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs1od_sinj a1 (by omega) (fam.R + 4 + j2) (by omega) (Prod.ext hp.1 hp.2); omega

private lemma odd1_hs11 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd1U1 fam q j₁ = 2 * j₂ + odd1U1 fam q j₂) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd1U1_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, hj1e, _, hs1⟩ <;>
    rcases odd1U1_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j2) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + j1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩
      (C.hs1od_g (fam.R + 4 + j1) (by omega)) (C.hs1od_g (fam.R + 4 + j2) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs1od_sinj (fam.R + 4 + j1) (by omega) (fam.R + 4 + j2) (by omega) (Prod.ext hp.1 hp.2)
    have hje : j1 = j2 := by omega
    subst hje; omega

private lemma odd1_hs22 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd1U2 fam q j₁ + 1 = 2 * j₂ + odd1U2 fam q j₂ + 1) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd1U2_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, hj1e, _, hs1⟩ <;>
    rcases odd1U2_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩
      (C.hs1ev_g (2 * j1) (by omega)) (C.hs1ev_g (2 * j2) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs1ev_sinj (2 * j1) (by omega) (2 * j2) (by omega) (Prod.ext hp.1 hp.2)
    have hje : j1 = j2 := by omega
    subst hje; omega

private lemma odd1_hs23 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd1U2 fam q j₁ + 1 = 2 * j₂ + odd1U3 fam q j₂ + 2) : False := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd1U2_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, _, _, hs1⟩ <;>
    rcases odd1U3_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, _, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩
      (C.hs1ev_g (2 * j1) (by omega)) (C.hs1ev_g (2 * j2 + 1) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs1ev_sinj (2 * j1) (by omega) (2 * j2 + 1) (by omega) (Prod.ext hp.1 hp.2); omega

private lemma odd1_hs33 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd1U3 fam q j₁ + 2 = 2 * j₂ + odd1U3 fam q j₂ + 2) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd1U3_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, hj1e, _, hs1⟩ <;>
    rcases odd1U3_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩
      (C.hs1ev_g (2 * j1 + 1) (by omega)) (C.hs1ev_g (2 * j2 + 1) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs1ev_sinj (2 * j1 + 1) (by omega) (2 * j2 + 1) (by omega) (Prod.ext hp.1 hp.2)
    have hje : j1 = j2 := by omega
    subst hje; omega

private lemma oddBand_odd_int {R d h q hs : ℕ} (hd : 2 * d + 1 = h) (hdR : d + 1 ≤ R)
    (hb : (R - d + 3 + 4 * q ≤ hs ∧ hs < R - d + R + 7 + 8 * q) ∨
          (2 * R + d + 1 + 7 + 8 * q ≤ hs ∧ hs < 2 * R + d + 1 + R + 11 + 12 * q)) :
    let t := 4 * (q + 1) + R
    let s : ℤ := ((2 * hs + 1 : ℕ) : ℤ)
    (((2 * t : ℤ) - (h : ℤ) ≤ s ∧ s < (4 * t : ℤ) - (h : ℤ)) ∨
     ((4 * t : ℤ) + (h : ℤ) ≤ s ∧ s < (6 * t : ℤ) + (h : ℤ))) := by
  dsimp only; subst hd
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2' : hs + 1 ≤ R - d + R + 7 + 8 * q := h2
    zify [show d ≤ R by omega] at h1 h2'
    left; exact ⟨by push_cast; linarith, by push_cast; linarith⟩
  · have h2' : hs + 1 ≤ 2 * R + d + 1 + R + 11 + 12 * q := h2
    zify at h1 h2'
    right; exact ⟨by push_cast; linarith, by push_cast; linarith⟩

private lemma oddBand_even_int {R d h q hs : ℕ} (hd : 2 * d + 1 = h) (hdR : d + 1 ≤ R)
    (hb : (R - d + 4 + 4 * q ≤ hs ∧ hs < R - d + R + 8 + 8 * q) ∨
          (2 * R + d + 1 + 8 + 8 * q ≤ hs ∧ hs < 2 * R + d + 1 + R + 12 + 12 * q)) :
    let t := 4 * (q + 1) + R
    let s : ℤ := ((2 * hs : ℕ) : ℤ)
    (((2 * t : ℤ) - (h : ℤ) ≤ s ∧ s < (4 * t : ℤ) - (h : ℤ)) ∨
     ((4 * t : ℤ) + (h : ℤ) ≤ s ∧ s < (6 * t : ℤ) + (h : ℤ))) := by
  dsimp only; subst hd
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2' : hs + 1 ≤ R - d + R + 8 + 8 * q := h2
    zify [show d ≤ R by omega] at h1 h2'
    left; exact ⟨by push_cast; linarith, by push_cast; linarith⟩
  · have h2' : hs + 1 ≤ 2 * R + d + 1 + R + 12 + 12 * q := h2
    zify at h1 h2'
    right; exact ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- Construct Sol 1 `ValidTail fam.h (4 * (q + 1) + fam.R)` for any verified `OddTailData`. -/
def oddTail1Valid (fam : OddTailData) (hchk : checkOddTailData fam = true) (q : ℕ) :
    ValidTail fam.h (4 * (q + 1) + fam.R) := by
  have C := unpack_odd hchk
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hs1p := C.hs1_pos; have hs2p := C.hs2_pos
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  have hsym : ∀ i : ℕ,
      (i : ℤ) + (oddTail1Col fam q i : ℤ) + tailDelta i (oddTail1Col fam q i) =
        match i % 4 with
        | 0 => ((2 * (2 * (i / 4) + odd1U0 fam q (i / 4) + 1) + 1 : ℕ) : ℤ)
        | 1 => ((2 * (2 * (i / 4) + odd1U1 fam q (i / 4)) + 1 : ℕ) : ℤ)
        | 2 => ((2 * (2 * (i / 4) + odd1U2 fam q (i / 4) + 1) : ℕ) : ℤ)
        | _ => ((2 * (2 * (i / 4) + odd1U3 fam q (i / 4) + 2) : ℕ) : ℤ) := by
    intro i; unfold oddTail1Col
    set j := i / 4
    have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    rcases hk with h | h | h | h
    · simp only [h]; rw [show i = 4 * j by omega]; exact tailDelta_mod0_odd j _
    · simp only [h]; rw [show i = 4 * j + 1 by omega]; exact tailDelta_mod1_even j _
    · simp only [h]; rw [show i = 4 * j + 2 by omega]; exact tailDelta_mod2_even j _
    · simp only [h]; rw [show i = 4 * j + 3 by omega]; exact tailDelta_mod3_odd j _
  refine {
    col := oddTail1Col fam q
    col_lt := fun i hi => by
      have hlt := odd1U_lt C q (i / 4) (by omega)
      unfold oddTail1Col
      have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      rcases hk with h | h | h | h <;> simp only [h] <;> omega
    col_inj := fun i₁ hi₁ i₂ hi₂ heq => by
      unfold oddTail1Col at heq
      have hk1 : i₁ % 4 = 0 ∨ i₁ % 4 = 1 ∨ i₁ % 4 = 2 ∨ i₁ % 4 = 3 := by omega
      have hk2 : i₂ % 4 = 0 ∨ i₂ % 4 = 1 ∨ i₂ % 4 = 2 ∨ i₂ % 4 = 3 := by omega
      rcases hk1 with k1 | k1 | k1 | k1 <;> rcases hk2 with k2 | k2 | k2 | k2 <;>
        simp only [k1, k2] at heq
      · have := odd1U0_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · omega
      · omega
      · exfalso; exact odd1_ev_disj C q (odd1U0 fam q (i₁ / 4)) (odd1U0_class C q _ (by omega))
          (by rw [show odd1U0 fam q (i₁ / 4) = odd1U3 fam q (i₂ / 4) by omega]; exact odd1U3_class C q _ (by omega))
      · omega
      · have := odd1U1_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · exfalso; exact odd1_ev_disj C q (odd1U2 fam q (i₂ / 4)) (odd1U2_class C q _ (by omega))
          (by rw [show odd1U2 fam q (i₂ / 4) = odd1U1 fam q (i₁ / 4) by omega]; exact odd1U1_class C q _ (by omega))
      · omega
      · omega
      · exfalso; exact odd1_ev_disj C q (odd1U2 fam q (i₁ / 4)) (odd1U2_class C q _ (by omega))
          (by rw [show odd1U2 fam q (i₁ / 4) = odd1U1 fam q (i₂ / 4) by omega]; exact odd1U1_class C q _ (by omega))
      · have := odd1U2_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · omega
      · exfalso; exact odd1_ev_disj C q (odd1U0 fam q (i₂ / 4)) (odd1U0_class C q _ (by omega))
          (by rw [show odd1U0 fam q (i₂ / 4) = odd1U3 fam q (i₁ / 4) by omega]; exact odd1U3_class C q _ (by omega))
      · omega
      · omega
      · have := odd1U3_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
    sym_band := fun i hi => by
      dsimp only; rw [hsym i]
      have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      have he1 : (mkOddParams fam).e1_0 = fam.R - (mkOddParams fam).d := rfl
      have he2 : (mkOddParams fam).e2_0 = 2 * fam.R + (mkOddParams fam).d + 1 := rfl
      rcases hk with h | h | h | h <;> simp only [h]
      · refine oddBand_odd_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd1U0_cases C q (i / 4) (by omega) with ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨idx, hidx, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g idx (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
      · refine oddBand_odd_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd1U1_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨ji, hji, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs1od_g (fam.R + 4 + ji) (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
      · refine oddBand_even_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd1U2_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨ji, hji, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * ji) (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
      · refine oddBand_even_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd1U3_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨ji, hji, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs1ev_g (2 * ji + 1) (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
    sym_inj := fun i₁ hi₁ i₂ hi₂ heq => by
      rw [hsym i₁, hsym i₂] at heq
      have hk1 : i₁ % 4 = 0 ∨ i₁ % 4 = 1 ∨ i₁ % 4 = 2 ∨ i₁ % 4 = 3 := by omega
      have hk2 : i₂ % 4 = 0 ∨ i₂ % 4 = 1 ∨ i₂ % 4 = 2 ∨ i₂ % 4 = 3 := by omega
      rcases hk1 with k1 | k1 | k1 | k1 <;> rcases hk2 with k2 | k2 | k2 | k2 <;>
        (simp only [k1, k2] at heq; replace heq := Int.ofNat.inj heq)
      · have := odd1_hs00 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · exact False.elim (odd1_hs01 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega))
      · omega
      · omega
      · exact False.elim (odd1_hs01 C q (j₁ := i₂ / 4) (j₂ := i₁ / 4) (by omega) (by omega) (by omega))
      · have := odd1_hs11 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · omega
      · omega
      · omega
      · omega
      · have := odd1_hs22 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · exact False.elim (odd1_hs23 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega))
      · omega
      · omega
      · exact False.elim (odd1_hs23 C q (j₁ := i₂ / 4) (j₂ := i₁ / 4) (by omega) (by omega) (by omega))
      · have := odd1_hs33 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
  }

/-! ### Sol 2 ValidTail Proof & Disjointness -/

private lemma odd2U_lt {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    odd2U0 fam q j < 2 * (4 * (q + 1) + fam.R) ∧
    odd2U1 fam q j < 2 * (4 * (q + 1) + fam.R) ∧
    odd2U2 fam q j < 2 * (4 * (q + 1) + fam.R) ∧
    odd2U3 fam q j < 2 * (4 * (q + 1) + fam.R) := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases odd2U0_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (s2Od_fst_lt C hji)
  · rcases odd2U1_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (s2Od_snd_lt C hji)
  · rcases odd2U2_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact evalRU_lt h12 h20 h03 h3R (s2Od_fst_lt C (C.hs2eva_lt ji hji))
  · rcases odd2U3_cases C q j hj with h | h | h | h | ⟨m, hm, _, hu, _⟩
    · omega
    · omega
    · omega
    · omega
    · rw [hu]; exact (evalUB2_spec C q _ (C.hs2evb_lt m hm)).1

private lemma odd2U0_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd2U0 fam q j₁ = odd2U0 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases odd2U0_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd2U0_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi2); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hi1); omega
  · have hru := evalRU_inj h12 h20 h03 (hu1.symm.trans (heq.trans hu2))
    have hi := s2Od_fst_inj C hi1 hi2 hru
    subst hi; rw [hj1e, hj2e]

private lemma odd2U1_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd2U1 fam q j₁ = odd2U1 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases odd2U1_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd2U1_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi2); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi2); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi1); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hi1); omega
  · have hru := evalRU_inj h12 h20 h03 (hu1.symm.trans (heq.trans hu2))
    have hi := s2Od_snd_inj C hi1 hi2 hru
    subst hi; rw [hj1e, hj2e]

private lemma odd2U2_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd2U2 fam q j₁ = odd2U2 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases odd2U2_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd2U2_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i2 hi2)); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i2 hi2)); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i2 hi2)); omega
  · omega
  · omega
  · omega
  · omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i2 hi2)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i1 hi1)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i1 hi1)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i1 hi1)); omega
  · have := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C (C.hs2eva_lt i1 hi1)); omega
  · have hru := evalRU_inj h12 h20 h03 (hu1.symm.trans (heq.trans hu2))
    have ha := s2Od_fst_inj C (C.hs2eva_lt i1 hi1) (C.hs2eva_lt i2 hi2) hru
    have hi := C.hs2eva_inj i1 hi1 i2 hi2 ha
    subst hi; rw [hj1e, hj2e]

private lemma odd2U3_inj {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (heq : odd2U3 fam q j₁ = odd2U3 fam q j₂) : j₁ = j₂ := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  have block_ne_rem : ∀ (b : ℕ) (hb : b < fam.R + 4) (u : ℕ),
      ((∃ r < q, u = (mkOddParams fam).U0_0 + 4 * (q + 1) + 2 * (r + 1)) ∨
       (∃ r < q, u = (mkOddParams fam).U3_0 + 6 * (q + 1) + 2 * (r + 1)) ∨
       (∃ r < q, u = (mkOddParams fam).U1_0 + 2 * (r + 1)) ∨
       (∃ r < q, u = (mkOddParams fam).U2_0 + 2 * (q + 1) + 2 * (r + 1))) →
      u ≠ evalUB2 fam q b := by
    intro b hb u hblk he
    have sb := evalUB2_spec C q b hb; dsimp only at sb
    rcases (by omega : b < fam.R ∨ b = fam.R ∨ b = fam.R + 1 ∨ b = fam.R + 2 ∨ b = fam.R + 3) with
      hb0 | hb1 | hb2 | hb3 | hb4
    · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_snd_lt C hb0)
      rw [sb.2.1 hb0] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sb.2.2.1 hb1] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sb.2.2.2.1 hb2] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sb.2.2.2.2.1 hb3] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
    · rw [sb.2.2.2.2.2 hb4] at he; rcases hblk with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
  rcases odd2U3_cases C q j₁ hj₁ with h1 | h1 | h1 | h1 | ⟨i1, hi1, hj1e, hu1, _⟩ <;>
    rcases odd2U3_cases C q j₂ hj₂ with h2 | h2 | h2 | h2 | ⟨i2, hi2, hj2e, hu2, _⟩
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs2evb_lt i2 hi2) _ (Or.inl ⟨j₁, by omega, h1.2.1⟩))
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs2evb_lt i2 hi2) _ (Or.inr (Or.inl ⟨j₁ - ((mkOddParams fam).j3_0 + (q + 1)), by omega, h1.2.2.1⟩)))
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs2evb_lt i2 hi2) _ (Or.inr (Or.inr (Or.inl ⟨j₁ - ((mkOddParams fam).j1_0 + 2 * (q + 1)), by omega, h1.2.2.1⟩))))
  · omega
  · omega
  · omega
  · omega
  · exact absurd (by rw [← hu2, ← heq]) (block_ne_rem _ (C.hs2evb_lt i2 hi2) _ (Or.inr (Or.inr (Or.inr ⟨j₁ - (fam.R + 3 * (q + 1)), by omega, h1.2.2.1⟩))))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs2evb_lt i1 hi1) _ (Or.inl ⟨j₂, by omega, h2.2.1⟩))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs2evb_lt i1 hi1) _ (Or.inr (Or.inl ⟨j₂ - ((mkOddParams fam).j3_0 + (q + 1)), by omega, h2.2.2.1⟩)))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs2evb_lt i1 hi1) _ (Or.inr (Or.inr (Or.inl ⟨j₂ - ((mkOddParams fam).j1_0 + 2 * (q + 1)), by omega, h2.2.2.1⟩))))
  · exact absurd (by rw [← hu1, heq]) (block_ne_rem _ (C.hs2evb_lt i1 hi1) _ (Or.inr (Or.inr (Or.inr ⟨j₂ - (fam.R + 3 * (q + 1)), by omega, h2.2.2.1⟩))))
  · have hb := evalUB2_inj C q (C.hs2evb_lt i1 hi1) (C.hs2evb_lt i2 hi2) (by rw [← hu1, ← hu2, heq])
    have hi := C.hs2evb_inj i1 hi1 i2 hi2 hb
    subst hi; rw [hj1e, hj2e]

private lemma odd2U0_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockOdd (mkOddParams fam) (q + 1) (odd2U0 fam q j) ∨
    ∃ a < fam.R, odd2U0 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s2OdPairs.getD a (0, 0)).1 := by
  rcases odd2U0_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
  · left; unfold inUBlockOdd; right; right; left; omega
  · left; unfold inUBlockOdd; right; right; right; omega
  · left; unfold inUBlockOdd; left; omega
  · left; unfold inUBlockOdd; right; left; omega
  · right; exact ⟨ji, hji, hu⟩

private lemma odd2U2_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockOdd (mkOddParams fam) (q + 1) (odd2U2 fam q j) ∨
    ∃ a < fam.R, odd2U2 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s2OdPairs.getD a (0, 0)).1 := by
  rcases odd2U2_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
  · left; unfold inUBlockOdd; right; right; left; omega
  · left; unfold inUBlockOdd; right; right; right; omega
  · left; unfold inUBlockOdd; left; omega
  · left; unfold inUBlockOdd; right; left; omega
  · right; exact ⟨fam.s2EvA.getD ji 0, C.hs2eva_lt ji hji, hu⟩

private lemma odd2U1_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockEven (mkOddParams fam) (q + 1) (odd2U1 fam q j) ∨
    ∃ b < fam.R, odd2U1 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s2OdPairs.getD b (0, 0)).2 := by
  rcases odd2U1_cases C q j hj with h | h | h | h | ⟨ji, hji, _, hu, _⟩
  · left; unfold inUBlockEven; right; right; left; omega
  · left; unfold inUBlockEven; right; right; right; omega
  · left; unfold inUBlockEven; left; omega
  · left; unfold inUBlockEven; right; left; omega
  · right; exact ⟨ji, hji, hu⟩

private lemma odd2U3_class {fam : OddTailData} (C : OddChecked fam) (q j : ℕ)
    (hj : j < 4 * (q + 1) + fam.R) :
    inUBlockEven (mkOddParams fam) (q + 1) (odd2U3 fam q j) ∨
    ∃ b < fam.R, odd2U3 fam q j = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
      (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s2OdPairs.getD b (0, 0)).2 := by
  rcases odd2U3_cases C q j hj with h | h | h | h | ⟨m, hm, _, hu, _⟩
  · left; unfold inUBlockEven; right; right; left; omega
  · left; unfold inUBlockEven; right; right; right; omega
  · left; unfold inUBlockEven; left; omega
  · left; unfold inUBlockEven; right; left; omega
  · set b := fam.s2EvB.getD m 0
    have hb := C.hs2evb_lt m hm
    have sb := evalUB2_spec C q b hb; dsimp only at sb
    rcases (by omega : b < fam.R ∨ b = fam.R ∨ b = fam.R + 1 ∨ b = fam.R + 2 ∨ b = fam.R + 3) with
      h0 | h1 | h2 | h3 | h4
    · right; exact ⟨b, h0, by rw [hu, sb.2.1 h0]⟩
    · left; unfold inUBlockEven; right; right; left; rw [hu, sb.2.2.1 h1]; omega
    · left; unfold inUBlockEven; left; rw [hu, sb.2.2.2.1 h2]; omega
    · left; unfold inUBlockEven; right; left; rw [hu, sb.2.2.2.2.1 h3]; omega
    · left; unfold inUBlockEven; right; right; right; rw [hu, sb.2.2.2.2.2 h4]; omega

private lemma odd2_od_disj {fam : OddTailData} (C : OddChecked fam) (q u : ℕ)
    (hA : inUBlockOdd (mkOddParams fam) (q + 1) u ∨
      ∃ a < fam.R, u = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
        (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s2OdPairs.getD a (0, 0)).1)
    (hB : inUBlockEven (mkOddParams fam) (q + 1) u ∨
      ∃ b < fam.R, u = evalRU (mkOddParams fam).U1_0 (mkOddParams fam).U2_0
        (mkOddParams fam).U0_0 (mkOddParams fam).U3_0 (q + 1) (fam.s2OdPairs.getD b (0, 0)).2) :
    False := by
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  rcases hA with ho | ⟨a, ha, rfl⟩ <;> rcases hB with he | ⟨b, hb, hbe⟩
  · exact inUBlockEven_not_odd h12 h20 h03 he ho
  · rw [hbe] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s2Od_snd_lt C hb) ho
  · exact evalRU_not_even_block h12 h20 h03 h3R (s2Od_fst_lt C ha) he
  · exact s2Od_fst_ne_snd C ha hb (evalRU_inj h12 h20 h03 hbe)

private lemma odd2_hs00 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd2U0 fam q j₁ + 1 = 2 * j₂ + odd2U0 fam q j₂ + 1) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd2U0_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, hj1e, _, hs1⟩ <;>
    rcases odd2U0_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩
      (C.hs2od_g (2 * j1) (by omega)) (C.hs2od_g (2 * j2) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs2od_sinj (2 * j1) (by omega) (2 * j2) (by omega) (Prod.ext hp.1 hp.2)
    have hje : j1 = j2 := by omega
    subst hje; omega

private lemma odd2_hs01 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd2U0 fam q j₁ + 1 = 2 * j₂ + odd2U1 fam q j₂) : False := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd2U0_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, _, _, hs1⟩ <;>
    rcases odd2U1_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, _, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩
      (C.hs2od_g (2 * j1) (by omega)) (C.hs2od_g (2 * j2 + 1) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs2od_sinj (2 * j1) (by omega) (2 * j2 + 1) (by omega) (Prod.ext hp.1 hp.2); omega

private lemma odd2_hs11 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd2U1 fam q j₁ = 2 * j₂ + odd2U1 fam q j₂) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd2U1_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, hj1e, _, hs1⟩ <;>
    rcases odd2U1_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j2 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * j1 + 1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩
      (C.hs2od_g (2 * j1 + 1) (by omega)) (C.hs2od_g (2 * j2 + 1) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs2od_sinj (2 * j1 + 1) (by omega) (2 * j2 + 1) (by omega) (Prod.ext hp.1 hp.2)
    have hje : j1 = j2 := by omega
    subst hje; omega

private lemma odd2_hs22 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd2U2 fam q j₁ + 1 = 2 * j₂ + odd2U2 fam q j₂ + 1) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd2U2_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, hj1e, _, hs1⟩ <;>
    rcases odd2U2_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨j2, hj2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j2 (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j2 (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j2 (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j2 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩
      (C.hs2ev_g j1 (by omega)) (C.hs2ev_g j2 (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs2ev_sinj j1 (by omega) j2 (by omega) (Prod.ext hp.1 hp.2)
    subst ha; omega

private lemma odd2_hs23 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd2U2 fam q j₁ + 1 = 2 * j₂ + odd2U3 fam q j₂ + 2) : False := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd2U2_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨j1, hj1, _, _, hs1⟩ <;>
    rcases odd2U3_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨m2, hm2, _, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g j1 (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩
      (C.hs2ev_g j1 (by omega)) (C.hs2ev_g (fam.R + m2) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs2ev_sinj j1 (by omega) (fam.R + m2) (by omega) (Prod.ext hp.1 hp.2); omega

private lemma odd2_hs33 {fam : OddTailData} (C : OddChecked fam) (q : ℕ)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < 4 * (q + 1) + fam.R) (hj₂ : j₂ < 4 * (q + 1) + fam.R)
    (hhs : 2 * j₁ + odd2U3 fam q j₁ + 2 = 2 * j₂ + odd2U3 fam q j₂ + 2) : j₁ = j₂ := by
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  rcases odd2U3_cases C q j₁ hj₁ with c1 | c1 | c1 | c1 | ⟨m1, hm1, hj1e, _, hs1⟩ <;>
    rcases odd2U3_cases C q j₂ hj₂ with c2 | c2 | c2 | c2 | ⟨m2, hm2, hj2e, _, hs2⟩
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · omega
  · omega
  · omega
  · omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m2) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m1) (by omega)); dsimp only at hg; omega
  · have hg := inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m1) (by omega)); dsimp only at hg; omega
  · have hp := inSGaps_inj (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩
      (C.hs2ev_g (fam.R + m1) (by omega)) (C.hs2ev_g (fam.R + m2) (by omega)) (hs1.symm.trans (hhs.trans hs2))
    have ha := C.hs2ev_sinj (fam.R + m1) (by omega) (fam.R + m2) (by omega) (Prod.ext hp.1 hp.2)
    have hme : m1 = m2 := by omega
    subst hme; omega

/-- Construct Sol 2 `ValidTail fam.h (4 * (q + 1) + fam.R)` for any verified `OddTailData`. -/
def oddTail2Valid (fam : OddTailData) (hchk : checkOddTailData fam = true) (q : ℕ) :
    ValidTail fam.h (4 * (q + 1) + fam.R) := by
  have C := unpack_odd hchk
  have hd := C.hd; have hdR := C.hdR
  have he1s1 := C.he1s1; have hs1e1 := C.hs1e1; have he2s2 := C.he2s2; have hs2e2 := C.hs2e2
  have hs1p := C.hs1_pos; have hs2p := C.hs2_pos
  have hc1a2_ev : (mkOddParams fam).e1_0 + fam.R + 8 ≤ (mkOddParams fam).e2_0 + 8 := by
    unfold mkOddParams; dsimp only; omega
  have hc1a2_od : (mkOddParams fam).e1_0 + fam.R + 7 ≤ (mkOddParams fam).e2_0 + 7 := by
    unfold mkOddParams; dsimp only; omega
  have hsym : ∀ i : ℕ,
      (i : ℤ) + (oddTail2Col fam q i : ℤ) + tailDelta i (oddTail2Col fam q i) =
        match i % 4 with
        | 0 => ((2 * (2 * (i / 4) + odd2U0 fam q (i / 4) + 1) + 1 : ℕ) : ℤ)
        | 1 => ((2 * (2 * (i / 4) + odd2U1 fam q (i / 4)) + 1 : ℕ) : ℤ)
        | 2 => ((2 * (2 * (i / 4) + odd2U2 fam q (i / 4) + 1) : ℕ) : ℤ)
        | _ => ((2 * (2 * (i / 4) + odd2U3 fam q (i / 4) + 2) : ℕ) : ℤ) := by
    intro i; unfold oddTail2Col
    set j := i / 4
    have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    rcases hk with h | h | h | h
    · simp only [h]; rw [show i = 4 * j by omega]; exact tailDelta_mod0_odd j _
    · simp only [h]; rw [show i = 4 * j + 1 by omega]; exact tailDelta_mod1_even j _
    · simp only [h]; rw [show i = 4 * j + 2 by omega]; exact tailDelta_mod2_even j _
    · simp only [h]; rw [show i = 4 * j + 3 by omega]; exact tailDelta_mod3_odd j _
  refine {
    col := oddTail2Col fam q
    col_lt := fun i hi => by
      have hlt := odd2U_lt C q (i / 4) (by omega)
      unfold oddTail2Col
      have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      rcases hk with h | h | h | h <;> simp only [h] <;> omega
    col_inj := fun i₁ hi₁ i₂ hi₂ heq => by
      unfold oddTail2Col at heq
      have hk1 : i₁ % 4 = 0 ∨ i₁ % 4 = 1 ∨ i₁ % 4 = 2 ∨ i₁ % 4 = 3 := by omega
      have hk2 : i₂ % 4 = 0 ∨ i₂ % 4 = 1 ∨ i₂ % 4 = 2 ∨ i₂ % 4 = 3 := by omega
      rcases hk1 with k1 | k1 | k1 | k1 <;> rcases hk2 with k2 | k2 | k2 | k2 <;>
        simp only [k1, k2] at heq
      · have := odd2U0_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · omega
      · omega
      · exfalso; exact odd2_od_disj C q (odd2U0 fam q (i₁ / 4)) (odd2U0_class C q _ (by omega))
          (by rw [show odd2U0 fam q (i₁ / 4) = odd2U3 fam q (i₂ / 4) by omega]; exact odd2U3_class C q _ (by omega))
      · omega
      · have := odd2U1_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · exfalso; exact odd2_od_disj C q (odd2U2 fam q (i₂ / 4)) (odd2U2_class C q _ (by omega))
          (by rw [show odd2U2 fam q (i₂ / 4) = odd2U1 fam q (i₁ / 4) by omega]; exact odd2U1_class C q _ (by omega))
      · omega
      · omega
      · exfalso; exact odd2_od_disj C q (odd2U2 fam q (i₁ / 4)) (odd2U2_class C q _ (by omega))
          (by rw [show odd2U2 fam q (i₁ / 4) = odd2U1 fam q (i₂ / 4) by omega]; exact odd2U1_class C q _ (by omega))
      · have := odd2U2_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · omega
      · exfalso; exact odd2_od_disj C q (odd2U0 fam q (i₂ / 4)) (odd2U0_class C q _ (by omega))
          (by rw [show odd2U0 fam q (i₂ / 4) = odd2U3 fam q (i₁ / 4) by omega]; exact odd2U3_class C q _ (by omega))
      · omega
      · omega
      · have := odd2U3_inj C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
    sym_band := fun i hi => by
      dsimp only; rw [hsym i]
      have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      have he1 : (mkOddParams fam).e1_0 = fam.R - (mkOddParams fam).d := rfl
      have he2 : (mkOddParams fam).e2_0 = 2 * fam.R + (mkOddParams fam).d + 1 := rfl
      rcases hk with h | h | h | h <;> simp only [h]
      · refine oddBand_odd_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd2U0_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨ji, hji, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * ji) (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
      · refine oddBand_odd_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd2U1_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨ji, hji, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_od, by omega, by omega, by omega⟩ (C.hs2od_g (2 * ji + 1) (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
      · refine oddBand_even_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd2U2_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨ji, hji, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g ji (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
      · refine oddBand_even_int hd hdR ?_
        rw [← he1, ← he2]
        rcases odd2U3_cases C q (i / 4) (by omega) with ⟨hb1, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨hb1, hb2, _, hhs⟩ | ⟨m, hm, _, _, hhs⟩
        · left; omega
        · right; omega
        · left; omega
        · right; omega
        · have hg := (inSGaps_spec (q := q) ⟨by omega, by omega, by omega, hc1a2_ev, by omega, by omega, by omega⟩ (C.hs2ev_g (fam.R + m) (by omega))).1
          rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> [left; right] <;> omega
    sym_inj := fun i₁ hi₁ i₂ hi₂ heq => by
      rw [hsym i₁, hsym i₂] at heq
      have hk1 : i₁ % 4 = 0 ∨ i₁ % 4 = 1 ∨ i₁ % 4 = 2 ∨ i₁ % 4 = 3 := by omega
      have hk2 : i₂ % 4 = 0 ∨ i₂ % 4 = 1 ∨ i₂ % 4 = 2 ∨ i₂ % 4 = 3 := by omega
      rcases hk1 with k1 | k1 | k1 | k1 <;> rcases hk2 with k2 | k2 | k2 | k2 <;>
        (simp only [k1, k2] at heq; replace heq := Int.ofNat.inj heq)
      · have := odd2_hs00 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · exact False.elim (odd2_hs01 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega))
      · omega
      · omega
      · exact False.elim (odd2_hs01 C q (j₁ := i₂ / 4) (j₂ := i₁ / 4) (by omega) (by omega) (by omega))
      · have := odd2_hs11 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · omega
      · omega
      · omega
      · omega
      · have := odd2_hs22 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
      · exact False.elim (odd2_hs23 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega))
      · omega
      · omega
      · exact False.elim (odd2_hs23 C q (j₁ := i₂ / 4) (j₂ := i₁ / 4) (by omega) (by omega) (by omega))
      · have := odd2_hs33 C q (j₁ := i₁ / 4) (j₂ := i₂ / 4) (by omega) (by omega) (by omega); omega
  }

/-- Sol 1 and Sol 2 of any verified `OddTailData` are completely disjoint for every `q : ℕ`. -/
theorem oddTail_disjoint (fam : OddTailData) (hchk : checkOddTailData fam = true) (q : ℕ) :
    ∀ i < 4 * (4 * (q + 1) + fam.R),
      (oddTail1Valid fam hchk q).col i ≠ (oddTail2Valid fam hchk q).col i := by
  have C := unpack_odd hchk
  have h12 := C.hU12; have h20 := C.hU20; have h03 := C.hU03; have h3R := C.hU3R
  have hj31 := C.hj31; have hj1R := C.hj1R
  intro i hi heq
  change oddTail1Col fam q i = oddTail2Col fam q i at heq
  unfold oddTail1Col oddTail2Col at heq
  set j := i / 4
  have hj : j < 4 * (q + 1) + fam.R := by omega
  have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hk with h | h | h | h <;> simp only [h] at heq
  · -- k = 0: odd1U0 fam q j = odd2U0 fam q j
    have hu : odd1U0 fam q j = odd2U0 fam q j := by omega
    have hcl1 := odd1U0_class C q j hj
    rcases odd2U0_cases C q j hj with c2 | c2 | c2 | c2 | ⟨ji, hji, hj_eq, hu2, _⟩
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd1U0 fam q j) := by
        rw [hu]; unfold inUBlockOdd; right; right; left; omega
      rcases hcl1 with he | ⟨a, ha, hae⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hae] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s1Ev_fst_lt C ha) ho
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd1U0 fam q j) := by
        rw [hu]; unfold inUBlockOdd; right; right; right; omega
      rcases hcl1 with he | ⟨a, ha, hae⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hae] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s1Ev_fst_lt C ha) ho
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd1U0 fam q j) := by
        rw [hu]; unfold inUBlockOdd; left; omega
      rcases hcl1 with he | ⟨a, ha, hae⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hae] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s1Ev_fst_lt C ha) ho
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd1U0 fam q j) := by
        rw [hu]; unfold inUBlockOdd; right; left; omega
      rcases hcl1 with he | ⟨a, ha, hae⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hae] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s1Ev_fst_lt C ha) ho
    · -- Gap ji < R: odd1U0 at j = evalRJ ji equals evalUA1 (s1OdA ji)
      have hu1_eq : odd1U0 fam q j = evalUA1 fam q (fam.s1OdA.getD ji 0) := by
        unfold evalRJ rjSlope at hj_eq
        unfold odd1U0; dsimp only
        by_cases c1 : ji < (mkOddParams fam).j3_0
        · rw [if_pos c1] at hj_eq
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact congrArg (fun k => evalUA1 fam q (fam.s1OdA.getD k 0)) (by omega)
        · by_cases c2 : ji < (mkOddParams fam).j1_0
          · rw [if_neg c1, if_pos c2] at hj_eq
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_pos (by omega)]
            exact congrArg (fun k => evalUA1 fam q (fam.s1OdA.getD k 0)) (by omega)
          · rw [if_neg c1, if_neg c2] at hj_eq
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_pos (by omega)]
            exact congrArg (fun k => evalUA1 fam q (fam.s1OdA.getD k 0)) (by omega)
      set a := fam.s1OdA.getD ji 0
      have sa := evalUA1_spec C q a (C.hs1oda_lt ji (by omega)); dsimp only at sa
      by_cases haR : a < fam.R
      · rw [hu1_eq, sa.2.1 haR, hu2] at hu
        exact C.hdisj_0 ji hji haR (evalRU_inj h12 h20 h03 hu)
      · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s2Od_fst_lt C hji)
        have ha_lt := C.hs1oda_lt ji (by omega)
        rcases (by omega : a = fam.R ∨ a = fam.R + 1 ∨ a = fam.R + 2 ∨ a = fam.R + 3) with h0 | h1 | h2 | h3
        · rw [hu1_eq, sa.2.2.1 h0, hu2] at hu; omega
        · rw [hu1_eq, sa.2.2.2.1 h1, hu2] at hu; omega
        · rw [hu1_eq, sa.2.2.2.2.1 h2, hu2] at hu; omega
        · rw [hu1_eq, sa.2.2.2.2.2 h3, hu2] at hu; omega
  · -- k = 1: odd1U1 fam q j = odd2U1 fam q j
    have hu : odd1U1 fam q j = odd2U1 fam q j := by omega
    unfold odd1U1 odd2U1 at hu; dsimp only at hu
    split_ifs at hu with h1 h2 h3 h4 h5 h6
    · omega
    · exact C.hdisj_1 (j - (q + 1)) (by omega) (evalRU_inj h12 h20 h03 hu)
    · omega
    · exact C.hdisj_1 (j - 2 * (q + 1)) (by omega) (evalRU_inj h12 h20 h03 hu)
    · omega
    · exact C.hdisj_1 (j - 3 * (q + 1)) (by omega) (evalRU_inj h12 h20 h03 hu)
    · omega
  · -- k = 2: odd1U2 fam q j = odd2U2 fam q j
    have hu : odd1U2 fam q j = odd2U2 fam q j := by omega
    unfold odd1U2 odd2U2 at hu; dsimp only at hu
    split_ifs at hu with h1 h2 h3 h4 h5 h6
    · omega
    · exact C.hdisj_2 (j - (q + 1)) (by omega) (evalRU_inj h12 h20 h03 hu)
    · omega
    · exact C.hdisj_2 (j - 2 * (q + 1)) (by omega) (evalRU_inj h12 h20 h03 hu)
    · omega
    · exact C.hdisj_2 (j - 3 * (q + 1)) (by omega) (evalRU_inj h12 h20 h03 hu)
    · omega
  · -- k = 3: odd1U3 fam q j = odd2U3 fam q j
    have hu : odd1U3 fam q j = odd2U3 fam q j := by omega
    have hcl2 := odd2U3_class C q j hj
    rcases odd1U3_cases C q j hj with c1 | c1 | c1 | c1 | ⟨ji, hji, hj_eq, hu1, _⟩
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd2U3 fam q j) := by
        rw [← hu]; unfold inUBlockOdd; right; right; left; omega
      rcases hcl2 with he | ⟨b, hb, hbe⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hbe] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s2Od_snd_lt C hb) ho
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd2U3 fam q j) := by
        rw [← hu]; unfold inUBlockOdd; right; right; right; omega
      rcases hcl2 with he | ⟨b, hb, hbe⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hbe] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s2Od_snd_lt C hb) ho
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd2U3 fam q j) := by
        rw [← hu]; unfold inUBlockOdd; left; omega
      rcases hcl2 with he | ⟨b, hb, hbe⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hbe] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s2Od_snd_lt C hb) ho
    · have ho : inUBlockOdd (mkOddParams fam) (q + 1) (odd2U3 fam q j) := by
        rw [← hu]; unfold inUBlockOdd; right; left; omega
      rcases hcl2 with he | ⟨b, hb, hbe⟩
      · exact inUBlockEven_not_odd h12 h20 h03 he ho
      · rw [hbe] at ho; exact evalRU_not_odd_block h12 h20 h03 h3R (s2Od_snd_lt C hb) ho
    · -- Gap ji < R: odd2U3 at j = evalRJ ji equals evalUB2 (s2EvB ji)
      have hu2_eq : odd2U3 fam q j = evalUB2 fam q (fam.s2EvB.getD ji 0) := by
        unfold evalRJ rjSlope at hj_eq
        unfold odd2U3; dsimp only
        by_cases c1 : ji < (mkOddParams fam).j3_0
        · rw [if_pos c1] at hj_eq
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact congrArg (fun k => evalUB2 fam q (fam.s2EvB.getD k 0)) (by omega)
        · by_cases c2 : ji < (mkOddParams fam).j1_0
          · rw [if_neg c1, if_pos c2] at hj_eq
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_pos (by omega)]
            exact congrArg (fun k => evalUB2 fam q (fam.s2EvB.getD k 0)) (by omega)
          · rw [if_neg c1, if_neg c2] at hj_eq
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_pos (by omega)]
            exact congrArg (fun k => evalUB2 fam q (fam.s2EvB.getD k 0)) (by omega)
      set b := fam.s2EvB.getD ji 0
      have sb := evalUB2_spec C q b (C.hs2evb_lt ji (by omega)); dsimp only at sb
      by_cases hbR : b < fam.R
      · rw [hu1, hu2_eq, sb.2.1 hbR] at hu
        exact C.hdisj_3 ji hji hbR (evalRU_inj h12 h20 h03 hu)
      · have hnb := evalRU_not_in_blocks h12 h20 h03 h3R (p := q + 1) (s1Ev_snd_lt C hji)
        have hb_lt := C.hs2evb_lt ji (by omega)
        rcases (by omega : b = fam.R ∨ b = fam.R + 1 ∨ b = fam.R + 2 ∨ b = fam.R + 3) with h0 | h1 | h2 | h3
        · rw [hu1, hu2_eq, sb.2.2.1 h0] at hu; omega
        · rw [hu1, hu2_eq, sb.2.2.2.1 h1] at hu; omega
        · rw [hu1, hu2_eq, sb.2.2.2.2.1 h2] at hu; omega
        · rw [hu1, hu2_eq, sb.2.2.2.2.2 h3] at hu; omega

theorem checkOddTail_2 : checkOddTailData oddTail_2 = true := by decide
theorem checkOddTail_6 : checkOddTailData oddTail_6 = true := by decide
theorem checkOddTail_10 : checkOddTailData oddTail_10 = true := by decide
theorem checkOddTail_14 : checkOddTailData oddTail_14 = true := by decide

end GhafariWanless
