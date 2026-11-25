import Conjectures.StableKneserK3.TransversalCertificate

namespace StableKneserK3

open TransversalCertificate

set_option Elab.async false

namespace TransversalData

variable {V : Type*} [DecidableEq V]

private def points (bits : ℕ) : TripleSet := Finset.univ.filter (fun x => bits.testBit x.val)

private theorem node10 : Refutes (V := V) [points 11,points 21,points 14,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 5 (by decide) (by decide +kernel) [[points 7],[points 11],[points 13],[points 14],[points 19],[points 21],[points 22],[points 25],[points 26],[points 28]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node9 : Refutes (V := V) [points 21,points 14,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 20) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 11] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node10

private theorem node12 : Refutes (V := V) [points 42,points 52,points 14,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 13],[points 14],[points 19],[points 22],[points 25],[points 26],[points 28],[points 42],[points 52]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node11 : Refutes (V := V) [points 52,points 14,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 20) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 42] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node12

private theorem node8 : Refutes (V := V) [points 14,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 21,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node9
  · exact node11

private theorem node14 : Refutes (V := V) [points 49,points 42,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13],[points 19],[points 22],[points 25],[points 26],[points 28],[points 42],[points 49]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node15 : Refutes (V := V) [points 52,points 42,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,1,0,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node14

private theorem node13 : Refutes (V := V) [points 42,points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 49,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node14
  · exact node15

private theorem node7 : Refutes (V := V) [points 19,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 17) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 14,points 42] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node8
  · exact node13

private theorem node17 : Refutes (V := V) [points 42,points 49,points 13,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13],[points 19,points 44],[points 22],[points 25],[points 26],[points 28],[points 42],[points 49]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node19 : Refutes (V := V) [points 11,points 44,points 49,points 13,points 22,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,0,1,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node14

private theorem node20 : Refutes (V := V) [points 42,points 44,points 49,points 13,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13],[points 22],[points 25],[points 26],[points 28],[points 42],[points 44],[points 49]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node18 : Refutes (V := V) [points 44,points 49,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 20) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 11,points 42] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node19
  · exact node20

private theorem node16 : Refutes (V := V) [points 49,points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 17) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 42,points 44] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node17
  · exact node18

private theorem node6 : Refutes (V := V) [points 13,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 19,points 49] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node7
  · exact node16

private theorem node23 : Refutes (V := V) [points 11,points 49,points 44,points 22,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node17

private theorem node24 : Refutes (V := V) [points 42,points 49,points 44,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13,points 50],[points 22],[points 25],[points 26],[points 28],[points 42],[points 44],[points 49]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node22 : Refutes (V := V) [points 49,points 44,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 20) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 11,points 42] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node23
  · exact node24

private theorem node26 : Refutes (V := V) [points 11,points 50,points 44,points 22,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,0,1,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node18

private theorem node27 : Refutes (V := V) [points 42,points 50,points 44,points 22,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,5,3,4,1,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node18

private theorem node29 : Refutes (V := V) [points 84,points 74,points 50,points 44,points 22,points 25,points 26,points 28,points 7] := by
  exact leaf 7 (by decide) (by decide +kernel) [[points 7],[points 14],[points 22],[points 25],[points 26],[points 28],[points 44],[points 50],[points 74],[points 84]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node28 : Refutes (V := V) [points 74,points 50,points 44,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 7 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 84] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node29

private theorem node25 : Refutes (V := V) [points 50,points 44,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 20) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 11,points 42,points 74] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node26
  · exact node27
  · exact node28

private theorem node21 : Refutes (V := V) [points 44,points 22,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 49,points 50] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node22
  · exact node25

private theorem node5 : Refutes (V := V) [points 22,points 25,points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 18) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 13,points 44] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node6
  · exact node21

private theorem node32 : Refutes (V := V) [points 14,points 41,points 50,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node22

private theorem node34 : Refutes (V := V) [points 49,points 42,points 41,points 50,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 19,points 44],[points 25],[points 26],[points 28],[points 41],[points 42],[points 49],[points 50]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node35 : Refutes (V := V) [points 52,points 42,points 41,points 50,points 25,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 14,points 49],[points 19,points 44],[points 25],[points 26],[points 28],[points 41],[points 42],[points 50],[points 52]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node33 : Refutes (V := V) [points 42,points 41,points 50,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 49,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node34
  · exact node35

private theorem node37 : Refutes (V := V) [points 21,points 44,points 41,points 50,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,0,2,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node24

private theorem node38 : Refutes (V := V) [points 49,points 44,points 41,points 50,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,0,2,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node35

private theorem node39 : Refutes (V := V) [points 52,points 44,points 41,points 50,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node35

private theorem node36 : Refutes (V := V) [points 44,points 41,points 50,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 21,points 49,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node37
  · exact node38
  · exact node39

private theorem node41 : Refutes (V := V) [points 81,points 74,points 41,points 50,points 25,points 26,points 28,points 7] := by
  exact leaf 7 (by decide) (by decide +kernel) [[points 7],[points 11],[points 19],[points 25],[points 26],[points 28],[points 41],[points 50],[points 74],[points 81]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node40 : Refutes (V := V) [points 74,points 41,points 50,points 25,points 26,points 28,points 7] := by
  apply branch 7 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 81] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node41

private theorem node31 : Refutes (V := V) [points 41,points 50,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 17) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 14,points 42,points 44,points 74] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact node32
  · exact node33
  · exact node36
  · exact node40

private theorem node42 : Refutes (V := V) [points 44,points 50,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,2,0,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node31

private theorem node30 : Refutes (V := V) [points 50,points 25,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 18) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 41,points 44] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node31
  · exact node42

private theorem node43 : Refutes (V := V) [points 52,points 25,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node30

private theorem node4 : Refutes (V := V) [points 25,points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 22,points 50,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node5
  · exact node30
  · exact node43

private theorem node47 : Refutes (V := V) [points 19,points 21,points 38,points 41,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13,points 50],[points 14,points 49],[points 19],[points 21],[points 26],[points 28],[points 38],[points 41]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node48 : Refutes (V := V) [points 49,points 21,points 38,points 41,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13,points 50],[points 19,points 44],[points 21],[points 26],[points 28],[points 38],[points 41],[points 49]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node49 : Refutes (V := V) [points 50,points 21,points 38,points 41,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 14,points 49],[points 19,points 44],[points 21],[points 26],[points 28],[points 38],[points 41],[points 50]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node46 : Refutes (V := V) [points 21,points 38,points 41,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 19,points 49,points 50] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node47
  · exact node48
  · exact node49

private theorem node50 : Refutes (V := V) [points 49,points 38,points 41,points 26,points 28,points 7] := by
  exact leaf 6 (by decide) (by decide +kernel) [[points 7],[points 11,points 52],[points 13,points 50],[points 19,points 44],[points 21,points 42],[points 26],[points 28],[points 38],[points 41],[points 49]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node51 : Refutes (V := V) [points 52,points 38,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[5,1,2,3,4,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node46

private theorem node45 : Refutes (V := V) [points 38,points 41,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 21,points 49,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node46
  · exact node50
  · exact node51

private theorem node53 : Refutes (V := V) [points 21,points 50,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[3,1,4,0,2,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node46

private theorem node54 : Refutes (V := V) [points 49,points 50,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,3,4,0,5,2,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node46

private theorem node56 : Refutes (V := V) [points 14,points 52,points 50,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[3,1,2,5,4,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node47

private theorem node57 : Refutes (V := V) [points 38,points 52,points 50,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[5,1,2,3,4,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node47

private theorem node58 : Refutes (V := V) [points 42,points 52,points 50,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,3,5,2,4,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node47

private theorem node59 : Refutes (V := V) [points 44,points 52,points 50,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,3,5,1,4,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node47

private theorem node55 : Refutes (V := V) [points 52,points 50,points 41,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 17) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 14,points 38,points 42,points 44] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact node56
  · exact node57
  · exact node58
  · exact node59

private theorem node61 : Refutes (V := V) [points 74,points 81,points 50,points 41,points 26,points 28,points 7] := by
  exact leaf 7 (by decide) (by decide +kernel) [[points 7],[points 11],[points 19],[points 25],[points 26],[points 28],[points 41],[points 50],[points 74],[points 81]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node60 : Refutes (V := V) [points 81,points 50,points 41,points 26,points 28,points 7] := by
  apply branch 7 (by decide) (points 17) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 74] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node61

private theorem node52 : Refutes (V := V) [points 50,points 41,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 21,points 49,points 52,points 81] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact node53
  · exact node54
  · exact node55
  · exact node60

private theorem node62 : Refutes (V := V) [points 52,points 41,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node52

private theorem node44 : Refutes (V := V) [points 41,points 26,points 28,points 7] := by
  apply branch 6 (by decide) (points 9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 38,points 50,points 52] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node45
  · exact node52
  · exact node62

private theorem node63 : Refutes (V := V) [points 49,points 26,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,1,2,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node44

private theorem node3 : Refutes (V := V) [points 26,points 28,points 7] := by
  apply branch 5 (by decide) (points 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 25,points 41,points 49] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node4
  · exact node44
  · exact node63

private theorem node65 : Refutes (V := V) [points 25,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,0,2,3,4,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node44

private theorem node66 : Refutes (V := V) [points 41,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,0,1,3,5,4,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node44

private theorem node68 : Refutes (V := V) [points 22,points 49,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[5,1,3,4,2,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node52

private theorem node69 : Refutes (V := V) [points 38,points 49,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[4,2,3,5,1,0,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node52

private theorem node70 : Refutes (V := V) [points 50,points 49,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[2,1,0,4,5,3,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node52

private theorem node71 : Refutes (V := V) [points 52,points 49,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,2,0,5,4,3,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node52

private theorem node73 : Refutes (V := V) [points 73,points 82,points 49,points 42,points 28,points 7] := by
  exact leaf 7 (by decide) (by decide +kernel) [[points 7],[points 11],[points 19],[points 25],[points 26,points 100],[points 28],[points 42],[points 49],[points 73],[points 82]]
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem node74 : Refutes (V := V) [points 100,points 82,points 49,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[1,2,0,4,5,3,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node73

private theorem node72 : Refutes (V := V) [points 82,points 49,points 42,points 28,points 7] := by
  apply branch 7 (by decide) (points 18) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 73,points 100] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node73
  · exact node74

private theorem node75 : Refutes (V := V) [points 100,points 49,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,3,5,4,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node72

private theorem node67 : Refutes (V := V) [points 49,points 42,points 28,points 7] := by
  apply branch 6 (by decide) (points 9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 22,points 38,points 50,points 52,points 82,points 100] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact node68
  · exact node69
  · exact node70
  · exact node71
  · exact node72
  · exact node75

private theorem node78 : Refutes (V := V) [points 37,points 70,points 73,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[3,0,6,1,2,5,4,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node60

private theorem node79 : Refutes (V := V) [points 100,points 70,points 73,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[3,1,5,6,2,0,4,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node60

private theorem node77 : Refutes (V := V) [points 70,points 73,points 42,points 28,points 7] := by
  apply branch 7 (by decide) (points 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 37,points 100] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact node78
  · exact node79

private theorem node80 : Refutes (V := V) [points 82,points 73,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,1,2,4,3,6,5,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node72

private theorem node81 : Refutes (V := V) [points 100,points 73,points 42,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,2,1,5,3,6,4,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node72

private theorem node76 : Refutes (V := V) [points 73,points 42,points 28,points 7] := by
  apply branch 7 (by decide) (points 9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 70,points 82,points 100] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node77
  · exact node80
  · exact node81

private theorem node64 : Refutes (V := V) [points 42,points 28,points 7] := by
  apply branch 6 (by decide) (points 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 25,points 41,points 49,points 73] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact node65
  · exact node66
  · exact node67
  · exact node76

private theorem node82 : Refutes (V := V) [points 50,points 28,points 7] := by
  let f (i : Point) : Point := #v[0,1,2,4,3,5,6,7,8,9][i]
  exact rename ⟨f, by unfold Function.Injective; decide +kernel⟩ (by decide +kernel) node64

private theorem node2 : Refutes (V := V) [points 28,points 7] := by
  apply branch 5 (by decide) (points 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 26,points 42,points 50] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact node3
  · exact node64
  · exact node82

private theorem node1 : Refutes (V := V) [points 7] := by
  apply branch 3 (by decide) (points 3) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 28] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node2

private theorem node0 : Refutes (V := V) [] := by
  apply branch 0 (by decide) (∅) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [points 7] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact node1

end TransversalData

/-- Every intersecting triple family without a transversal pair has at most ten members. -/
theorem no_pair_bound_ten {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}
    (hu : ∀ t ∈ F, t.card = 3) (hi : (F : Set (Finset V)).Intersecting)
    (ht : ¬PairTransversal F) : F.card ≤ 10 := by
  classical
  obtain hF | nonempty := F.eq_empty_or_nonempty
  · simp [hF]
  let e : V ↪ V ⊕ Point := Function.Embedding.inl
  let H := F.image (Finset.map e)
  have hcard : H.card = F.card := Finset.card_image_of_injective _ (Finset.map_injective e)
  rw [← hcard]
  apply TransversalData.node0 H Function.Embedding.inr
  · intro t h
    obtain ⟨u,hu',rfl⟩ := Finset.mem_image.mp h
    simpa using hu u hu'
  · intro s hs t ht' hd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ht'
    exact hi ha hb ((Finset.disjoint_map e).mp hd)
  · rintro ⟨x,y,hxy,hcov⟩
    have two (a : V) : ∃ b : V, a ≠ b := by
      by_contra! hall
      obtain ⟨s,hs⟩ := nonempty
      have hsub : s ⊆ {a} := fun x _ => Finset.mem_singleton.mpr (hall x).symm
      have hh := Finset.card_le_card hsub
      simp [hu s hs] at hh
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        apply ht ⟨a,b,fun h => hxy (congrArg Sum.inl h),?_⟩
        intro s hs
        simpa [e] using hcov (s.map e) (Finset.mem_image_of_mem _ hs)
      | inr j =>
        obtain ⟨b,hab⟩ := two a
        apply ht ⟨a,b,hab,?_⟩
        intro s hs
        exact Or.inl (by simpa [e] using hcov (s.map e) (Finset.mem_image_of_mem _ hs))
    | inr j =>
      cases y with
      | inl a =>
        obtain ⟨b,hab⟩ := two a
        apply ht ⟨a,b,hab,?_⟩
        intro s hs
        exact Or.inl (by simpa [e] using hcov (s.map e) (Finset.mem_image_of_mem _ hs))
      | inr k =>
        obtain ⟨s,hs⟩ := nonempty
        simpa [e] using hcov (s.map e) (Finset.mem_image_of_mem _ hs)
  · simp

end StableKneserK3
