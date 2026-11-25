import Conjectures.StableKneserK3.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.IntervalCases

namespace StableKneserK3

open Finset SimpleGraph

variable {V W : Type*}

/-- Check a cover by explicitly supplied intersecting families. -/
private theorem of_cover [Fintype V] [DecidableEq V] (G : SimpleGraph V) {q : ℕ}
    (C : Fin q → List (Finset V))
    (hcover : ∀ s ∈ (univ : Finset V).powersetCard 3,
      (∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y) → ∃ i, s ∈ C i)
    (hinter : ∀ i, ∀ s ∈ C i, ∀ t ∈ C i, ¬ Disjoint s t) : Colorable G q := by
  classical
  have h (s : Triple G) : ∃ i, s.val ∈ C i :=
    hcover _ (mem_powersetCard.mpr ⟨subset_univ _, s.property.1⟩) s.property.2
  refine ⟨fun s => (h s).choose, fun s t hd heq => ?_⟩
  apply hinter _ _ (h s).choose_spec _ _ hd
  change (h s).choose = (h t).choose at heq
  rw [heq]
  exact (h t).choose_spec

private abbrev padded (H : SimpleGraph W) (r : ℕ) := H.sum (⊥ : SimpleGraph (Fin r))

private instance {H : SimpleGraph W} [DecidableRel H.Adj] {r : ℕ} :
    DecidableRel (padded H r).Adj
  | .inl _, .inl _ => inferInstanceAs (Decidable (H.Adj _ _))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)
  | .inl _, .inr _ | .inr _, .inl _ => inferInstanceAs (Decidable (false = true))

private theorem lift_obstruction [Fintype V] [Fintype W] {H : SimpleGraph W}
    {G : SimpleGraph V} (f : W ↪ V) (hf : ∀ ⦃x y⦄, H.Adj x y → G.Adj (f x) (f y))
    {r : ℕ} (hsize : Fintype.card W + r ≤ Fintype.card V) (hmin : 5 ≤ Fintype.card W + r)
    (hc : Colorable (padded H r) (Fintype.card W + r - 5)) :
    Colorable G (Fintype.card V - 5) := by
  classical
  let P := fun x : V => x ∈ Set.range f
  have hP : Fintype.card {x // ¬P x} = Fintype.card V - Fintype.card W :=
    (Fintype.card_subtype_compl P).trans (congrArg (Fintype.card V - ·) (Fintype.card_range f))
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := {x // ¬P x}) (by rw [hP, Fintype.card_fin]; omega)
  let emb := ((Equiv.ofInjective f f.injective).toEmbedding.sumMap g).trans
    (Equiv.sumCompl P).toEmbedding
  have he : ∀ ⦃x y⦄, (padded H r).Adj x y → G.Adj (emb x) (emb y) := by
    rintro (x | x) (y | y) h
    · exact hf h
    · cases h
    · cases h
    · cases h
  have h := colorable_of_subgraph emb he hc
  rw [Fintype.card_sum, Fintype.card_fin] at h
  convert h using 1
  omega

/-- The claw with center zero. -/
private def claw : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun x y => x = 0 ∧ y ≠ 0)

private instance : DecidableRel claw.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ((x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0))))


private theorem claw_colorable : Colorable (padded claw 3) 2 := by
  let a (x : Fin 7) : Fin 4 ⊕ Fin 3 := finSumFinEquiv.symm x
  let C : Fin 2 → List (Finset (Fin 4 ⊕ Fin 3))
    | 0 => [{a 0, a 4, a 5}, {a 0, a 4, a 6}, {a 0, a 5, a 6}, {a 1, a 4, a 5},
      {a 1, a 4, a 6}, {a 1, a 5, a 6}, {a 2, a 4, a 5}, {a 2, a 4, a 6},
      {a 2, a 5, a 6}, {a 3, a 4, a 5}, {a 3, a 4, a 6}, {a 3, a 5, a 6},
      {a 4, a 5, a 6}]
    | _ => [{a 1, a 2, a 3}, {a 1, a 2, a 4}, {a 1, a 2, a 5}, {a 1, a 2, a 6},
      {a 1, a 3, a 4}, {a 1, a 3, a 5}, {a 1, a 3, a 6}, {a 2, a 3, a 4},
      {a 2, a 3, a 5}, {a 2, a 3, a 6}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

private theorem cycle3_colorable : Colorable (padded (cycleGraph 3) 4) 2 := by
  let a (x : Fin 7) : Fin 3 ⊕ Fin 4 := finSumFinEquiv.symm x
  let C : Fin 2 → List (Finset (Fin 3 ⊕ Fin 4))
    | 0 => [{a 0, a 3, a 4}, {a 0, a 3, a 5}, {a 0, a 3, a 6}, {a 1, a 3, a 4},
      {a 1, a 3, a 5}, {a 1, a 3, a 6}, {a 2, a 3, a 4}, {a 2, a 3, a 5},
      {a 2, a 3, a 6}, {a 3, a 4, a 5}, {a 3, a 4, a 6}, {a 3, a 5, a 6},
      {a 4, a 5, a 6}]
    | _ => [{a 0, a 4, a 5}, {a 0, a 4, a 6}, {a 0, a 5, a 6}, {a 1, a 4, a 5},
      {a 1, a 4, a 6}, {a 1, a 5, a 6}, {a 2, a 4, a 5}, {a 2, a 4, a 6},
      {a 2, a 5, a 6}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

private theorem cycle4_colorable : Colorable (padded (cycleGraph 4) 3) 2 := by
  let a (x : Fin 7) : Fin 4 ⊕ Fin 3 := finSumFinEquiv.symm x
  let C : Fin 2 → List (Finset (Fin 4 ⊕ Fin 3))
    | 0 => [{a 0, a 2, a 4}, {a 0, a 2, a 5}, {a 0, a 2, a 6}, {a 0, a 4, a 5},
      {a 0, a 4, a 6}, {a 0, a 5, a 6}, {a 2, a 4, a 5}, {a 2, a 4, a 6},
      {a 2, a 5, a 6}, {a 4, a 5, a 6}]
    | _ => [{a 1, a 3, a 4}, {a 1, a 3, a 5}, {a 1, a 3, a 6}, {a 1, a 4, a 5},
      {a 1, a 4, a 6}, {a 1, a 5, a 6}, {a 3, a 4, a 5}, {a 3, a 4, a 6},
      {a 3, a 5, a 6}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

private theorem cycle5_colorable : Colorable (padded (cycleGraph 5) 2) 2 := by
  let a (x : Fin 7) : Fin 5 ⊕ Fin 2 := finSumFinEquiv.symm x
  let C : Fin 2 → List (Finset (Fin 5 ⊕ Fin 2))
    | 0 => [{a 0, a 2, a 5}, {a 0, a 3, a 5}, {a 0, a 5, a 6}, {a 1, a 3, a 5},
      {a 1, a 4, a 5}, {a 1, a 5, a 6}, {a 2, a 4, a 5}, {a 2, a 5, a 6},
      {a 3, a 5, a 6}, {a 4, a 5, a 6}]
    | _ => [{a 0, a 2, a 6}, {a 0, a 3, a 6}, {a 1, a 3, a 6}, {a 1, a 4, a 6},
      {a 2, a 4, a 6}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

private theorem cycle6_colorable : Colorable (padded (cycleGraph 6) 1) 2 := by
  let a (x : Fin 7) : Fin 6 ⊕ Fin 1 := finSumFinEquiv.symm x
  let C : Fin 2 → List (Finset (Fin 6 ⊕ Fin 1))
    | 0 => [{a 0, a 2, a 4}, {a 0, a 2, a 6}, {a 0, a 3, a 6}, {a 0, a 4, a 6},
      {a 1, a 4, a 6}, {a 2, a 4, a 6}, {a 2, a 5, a 6}]
    | _ => [{a 1, a 3, a 5}, {a 1, a 3, a 6}, {a 1, a 5, a 6}, {a 3, a 5, a 6}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

private theorem cycle7_colorable : Colorable (padded (cycleGraph 7) 1) 3 := by
  let a (x : Fin 8) : Fin 7 ⊕ Fin 1 := finSumFinEquiv.symm x
  let C : Fin 3 → List (Finset (Fin 7 ⊕ Fin 1))
    | 0 => [{a 0, a 2, a 4}, {a 0, a 2, a 5}, {a 0, a 2, a 7}, {a 0, a 3, a 5},
      {a 0, a 3, a 7}, {a 0, a 4, a 7}, {a 0, a 5, a 7}, {a 2, a 5, a 7}]
    | 1 => [{a 1, a 4, a 6}, {a 1, a 4, a 7}, {a 2, a 4, a 6}, {a 2, a 4, a 7},
      {a 2, a 6, a 7}, {a 4, a 6, a 7}]
    | _ => [{a 1, a 3, a 5}, {a 1, a 3, a 6}, {a 1, a 3, a 7}, {a 1, a 5, a 7},
      {a 1, a 6, a 7}, {a 3, a 5, a 7}, {a 3, a 6, a 7}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

private theorem cycle8_colorable : Colorable (padded (cycleGraph 8) 1) 4 := by
  let a (x : Fin 9) : Fin 8 ⊕ Fin 1 := finSumFinEquiv.symm x
  let C : Fin 4 → List (Finset (Fin 8 ⊕ Fin 1))
    | 0 => [{a 1, a 3, a 6}, {a 1, a 3, a 7}, {a 1, a 3, a 8}, {a 1, a 4, a 7},
      {a 1, a 4, a 8}, {a 1, a 5, a 7}, {a 1, a 5, a 8}, {a 1, a 7, a 8},
      {a 3, a 7, a 8}]
    | 1 => [{a 0, a 2, a 6}, {a 0, a 3, a 6}, {a 0, a 4, a 6}, {a 0, a 4, a 8},
      {a 0, a 6, a 8}, {a 1, a 4, a 6}, {a 1, a 6, a 8}, {a 2, a 6, a 8},
      {a 3, a 6, a 8}, {a 4, a 6, a 8}]
    | 2 => [{a 0, a 2, a 4}, {a 0, a 2, a 8}, {a 2, a 4, a 6}, {a 2, a 4, a 7},
      {a 2, a 4, a 8}, {a 2, a 5, a 7}, {a 2, a 7, a 8}, {a 4, a 7, a 8}]
    | _ => [{a 0, a 2, a 5}, {a 0, a 3, a 5}, {a 0, a 3, a 8}, {a 0, a 5, a 8},
      {a 1, a 3, a 5}, {a 2, a 5, a 8}, {a 3, a 5, a 7}, {a 3, a 5, a 8},
      {a 5, a 7, a 8}]
  exact of_cover _ C (by decide +kernel) (by decide +kernel)

/-- A vertex of degree at least three saves a color (Theorem 1.2, claw case). -/
theorem colorable_of_degree_ge_three [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 7 ≤ Fintype.card V) (v : V) (hv : 3 ≤ G.degree v) :
    Colorable G (Fintype.card V - 5) := by
  classical
  obtain ⟨leaves, hl⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := G.neighborFinset v) (by simpa using hv)
  have hadj (i : Fin 3) : G.Adj v (leaves i) := (G.mem_neighborFinset _ _).mp (hl ⟨i, rfl⟩)
  have hroot : v ∉ Set.range leaves := by
    rintro ⟨i, h⟩
    exact (hadj i).ne h.symm
  let f : Fin 4 ↪ V := ⟨Fin.cons v leaves, Fin.cons_injective_of_injective hroot leaves.injective⟩
  have he : ∀ ⦃x y⦄, claw.Adj x y → G.Adj (f x) (f y) := by
    intro x y h
    rcases h.2 with ⟨rfl, hy⟩ | ⟨rfl, hx⟩
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hy
      exact hadj i
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hx
      exact (hadj i).symm
  exact lift_obstruction f he (r := 3) (by simpa using hn) (by decide)
    (by simpa using claw_colorable)

/-- An embedded cycle of length at most eight with a vertex outside the cycle saves a color. -/
theorem colorable_of_short_cycle [Fintype V] (G : SimpleGraph V) (hn : 7 ≤ Fintype.card V)
    {m : ℕ} (hm : 3 ≤ m) (hshort : m ≤ 8) (hout : m < Fintype.card V)
    (f : Fin m ↪ V) (hf : ∀ ⦃x y⦄, (cycleGraph m).Adj x y → G.Adj (f x) (f y)) :
    Colorable G (Fintype.card V - 5) := by
  have hc : Colorable (padded (cycleGraph m) (max 7 (m+1) - m)) (max 7 (m+1) - 5) := by
    interval_cases m
    · exact cycle3_colorable
    · exact cycle4_colorable
    · exact cycle5_colorable
    · exact cycle6_colorable
    · exact cycle7_colorable
    · exact cycle8_colorable
  apply lift_obstruction f hf (r := max 7 (m+1) - m)
  · rw [Fintype.card_fin]
    omega
  · rw [Fintype.card_fin]
    omega
  · rw [Fintype.card_fin, show m + (max 7 (m+1) - m) = max 7 (m+1) by omega]
    exact hc

/-- This includes the case of a spanning short cycle with an extra edge. -/
theorem colorable_of_proper_short_cycle [Fintype V] (G : SimpleGraph V)
    (hn : 7 ≤ Fintype.card V) {m : ℕ} (hm : 3 ≤ m) (hshort : m ≤ 8)
    (f : Fin m ↪ V) (hf : ∀ ⦃x y⦄, (cycleGraph m).Adj x y → G.Adj (f x) (f y))
    (hproper : m < Fintype.card V ∨ ∃ x y, G.Adj (f x) (f y) ∧ ¬(cycleGraph m).Adj x y) :
    Colorable G (Fintype.card V - 5) := by
  classical
  obtain hout | ⟨x, y, he, hchord⟩ := hproper
  · exact colorable_of_short_cycle G hn hm hshort hout f hf
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  let N := ((cycleGraph (k + 3)).neighborFinset x).map f
  have hsub : N ⊆ G.neighborFinset (f x) := by
    rintro _ hz
    obtain ⟨z, hz', rfl⟩ := mem_map.mp hz
    exact (G.mem_neighborFinset _ _).mpr (hf (((cycleGraph _).mem_neighborFinset _ _).mp hz'))
  have hlt : N ⊂ G.neighborFinset (f x) := by
    apply Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro h
    have hy := (G.mem_neighborFinset _ _).mpr he
    rw [← h] at hy
    exact hchord (((cycleGraph _).mem_neighborFinset _ _).mp ((mem_map' f).mp hy))
  have hdeg := card_lt_card hlt
  have hN : N.card = 2 := by
    dsimp only [N]
    rw [card_map, card_neighborFinset_eq_degree, cycleGraph_degree_three_le]
  rw [hN] at hdeg
  exact colorable_of_degree_ge_three G hn (f x) hdeg

end StableKneserK3
