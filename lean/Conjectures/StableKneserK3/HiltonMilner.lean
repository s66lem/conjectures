import Conjectures.StableKneserK3.TransversalBound

namespace StableKneserK3

open Finset

/-- The Hilton–Milner bound for nonstar intersecting triples on at least six points. -/
theorem hiltonMilner {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}
    (hn : 6 ≤ Fintype.card V) (hu : ∀ t ∈ F, t.card = 3)
    (hi : (F : Set (Finset V)).Intersecting) (hns : ∀ x, ∃ t ∈ F, x ∉ t) :
    F.card ≤ 3 * Fintype.card V - 8 := by
  classical
  by_cases h : Fintype.card V = 6
  · let e : Finset V ↪ Finset V := ⟨compl,compl_injective⟩
    have sub : F ∪ F.map e ⊆ univ.powersetCard 3 := by
      intro s hs
      refine mem_powersetCard.mpr ⟨subset_univ _,?_⟩
      rcases mem_union.mp hs with hs | hs
      · exact hu s hs
      · obtain ⟨t,ht,rfl⟩ := mem_map.mp hs
        change tᶜ.card = 3
        rw [card_compl, h, hu t ht]
    have hle := card_le_card sub
    rw [card_union_of_disjoint hi.disjoint_map_compl,card_map,card_powersetCard,card_univ,h] at hle
    rw [h]
    change F.card + F.card ≤ 20 at hle
    omega
  by_cases hp : PairTransversal F
  · exact hiltonMilner_of_pair (by omega) hu hi hns hp
  · have := no_pair_bound_ten hu hi hp
    omega

end StableKneserK3

