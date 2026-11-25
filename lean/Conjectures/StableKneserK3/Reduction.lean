import Conjectures.StableKneserK3.Counting
import Conjectures.StableKneserK3.Intersecting

namespace StableKneserK3

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {q : ℕ}

/-- When a color is contained in a star, deleting its center eliminates that color. -/
theorem delete_star_color (c : Triple G → Fin q) (hc : IsProperColoring G q c)
    (i : Fin q) (x : V) (hstar : ∀ s, c s = i → x ∈ s.val) :
    Colorable (G.induce {v | v ≠ x}) (q-1) := by
  classical
  let f := Function.Embedding.subtype (fun v : V => v ≠ x)
  let lift (s : Triple (G.induce {v | v ≠ x})) : Triple G :=
    ⟨s.val.map f, by simpa using s.property.1, by
      intro a ha b hb hab
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
      exact s.property.2 u hu v hv hab⟩
  have havoid (s) : c (lift s) ≠ i := by
    intro h
    obtain ⟨u, _, he⟩ := mem_map.mp (hstar _ h)
    exact u.property he
  let e := Fintype.equivFinOfCardEq (α := {j : Fin q // j ≠ i}) (n := q-1) (by simp)
  refine ⟨fun s => e ⟨c (lift s),havoid s⟩, fun s t hd heq => ?_⟩
  exact hc (lift s) (lift t) ((disjoint_map f).mpr hd) (congrArg Subtype.val (e.injective heq))

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- At order at least twenty any putative deficient coloring has a star class. -/
theorem large_coloring_has_star (hn : 20 ≤ Fintype.card V)
    (hdeg : ∀ x, G.degree x ≤ 2) (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    (c : Triple G → Fin (Fintype.card V - 5)) (hc : IsProperColoring G _ c) :
    ∃ i x, ∀ s, c s = i → x ∈ s.val := by
  classical
  by_contra! h
  let n := Fintype.card V
  let color (s : Finset V) : Fin (n-5) :=
    if hs : StableTriple G s then c ⟨s,hs⟩ else ⟨0, by dsimp [n]; omega⟩
  have he (t : Triple G) : color t.val = c t := by simp [color, t.property]
  let family (i : Fin (n-5)) := (stableTriples G).filter (fun s => color s = i)
  have hmem {t i} (ht : t ∈ family i) : StableTriple G t :=
    (mem_stableTriples G).mp (mem_filter.mp ht).1
  have hbound (i : Fin (n-5)) : (family i).card ≤ 3*n-8 := by
    apply hiltonMilner_large (by omega : 12 ≤ Fintype.card V) (fun t ht => (hmem ht).1)
    · intro s hs t ht hst
      let u : Triple G := ⟨s,hmem hs⟩
      let v : Triple G := ⟨t,hmem ht⟩
      exact hc u v hst ((he u).symm.trans (((mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm).trans (he v)))
    · intro x
      obtain ⟨s,hs,hx⟩ := h i x
      exact ⟨s.val,mem_filter.mpr ⟨(mem_stableTriples G).mpr s.property, (he s).trans hs⟩,hx⟩
  have cap := card_le_mul_card_image_of_maps_to (s := stableTriples G)
    (f := color) (fun _ _ => mem_univ _) (3*n-8) (fun i _ => hbound i)
  simp only [card_univ, Fintype.card_fin] at cap
  rw [Nat.mul_comm] at cap
  have hl := stableTriple_count_lower G (by omega) hdeg htri
  have hf := hiltonMilner_cutoff hn
  change (stableTriples G).card ≤ (Fintype.card V-5)*(3*Fintype.card V-8) at cap
  omega

/-- A vertex-deletion-minimal failure in this graph class has order at most nineteen. -/
theorem minimal_failure_order_le_nineteen (hdeg : ∀ x, G.degree x ≤ 2)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬G.Adj x z) (hbad : ¬ K3Tight G)
    (hdel : ∀ x : V, K3Tight (G.induce {v | v ≠ x})) : Fintype.card V ≤ 19 := by
  by_contra! hn
  have hc : Colorable G (Fintype.card V-5) := by
    by_contra h
    exact hbad ⟨h,upper_bound G (by omega)⟩
  obtain ⟨c,hc⟩ := hc
  obtain ⟨i,x,hs⟩ := large_coloring_has_star hn hdeg htri c hc
  apply (hdel x).1
  have h := delete_star_color c hc i x hs
  have he : Fintype.card {v : V // v ≠ x} = Fintype.card V - 1 := by simp
  convert h using 1
  change Fintype.card {v : V // v ≠ x} - 5 = Fintype.card V - 5 - 1
  omega

end StableKneserK3

