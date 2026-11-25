import Conjectures.StableKneserK3.Basic
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Powerset

namespace StableKneserK3

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {q : ℕ}

private theorem colorable_omitting (c : Triple G → Fin q) (hc : IsProperColoring G q c)
    (i : Fin q) (hi : ∀ s, c s ≠ i) : Colorable G (q-1) := by
  classical
  let e := Fintype.equivFinOfCardEq (α := {j : Fin q // j ≠ i})
    (n := q-1) (by simp)
  exact ⟨fun s => e ⟨c s, hi s⟩, fun s t hd h => hc s t hd (congrArg Subtype.val (e.injective h))⟩

/-- In each essential color, some triple has a neighbor in every other color. -/
theorem exists_saturated_triple (c : Triple G → Fin q) (hc : IsProperColoring G q c)
    (hmin : ¬ Colorable G (q-1)) (i : Fin q) :
    ∃ s, c s = i ∧ ∀ j ≠ i, ∃ t, Disjoint s.val t.val ∧ c t = j := by
  classical
  by_contra! h
  choose d hd using fun s (hs : c s = i) => h s hs
  let c' (s : Triple G) := if hs : c s = i then d s hs else c s
  have hproper : IsProperColoring G q c' := by
    intro s t hst heq
    dsimp only [c'] at heq
    split at heq <;> split at heq
    · rename_i hs ht
      exact hc s t hst (hs.trans ht.symm)
    · rename_i hs ht
      exact (hd s hs).2 t hst heq.symm
    · rename_i hs ht
      exact (hd t ht).2 s hst.symm heq
    · exact hc s t hst heq
  apply hmin (colorable_omitting c' hproper i ?_)
  intro s
  simp only [c']
  split
  · exact (hd ..).1
  · assumption

/-- An isolated ground vertex adjoined to the original graph. -/
abbrev withIsolate (G : SimpleGraph V) := G.sum (⊥ : SimpleGraph Unit)

def onBase (s : Triple G) : Triple (withIsolate G) := by
  refine ⟨s.val.map Function.Embedding.inl, by simpa using s.property.1, ?_⟩
  intro x hx y hy h
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
  exact s.property.2 a ha b hb h

private theorem disjoint_onBase {s t : Triple G} (h : Disjoint s.val t.val) :
    Disjoint (onBase s).val (onBase t).val := (Finset.disjoint_map _).mpr h

private def isolateTriple [DecidableEq V] (p : Finset V) (hp : p.card = 2)
    (hs : ∀ x ∈ p, ∀ y ∈ p, ¬ G.Adj x y) : Triple (withIsolate G) := by
  let f : V ↪ V ⊕ Unit := Function.Embedding.inl
  refine ⟨insert (.inr ()) (p.map f), ?_, ?_⟩
  · have hz : Sum.inr () ∉ p.map f := by simp [f]
    rw [card_insert_of_notMem hz, card_map, hp]
  · intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
    · exact hxy
    · obtain ⟨b, _, rfl⟩ := mem_map.mp hy
      cases hxy
    · obtain ⟨a, _, rfl⟩ := mem_map.mp hx
      cases hxy
    · obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
      exact hs _ ha _ hb hxy

private theorem disjoint_isolateTriple [DecidableEq V] {p : Finset V}
    {hp : p.card = 2} {hs : ∀ x ∈ p, ∀ y ∈ p, ¬ G.Adj x y}
    {s : Triple G} (h : Disjoint p s.val) :
    Disjoint (isolateTriple p hp hs).val (onBase s).val := by
  change Disjoint (insert (Sum.inr ()) (p.map Function.Embedding.inl)) (s.val.map _)
  simpa [Finset.disjoint_insert_left, Finset.disjoint_map] using h

/-- An optimal coloring extending over an isolate forces a two-point overlap with each anchor. -/
theorem exists_anchors [DecidableEq V] (c : Triple (withIsolate G) → Fin q)
    (hc : IsProperColoring (withIsolate G) q c) (hmin : ¬ Colorable G (q-1)) :
    ∃ A : Fin q → Triple G, ∀ s : Triple G, 2 ≤ (s.val ∩ (A (c (onBase s))).val).card := by
  classical
  let d (s : Triple G) := c (onBase s)
  have hd : IsProperColoring G q d := fun _ _ h => hc _ _ (disjoint_onBase h)
  choose A hA hsat using exists_saturated_triple d hd hmin
  refine ⟨A, fun s => ?_⟩
  let i := d s
  have hmeet : ¬ Disjoint (A i).val s.val := fun h => hd _ _ h (hA i)
  by_contra! hlt
  have hpos : 0 < (s.val ∩ (A i).val).card := card_pos.mpr (by
    rw [inter_comm]
    exact not_disjoint_iff_nonempty_inter.mp hmeet)
  change (s.val ∩ (A i).val).card < 2 at hlt
  have hone : (s.val ∩ (A i).val).card = 1 := by omega
  let p := (A i).val \ s.val
  have hp : p.card = 2 := by
    have := card_sdiff_add_card_inter (A i).val s.val
    rw [inter_comm, hone, (A i).property.1] at this
    change ((A i).val \ s.val).card = 2
    omega
  have hs : ∀ x ∈ p, ∀ y ∈ p, ¬G.Adj x y := fun x hx y hy =>
    (A i).property.2 x (sdiff_subset hx) y (sdiff_subset hy)
  let u := isolateTriple p hp hs
  have hu : c u ≠ i := hc _ (onBase s) (disjoint_isolateTriple disjoint_sdiff_self_left)
  obtain ⟨t, ht, htc⟩ := hsat i (c u) hu
  exact hc u (onBase t) (disjoint_isolateTriple (ht.mono_left sdiff_subset)) htc.symm

end StableKneserK3

