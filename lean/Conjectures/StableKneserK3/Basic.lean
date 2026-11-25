import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

namespace StableKneserK3

open Finset

variable {V W : Type*}

def StableTriple (G : SimpleGraph V) (t : Finset V) : Prop :=
  t.card = 3 ∧ ∀ x ∈ t, ∀ y ∈ t, ¬ G.Adj x y

abbrev Triple (G : SimpleGraph V) := {t // StableTriple G t}

def IsProperColoring (G : SimpleGraph V) (q : ℕ) (c : Triple G → Fin q) : Prop :=
  ∀ s t, Disjoint s.val t.val → c s ≠ c t

def Colorable (G : SimpleGraph V) (q : ℕ) : Prop := ∃ c, IsProperColoring G q c

def K3Tight [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ Colorable G (Fintype.card V - 5) ∧ Colorable G (Fintype.card V - 4)

/-- Restrict a triple to an embedded ground graph when it lies in the image. -/
private noncomputable def pullTriple {H : SimpleGraph W} {G : SimpleGraph V}
    (f : W ↪ V) (hf : ∀ ⦃x y⦄, H.Adj x y → G.Adj (f x) (f y))
    (s : Triple G) (h : ∀ x ∈ s.val, x ∈ Set.range f) : Triple H := by
  classical
  refine ⟨s.val.preimage f f.injective.injOn, ?_, ?_⟩
  · rw [card_preimage, filter_true_of_mem h, s.property.1]
  · intro x hx y hy hxy
    exact s.property.2 _ (mem_preimage.mp hx) _ (mem_preimage.mp hy) (hf hxy)

/-- Extend a coloring from a subgraph by giving each outside vertex a star color. -/
theorem colorable_of_subgraph [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (f : W ↪ V) (hf : ∀ ⦃x y⦄, H.Adj x y → G.Adj (f x) (f y)) {q : ℕ}
    (hc : Colorable H q) : Colorable G (q + (Fintype.card V - Fintype.card W)) := by
  classical
  obtain ⟨c, hc⟩ := hc
  let Outside := {x : V // x ∉ Set.range f}
  let pick (s : Triple G) (h : ¬ ∀ x ∈ s.val, x ∈ Set.range f) :
      {x : Outside // x.val ∈ s.val} := by
    apply Classical.choice
    push Not at h
    obtain ⟨x, hx, hxr⟩ := h
    exact ⟨⟨⟨x, hxr⟩, hx⟩⟩
  let color (s : Triple G) : Fin q ⊕ Outside :=
    if h : ∀ x ∈ s.val, x ∈ Set.range f then .inl (c (pullTriple f hf s h))
    else .inr (pick s h).val
  have hn : Fintype.card (Fin q ⊕ Outside) = q + (Fintype.card V - Fintype.card W) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    congr 1
    exact (Fintype.card_subtype_compl (fun x => x ∈ Set.range f)).trans
      (congrArg (Fintype.card V - ·) (Fintype.card_range f))
  let e := Fintype.equivFinOfCardEq hn
  refine ⟨fun s => e (color s), fun s t hd heq => ?_⟩
  have hst := e.injective heq
  dsimp only [color] at hst
  split at hst <;> split at hst
  · exact hc _ _ (disjoint_preimage (hs := f.injective.injOn) (ht := f.injective.injOn) hd)
      (Sum.inl.inj hst)
  · contradiction
  · contradiction
  · rename_i hs ht
    exact disjoint_left.mp hd (pick s hs).property
      (by rw [Sum.inr.inj hst]; exact (pick t ht).property)

/-- Any five ground vertices support an intersecting family of triples. -/
theorem upper_bound [Fintype V] (G : SimpleGraph V) (hn : 5 ≤ Fintype.card V) :
    Colorable G (Fintype.card V - 4) := by
  classical
  obtain ⟨S, _, hS⟩ := exists_subset_card_eq (s := (univ : Finset V)) (n := 5) (by simpa using hn)
  have hcard : Fintype.card S = 5 := by simpa using hS
  have hc : Colorable (G.induce (S : Set V)) 1 := by
    refine ⟨fun _ => 0, fun s t hd => ?_⟩
    have hle := (s.val ∪ t.val).card_le_univ
    rw [card_union_of_disjoint hd, s.property.1, t.property.1] at hle
    exact False.elim (by change 6 ≤ Fintype.card S at hle; omega)
  have h := colorable_of_subgraph (Function.Embedding.subtype (· ∈ S))
    (G := G) (H := G.induce (S : Set V)) (fun _ _ h => h) hc
  convert h using 1
  change Fintype.card V - 4 = 1 + (Fintype.card V - Fintype.card S)
  omega

theorem tight_of_subgraph [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (f : W ↪ V) (hf : ∀ ⦃x y⦄, H.Adj x y → G.Adj (f x) (f y))
    (hn : 5 ≤ Fintype.card W) (ht : K3Tight G) : K3Tight H := by
  refine ⟨fun hc => ht.1 ?_, upper_bound H hn⟩
  have hle := Fintype.card_le_of_embedding f
  have h := colorable_of_subgraph f hf hc
  convert h using 1
  omega

end StableKneserK3
