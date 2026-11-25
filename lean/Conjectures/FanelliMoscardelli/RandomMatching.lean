import Conjectures.FanelliMoscardelli.Component

namespace FanelliMoscardelli.Market
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m}
local notation "V" => Agent m
local notation "E" => Edge p
local notation "J" => active p

/-- An alternating switch on a perfect matching leaves two endpoints; random
matchability forces the endpoints to be adjacent. -/
structure Frame (p : Market m) where
  g : V → V
  inv : Function.Involutive g
  adj : ∀ i ∈ active p, Edge p i (g i)
  finish : ∀ {S : Finset V}, Pairs S (Edge p) → Pairs (active p \ S) (Edge p)

theorem frame (hm : 0 < m) (bad : ¬Solved p) : Nonempty (Frame p) := by
  have h := residual_extend hm bad (S := ∅) (p := p) Pairs.empty
  rw [sdiff_empty] at h
  obtain ⟨g,hg⟩ := h
  classical
  refine ⟨⟨fun i ↦ if i ∈ J then g i else i, ?_, ?_, residual_extend hm bad⟩⟩
  · intro i
    by_cases hi : i ∈ J <;> simp [hi, (fun h : i ∈ J ↦ (hg i h).1), (fun h : i ∈ J ↦ (hg i h).2.1)]
  · intro i hi
    simpa [hi] using (hg i hi).2.2

namespace Frame
variable (F : Frame p)
local notation "g" => F.g

@[grind =] theorem twice (i : V) : g (g i) = i := F.inv i
theorem g_mem {i : V} (hi : i ∈ J) : g i ∈ J := mem_active.mpr ⟨i,edge_symm p (F.adj _ hi)⟩
theorem g_ne {i : V} (hi : i ∈ J) : g i ≠ i := by
  intro eq
  have he := F.adj i hi
  rw [eq] at he
  exact edge_irrefl p i he

private theorem close {S : Finset V} {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hS : S ⊆ J) (hg : ∀ i ∈ S, g i ∈ S)
    (hp : Pairs (S \ {a,b}) E) : E a b := by
  have hr : Pairs (J \ S) E := by
    refine ⟨g, fun i hi ↦ ?_⟩
    obtain ⟨hij,his⟩ := mem_sdiff.mp hi
    refine ⟨mem_sdiff.mpr ⟨F.g_mem hij, fun h ↦ his (F.inv i ▸ hg _ h)⟩,F.inv i,F.adj _ hij⟩
  have h := F.finish (hr.union hp (by simp [Finset.disjoint_left]; grind))
  have eq : J \ ((J \ S) ∪ (S \ {a,b})) = {a,b} := by
    ext i; simp only [mem_sdiff,mem_union,mem_insert,mem_singleton]; have := hS ha; have := hS hb; grind
  rw [eq] at h
  obtain ⟨t,ht⟩ := h
  obtain ⟨ht',_,he⟩ := ht a (by simp)
  simp only [mem_insert, mem_singleton] at ht'
  rcases ht' with e | e
  · rw [e] at he; exact (edge_irrefl p a he).elim
  · rwa [e] at he

theorem flip {a b : V} (he : E a b) : E (g a) (g b) := by
  have ha := mem_active.mpr ⟨b,he⟩
  have hb := mem_active.mpr ⟨a,edge_symm p he⟩
  have hab : a ≠ b := fun e ↦ edge_irrefl p b (e ▸ he)
  by_cases h : g a = b
  · rw [← h, F.inv]; rw [h]; exact edge_symm p he
  have h₁ := F.g_ne ha
  have h₂ := F.g_ne hb
  have hn : g b ≠ a := fun e ↦ h ((congrArg g e).symm.trans (F.inv b))
  let S : Finset V := {a,g a,b,g b}
  have eq : S \ {g a,g b} = {a,b} := by ext; simp [S]; grind
  apply F.close (S := S) (by simp [S]) (by simp [S])
    (by have := F.g_mem ha; have := F.g_mem hb; intro i; simp only [S,mem_insert,mem_singleton]; grind) (by simp [S,F.twice])
  rw [eq]
  exact Pairs.pair he (edge_symm p he)

/-- On the active vertices, two vertices are in the same component exactly
when the first is adjacent to an endpoint of the second's matched pair. -/
def Related (a b : V) := E a b ∨ E a (g b)

theorem self {a : V} (ha : a ∈ J) : F.Related a a := Or.inr (F.adj a ha)
theorem symm {a b : V} (h : F.Related a b) : F.Related b a := by
  rcases h with h|h
  · exact Or.inl (edge_symm p h)
  · exact Or.inr (by simpa [F.twice] using edge_symm p (F.flip h))
@[simp] theorem related_g (a b : V) : F.Related a (g b) ↔ F.Related a b := by
  simp [Related,F.twice,or_comm]

private theorem chain {a b c : V} (h₁ : E a b) (h₂ : E (g b) c) : F.Related a c := by
  have ha := mem_active.mpr ⟨b,h₁⟩
  have hb := mem_active.mpr ⟨a,edge_symm p h₁⟩
  have hc := mem_active.mpr ⟨g b,edge_symm p h₂⟩
  by_contra hn
  have na := F.g_ne ha
  have nb := F.g_ne hb
  have nc := F.g_ne hc
  have hac : a ≠ c := by intro e; subst c; exact hn (F.self ha)
  have hac' : a ≠ g c := by
    intro e; apply hn; left; rw [e]; exact edge_symm p (F.adj c hc)
  have hab : a ≠ b := fun e ↦ edge_irrefl p b (e ▸ h₁)
  have hbc : g b ≠ c := fun e ↦ edge_irrefl p c (e ▸ h₂)
  by_cases hab' : a = g b
  · exact hn (Or.inl (hab' ▸ h₂))
  by_cases hbc' : b = c
  · exact hn (Or.inl (hbc' ▸ h₁))
  have := F.inv a
  have := F.inv b
  have := F.inv c
  let S : Finset V := {a,g a,b,g b,c,g c}
  have eq : S \ {g a,g c} = {a,b} ∪ {g b,c} := by ext; simp [S]; grind
  have hclose : E (g a) (g c) := by
    apply F.close (S := S) (by simp [S]) (by simp [S])
      (by have := F.g_mem ha; have := F.g_mem hb; have := F.g_mem hc; intro i; simp only [S,mem_insert,mem_singleton]; grind) (by simp [S,F.twice])
    rw [eq]
    exact (Pairs.pair h₁ (edge_symm p h₁)).union (Pairs.pair h₂ (edge_symm p h₂))
      (by simp [Finset.disjoint_right]; grind)
  exact hn (Or.inl (by simpa [F.twice] using F.flip hclose))

theorem trans {a b c : V} (h₁ : F.Related a b) (h₂ : F.Related b c) : F.Related a c := by
  have go : ∀ {i j k}, E i j → E j k → F.Related i k := by
    intro i j k hij hjk
    exact (F.related_g i k).mp (F.chain hij (F.flip hjk))
  rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂
  · exact go h₁ h₂
  · exact (F.related_g ..).mp (go h₁ h₂)
  · exact F.chain h₁ (by simpa [F.twice] using h₂)
  · exact (F.related_g ..).mp (F.chain h₁ (by simpa [F.twice] using h₂))

/-- At least half of a component consists of neighbors of any of its vertices. -/
theorem size_le_twice_degree (i : V) :
    ((active p).filter (F.Related i)).card ≤ 2 * ((active p).filter (E i)).card := by
  classical
  let N := (active p).filter (E i)
  have hsub : (active p).filter (F.Related i) ⊆ N ∪ N.image g := by
    intro j hj
    obtain ⟨hj, h|h⟩ := mem_filter.mp hj
    · exact mem_union_left _ (mem_filter.mpr ⟨hj,h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨g j, mem_filter.mpr ⟨F.g_mem hj,h⟩,F.inv _⟩)
  have h := (card_le_card hsub).trans (card_union_le ..)
  have h' : (N.image g).card ≤ N.card := card_image_le
  change _ ≤ 2*N.card
  omega

end Frame
end FanelliMoscardelli.Market
