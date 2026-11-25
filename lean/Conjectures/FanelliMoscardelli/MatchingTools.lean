import Conjectures.Roommates
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace FanelliMoscardelli

variable {V : Type*} [DecidableEq V]

/-- An involution restricted to a finite set, with an assignment constraint on that set. -/
def Pairs (S : Finset V) (E : V → V → Prop) : Prop :=
  ∃ f : V → V, ∀ i ∈ S, f i ∈ S ∧ f (f i) = i ∧ E i (f i)

namespace Pairs
variable {S T : Finset V} {E D : V → V → Prop} {a b : V}

theorem empty : Pairs ∅ E := ⟨id, by simp⟩

theorem single (h : E a a) : Pairs {a} E := ⟨id, by simpa using h⟩

theorem pair (h : E a b) (h' : E b a) : Pairs {a,b} E := by
  refine ⟨Equiv.swap a b, ?_⟩
  simp [h, h']

theorem mono (h : Pairs S E) (hd : ∀ i ∈ S, ∀ j ∈ S, E i j → D i j) : Pairs S D := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun i hi ↦ ⟨(hf i hi).1, (hf i hi).2.1, hd i hi _ (hf i hi).1 (hf i hi).2.2⟩⟩

theorem union (hs : Pairs S E) (ht : Pairs T E) (hd : Disjoint S T) : Pairs (S ∪ T) E := by
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := ht
  rw [Finset.disjoint_left] at hd
  refine ⟨fun i ↦ if i ∈ S then f i else g i, ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · simpa [hi, (hf _ hi).1] using (hf i hi).2
  · have hi' : i ∉ S := fun h ↦ hd h hi
    have hg' : g i ∉ S := fun h ↦ hd h (hg i hi).1
    simp [hi', hg', (hg i hi).1, (hg i hi).2]

theorem sdiff (h : Pairs S E) (hT : ∀ i ∈ T, ∀ j ∈ S, E i j → j ∈ T) :
    Pairs (S \ T) E := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun i hi ↦ ?_⟩
  obtain ⟨his, hit⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨hfs, hff, he⟩ := hf i his
  have : f i ∉ T := by
    intro ht
    exact hit (hff ▸ hT _ ht _ (hf _ hfs).1 (hf _ hfs).2.2)
  exact ⟨Finset.mem_sdiff.mpr ⟨hfs, this⟩, hff, he⟩

theorem card_even (h : Pairs S E) (hirr : ∀ i ∈ S, ¬ E i i) : Even S.card := by
  obtain ⟨f, hf⟩ := h
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    obtain ⟨hb, hba, he⟩ := hf a ha
    have hab : f a ≠ a := fun hh ↦ hirr a ha (by simpa only [hh] using he)
    let T := (S.erase a).erase (f a)
    have hsub : T ⊆ S := (Finset.erase_subset ..).trans (Finset.erase_subset ..)
    have hlt : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h ↦ by
      have : a ∈ T := h ▸ ha
      simp [T] at this⟩
    have hc : Even T.card := ih T hlt (fun i hi ↦ hirr i (hsub hi)) (by
      intro i hi
      obtain ⟨hfi, hii, hei⟩ := hf i (hsub hi)
      refine ⟨?_, hii, hei⟩
      simp only [T, Finset.mem_erase] at hi ⊢
      grind)
    have hc' : T.card + 2 = S.card := by
      dsimp [T]
      have h₁ := Finset.card_erase_add_one ha
      have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hab, hb⟩)
      omega
    obtain ⟨k,hk⟩ := hc
    exact ⟨k+1, by omega⟩

theorem of_even (h : Even S.card) : Pairs S (· ≠ ·) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact empty
    obtain ⟨k,hk⟩ := h
    have h₁ := Finset.card_erase_add_one ha
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (S.erase a).card by omega)
    let T := (S.erase a).erase b
    have h₂ := Finset.card_erase_add_one hb
    have hlt : T ⊂ S := (Finset.erase_ssubset hb).trans (Finset.erase_ssubset ha)
    have ht := ih T hlt ⟨k-1, by dsimp [T]; omega⟩
    have hba := (Finset.mem_erase.mp hb).1
    have heq : T ∪ {a,b} = S := by ext i; simp [T]; grind
    rw [← heq]
    exact ht.union (pair hba.symm hba) (by simp [Finset.disjoint_right, T])

theorem toMatching [Fintype V] (h : Pairs Finset.univ E) :
    ∃ μ : Roommates.Matching V, ∀ i, E i (μ.val i) := by
  obtain ⟨f, hf⟩ := h
  have hinv : Function.Involutive f := fun i ↦ (hf i (Finset.mem_univ i)).2.1
  exact ⟨⟨hinv.toPerm f, hinv⟩, fun i ↦ (hf i (Finset.mem_univ i)).2.2⟩

end Pairs
end FanelliMoscardelli
