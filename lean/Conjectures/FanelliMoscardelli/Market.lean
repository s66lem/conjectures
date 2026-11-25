import Conjectures.FanelliMoscardelli.MatchingTools

namespace FanelliMoscardelli
open Roommates
abbrev Agent (m : ℕ) := Fin (2*m+1)
abbrev Market (m : ℕ) := CompleteProfile (2*m+1)

namespace Market
variable {m : ℕ} (p : Market m)
local notation "V" => Agent m
local notation "r" => p.partnerRank

def choice (i : V) (k : Fin (2*m+1)) : V := (p.rank i).symm k
def mid (i : V) := choice p i ⟨m, by omega⟩
def first (i : V) := choice p i 0
def Edge (i j : V) : Prop := r i j ≤ m ∧ r j i ≤ m
def Solved := ∃ μ : Matching V, IsKStable ⊤ r m μ

@[grind =] theorem rank_mid (i : V) : r i (mid p i) = m+1 := by
  simp [mid, choice, CompleteProfile.partnerRank]
@[grind =] theorem rank_first (i : V) : r i (first p i) = 1 := by
  simp [first, choice, CompleteProfile.partnerRank]
theorem rank_inj (i : V) : Function.Injective (r i) := by
  intro j k h
  apply (p.rank i).injective
  exact Fin.ext (Nat.succ.inj h)
@[grind .] theorem rank_pos (i j : V) : 0 < r i j := Nat.zero_lt_succ _
@[grind .] theorem rank_other {i j : V} (h : j ≠ i) : r i j ≤ 2*m := by
  have hb := p.partnerRank_le i j
  have hn : r i j ≠ r i i := fun e ↦ h (rank_inj p i e)
  simp only [CompleteProfile.partnerRank_self] at hn
  omega
theorem mid_ne (hm : 0 < m) (i : V) : mid p i ≠ i := by
  intro h
  have := rank_mid p i
  rw [h, CompleteProfile.partnerRank_self] at this
  omega
theorem edge_symm {i j : V} (h : Edge p i j) : Edge p j i := h.symm
theorem edge_irrefl (i : V) : ¬Edge p i i := by simp [Edge]; omega

/-- A blocking pair outside the mutual-top graph must involve the single agent
and that agent's middle choice. -/
theorem criterion {D : V → V → Prop} {u : V} (h : Pairs Finset.univ D)
    (hs : ∀ i, D i i → i = u)
    (hg : ∀ i j k l, Edge p i j → D i k → D j l →
      r i k < r i j + m ∨ r j l < r j i + m)
    (hx : ∀ l, D (mid p u) l → r (mid p u) l < r (mid p u) u + m) : Solved p := by
  obtain ⟨μ, hμ⟩ := h.toMatching
  refine ⟨μ, fun i ↦ ?_, ?_⟩
  · by_cases hi : μ.val i = i
    · exact Or.inl hi
    · exact Or.inr ((SimpleGraph.top_adj ..).mpr (Ne.symm hi))
  intro i j hb
  obtain ⟨hij, _, hi, hj⟩ := hb
  have hm₁ := p.partnerRank_le i (μ.val i)
  have hm₂ := p.partnerRank_le j (μ.val j)
  by_cases he : Edge p i j
  · rcases hg i j _ _ he (hμ _) (hμ _) with h | h <;> omega
  have extra : ∀ a b, r a b > m → r a b + m ≤ r a (μ.val a) →
      a = u ∧ b = mid p u := by
    intro a b hgt hbl
    have hbound := p.partnerRank_le a (μ.val a)
    have heq : μ.val a = a := by
      by_contra hn
      have := rank_other p hn
      omega
    have hau := hs a (by simpa only [heq] using hμ a)
    subst a
    exact ⟨rfl, rank_inj p _ (by rw [rank_mid]; omega)⟩
  unfold Edge at he
  push Not at he
  by_cases hi' : m < r i j
  · obtain ⟨rfl, rfl⟩ := extra i j hi' hi
    have := hx _ (hμ _)
    omega
  · obtain ⟨rfl, e⟩ := extra j i (he (by omega)) hj
    subst i
    have := hx _ (hμ _)
    omega

/-- Cardinality of an initial segment of an agent's preference order. -/
theorem card_choices (i : V) {k : ℕ} (hk : k ≤ 2*m+1) :
    (Finset.univ.filter (fun j ↦ r i j ≤ k)).card = k := by
  classical
  let e : {j : V // r i j ≤ k} ≃ Fin k :=
    { toFun := fun j ↦ ⟨(p.rank i j).val, j.property⟩
      invFun := fun t ↦ ⟨choice p i ⟨t.val, lt_of_lt_of_le t.isLt hk⟩, by
        simp [choice, CompleteProfile.partnerRank]⟩
      left_inv := fun j ↦ by simp [choice]
      right_inv := fun t ↦ by simp [choice] }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

end Market
end FanelliMoscardelli
